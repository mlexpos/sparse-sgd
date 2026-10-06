"""Bigram softmax language model trained with one global (eta, beta), for the momentum-vs-batch-size test.

Model: logits(y | x) = <E[x], W[y]>, E, W in R^{V x d}, untied, no bias; loss = cross-entropy of the next token.
Data: each step draws B independent (x, y) pairs from the empirical joint P(x, y) of build_bigram_data.py.
Optimizer (the paper's convention): m <- beta m + (1 - beta) g,  theta <- theta - eta m, constant eta, for E and W.
A whole (eta, beta) grid trains at once: configs are vmapped and their axis is sharded across local devices; every config
sees the same batches and the same initialization (common random numbers); the seed changes both.
Evaluation is exact: L = -sum_{x,y} P(x, y) log softmax(E W^T)[x, y], plus the same loss restricted to input-rank bins.

--mode reference: full-batch Adam on the exact loss, to estimate the best achievable loss L_ref (and per-bin values).
"""
import argparse
import json
import os
import time

import numpy as np


def load_data(path):
    z = np.load(path)
    V = int(z["vocab"])
    pairs = z["pairs"].astype(np.int64)
    counts = z["counts"].astype(np.int64)
    px = z["px"]
    order = np.argsort(-px, kind="stable")
    rank = np.empty(V, dtype=np.int64)
    rank[order] = np.arange(V)
    edges = np.unique(np.round(np.logspace(0, np.log10(V), 9)).astype(int)) - 1
    edges[-1] = V
    bin_of = np.searchsorted(edges[1:], rank, side="right")
    return dict(V=V, pairs=pairs, counts=counts, px=px, bin_of=bin_of, n_bins=int(bin_of.max()) + 1)


def schedule_factors(name, T, warmup_frac=0.0, cooldown_frac=0.2):
    """Warmup factor w(t) and decay factor d(t) for t = 0..T-1; the learning rate is eta_peak * w * d."""
    t = np.arange(T, dtype=np.float64)
    w = np.minimum(1.0, (t + 1) / max(1.0, warmup_frac * T)) if warmup_frac > 0 else np.ones(T)
    c0 = (1 - cooldown_frac) * T
    if name == "constant":
        dcy = np.ones(T)
    elif name == "cosine":
        dcy = 0.5 * (1 + np.cos(np.pi * t / T))
    elif name == "wsd_linear":
        dcy = np.where(t < c0, 1.0, (T - t) / (cooldown_frac * T))
    elif name == "wsd_sqrt":
        dcy = np.where(t < c0, 1.0, 1 - np.sqrt(np.clip((t - c0) / (cooldown_frac * T), 0, 1)))
    elif name == "step":
        dcy = 0.5 ** np.floor(8 * t / T)
    elif name == "inv_t":
        dcy = 1 / (1 + t / (T / 20))
    else:
        raise ValueError(name)
    return w.astype(np.float32), np.maximum(dcy, 0).astype(np.float32)


def build(data, d, B, chunk, beta_cap=0.999):
    import jax
    import jax.numpy as jnp
    V = data["V"]
    total = int(data["counts"].sum())
    assert total < 2**31 - 1
    cum = jnp.asarray(np.cumsum(data["counts"]), dtype=jnp.int32)
    pairs = jnp.asarray(data["pairs"], dtype=jnp.int32)
    w_pair = jnp.asarray(data["counts"] / total, dtype=jnp.float32)
    bin_of = jnp.asarray(data["bin_of"], dtype=jnp.int32)
    px_bin = np.bincount(data["bin_of"], weights=data["px"], minlength=data["n_bins"])
    px_bin = jnp.asarray(px_bin, dtype=jnp.float32)
    n_chunks = max(1, B // chunk)
    cb = B // n_chunks
    assert cb * n_chunks == B, (B, chunk)

    def sample(key):
        u = jax.random.randint(key, (B,), 0, total, dtype=cum.dtype)
        k = jnp.searchsorted(cum, u, side="right")
        f = pairs[k]
        return f // V, f % V

    def loss_on(params, x, y):
        E, W = params
        h = E[x]
        logits = h @ W.T
        return jnp.mean(jax.nn.logsumexp(logits, axis=-1) - jnp.sum(h * W[y], axis=-1))

    grad_on = jax.grad(loss_on)

    def grad_batch(params, x, y):
        if n_chunks == 1:
            return grad_on(params, x, y)
        xs, ys = x.reshape(n_chunks, cb), y.reshape(n_chunks, cb)

        def body(acc, xy):
            g = grad_on(params, xy[0], xy[1])
            return jax.tree_util.tree_map(lambda a, b: a + b / n_chunks, acc, g), None

        zero = jax.tree_util.tree_map(jnp.zeros_like, params)
        return jax.lax.scan(body, zero, (xs, ys))[0]

    def step_one(params, mom, eta_peak, beta_peak, co, w_t, d_t, x, y):
        eta = eta_peak * w_t * d_t
        beta = jnp.where(co > 0, jnp.minimum(1 - (1 - beta_peak) * d_t, beta_cap), beta_peak)
        g = grad_batch(params, x, y)
        mom = jax.tree_util.tree_map(lambda m, gi: beta * m + (1 - beta) * gi, mom, g)
        params = jax.tree_util.tree_map(lambda p, m: p - eta * m, params, mom)
        return params, mom

    step_cfg = jax.vmap(step_one, in_axes=(0, 0, 0, 0, 0, None, None, None, None))

    def segment(params, mom, etas, betas, cos, key, ws, ds, n_steps):
        def body(carry, xs):
            p, m = carry
            k, w_t, d_t = xs
            x, y = sample(k)
            return step_cfg(p, m, etas, betas, cos, w_t, d_t, x, y), None
        keys = jax.random.split(key, n_steps)
        (params, mom), _ = jax.lax.scan(body, (params, mom), (keys, ws, ds))
        return params, mom

    def eval_one(params):
        E, W = params
        logq = jax.nn.log_softmax(E @ W.T, axis=-1).reshape(-1)
        nll = -logq[pairs] * w_pair
        total_loss = jnp.sum(nll)
        per_bin = jax.ops.segment_sum(nll, bin_of[pairs // V], num_segments=px_bin.shape[0]) / px_bin
        return total_loss, per_bin

    eval_cfg = jax.vmap(eval_one)
    return segment, eval_cfg, sample


def run_sweep(args):
    import jax
    import jax.numpy as jnp
    data = load_data(args.data)
    V, d, B = data["V"], args.d, args.batch_size
    etas = np.array([float(e) for e in args.etas.split(",")])
    betas = np.array([float(b) for b in args.betas.split(",")])
    scale = (lambda b: (1 + b) / (1 - b)) if args.momentum_scaled_etas else (lambda b: 1.0)
    modes = [m.strip() for m in args.beta_modes.split(",")]
    grid = [(float(e * scale(b)), float(b), 1 if mode == "co" else 0) for mode in modes for b in betas for e in etas]
    nd = jax.local_device_count()
    G = len(grid)
    Gp = -(-G // nd) * nd
    grid_p = grid + [grid[-1]] * (Gp - G)
    from jax.sharding import Mesh, NamedSharding, PartitionSpec as P
    mesh = Mesh(np.array(jax.devices()), ("cfg",))
    shard = NamedSharding(mesh, P("cfg"))
    eta_arr = jax.device_put(np.array([g[0] for g in grid_p], np.float32), shard)
    beta_arr = jax.device_put(np.array([g[1] for g in grid_p], np.float32), shard)
    co_arr = jax.device_put(np.array([g[2] for g in grid_p], np.float32), shard)
    segment, eval_cfg, _ = build(data, d, B, args.chunk, args.beta_cap)
    w_all, d_all = schedule_factors(args.schedule, args.num_steps, args.warmup_frac, args.cooldown_frac)
    key = jax.random.PRNGKey(args.seed)
    k_init, k_data = jax.random.split(key)
    kE, kW = jax.random.split(k_init)
    E0 = jax.random.normal(kE, (V, d)) / np.sqrt(d)
    W0 = jax.random.normal(kW, (V, d)) / np.sqrt(d)
    rep = lambda a: jax.device_put(jnp.broadcast_to(a, (Gp,) + a.shape), shard)  # noqa: E731
    params = (rep(E0), rep(W0))
    mom = (rep(jnp.zeros_like(E0)), rep(jnp.zeros_like(W0)))
    seg_len = max(1, args.num_steps // args.n_evals)
    n_seg = args.num_steps // seg_len
    p_segment = jax.jit(lambda p, m, e, b, c, k, ws, ds: segment(p, m, e, b, c, k, ws, ds, seg_len),
                        out_shardings=((shard, shard), (shard, shard)))
    p_eval = jax.jit(eval_cfg)
    eval_steps, losses, bins = [], [], []

    def do_eval(step, params):
        tl, pb = p_eval(params)
        eval_steps.append(step)
        losses.append(np.asarray(tl).reshape(-1)[:G])
        bins.append(np.asarray(pb)[:G])

    t0 = time.time()
    do_eval(0, params)
    keys = jax.random.split(k_data, n_seg)
    for s in range(n_seg):
        sl = slice(s * seg_len, (s + 1) * seg_len)
        params, mom = p_segment(params, mom, eta_arr, beta_arr, co_arr, keys[s], jnp.asarray(w_all[sl]), jnp.asarray(d_all[sl]))
        do_eval((s + 1) * seg_len, params)
    wall = time.time() - t0
    os.makedirs(args.results_dir, exist_ok=True)
    np.savez_compressed(os.path.join(args.results_dir, "trajectories.npz"), steps=np.array(eval_steps),
                        loss=np.array(losses).T, bin_loss=np.transpose(np.array(bins), (1, 0, 2)),
                        etas=np.array([g[0] for g in grid]), betas=np.array([g[1] for g in grid]),
                        co=np.array([g[2] for g in grid]), schedule=args.schedule, warmup_frac=args.warmup_frac,
                        cooldown_frac=args.cooldown_frac, beta_cap=args.beta_cap,
                        batch_size=B, d=d, seed=args.seed, V=V)
    final = np.array(losses[-1])
    best = int(np.nanargmin(np.where(np.isfinite(final), final, np.inf)))
    metrics = {"status": "done", "final_step": int(eval_steps[-1]), "final_loss": float(final[best]),
               "best_eta": float(grid[best][0]), "best_beta": float(grid[best][1]), "best_co": int(grid[best][2]),
               "schedule": args.schedule, "n_configs": G,
               "n_diverged": int(np.sum(~np.isfinite(final))), "wall_time_sec": wall, "num_devices": nd,
               "device_info": str(jax.devices()[0].device_kind)}
    with open(os.path.join(args.results_dir, "summary.json"), "w") as f:
        json.dump(metrics, f, indent=2)
    print(json.dumps(metrics))


def run_reference(args):
    import jax
    import jax.numpy as jnp
    data = load_data(args.data)
    V, d = data["V"], args.d
    _, eval_cfg, _ = build(data, d, 1, 1)
    pairs = jnp.asarray(data["pairs"], dtype=jnp.int32)
    w_pair = jnp.asarray(data["counts"] / data["counts"].sum(), dtype=jnp.float32)

    def loss(params):
        E, W = params
        logq = jax.nn.log_softmax(E @ W.T, axis=-1).reshape(-1)
        return -jnp.sum(logq[pairs] * w_pair)

    key = jax.random.PRNGKey(args.seed)
    kE, kW = jax.random.split(key)
    params = (jax.random.normal(kE, (V, d)) / np.sqrt(d), jax.random.normal(kW, (V, d)) / np.sqrt(d))
    m = jax.tree_util.tree_map(jnp.zeros_like, params)
    v = jax.tree_util.tree_map(jnp.zeros_like, params)

    @jax.jit
    def adam(params, m, v, t, lr):
        g = jax.grad(loss)(params)
        m = jax.tree_util.tree_map(lambda a, b: 0.9 * a + 0.1 * b, m, g)
        v = jax.tree_util.tree_map(lambda a, b: 0.999 * a + 0.001 * b * b, v, g)
        mh = jax.tree_util.tree_map(lambda a: a / (1 - 0.9 ** t), m)
        vh = jax.tree_util.tree_map(lambda a: a / (1 - 0.999 ** t), v)
        params = jax.tree_util.tree_map(lambda p, a, b: p - lr * a / (jnp.sqrt(b) + 1e-9), params, mh, vh)
        return params, m, v

    hist = []
    for t in range(1, args.num_steps + 1):
        lr = args.ref_lr * 0.5 * (1 + np.cos(np.pi * t / args.num_steps))
        params, m, v = adam(params, m, v, t, lr)
        if t % max(1, args.num_steps // 50) == 0 or t == args.num_steps:
            hist.append((t, float(loss(params))))
    tl, pb = eval_cfg(jax.tree_util.tree_map(lambda a: a[None], params))
    os.makedirs(args.results_dir, exist_ok=True)
    np.savez_compressed(os.path.join(args.results_dir, "reference.npz"), loss=float(tl[0]), bin_loss=np.asarray(pb[0]),
                        hist=np.array(hist), d=d, V=V, seed=args.seed)
    metrics = {"status": "done", "final_step": args.num_steps, "final_loss": float(tl[0])}
    print(json.dumps(metrics), hist[-3:])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["sweep", "reference"], default="sweep")
    ap.add_argument("--data", default="data/bigram_v4096.npz")
    ap.add_argument("--d", type=int, default=64)
    ap.add_argument("--batch-size", type=int, default=1024)
    ap.add_argument("--chunk", type=int, default=4096)
    ap.add_argument("--num-steps", type=int, default=1000)
    ap.add_argument("--n-evals", type=int, default=400)
    ap.add_argument("--etas", default="0.1,1.0")
    ap.add_argument("--betas", default="0.0,0.9")
    ap.add_argument("--schedule", default="constant",
                    choices=["constant", "cosine", "wsd_linear", "wsd_sqrt", "step", "inv_t"])
    ap.add_argument("--warmup-frac", type=float, default=0.0)
    ap.add_argument("--cooldown-frac", type=float, default=0.2)
    ap.add_argument("--beta-modes", default="fixed", help="comma list of fixed, co (1 - beta co-scheduled with the decay)")
    ap.add_argument("--beta-cap", type=float, default=0.999)
    ap.add_argument("--momentum-scaled-etas", type=int, default=1,
                    help="multiply each eta by (1+beta)/(1-beta), the growth of the curvature ceiling with momentum")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--ref-lr", type=float, default=0.03)
    ap.add_argument("--results-dir", default="results")
    args = ap.parse_args()
    (run_reference if args.mode == "reference" else run_sweep)(args)


if __name__ == "__main__":
    main()
