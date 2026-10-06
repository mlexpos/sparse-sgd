"""Analyze the sweep of sweep_bigram.py (bigram softmax, one global (eta, beta)): tuned momentum and its speedup vs batch size.

For every task (batch size B, seed) and config (eta, beta): steps to reach a loss target L_ref + f (L0 - L_ref), with
L_ref the best reference loss and L0 = ln V the loss at initialization; linear interpolation between evaluations;
targets never reached count as censored (infinite). Per B and seed: S_beta = min over eta, tuned S* = min over beta,
beta* = argmin, speedup = S_0 / S*. Predicted crossover B_x = (d_eff + 2)/p_max with d_eff + 2 from the SGD ceiling.
"""
import glob
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "results")
FRACS = (0.3, 0.15, 0.08, 0.04)


def steps_to(steps, loss, target):
    ok = np.isfinite(loss) & (loss <= target)
    if not ok.any():
        return np.inf
    k = int(np.argmax(ok))
    if k == 0:
        return float(steps[0])
    l0, l1 = loss[k - 1], loss[k]
    if not np.isfinite(l0) or l0 == l1:
        return float(steps[k])
    return float(steps[k - 1] + (steps[k] - steps[k - 1]) * (l0 - target) / (l0 - l1))


def load():
    tasks, refs = [], []
    for d in sorted(glob.glob(os.path.join(RES, "*"))):
        cfg = json.load(open(os.path.join(d, "config.json"))) if os.path.exists(os.path.join(d, "config.json")) else {}
        if os.path.exists(os.path.join(d, "trajectories.npz")):
            tasks.append(dict(np.load(os.path.join(d, "trajectories.npz"))))
        elif os.path.exists(os.path.join(d, "reference.npz")):
            refs.append(dict(np.load(os.path.join(d, "reference.npz"))))
        elif cfg:
            print("no output yet:", os.path.basename(d), cfg.get("name", cfg.get("mode")), file=sys.stderr)
    return tasks, refs


def main():
    tasks, refs = load()
    V = int(tasks[0]["V"])
    L0 = np.log(V)
    L_ref = min(float(r["loss"]) for r in refs) if refs else min(np.nanmin(t["loss"]) for t in tasks)
    best_seen = min(np.nanmin(np.where(np.isfinite(t["loss"]), t["loss"], np.inf)) for t in tasks)
    print(f"V={V}, L0=ln V={L0:.4f}, L_ref={L_ref:.4f} (from {len(refs)} reference runs), best loss seen in sweeps {best_seen:.4f}")
    px = np.load(os.path.join(HERE, "data", "bigram_v4096.npz"))["px"]
    rows = []
    for t in tasks:
        B, seed = int(t["batch_size"]), int(t["seed"])
        etas, betas, steps, loss = t["etas"], t["betas"], t["steps"], t["loss"]
        for f in FRACS:
            target = L_ref + f * (L0 - L_ref)
            S = np.array([steps_to(steps, loss[g], target) for g in range(len(etas))])
            per_beta = {}
            for b in np.unique(betas):
                k = betas == b
                j = int(np.argmin(S[k]))
                per_beta[float(b)] = (S[k][j], float(etas[k][j]))
            S0 = per_beta[0.0][0]
            bstar = min(per_beta, key=lambda b: per_beta[b][0])
            rows.append(dict(B=B, seed=seed, f=f, S0=S0, Sstar=per_beta[bstar][0], beta_star=bstar,
                             eta_star=per_beta[bstar][1], eta0=per_beta[0.0][1], per_beta=per_beta))
    np.save(os.path.join(HERE, "analysis.npy"), rows, allow_pickle=True)
    for f in FRACS:
        print(f"\n--- target: excess loss fraction {f} (L = {L_ref + f * (L0 - L_ref):.4f})")
        print(f"{'B':>6} {'seed':>4} | {'S_SGD':>10} {'eta_SGD':>8} | {'S*':>10} {'beta*':>6} {'eta*':>8} | {'speedup':>8}")
        for r in sorted([r for r in rows if r["f"] == f], key=lambda r: (r["B"], r["seed"])):
            sp = r["S0"] / r["Sstar"] if np.isfinite(r["S0"]) and np.isfinite(r["Sstar"]) else np.nan
            print(f"{r['B']:6d} {r['seed']:4d} | {r['S0']:10.4g} {r['eta0']:8.3g} | {r['Sstar']:10.4g} {r['beta_star']:6.3g} "
                  f"{r['eta_star']:8.3g} | {sp:8.3f}")
    print(f"\npredicted B_x = (d_eff + 2)/p_max with d_eff + 2 ~ 2.7 and p_max = {px.max():.4f}: {2.7 / px.max():.1f} tokens")


if __name__ == "__main__":
    main()
