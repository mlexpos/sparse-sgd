"""Sweep: tuned momentum vs batch size in a bigram softmax model.

One run = one (batch size, seed); inside it the whole (eta, beta) grid trains at once on the same batches, sharded
across the local devices (bigram_momentum.py). Two reference runs use full-batch Adam on the exact loss to estimate
the best achievable loss. Runs execute one after another, results go to results/<run name>/, and finished runs are
skipped on a restart. Then run analyze_bigram.py.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data", "bigram_v4096.npz")
BATCHES = (1, 2, 4, 8, 16, 32, 64, 128, 256, 1024, 4096, 16384)
SEEDS = (0, 1)
TOKENS, MIN_STEPS, MAX_STEPS = 4e7, 20_000, 10_000_000
ETAS = "0.0625,0.125,0.25,0.5,1,2,4,8,16,32,64,128,256"
BETAS = "0.0,0.5,0.8,0.9,0.95,0.98,0.99,0.995"


def steps_for(B):
    return int(min(MAX_STEPS, max(MIN_STEPS, TOKENS / B)))


def run(name, **flags):
    out = os.path.join(HERE, "results", name)
    if any(os.path.exists(os.path.join(out, f)) for f in ("trajectories.npz", "reference.npz")):
        print("done, skipping:", name)
        return
    cmd = [sys.executable, os.path.join(HERE, "bigram_momentum.py"), "--data", DATA, "--d", "64", "--n-evals", "400",
           "--results-dir", out]
    for k, v in flags.items():
        cmd += ["--" + k.replace("_", "-"), str(v)]
    print(" ".join(cmd), flush=True)
    subprocess.run(cmd, check=True)


def main():
    for B in BATCHES:
        for seed in SEEDS:
            run(f"sweep_B{B}_s{seed}", mode="sweep", batch_size=B, chunk=min(B, 1024), num_steps=steps_for(B),
                seed=seed, etas=ETAS, betas=BETAS, momentum_scaled_etas=1)
    for lr in (0.01, 0.03):
        run(f"reference_lr{lr}", mode="reference", batch_size=1, chunk=1, num_steps=200_000, seed=0, ref_lr=lr)


if __name__ == "__main__":
    main()
