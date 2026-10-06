"""Bigram data for the momentum-vs-batch-size experiment.

Tokenizes the wikitext-103 train split with the Pythia tokenizer, keeps the V most frequent tokens, and counts
consecutive (input, next) pairs in which both tokens are kept. The joint distribution of kept pairs, P(x, y), is the
data distribution of the experiment: each batch is B independent draws from it, and the population loss is
-sum_{x,y} P(x, y) log q(y | x), computed exactly. Saved: the kept token ids (by frequency), the nonzero pairs as flat
indices x * V + y (local indices), their counts, and the input marginal p_x.
"""
import argparse
import os

import numpy as np


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--vocab", type=int, default=4096)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "data"))
    args = ap.parse_args()
    from datasets import load_dataset
    from transformers import AutoTokenizer
    tok = AutoTokenizer.from_pretrained("EleutherAI/pythia-70m")
    ds = load_dataset("wikitext", "wikitext-103-raw-v1", split="train")
    lines = [t for t in ds["text"] if t.strip()]
    ids = []
    step = 20000
    for i in range(0, len(lines), step):
        enc = tok(lines[i:i + step])["input_ids"]
        for e in enc:
            ids.extend(e)
    ids = np.asarray(ids, dtype=np.int64)
    counts = np.bincount(ids)
    keep = np.argsort(-counts, kind="stable")[: args.vocab]
    local = np.full(counts.size, -1, dtype=np.int64)
    local[keep] = np.arange(args.vocab)
    x, y = local[ids[:-1]], local[ids[1:]]
    ok = (x >= 0) & (y >= 0)
    flat = x[ok] * args.vocab + y[ok]
    pairs, pair_counts = np.unique(flat, return_counts=True)
    px = np.bincount(pairs // args.vocab, weights=pair_counts, minlength=args.vocab) / pair_counts.sum()
    os.makedirs(args.out, exist_ok=True)
    path = os.path.join(args.out, f"bigram_v{args.vocab}.npz")
    np.savez_compressed(path, token_ids=keep, pairs=pairs.astype(np.int32), counts=pair_counts.astype(np.int64),
                        px=px, vocab=args.vocab, n_tokens=ids.size, n_pairs_kept=int(pair_counts.sum()))
    order = np.sort(px)[::-1]
    print(f"tokens {ids.size:,}; kept pairs {pair_counts.sum():,} ({pair_counts.sum() / (ids.size - 1):.1%}); "
          f"nonzero pairs {pairs.size:,}; p_max {order[0]:.4g}, p_min {order[-1]:.3g}, "
          f"B_x(d=64) = {66 / (order[0] - order[-1]):.4g}; saved {path} ({os.path.getsize(path) / 1e6:.1f} MB)")


if __name__ == "__main__":
    main()
