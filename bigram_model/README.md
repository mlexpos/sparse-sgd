# Bigram experiment

Code for the bigram experiment. The model is a bigram softmax model with
an embedding vector and a readout vector of dimension 64 for each of the 4096 most frequent tokens, so that the logit
of token y after token x is the inner product of their vectors. All parameters are trained with one learning rate and
one momentum β, and the sweep measures how many steps the tuned optimizer needs at each batch size.

Requirements: Python 3, NumPy and JAX. Building the data also needs the HuggingFace `datasets` and `transformers`
packages.

1. `python build_bigram_data.py` tokenizes the WikiText-103 training split with the Pythia tokenizer, keeps the 4096
   most frequent tokens, and writes the counts of consecutive token pairs to `data/bigram_v4096.npz`.
2. `python sweep_bigram.py` trains 12 batch sizes from 1 to 16384 with 2 seeds each. Each run trains all 104
   combinations of 13 learning rates and 8 values of β at once, sharded across the local devices. Two full-batch Adam
   runs then estimate the best achievable loss. Results go to `results/<run name>/`, and finished runs are skipped if
   the script is restarted.
3. `python analyze_bigram.py` finds, for each batch size and seed, the fewest steps that SGD (β = 0) and momentum
   (best β) need to reach a target loss, and writes `analysis.npy`. The paper uses the target that closes 92% of
   the gap between the initial loss ln 4096 and the reference loss (`f = 0.08` in the printed tables).

In the paper, each sweep run used one 4-chip TPU v4 or v6e host, and the 24 runs took about 18 hours in total.
`sweep_bigram.py` runs them one after another on whatever devices JAX finds; on a CPU the small-batch runs, with up to
10^7 steps, are slow.
