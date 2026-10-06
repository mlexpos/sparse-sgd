# Sparse momentum: supplementary code

Code accompanying a paper on SGD with momentum when each parameter receives a gradient only
on some steps, as the embedding and readout vectors of a language model do. It has two
parts:

| Directory | Contents |
|---|---|
| [`lean/`](lean/) | A Lean 4 / Mathlib formalization of the mathematical appendix. |
| [`bigram_model/`](bigram_model/) | The bigram experiment: data preparation, training sweep and analysis. |

## `lean/`: formalization of the appendix

Every theorem, proposition, lemma, corollary, definition and assumption of Appendices B–H
of the paper has a Lean counterpart, and Lean's kernel checks all the proofs. There is no
`sorry`, and nothing depends on an axiom beyond Lean's standard three. Standard results
that the paper cites, such as the Jury criterion and Gaussian integration by parts, are
explicit hypotheses of the theorems that use them.

Of the 54 registered items, 46 results are formalized in full, and Corollary G.17 and
Proposition G.19 in part. The rest are two partly formalized remarks, two assumptions and two
definitions.

The appendix and its formalization were developed together, over several rounds. Each round
formalized the current text, and the gaps it found (a missing hypothesis, a lost error term,
an imprecise scope) led to revisions of the written statements and proofs before the next
round.

- [`lean/RESULTS.md`](lean/RESULTS.md) lists each result by its number in the paper, with
  its status and its main Lean declarations.
- [`lean/README.md`](lean/README.md) explains the statuses, the notation (Lean names follow
  an earlier notation of the paper), the trust boundary, what the formalization changed in
  the written proofs, an independent audit of four central results, and how the code was
  produced: by an automated pipeline of language-model agents.

To build and check it, with [elan](https://github.com/leanprover/elan) installed:

```sh
cd lean
lake exe cache get        # prebuilt Mathlib
lake build
python3 scripts/verify.py # module reachability, axiom audit, registry check
```

## `bigram_model/`: the bigram experiment

This is the experiment of Figure 4(d) and Appendix H.4 (with Figure 10). It trains a bigram
softmax model on WikiText-103, with the 4096 most frequent tokens of the Pythia tokenizer
and an embedding and a readout vector of dimension 64 for each token. One learning rate
and one momentum `β` are shared by all parameters. For each batch size from 1 to 16384,
the sweep finds the fewest steps that SGD (`β = 0`) and tuned momentum need to reach a
target loss.

```sh
cd bigram_model
python build_bigram_data.py   # tokenize WikiText-103, count token pairs
python sweep_bigram.py        # 12 batch sizes x 2 seeds, each over a 13 x 8 (eta, beta) grid
python analyze_bigram.py      # steps to the target loss for SGD and tuned momentum
```

The sweep needs NumPy and JAX, and building the data also needs the HuggingFace `datasets`
and `transformers` packages. In the paper, each sweep run used one 4-chip TPU host, and the
24 runs took about 18 hours in total. [`bigram_model/README.md`](bigram_model/README.md)
has the details.

<!-- public-only:start -->
## Removed: the SymPy scripts

Earlier versions of this repository contained SymPy scripts (`core.py`,
`step1_closed_form_identities.py`, `step2_per_region_scalings.py`) for an earlier
Routh–Hurwitz stability analysis of the second-moment ODE. That analysis contains an error
and has been superseded by the analysis formalized in `lean/`. The scripts have been
removed and should not be consulted; they remain in the git history.
<!-- public-only:end -->

## License

Apache 2.0; see [`LICENSE`](LICENSE).
