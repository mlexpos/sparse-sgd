# Lean formalization

This directory is a Lean 4 / Mathlib formalization of the mathematical appendix of the paper
(Appendices B–H). Every theorem, proposition, lemma, corollary, definition and assumption in
those appendices has an entry in the registry [`coverage.json`](coverage.json), which lists
the Lean declarations that prove it. [`RESULTS.md`](RESULTS.md) gives the same entries in the
order of the paper, with their numbers. Remarks are discussion; no numbered result relies on
one, and only three remarks are registered.

Lean's kernel checks every proof. No file contains `sorry`, and no declaration depends on an
axiom other than Lean's standard `propext`, `Classical.choice` and `Quot.sound`. Standard
results that the paper cites are not proved here: they are explicit hypotheses of the
theorems that use them (see [Trust boundary](#trust-boundary)).

The formalization and the appendix were developed together, over several rounds, and the
formalization improved the written proofs (see
[The formalization and the written proofs](#the-formalization-and-the-written-proofs)).

## Status of each result

| Status | Meaning | Results |
|---|---|---|
| complete | Every part of the statement is proved. In [`RESULTS.md`](RESULTS.md), 14 of these are marked `complete*` (see [below](#the-formalization-and-the-written-proofs)). | 47 |
| partial | Corollary G.17: part of the argument is not formalized (below). | 1 |
| remark, partly formalized | Remarks E.10 and H.11: some claims proved. | 2 |
| assumption, definition | Assumptions A and B, Definition D.1 and the definition of the decay rate in Appendix H.1. | 4 |

The partial result is **Corollary G.17** (the drift recursion converges). The recursion is
formalized with the tame coefficients of Lemma G.3, not the Gaussian coefficients of
Proposition G.9, and its constants are uniform near one parameter point, not over compact
parameter sets.

## Notation

The Lean names follow an earlier notation of the paper. The main translations are below;
[`NOTATION.md`](NOTATION.md) has the complete list.

| Paper | Lean |
|---|---|
| stiffness `ω² = ηp/ε` (matched: `ω̄²`) | `Δ`, `delta`, `Delta` (`matchedDelta`) |
| per-step curvature `λ = ηεp` | `w` |
| noise, curvature and total feedback `H_n`, `H_c`, `H` | `Params.noise` (`un`), `Params.curvature` (`uc`), `Params.totalLoad` (`u`) |
| amplified feedback `H̃ = H_n/(1-H_c)` | `Params.renormNoise` |
| ambient temperature `φ`, amplified `φ̃` | `Params.additive` (`phi`), `Params.renormAdditive` |
| LR curvature factor `ϱ` | `alpha` in the `Logistic` modules |
| eigenvalues and roots `z` | names containing `Lambda`, e.g. `smallDeltaLambdaPlus` |

The core objects:

- `Params` holds `(β, λ, H_n, φ)` as `beta`, `w`, `noise`, `additive`, and
  `Params.trajectory` iterates the exact second-moment recursion of Lemma B.1.
- `continuumFlow Δ u φ` solves the continuum moment system of Lemma C.5.
- `Params.matchedStep` (`ε̄ = -log β`), `Params.matchedDelta`, `Params.foldedAngle`,
  `Params.renormNoise` and `Params.renormAdditive` are the matched parameters of
  Definition D.1, and `Params.comparisonFlow` runs the continuum system at them.
- `Probability.LeastSquares.process` is the sparse least-squares SGD process itself.
  `Probability.LeastSquares.leastSquares_moment_trajectory` shows that its second moments
  equal `Params.trajectory` at every step, with the parameters of the paper
  (`Probability.LeastSquares.params_explicit`). The least-squares
  results therefore hold for the sampled process, not only for an abstract oracle.
- `Logistic.process` is the logistic-regression process. The fluid limits of Corollary G.6
  compare this sampled chain with its deterministic drift.
- `Scaling.Helps.stepRadius` and `Scaling.Helps.perStepRate` are the spectral radius `ρ(T)`
  and the decay rate `Λ = -ln ρ(T)` of Appendix H.

## Trust boundary

**Axioms.** [`Audit.lean`](Audit.lean) walks every declaration defined in the project,
including private helpers, and fails if any depends on an axiom other than the standard
three.

**Cited results.** These standard results enter as explicit hypotheses, never as axioms:

- the Jury stability criterion for 2×2 matrices (Elaydi 2005);
- the first- and second-order Gaussian integration-by-parts identities (Stein 1981);
- a conditional martingale Bernstein inequality (Freedman 1975; Boucheron, Lugosi and Massart 2013);
- the Bernstein moment condition and Hoeffding's lemma (Boucheron, Lugosi and Massart 2013);
- a chi-square moment-generating-function bound (ibid., §2.4).

Their Lean statements are in [`SparseSGD/External`](SparseSGD/External), and
[`EXTERNAL_RESULTS.md`](EXTERNAL_RESULTS.md) lists every theorem that uses each one. A false
hypothesis of this kind would make a theorem vacuous. Each statement was checked to be a
true form of the standard result.

**Assumptions of the paper.** Assumption A (the second-order oracle) is proved for least
squares from the sampling law. Assumption B (cells 7–8 of logistic regression) is stated as
the structure `Logistic.V2.AssumptionW2`; no theorem uses it.

## The formalization and the written proofs

The appendix and its formalization were developed together, over several rounds. In each
round the current appendix was frozen, its results were formalized, and every place where a
statement or proof could not be formalized as written was recorded in
[`CORRECTIONS.md`](CORRECTIONS.md). The authors then revised the appendix, and the next
round started from the revised text. Improvements to the paper that came out of this
process include:

- Corollary E.4: with integer batch sizes, the error has the extra term `|B_* d^σ/B - 1|`.
- Theorem G.4: the neighbourhoods are closed balls, since the induction reaches the radius.
- Corollary G.6: the statement requires `η = o(√(d/log d))` and a horizon polynomial in
  `d`, which the proof uses.
- Proposition G.23: part (iv) keeps an `O(ε_B)` error term, and part (v) needs a bounded `Φ`.
- Proposition G.12: the dissipation identity is stated on the states with `Q > 0`, where it
  holds.
- Proposition G.15: the hypothesis `r > 0`, which the oscillatory eigenvectors need.
- Proposition G.19: parts (ii) and (iii) need `R* > 0`, and the proof of (iii) needed an
  argument that the Jacobian of the drift recursion converges to `J0`. Lean derives this from
  the exact location of the fixed point.
- Proposition H.10: the limit `ε → 0` is taken with the noise feedback fixed, and its exact
  counterpart needs SGD to be stable.

The 14 results in which the formalization found such a gap are marked `complete*` in
[`RESULTS.md`](RESULTS.md). The last revision also wrote into the paper the conditions that
the formal statements need but the text had left implicit: integer batch sizes
(Appendix E), the dependence of the error of Corollary E.11 on the initial size, one-sided
derivatives at zero variance (Lemma G.3), a deterministic initial state (Theorem G.4), a
bounded effective step `η𝒜` (Lemma G.5), and a common initial state for the recursion and
the limiting ODE (Proposition G.9). `CORRECTIONS.md` is the full log of the gaps, in the
notation of the time.

## Statement fidelity

The rounds were run against frozen snapshots of the appendix source, the last of them taken
on 5 October 2026; the SHA-256 hashes are in [`source/manifest.json`](source/manifest.json)
and [`source/v2/manifest.json`](source/v2/manifest.json), and the text itself is not
distributed. Since then the appendix has changed its notation, some wording, figures and
numerical tables, three remarks have become lemmas (the registry uses the new labels), and
the conditions listed above have been written in.

Separately from the pipeline that wrote the code, four central results were compared with
the paper line by line, with every Lean definition they use traced back to the model:
Theorem D.6 (the moment comparison theorem), Corollary E.4, Corollary G.6 and
Proposition G.23, together with the least-squares process and the matched parameters. The
definitions and statements match the paper as revised. Lean's Theorem D.6 gives an explicit
threshold, and Lean's Corollary G.6 is slightly narrower: its initial data are fixed in `d`.
The other results have not been audited this way; for them, the registry and
`CORRECTIONS.md` are the record.

## How it was produced

The Lean code was written by an automated pipeline of language-model agents. A coordinator
owned the shared interfaces, imports and integration, and up to three workers at a time
edited disjoint files (gpt-6-luna at medium reasoning effort, escalating to gpt-6.1-sol and
then gpt-6-astra at high effort on failed proofs). Workers could not add assumptions or
replace a conclusion of the paper by a hypothesis, and every change to a printed statement
had to be recorded in `CORRECTIONS.md`. The audit above was carried out separately with
Claude (Anthropic). [`HISTORY.md`](HISTORY.md) is the pipeline's development log, in the
notation of the time.

## Building and verifying

You need [elan](https://github.com/leanprover/elan). The toolchain (Lean 4.34.1) is pinned
in `lean-toolchain`, and Mathlib is pinned to `v4.34.1` (commit `d13f23b`) in
`lake-manifest.json`. From this directory:

```sh
lake exe cache get        # download prebuilt Mathlib (about 8 GB on disk with the build)
lake build                # about 20 minutes on an 8-core laptop
python3 scripts/verify.py # about 3 minutes
```

`scripts/verify.py` builds the project and writes its output to
[`verification.log`](verification.log). It checks that:

1. every module is reachable from `SparseSGD.lean`, so nothing escapes the build or the audit;
2. the project builds;
3. `Audit.lean` passes;
4. all 871 declarations cited in [`obligations.json`](obligations.json) exist;
5. the source snapshot matches its hashes, when it is present (it is not distributed, and
   the check is then skipped).

It also regenerates `coverage.json` and `declarations.json`. The current log reports 379
modules, 2,909 authored theorems, 6,668 audited declarations (5,662 of them theorems) and
only the three standard axioms.

## Layout

| Path | Contents |
|---|---|
| `SparseSGD/Foundations.lean` | `Params`, `Moments`, the exact recursion (Lemma B.1) |
| `SparseSGD/Probability` | the oracle and the least-squares sampling process (Appendix B) |
| `SparseSGD/Discrete` | renewal, stability and floor (Appendix C); `Discrete/General` for `β ∈ [0,1)` |
| `SparseSGD/Continuum` | the continuum moment system (Lemma C.5) and its modes (Lemma D.5) |
| `SparseSGD/Comparison` | matching, embedding, quadrature, Theorem D.6; `Comparison/General` for matching, embedding and the square-root lift at `β ∈ (0,1)` |
| `SparseSGD/Scaling` | the least-squares corollaries (Appendix E) and the phase dictionary (Appendix F) |
| `SparseSGD/Scaling/Helps` | benefits of momentum (Appendix H) |
| `SparseSGD/Logistic` | logistic regression (Appendix G); `Logistic/V2` for Propositions G.12, G.15, G.19 and Corollary G.17 |
| `SparseSGD/External` | the statements of the cited results |
| `SparseSGD/Examples` | small worked instances (a one-step risk, end-to-end fluid limits) |
| `Audit.lean`, `scripts/` | axiom audit, verification and coverage scripts |
| `coverage.json`, `obligations.json`, `declarations.json` | the result-to-declaration registry |
| `RESULTS.md`, `NOTATION.md`, `CORRECTIONS.md`, `EXTERNAL_RESULTS.md`, `HISTORY.md` | results by paper number, notation, repairs, cited results, development log |
