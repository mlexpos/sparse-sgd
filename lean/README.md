# Lean formalization: scaling limits of sparse heavy-ball SGD

This directory contains a Lean 4 / Mathlib formalization of the results of a
note in preparation, *Scaling limits of sparse heavy-ball SGD: one moment
comparison for least squares and logistic regression*. The note itself is not
in this repository. Results are referred to below by their labels in the note
(`thm:M`, `cor:fluid`, …) and by their titles.

Lean's kernel checks every proof. No file contains `sorry` or adds an axiom.
That establishes that the Lean theorems are true. Whether each Lean theorem says
what the note says is a separate question, discussed under
[Statement fidelity](#statement-fidelity).

## What the note proves

The algorithm is mini-batch SGD with momentum in exponential-moving-average
form,

$$m_{k+1}=\beta m_k+(1-\beta)g_k,\qquad \theta_{k+1}=\theta_k-\eta\,m_{k+1},$$

applied to two models. The first is least squares with sparse Gaussian features
$x=s\tilde x$, where $s\sim\mathrm{Ber}(p)$ and $\tilde x\sim\mathcal N(0,I_d)$,
plus label noise. The second is logistic regression with a rare class,
$y\sim\mathrm{Ber}(p)$ and $x=y\mu+z$.

**Least squares.**

- The traced second moments of the error $e_k$ and the scaled momentum
  $\eta m_k$ obey an exact, closed, affine $2\times2$ matrix recursion. The
  hyperparameters $(p,B,d,\eta,\beta,\varsigma)$ enter only through four numbers
  (`lem:L1`).
- In suitable coordinates, this recursion *is* a three-dimensional linear ODE
  sampled on a grid, with the noise arriving as impulses (`lem:match`,
  `lem:embed`). The ODE is the second-moment system of a damped oscillator with
  multiplicative and additive noise.
- One moment comparison theorem bounds the distance between the chain and the
  ODE by $O(\bar\varepsilon)$, where $\bar\varepsilon=-\log\beta$. The bound is
  uniform in time and in the ratio of learning rate to retention rate (`thm:M`).
- Every scaling limit under the co-scaling
  $p=p_*d^{-\kappa},\ B=B_*d^{\sigma},\ 1-\beta=\varepsilon_*d^{-\gamma},\ \eta=\eta_*d^{-\alpha}$
  is then a corollary. These limits are collected in a phase dictionary.

**Logistic regression.**

- The state reduces to five variables, and the conditional drift of the bulk is
  the same moment recursion with state-dependent parameters (`lem:LR0`,
  `lem:LRdrift`, `lem:B`).
- A general fluid-limit theorem for Markov chains shows that, over finite
  horizons, the random chain stays within $O(\sqrt{\log d/d})$ of its drift
  recursion (`thm:A`, `lem:LRinc`, `cor:fluid`).
- The drift recursion is then analysed cell by cell (`prop:LR2`, `prop:LR34`),
  and its equilibrium and excess-risk floor are identified (`prop:D`).
- Two statements are assumptions of the note, not theorems: global stability
  (`ass:S`) and window averaging (`ass:W`).

## What is formalized

The note has 27 numbered or displayed results. Every one has a Lean
counterpart, with the status below:

- **complete**: the Lean statement is the result as printed.
- **corrected**: the printed statement needed a repair, recorded in
  [`CORRECTIONS.md`](CORRECTIONS.md).

The note's three assumptions and its definition of the matched parameters are
recorded separately.

Names omit the `SparseSGD.` prefix. [`coverage.json`](coverage.json) lists
every declaration, subclaim by subclaim.

| Label | Result | Status | Main Lean declarations |
|---|---|---|---|
| `ass:G` | Second-order oracle | assumption | `RawOracleHypotheses` |
| `eq:LSoracle` | Sparse Gaussian minibatch oracle | complete | `Probability.LeastSquares.leastSquares_conditional_oracle` |
| `lem:L1` | Exact reduction | complete | `raw_oracle_moment_trajectory`, `Probability.LeastSquares.leastSquares_moment_trajectory` |
| `lem:L2` | Discrete renewal | complete | `Params.trajectory_R_renewal`, `stable_kernel_masses` |
| `cor:stab` | Stability, floor, a priori bound | complete | `trajectory_risk_uniform_bound`, `trajectory_risk_tendsto_floor`, `trajectory_risk_not_summable` |
| `lem:L3` | Structure of the continuum system | complete | `continuum_solution_unique`, `continuumFlow_renewal`, `continuumFlow_exponentially_stable_iff` |
| `def:matched` | Matched parameters | definition | `Params.matchedStep`, `Params.matchedDelta`, `Params.foldedAngle` |
| `lem:match` | Matching | complete | `Params.exact_matching_similarity`, `Params.exact_matching_existsUnique` |
| `lem:embed` | Exact embedding: impulses on a grid | complete | `Params.exact_embedding_step`, `Params.exact_embedding_renewal` |
| `lem:quad` | Quadrature of exponential pairs | complete | `sampled_pair_sum_quadrature`, `quadrature_factor_bound` |
| `lem:modes` | Modes for large Δ | complete | `exists_largeMode_parameter` |
| `thm:M` | Moment comparison theorem | complete | `moment_comparison` |
| `cor:tikhonov` | Small Δ: one-dimensional SGD with floor | complete | `cor_tikhonov` |
| `cor:regular` | Fixed Δ: the three-dimensional limit | complete | `cor_regular` |
| `cor:resonance` | Boundary 1: the resonance line | corrected | `Scaling.cor_resonance_rate`, `cor_resonance_rank`, `cor_resonance_neighboring_limits` |
| `cor:window` | Large Δ: the long-oscillation window | complete | `window_chain_energy_comparison`, `window_chain_risk_comparison` |
| `cor:lift` | Square-root lift and its defect | complete | `Params.comparisonFlow_squareRootLift_R`, `Params.squareRootLift_oscillator_defect` |
| `cor:curv` | Curvature ceiling and the noise/curvature switch | corrected | `curvature_window_comparison`, `curvature_switch_rate` |
| `phase-dictionary` | Scaling limits, rates, cells and boundaries | corrected | `eight_cells_exhaustive`, `Scaling.ls_learning_cells_all_batches` |
| `lem:nonboundary` | Non-boundaries | corrected | `Scaling.actual_sparse_activity_ratio`, `Scaling.actual_signal_increment_ratio_tendsto` |
| `lem:LR0` | Exact Markov reduction | complete | `Logistic.reducedProcess_markov` |
| `lem:LRdrift` | Exact conditional drift | complete | `Logistic.process_conditional_signal_drift`, `Logistic.process_conditional_bulk_drift` |
| `lem:B` | Tame coefficients | corrected | `Logistic.tame_coefficients`, `Logistic.tame_scalarJets_first_second` |
| `thm:A` | Fluid limit | corrected | `Logistic.fluid_limit_normingFamily`, `Logistic.fluid_limit_supNorm` |
| `lem:LRinc` | LR increments | corrected | `Logistic.process_tame_matchedIncrement_dual_condLExp` |
| `cor:fluid` | Fluid limit in cells 2–4 | corrected | `Logistic.cor_fluid_tame_cell_two_warm`, `Logistic.cor_fluid_tame_cells_three_four` |
| `prop:LR34` | Cells 3–4: dynamic-α limit | corrected | `Logistic.prop_LR34` |
| `prop:LR2` | Cell 2: slow system, globally stable | complete | `Logistic.prop_LR2`, `Logistic.slow_global_convergence` |
| `ass:S` | Global stability | assumption | `Logistic.SourceAssumptionS` |
| `ass:W` | Window averaging | assumption | `Logistic.SourceAssumptionW` |
| `prop:D` | Equilibrium and floor | corrected | `Logistic.populationLoss_equilibrium_floor`, `Logistic.equilibriumBulk_integerBatch_comparable` |

The least-squares results are proved for the actual sampled process, not only
for an abstract oracle.
`Probability.LeastSquares.leastSquares_moment_trajectory` shows that, for every
iteration, the second moments of the sparse Gaussian minibatch process equal
the deterministic recursion. Its parameters are the note's, given explicitly
by `Probability.LeastSquares.params_explicit`.

Similarly, the logistic fluid limits compare the actual sampled logistic chain
with its deterministic drift.

## Reading a Lean statement against the note

The note's objects correspond to the following Lean definitions.

- `Params` holds $(\beta, w, u_n, \varphi)$ as `beta`, `w`, `noise`, `additive`.
  `Params.trajectory` iterates the second-moment recursion (L1) of the note.
- `continuumFlow Δ u φ` is the solution of the continuum system (L3), defined
  by a matrix exponential.
- The matched parameters are `Params.matchedStep` ($\bar\varepsilon=-\log\beta$),
  `Params.matchedDelta` ($\bar\Delta$), `Params.foldedAngle` ($\theta^*$),
  `Params.renormNoise` ($\tilde u$) and `Params.renormAdditive` ($\tilde\varphi$).
  `Params.comparisonFlow` runs the continuum system at the matched parameters
  from the matched initial condition.
- `Probability.LeastSquares.process` is the sparse least-squares SGD process.
  `Logistic.process`, together with `Logistic.matchedSummary`, gives the
  logistic process in the five matched coordinates.
- `slowEnergy` and `oscillatoryEnergy` are the eigenfunctionals $S$ and $Z$.

## Trust boundary

**Axioms.** [`Audit.lean`](Audit.lean) walks every declaration defined in the
project, including private helpers, and fails if any of them depends on an
axiom other than `propext`, `Classical.choice` and `Quot.sound`.

**Cited results.** Standard results that the note cites are not proved here.
They enter as explicit hypotheses of the theorems that use them, never as
axioms:

- the Jury stability criterion for $2\times2$ matrices;
- the first- and second-order Gaussian (Stein) integration-by-parts identities;
- a conditional martingale Bernstein inequality;
- the Bernstein moment condition;
- Hoeffding's lemma;
- a chi-square moment-generating-function bound.

Their exact statements are in [`SparseSGD/External`](SparseSGD/External) and
[`EXTERNAL_RESULTS.md`](EXTERNAL_RESULTS.md). A false hypothesis of this kind
would make a theorem vacuous. Each of these six statements has been checked to
be a true statement of the standard result, so none of them does.

**Assumptions of the note.**
- **G:** for least squares, assumption G is proved from the sampling law.
- **S and W:** these are explicit propositions. They are not used by any of the
  finite-horizon results.

## Where the formal statements differ from the note

The formalization was carried out against a frozen copy of the note dated
3 October 2026. Its record of every place where the printed statement had to
be changed is [`CORRECTIONS.md`](CORRECTIONS.md). The audit described below
re-checked part of that record.

**Confirmed errors in the note.** These have been addressed in the current
draft.

- **`cor:resonance`.** With integer batch sizes $B=\lfloor B_*d^\sigma\rfloor$,
  the rate is $d^{-\min(\gamma,1,\sigma)}$, not $d^{-\min(\gamma,1)}$. The extra
  $d^{-\sigma}$ cannot be removed: it shifts the noise floor by that amount along
  infinitely many $d$.
- **`prop:D`, part (iv).** The equilibrium excess risk is
  $\tfrac12p\Phi\,(1+O(\Phi+\epsilon_B))$. The $\epsilon_B$ term cannot be
  dropped, because at fixed $p$ the ratio to $\tfrac12p\Phi$ does not tend to
  $1$ as $\Phi\to0$.
- **`prop:D`, part (v).** $R^*\asymp d^{1-\sigma-\alpha_\eta}$ requires a
  bounded load. When $\Phi\to\infty$, $R^*$ grows only like $2\log\Phi$.
- **`cor:fluid`.**
  - The proof uses $\eta=o(\sqrt{d/\log d})$ and a horizon polynomial in $d$,
    but the statement omitted both.
  - The constant depends on the deterministic path, not only on the horizon.
  - The cell-2 stability argument did not account for an initial layer when
    the momentum starts large.
- **`thm:A`.** The induction reaches distance exactly $\rho$, so the
  neighbourhoods must be closed balls (or have a strict margin). The smoothness
  hypothesis is needed only on physical states.

**A recorded correction that is not needed.** `CORRECTIONS.md` says the
covariance limit $C_\perp\to0$ in `prop:D` needs extra hypotheses: a vanishing
rare-class probability and bounded bulk energy. It does not. In the tame
regime, $p\alpha R_\perp\le\epsilon_B$, so $C_\perp\to0$ already. The Lean lemma
`Logistic.tame_fixedPoint_covariance_tendsto` remains valid, but it is weaker
than necessary.

**Not independently re-checked.** `CORRECTIONS.md` also records smaller
repairs that the audit did not re-derive:

- `lem:B`: one-sided derivatives at variance zero;
- `cor:curv`: the error keeps the initial-energy and forcing factor;
- the window remark: strict separation of the two rates needs positive noise;
- `lem:nonboundary`: a qualification of its last sentence;
- `lem:LRinc`: a bounded effective step $\eta p$;
- `prop:LR34`: a common initial state.

## Statement fidelity

A kernel-checked theorem can still differ from the theorem in the note: it can
use a different definition, assume more, or conclude less. On 4 October 2026
four central results were compared with the note line by line. Each Lean
definition they use was traced back to the model.

- **Core definitions.** The moment recursion, the continuum system and the
  matched parameters match the note exactly.
- **Least-squares process.** This matches exactly: the sampling law, the update,
  and the parameter formulas $w=\eta(1-\beta)p$,
  $u_n=\eta(d+2-p)/(2B)$ and $\varphi=\eta\varsigma^2d/(2B)$.
- **`thm:M`.** The statement matches. The Lean version is slightly stronger: it
  gives an explicit $\Delta_0(\delta)=\max(4,\tfrac14+(22/\delta)^2)$, and it
  does not require $\delta\le\tfrac14$.
- **`cor:resonance`.** Faithful, with the integer-batch correction.
  - Parts (ii) and (iii) are stronger than the note; the limits in (iii) are
    uniform on $\tau\ge0$.
  - The parameter limits displayed in the statement are proved only inside the
    proof, not exported as a theorem.
- **`prop:D`.** Faithful, with the corrections above. Two side remarks of the
  statement have no separate Lean form: $\eta C_\perp/\varepsilon=O(w/\varepsilon)$
  and $u_c=O(\eta\varepsilon p\alpha)$.
- **`cor:fluid`.** Faithful, with corrections, but narrower than the note:
  - it assumes $\eta\sqrt{\log d/d}\to0$, which can fail only for batches
    $B\gtrsim d^{3/2}$;
  - the normalized initial data must be exactly fixed in $d$;
  - the constant is chosen after the dimension-indexed family, although the
    proof builds one that does not depend on it;
  - the worked examples in [`SparseSGD/Examples`](SparseSGD/Examples)
    instantiate only the corner $\Phi\to0$, $\gamma=0$.

The other 23 results have not yet been audited this way.

## How it was produced

The Lean code was written by an automated multi-agent pipeline of large
language models:

- A coordinator owned the shared interfaces, the imports and the integration.
  Up to three workers at a time edited disjoint files.
- Workers started with gpt-6-luna at medium reasoning effort. A failed proof
  attempt was escalated to gpt-6.1-sol and then gpt-6-astra, both at high
  reasoning effort.
- Workers could not add assumptions or replace a conclusion of the note by a
  hypothesis. Every change to a printed statement had to be recorded in
  `CORRECTIONS.md`.

The pipeline worked from the frozen copy of the note described above. The
SHA-256 hashes of its 29 source files are kept in
[`source/manifest.json`](source/manifest.json), but the text itself is not
distributed.

The statement-fidelity audit was carried out separately, with Claude
(Anthropic), at the author's request.

## Building and verifying

You need [elan](https://github.com/leanprover/elan). The toolchain
(Lean 4.34.1) is pinned in `lean-toolchain`, and Mathlib is pinned to
`v4.34.1` (commit `d13f23b`) in `lake-manifest.json`.

```sh
cd lean
lake exe cache get        # download prebuilt Mathlib
lake build
python3 scripts/verify.py
```

`scripts/verify.py` runs the following checks and writes their output to
[`verification.log`](verification.log):

1. Every module is reachable from `SparseSGD.lean`, so nothing escapes the build
   or the audit.
2. The whole project builds.
3. `Audit.lean` passes.
4. All 281 declarations cited in [`obligations.json`](obligations.json) exist.
5. It regenerates `coverage.json` and `declarations.json`.
6. If copies of the frozen note are placed under `source/`, it checks them
   against the recorded hashes.

The current log reports the following:

- 332 modules;
- 1,887 authored theorem declarations;
- 4,501 audited declarations (3,766 of them theorems);
- only the three standard axioms.

## Layout

| Path | Contents |
|---|---|
| `SparseSGD/Foundations.lean` | `Params`, `Moments`, the recursion (L1) |
| `SparseSGD/Discrete` | renewal, stability, floor (`lem:L2`, `cor:stab`) |
| `SparseSGD/Continuum` | the continuum system (`lem:L3`, `lem:modes`) |
| `SparseSGD/Comparison` | matching, embedding, quadrature, `thm:M` |
| `SparseSGD/Scaling` | the least-squares corollaries and the phase dictionary |
| `SparseSGD/Probability` | the oracle and the least-squares sampling process |
| `SparseSGD/Logistic` | logistic regression, `lem:LR0` through `prop:D` |
| `SparseSGD/External` | statements of the cited external results |
| `SparseSGD/Examples` | small worked instantiations (one-step risk, end-to-end fluid examples) |
| `Audit.lean`, `scripts/` | axiom audit and verification script |
| `coverage.json`, `obligations.json`, `declarations.json` | result-to-declaration registry |
| `CORRECTIONS.md`, `EXTERNAL_RESULTS.md` | corrections to the note, cited results |
