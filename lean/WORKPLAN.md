# Full-paper implementation

> **Notation (2026-10-05).** Entries here record corrections in the manuscript notation of
> their date: `Δ` (now the stiffness `ω²`), `w` (now `λ`), `u`, `u_n`, `u_c`, "load" (now the
> feedback `H`, `H_n`, `H_c`), "additive load" (now the ambient temperature `φ`), and the LR
> curvature factor `α` (now `ϱ`). See `NOTATION.md`.

Scope: every numbered result in the frozen active manuscript, the actual
least-squares oracle, and the phase dictionary. The approved completion contract
allows documented corrections and explicit assumptions for cited standard
results. The manuscript's G/S/W assumptions remain distinct from proved results.

## Delivered proof groups

1. Foundations, a frozen source snapshot, subclaim coverage and transitive axiom audits.
2. Actual sparse Gaussian least-squares sampling, conditional moments, all-time
   square integrability and deterministic moment reduction; discrete renewal,
   stability, geometric convergence, noise floor and necessity of the load threshold.
3. Continuum existence and uniqueness, covariance and renewal identities, positivity,
   kernel estimates, exponential stability, Perron rate, inversion and strict rank growth.
4. Exact matching in every damping branch, similarity and impulse embedding,
   quantitative quadrature and the full uniform-in-time moment comparison.
5. Every limiting regime and the phase dictionary, including actual integer-rounded
   batches, resonance corrections, windows, curvature and activity probabilities.
6. Actual logistic sampling, Markov reduction, conditional drift, Gaussian
   coefficient calculus, all first/second derivatives, equilibrium and loss asymptotics.
7. Logistic conditional concentration, the stopped fluid theorem, physical-domain
   Taylor estimates, bounded fast-block products and actual stochastic fluid limits.
8. Slow global dynamics, regular dynamic-alpha limits, covariance preservation,
   finite-horizon global existence and the rank-one oscillator lift.
9. Final cell-2 warm-start and cells-3/4 physical-initial-data fluid corollaries.
   Both prove a positive rarity cap before choosing the actual family, including
   fixed small probabilities. Neither assumes S/W, an ODE reference, a path bound,
   Jacobian products or Taylor estimates. Power-law specializations discharge
   the parameter-limit and horizon conditions.

`obligations.json` links each subclaim to public Lean declarations. The generated
`coverage.json` has 27 complete or corrected result entries, no partial/pending
entries, three explicit source assumptions and one definition. Corrections,
including the Bernstein linear term, initial data, rarity cap and integer rounding,
are recorded in `CORRECTIONS.md`.

## V2 (revised appendix)

Scope: the v2 drafts frozen in `source/v2/`:
- `prop:S` replaces `ass:S`;
- `prop:W1`, `cor:recursion` and `prop:W2`, together with the narrower assumption
  `ass:W2`, replace `ass:W`.

The v1 declarations remain, marked as v1 in their docstrings, with registry status
`v1_superseded`.

Delivered modules, all in `SparseSGD/Logistic/V2/`:

| Module | Content |
| --- | --- |
| `Lyapunov` | Lyapunov function, dissipation, coercivity, strict convexity |
| `PositiveDeterminant` | `Q > 0` for `t > 0` |
| `Barbalat` | Barbalat lemmas |
| `GlobalConvergence` | `prop:S` (i) |
| `Hurwitz` | `prop:S` (ii) |
| `LyapunovCertificate` | Lyapunov certificates and their robustness |
| `UniformRate` | `prop:S` (iii) and uniform entry |
| `LargeDeltaAlgebra`, `LargeDeltaPerturbation` | `prop:W1` |
| `RecursionContraction`, `RecursionTame` | `cor:recursion` |
| `WindowMapAlgebra`, `WindowUnitCircle` | `prop:W2` |
| `All` | `prop_S`, `cor_recursion_tame'`, `AssumptionW2` |

Partial items:

- `cor:recursion`:
  - not instantiated with the actual Gaussian coefficients of `prop:LR34`, which
    are non-autonomous through `theta`;
  - constants not made uniform over compact sets of `(Delta*, Phi*, r)`.
- `prop:W2` (iii): convergence of the drift-recursion Jacobian to `J0` is a
  hypothesis.

Each of these is a natural next work item. The tex corrections are in
`CORRECTIONS.md`, section "V2 drafts".

Execution: Sonnet workers wrote one file each in `V2/`, checked with
`lake env lean`. The integration step then did the following:
- renamed the duplicate `hasFDerivAt_dynamicAlpha` in `WindowMapAlgebra` to
  `hasFDerivAt_dynamicAlpha_window`;
- added `V2/All.lean` and the root import;
- registered the five v2 labels;
- extended `scripts/coverage.py` with the `v1_superseded` status and
  `scripts/verify.py` with the v2 manifest;
- ran `scripts/verify.py`, which passed.

### V2 momentum-helps appendix

Scope: `source/v2/momentum_helps.tex` (section `sec:helps-app`), first frozen on
2026-10-04 and re-frozen on 2026-10-05 after the tex merge with KE's version (see
"Re-pin after the tex merge" below). Twelve labels are registered:
- 2026-10-04: `lem:helps-sgd`, `lem:helps-rate`, `lem:helps-roots`,
  `lem:helps-transfer`, `lem:ray`, `cor:samplecost`, `lem:speedup`,
  `cor:helps-speedup`, `lem:helps-onecopy` and `lem:helps-vocab`;
- final 2026-10-04 snapshot: `lem:helps-twocurv` and `prop:helps-critical`.

Status against the 2026-10-05 snapshot:
- 6 complete: `lem:helps-sgd`, `lem:ray`, `lem:speedup`, `lem:helps-onecopy`,
  `lem:helps-twocurv`, `prop:helps-critical`;
- 2 partial: `cor:samplecost`, `lem:helps-vocab`;
- 4 supporting (dropped from the tex, Lean proofs kept): `lem:helps-rate`,
  `lem:helps-roots`, `lem:helps-transfer`, `cor:helps-speedup`.

Delivered modules, all in `SparseSGD/Scaling/Helps/`:

| Module | Content |
| --- | --- |
| `StepMatrix` | 3x3 matrix of `L`, `det(z-L)`, radius and per-step rate, retention-clock conjugation |
| `CubicRoots` | root facts for `chi`, `Gamma`, `lem:speedup` (i), (ii), (iv) first sentence |
| `RootPerturbation` | `lem:helps-roots` (cubic), continuity and positivity of `r_c` |
| `Ray` | `lem:ray`, the hyperbola algebra |
| `ExactRate` | `lem:helps-sgd`, `rem:retention-cap` (a) bounds, `lem:helps-onecopy` |
| `SpeedupExpansion` | `lem:speedup` (ii) limit, (iii) and (iv) |
| `Transfer` | `lem:helps-transfer` |
| `Stability` | `rem:stab-large-w` radius form, `lem:helps-rate` first clause |
| `Limits` | `cor:samplecost`, `cor:helps-speedup`, `lem:helps-vocab` (iii) asymptotic clause |
| `Vocabulary` | `lem:helps-vocab` (i)-(iv) and the large-batch limit |
| `CriticalBatch` | `lem:helps-twocurv`, `prop:helps-critical` (`admSet`, `Sfun`, `Efun`, `Sinf`, `Einf`, `Bcrit`) |
| `All` | `lem_ray_bundle`, `lem_speedup`, `lem_helps_sgd`, `lem_helps_transfer` |

Partial items against the 2026-10-05 snapshot, which are natural next work items
(Lean-only; the tex is unchanged by them):

- `cor:samplecost` (KE's `cor:sample_cost` (ii)) off the resonance line.
  - `s -> 0`: assemble `perStepRate_le_neg_log_beta`, `helps_transfer_compact` at
    `Delta = 1/2` and `continuous_continuumPerronRate` into a statement along
    rays with `s -> 0`.
  - `s -> infinity`: formalize a small-`Delta` rate in the spirit of KE's
    `lem:small_delta`, `r = 2 eta p (1-u)(1+theta)` with
    `|theta| <= C(eps + Delta)`, uniform in `u`. Then derive
    `r* = (eps/s)(1+o(1))`.
- `lem:helps-vocab` (iii), last claim, off the resonance line. For `s <= 1 - eps`
  it is a two-line consequence of `perStepRate_le_neg_log_beta`; for
  `s -> infinity` it follows from the item above.
- Optional: register KE's new exact statements (`lem:step_speed`, `lem:chi_roots`,
  `lem:step_spectrum`, `lem:small_delta`, `lem:vocab_rows`) and `prop:vocab_full`.
  `lem:step_speed` is `beta_le_stepRadius` as it stands.

Items that no longer bind: `lem:helps-rate` (the fixed point and the `limsup` rate)
and `lem:helps-roots` (general degree) are now `supporting`, because their tex
statements were dropped.

Earlier partial item, closed:
- `prop:helps-critical`: no partial items remain. The `1/sqrt 5` branch of
  `c_kappa = max(1 - 4/sqrt kappa_V, 1/sqrt 5)` and the closing `sqrt(kappa_V)/19`
  claim were added in a follow-up (`neg_log_one_sub_le_div_sqrt`, `Mk_props`,
  `helps_critical_ii_mom'`, `Bratio_ge'`, `Bratio_ge_div19`); `d >= 0` suffices.

Execution: Sonnet workers wrote one file each in `Helps/`, checked with
`lake env lean`. None needed escalation. The integration step then did the
following:
- renamed the duplicate `neg_log_one_sub_le` in `Vocabulary` to
  `neg_log_one_sub_le_vocab`;
- added `Helps/All.lean` and the root import;
- registered the ten labels with source `v2/momentum_helps.tex`;
- added the snapshot and its hash to `source/v2/manifest.json`;
- ran `scripts/verify.py`, which passed.

Critical-batch step (2026-10-04). A Sonnet worker wrote `Helps/CriticalBatch.lean`
against the draft of `prop:helps-critical`. The integration step then did the following:
- imported it from `Helps/All.lean`, with no name clashes;
- refreshed `source/v2/momentum_helps.tex` to the final tex and updated its hash;
- registered `lem:helps-twocurv` (complete) and `prop:helps-critical` (first as
  partial; complete after the follow-up that added the `1/sqrt 5` branch of
  `c_kappa` and the `sqrt(kappa_V)/19` claim);
- ran `scripts/verify.py`, which passed.

Re-pin after the tex merge (2026-10-05). The appendix section was merged with KE's
version: her framing and statements are the base, and EP's `app:critical_batch`
subsection is kept. No `.lean` file changed. The re-pin did the following:
- copied the merged `paper/appendix/momentum_helps.tex` over
  `source/v2/momentum_helps.tex` (byte-identical) and updated its sha256 in
  `source/v2/manifest.json`;
- compared every registered label with the merged text:
  - kept, notation-only changes: `lem:helps-sgd`, `lem:helps-onecopy`,
    `lem:helps-twocurv`, `prop:helps-critical`;
  - kept but with (iii)'s last claim rewritten as a co-scaling-ray `o(1)`
    statement: `lem:helps-vocab`, now partial;
  - now pointing to KE's statements, which were compared with Lean: `lem:ray`
    (complete), `cor:samplecost` (partial), `lem:speedup` (complete);
  - dropped from the tex and marked `supporting`: `lem:helps-rate`,
    `lem:helps-roots`, `lem:helps-transfer`, `cor:helps-speedup`;
- taught `scripts/coverage.py` the `supporting` status;
- ran `scripts/verify.py`, which passed: 358 modules, 599 obligation references,
  35 complete, 4 partial and 4 supporting entries.

The tex review is in `CORRECTIONS.md`, section "V2 momentum-helps".

### V2 merged appendix (2026-10-05)

Scope: the harmonized `momentum_helps.tex` (sha256 `90c5bcc8...5c07`) and the live
appendix chunks 01, 02, 03, 04, 05, 07, 08 (`source/v2/chunks/`), which relax the momentum
range to `beta in [0,1)`. The statuses above ("Status against the 2026-10-05 snapshot")
are superseded by this subsection.

Work items, one file each (Sonnet implementers, `lake env lean` per file):

| Item | File | Result |
| --- | --- | --- |
| chi-roots | `Helps/ChiRoots` | `lem:chi_roots` (a)-(e), complete |
| step-speed | `Helps/StepSpeed` | `lem:step_speed` = `lem:helps-onecopy` (`beta in [0,1)`), `rem:retention-cap` (a); (b) skipped |
| step-spectrum | `Helps/StepSpectrum` | `lem:step_spectrum`, complete |
| small-delta-bracket, small-delta-factor, small-delta | `Helps/SmallDeltaSlowRoot`, `Helps/SmallDeltaFactor`, `Helps/SmallDelta` | `lem:small_delta`, complete |
| sample-cost-above, sample-cost | `Helps/SampleCostAbove`, `Helps/SampleCost` | `cor:sample_cost` (i), (ii) all cases and uniform in `s`; `rem:sgd_cost`; co-scaling clauses of `lem:helps-vocab` (iii), `prop:vocab_full` (i) |
| schedule | `Helps/Schedule` | `rem:schedule` except the Cramér–Rao/minimax sentence |
| fixed-floor | `Helps/FixedFloor` | `prop:fixed_floor`, corrections MF-1, MF-2 |
| vocabulary-v2 | `Helps/Vocabulary` (appended) | `lem:helps-vocab` (iii) for `beta in [0,1)`, (v) |
| vocab-rows | `Helps/VocabRows` | `lem:vocab_rows`, complete |
| critical-batch-v2 | `Helps/CriticalBatch` (appended) | `prop:helps-critical` (i) limit, (iii) absolute bounds, (iv) |
| vocab-full | `Helps/VocabFull` | `prop:vocab_full` = `rem:vocab`, complete |
| general-renewal | `Discrete/General/Renewal` | `lem:L2`, `cor:stab`, `cor:lift` (ii) for `beta in [0,1)` |
| general-tikhonov | `Discrete/General/Tikhonov` | `cor:tikhonov` for `eps in (0,1]` |

Integration (this step):
- imported the twelve new `Helps` modules from `Helps/All.lean` (module docstring now maps
  the merged labels) and added `Discrete/General/All.lean`, imported from `SparseSGD.lean`;
  full `lake build` passed with no name clashes and no source change to the new files;
- re-froze `source/v2/momentum_helps.tex` and added `source/v2/chunks/` with hashes;
  `verify.py` now requires every `required_live_chunks` entry to be hashed and resolves
  the `relaxed_by` and `v1_declarations` names;
- registered `app:rates` (definition), `lem:chi_roots`, `lem:step_spectrum`,
  `lem:small_delta`, `rem:sgd_cost`, `rem:crit_single`, `rem:schedule`, `lem:vocab_rows`,
  `prop:vocab_full`, `rem:retention-cap`; rewrote `lem:helps-onecopy` (as
  `lem:step_speed`), `cor:samplecost`, `lem:speedup`, `lem:helps-vocab`,
  `prop:helps-critical`; moved the hyperbola and SGD comparison of `cor:samplecost` to
  `rem:crit_single` and `rem:sgd_cost`; re-sourced `lem:L1`, `lem:L2`, `cor:stab`,
  `cor:tikhonov`, `cor:lift` to the live chunks;
- taught `scripts/coverage.py` the `v1_restricted` status and the `relaxed_by` /
  `v1_declarations` fields;
- ran `scripts/verify.py`, which passed (373 modules, 847 obligation references).

Status against the current tex:
- complete: `lem:chi_roots`, `lem:helps-sgd`, `lem:step_speed` = `lem:helps-onecopy`,
  `lem:step_spectrum`, `lem:small_delta`, `lem:ray`, `cor:sample_cost`, `rem:sgd_cost`,
  `rem:crit_single`, `prop:fixed_floor` (with corrections MF-1, MF-2), `lem:vocab_rows`,
  `lem:helps-vocab`, `lem:helps-twocurv`, `prop:helps-critical`, `prop:vocab_full`;
  `lem:L1`, `lem:L2`, `cor:stab`, `cor:tikhonov`; `app:rates` defined;
- partial: `rem:schedule` (statistical interpretation), `rem:retention-cap` ((b));
- v1_restricted: `cor:lift` (matched form of (i));
- supporting: `lem:helps-rate`, `lem:helps-roots`, `lem:helps-transfer`,
  `cor:helps-speedup`.

Next work items (Lean only):
- `rem:retention-cap` (b): `limsup R_k^(1/k) >= rho(F)^2` from the cold start
  (Cauchy–Hadamard on `sum_k x_k z^k = (1 - beta z)/(1 - (1+beta-w) z + beta z^2)`, then
  `R_k >= a_k = R_0 x_k^2`).
- Done 2026-10-06: the matched-coordinate layer is relaxed to `beta in (0,1)` in
  `Comparison/General/` (`_v2` declarations); the matched form of `cor:lift` (i) is
  registered, and `def:matched`, `lem:match`, `lem:embed` are re-sourced to the live
  chunk 03 (see the README section "Matched layer for β ∈ (0,1)").
- Optional: the `rem:schedule` statistical sentence needs a cited statement first.

## Multi-agent execution

The coordinator owns shared interfaces, root imports, source coverage and final
integration. Three workers at a time own disjoint modules. Work starts with
gpt-6-luna at medium reasoning; failures retry with gpt-6.1-sol at high reasoning,
then gpt-6-astra at high reasoning. Assignments have bounded lemma families and
compile checks; a worker cannot replace a paper conclusion by an assumption.

First-tier retries repaired discrete matrix identities, renewal, matching,
quadrature, continuum calculus, sample moments, freshness, logistic calculus,
ODE containment and probability assembly. A second-tier retry completed the
long-window proof after a first-tier capacity failure. This records orchestration,
not measured billing.

The final review checked the actual process, minimum clock, corrected rate,
initial layers, probability-cap quantifier order and absence of assumed
containment or variational bounds. It also replaced all-dimension positive
teacher-norm premises in the power wrappers by eventual premises: dimension zero
cannot contain a vector of positive norm. `Examples/LogisticTeacher.lean` constructs
a family satisfying the corrected norm premise.

## Verification

Run `python3 scripts/verify.py`. It checks every local module is reachable from
`SparseSGD.lean`, builds the root target, audits all authored declarations and
private helpers with transitive dependencies, resolves every source-obligation
reference, regenerates coverage, and checks the 29 frozen v1 source hashes and the
v2 hashes in `source/v2/manifest.json`.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed axiom dependencies.
The authoritative output is `verification.log`; explicit external theorem
parameters are documented separately in `EXTERNAL_RESULTS.md`.

Final verification passed: 332 imported modules; 1,887 authored theorem
declarations; 4,501 audited declarations, including 3,766 kernel theorem
declarations; 281 resolved source-obligation references; all 29 source hashes
unchanged. Coverage: 27 complete or corrected results, zero partial or pending.
The ordinary and fixed-probability end-to-end logistic examples both compile.
