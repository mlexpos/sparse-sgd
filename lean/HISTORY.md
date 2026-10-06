<!-- Generated from the development README of the formalization; see README.md for the guide. -->
# Sparse SGD formalization

Lean 4.34.1 / Mathlib v4.34.1, revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The formalization covers all 27 registered results of the frozen manuscript,
with the approved corrections in `CORRECTIONS.md`. The three manuscript
assumptions G/S/W and the matched-coordinate definition are recorded separately.
Cited standard results remain explicit theorem parameters, as permitted by the
completion contract. `coverage.json` records each source result and its public
Lean declarations. The v1 snapshot in `source/` (hashes in `source/manifest.json`) is
unchanged; the v2 appendix drafts are frozen separately in `source/v2/` (see the V2 section
below).

## Notation

On 2026-10-05 the paper renamed its main quantities; the Lean identifiers kept their names.
The paper's stiffness `ω²` is `Δ`/`delta`/`Delta` here, the per-step curvature `λ` is `w`,
the feedback `H`, `H_n`, `H_c`, `H̃` is `Params.totalLoad`/`u`, `Params.noise`/`un`,
`Params.curvature`/`uc`, `Params.renormNoise`, the ambient temperature `φ` is
`Params.additive`/`phi`, and the LR curvature factor `ϱ` is `alpha` in the `Logistic` modules.
The paper's eigenvalues are now `z`, and the earlier "load" is "feedback" or "ambient
temperature". `NOTATION.md` has the full table, and `SparseSGD/Foundations.lean` carries it
as its module docstring. Entries below written before 2026-10-05 use the earlier notation.

From this directory:

```sh
export ELAN_HOME="$(cd .. && pwd)/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
lake build
python3 scripts/verify.py
```

The local dependency uses `../.lake/packages/mathlib`; `.lake/packages` links to
the parent's resolved packages to reuse the cache. For an independent checkout,
replace the Mathlib `path` entry in `lakefile.toml` by
`git = "https://github.com/leanprover-community/mathlib4.git"` and
`rev = "d13f23b723b8a846827a245b89c10fc7d3f11612"`, then run `lake update`
and `lake exe cache get` with the pinned toolchain.

## Trust boundary

No paper-specific result may be introduced as an axiom. Cited external results
may be explicit, documented hypotheses with their application conditions proved.
The manuscript's oracle assumption and assumptions S/W remain distinct from
external theorems. Missing hypotheses or incorrect claims are tracked in
`CORRECTIONS.md`; the linked manuscript is never modified.

`scripts/verify.py` checks the frozen source hashes, requires every project module
to be reachable from the root import, builds the project, and runs `Audit.lean`.
The audit examines all declarations defined in project modules, including private
helpers and their transitive dependencies; it rejects `sorryAx` and nonstandard
axioms. Its output is saved in `verification.log`. An explicit theorem hypothesis
does not appear as an axiom dependency: read `EXTERNAL_RESULTS.md` and the exported
types to see the assumed Jury criterion, Gaussian Stein identities, scalar Bernstein
inequality and each
theorem's other prerequisites.

## Implemented components

- Actual sparse Gaussian minibatch SGD with a global Bernoulli mask and independent
  centered square-integrable label noise: conditional oracle identities, recursively
  proved square integrability, and the full deterministic moment trajectory.
  Initial error and scaled momentum may be correlated.
- General conditional-oracle L2 propagation and exact moment reduction; discrete
  positivity, renewal, kernel masses, geometric convergence, floor and necessity
  of the feedback threshold.
- The actual continuum flow: uniqueness, covariance and scalar renewal formulas,
  real Laplace transform, mass and variation bounds, exponential stability,
  Perron rate, modal inversion and strict rank growth.
- Exact matching in all damping and sign branches, normalized impulse embedding,
  exponential quadrature, controlled large-parameter modes, and the complete
  uniform-in-time moment comparison for risk and both eigenfunctionals.
- The long-window corollary: all-time slow/oscillatory comparison, risk
  reconstruction, finite local averaging and the actual spectral-rate bound.
- The curvature-ceiling limits, rate ordering and matched-step trajectory/local-average bounds.
- The full small-Delta corollary, uniform over all iterations and including fixed momentum.
- The full regular scaling corollary: quantitative risk convergence over all times,
  uniformly on compact positive curvature sets.
- The matched square-root oscillator and its defect, actual integer-batch learning
  and regular limits, corrected resonance rates, actual window/curvature families,
  activity probabilities, and exponent classification.
- Actual logistic sampling and minibatch process, five-variable Markov reduction,
  exact conditional drift, quantitative tame coefficients and all first/second derivatives, exact drift
  fixed-point identities and error bounds, equilibrium bias, small-temperature expansion,
  Jacobian and bounded-temperature scaling with actual integer minibatches.
- Actual population loss, gradient and Hessian, with the corrected equilibrium KL floor.
- Actual five-coordinate logistic increment concentration, including rare-event linear and quadratic terms, constructed Gaussian frames, and full-history conditional MGF bounds.
- Actual dynamic-alpha finite-horizon drift convergence with a proved compact bootstrap;
  full-interval rank-one oscillator lift; slow-system global existence and convergence, zero-bulk boundary cases and an invariant rectangle.
- The general stopped fluid theorem with a finite norming dual family: conditional
  concentration, predictable stopping, union bound and nonlinear bootstrap.
- Actual scalar Gaussian projection and mean/variance calculus (including the
  variance-zero boundary), higher sigmoid derivatives and their tame integral bounds.

The final fluid endpoints are `cor_fluid_tame_cell_two_warm` and
`cor_fluid_tame_cells_three_four` in `Logistic/FluidTameComplete.lean`. They compare
the actual sampled chain with its actual deterministic drift, uniformly over a
finite minimum-clock horizon, with error `C*sqrt(log d/d)` and probability at
least `1-d^(-10)`. A positive rare-class cap is proved before choosing the family;
this covers sufficiently small fixed probabilities as well as vanishing ones.
Warm cell-2 momentum, physical-state preservation, finite-horizon ODE existence,
containment, Jacobian products and the stochastic bootstrap are all proved.
The explicit initial-data, step-size and horizon requirements are documented in
`CORRECTIONS.md`; S/W are not used for these finite-horizon conclusions.

`obligations.json` records individual subclaims and their Lean declarations;
`coverage.json` is generated from that registry. Remarks are discussion: no numbered
result in the paper relies on a remark, and only numbered results are formalized; remarks
that are proved are listed, others are recorded as not required (status
`remark_not_required`, reported separately by `scripts/coverage.py`). All 27 result entries are
complete or complete with documented corrections (v1 registry), with no partial or pending
entries. The final verification passed: 332 imported modules, 1,887 authored
theorem declarations, 4,501 audited declarations (3,766 kernel theorem
declarations, including generated helpers), 281 source-obligation references
and all 29 frozen source hashes. Only `propext`, `Classical.choice` and
`Quot.sound` occur as axiom dependencies. `verification.log` records the full
build and trust audit.

`SparseSGD/Examples/OneStep.lean` is a small runnable formalization example: a
specified cold-start update has risk `75/128` and covariance determinant `3/128`.
The regular build checks its exact rational calculation.
`SparseSGD/Examples/LogisticFluid.lean` is an end-to-end stochastic fluid
application with unit teacher norm, `B=d`, `eta=p=1/d`, `beta=1/2` and a zero
initial state. Lean discharges every parameter-family, containment and rate
hypothesis; the documented generic probability certificates are its only
external inputs. A second example in
`SparseSGD/Examples/LogisticFixedProbability.lean` constructs an admissible fixed
positive probability from the proved cap and discharges the same family
conditions for the `kappa=0` branch.

## V2 (revised appendix)

The v2 drafts `source/v2/lr5_global_stability.tex` and `source/v2/lr_windows.tex`
replace the v1 assumptions `ass:S` and `ass:W` by proved results and a narrower
assumption `ass:W2`. They are frozen in `source/v2/manifest.json`, and
`scripts/verify.py` checks them in addition to the 29 v1 hashes. The modules are in
`SparseSGD/Logistic/V2/`, namespace `SparseSGD.Logistic.V2`. `V2/All.lean` imports
all of them and is imported by `SparseSGD.lean`.

v1 versus v2. The v1 declarations `SourceAssumptionS`, `SourceAssumptionW` and
`LRWindowInput` (`Logistic/SourceAssumptions.lean`) are kept unchanged. Their
docstrings mark them as v1, and no theorem consumes them. In the registry, `ass:S`
and `ass:W` have status `v1_superseded` and a `superseded_by` list.

What v2 proves:

- `prop:S`, complete with corrections V2-1 and V2-2. The bundled statement is
  `V2.prop_S`.
  - Lyapunov function and dissipation identity: `Lyapunov.lean`.
  - `Q' = -2Q + 2bR`, and `Q > 0` for `t > 0`: `PositiveDeterminant.lean`.
  - Global existence, boundedness and convergence for `Phi* >= 0` (`prop_S_i`):
    `GlobalConvergence.lean`, with the Barbalat lemmas in `Barbalat.lean`.
  - Hurwitz Jacobian via `A^T H + H A = -S` and the observability determinant
    (`prop_S_ii`): `Hurwitz.lean`.
  - Uniform exponential rate on compact initial data and parameters
    (`prop_S_iii`, `prop_S_iii_proportional`): `UniformRate.lean`, using
    `LyapunovCertificate.lean`. The constant depends on the compact set of initial
    states, so v2 does not prove the all-physical-states form of v1
    `SourceAssumptionS`.
- `prop:W1`, complete with corrections V2-3 and V2-4.
  - Exact algebra of `Omega`, `D`, `H`, `S`, the frequency quartic, the null vectors,
    the Rayleigh shifts, and the exact trace identity `lambda_0 + 2 mu_1 + 2 mu_2 = -4`:
    `LargeDeltaAlgebra.lean`.
  - Large-`Delta*` eigenvalue asymptotics: `LargeDeltaPerturbation.lean`. It
    shows that all five eigenvalues are within `K/sqrt(Delta*)` of the predicted
    values, and `lambda_0` within `K/Delta*`. The proof uses the explicit
    characteristic polynomial, not analytic perturbation theory.
- `cor:recursion`, partial.
  - Abstract contraction, fixed point, tracking and Jacobian products:
    `RecursionContraction.lean`.
  - Tame-coefficient drift recursion (`cor_recursion_tame`, and
    `cor_recursion_tame'` with uniform entry discharged by `prop:S` (iii)):
    `RecursionTame.lean`.
  - Not formalized:
    - the actual Gaussian-coefficient recursion of `prop:LR34`;
    - uniformity of the constants over compact sets of `(Delta*, Phi*, r)` (V2-6).
- `prop:W2`, partial.
  - Window map, fixed point and Jacobian; `det J0 = 1`, `det(J0 - I) = 0`,
    `det(J0 + I) = -(w-2) P(w)`; characteristic polynomial; `p(±2)`;
    discriminant; `0 < w_c < 2`; and the `R -> 0+` limit: `WindowMapAlgebra.lean`.
  - Unit-circle spectrum with simple eigenvalues for `0 < w < w_c`, and period
    doubling of the undamped map at and above `w_c`: `WindowUnitCircle.lean`.
  - The instability of the drift recursion is proved for any Jacobian family
    converging to `J0`. That the drift-recursion Jacobian converges to `J0` is a
    hypothesis (V2-8).
- `ass:W2`, an assumption. It is stated as the `Prop` structure
  `V2.AssumptionW2` in `V2/All.lean`. It is not an axiom, and nothing consumes it.

The discussion around `prop:W1` is not formalized. This covers the nonzero
`R`-components of the eigenvectors at large `Delta*` and the generic excess-risk
rate.

### V2 momentum-helps appendix

*History. This subsection describes the state against the first 2026-10-05 snapshot
(sha256 `f8c99009...8c32`). It is superseded by the section "V2 merged appendix
(2026-10-05)" below, which describes the current snapshot, modules and coverage.*

Source: `source/v2/momentum_helps.tex` (section `sec:helps-app`, now "Benefits of
momentum"), re-frozen on 2026-10-05 in `source/v2/manifest.json` after the tex was
merged with a co-author's (KE's) version of the section. The modules are in
`SparseSGD/Scaling/Helps/`, namespace `SparseSGD.Scaling.Helps`. `Helps/All.lean`
imports all of them, bundles the main statements and is imported by
`SparseSGD.lean`. No `.lean` file changed in the re-pin.

The merged tex has two layers. KE's statements are `lem:chi_roots`,
`lem:step_speed`, `lem:step_spectrum`, `lem:small_delta`, `lem:ray`,
`cor:sample_cost` (alias `cor:samplecost`), `prop:fixed_floor` (alias
`lem:speedup`), `rem:schedule`, `lem:vocab_rows` and `prop:vocab_full` (alias
`rem:vocab`). EP's kept statements, in subsection `app:critical_batch`, are
`lem:helps-sgd`, `lem:helps-onecopy`, `lem:helps-vocab`, `lem:helps-twocurv` and
`prop:helps-critical`. EP's `lem:helps-rate`, `lem:helps-roots`,
`lem:helps-transfer` and `cor:helps-speedup` were dropped from the tex. Their Lean
proofs are kept: the registry marks them `supporting`, with a note naming the
nearest surviving tex statement. The labels `lem:ray`, `cor:samplecost` and
`lem:speedup` now point to KE's statements, which were compared with what Lean
proves. Notation in the tex changed (`\mathcal L -> \mathcal T`, `log -> ln`,
`V, kappa_V -> |\mathcal V|, kappa_{\mathcal V}`, `p_1, p_V -> p_max, p_min`); Lean
names are unchanged.

Conventions. The per-step rate `Lambda = -log rho(L)` is `perStepRate`. Here
`rho(L) = stepRadius` is the maximal modulus of the roots of the closed-form
characteristic polynomial `stepCharPoly` of the linear part, and
`det_stepLinearMatrix` identifies that polynomial with `det(z - L)` for the 3x3
matrix of `L`. Lean has `Real.log 0 = 0`, so `Lambda = +infinity` (radius `0`) is
not encoded, and statements that need a finite rate assume a positive radius. For
`0 < beta` this is automatic by `beta_le_stepRadius`. The `eps -> 0` statements are
proved in uniform form: there are explicit `eps0` and `C` depending only on `nu0`,
resp. `(D, c)` or `K`. The "vary so that" formulations follow from these.

What is proved, against the 2026-10-05 snapshot:

- `lem:helps-sgd`, complete (`lem_helps_sgd`, `ls_beta_zero_sup`): `Helps/ExactRate.lean`.
- `lem:ray` (KE's statement), complete (`lem_ray_bundle`, `one_sub_two_rayDelta`):
  `Helps/Ray.lean`. Her `s`, `mu*(s) = 1 - e*` and `Delta* = (1 - e*^2)/2` are
  `nu`, `rayRate nu = 1 - nu * rayDelta nu` and `1 - 2 rayDelta = (nu rayDelta)^2`.
- `cor:samplecost` (KE's `cor:sample_cost`), partial: `Helps/ExactRate.lean`,
  `Helps/Limits.lean`.
  - (i), `N_1 >= Bp/ln(1/beta)`, follows from `perStepRate_le_neg_log_beta`, applied
    to every LS point. The `sSup` step is not a separate declaration.
  - (ii), `N_1 = N(1+o(1))` along a co-scaling ray with `gamma > 0`. It is
    formalized only on the resonance line, where `s -> s0` in `(0, infinity)`:
    there `cor_samplecost` gives `|N_1/N - 1| <= C eps^(1/3)` uniformly on
    `s in [s0/2, 2 s0]`, which implies `o(1)`.
  - Not formalized: the case `s -> infinity`, whose tex proof uses `lem:small_delta`
    (no Lean counterpart; the Lean curvature cap loses a factor 8), and the case
    `s -> 0`. All the ingredients of the `s -> 0` case are in Lean, but they are
    not assembled.
  - `rem:crit_single`'s hyperbola and `rem:sgd_cost`'s comparison are also
    formalized (`hyperbola_relation`, `lsNfoldSGD_le`).
- `lem:speedup` (KE's `prop:fixed_floor`), complete: `cor_helps_speedup` gives the
  `eps -> 0` ratio limit `Gamma(Delta, u_n)` uniformly on compacts, and `lem_speedup`
  gives (i) `Gamma < 2` and (ii) `Gamma(1/4, u_n) = 2/(1+a+a^2)` for `u_n` in `(0,1)`.
  For LS, `u_n > 0` holds automatically. At `u_n = 0`, (i) would fail with
  equality at `Delta = 1/4`; see `CORRECTIONS.md`, MH-2. The text after the
  proposition (the ratio `1 + Delta(1-3u) + O(Delta^2)` and the `u < 1/3`
  dichotomy) is also formalized. Part (iii) of the old lemma is proved by an
  explicit real-root bracket instead of the implicit function theorem.
- `lem:helps-onecopy`, complete (`perStepRate_le_onecopy`): `Helps/ExactRate.lean`.
  `beta_le_stepRadius` also proves KE's `lem:step_speed`, which is not registered.
- `lem:helps-vocab`, partial: `Helps/Vocabulary.lean`, with the asymptotic clause
  of (iii) in `Helps/Limits.lean`. `min_j Lambda_j` is formalized as
  `Lmin = -log max_j rho(L_j)`. Part (i) uses the Jury hypothesis. Everything
  except the last claim of (iii) is formalized exactly.
  - The merge rewrote the last claim of (iii) as "along a co-scaling ray with
    `gamma > 0`, `1/Lambda_min >= (d+2-p_min)/(B p_min)(1+o(1))`".
  - `helps_vocab_asymptotic` implies the rewritten claim on the resonance line.
  - For `s -> 0` it follows in two lines from `perStepRate_le_neg_log_beta`, but
    no Lean statement records it.
  - For `s -> infinity` it is not formalized.
- `lem:helps-twocurv`, complete: `Helps/CriticalBatch.lean`. The real-variable core
  is `twocurv_real`. `rhoMax_ge_twocurv` transfers it to the radius of `L` through
  `rho(L_j) >= rho(F_j)^2`. The spectral radius of `F` is not defined in Lean: `r`
  enters through `beta <= r^2` and through the bound on the moduli of the real
  eigenvalues.
- `prop:helps-critical`, complete: `Helps/CriticalBatch.lean`, bundled as
  `prop_helps_critical`. The definitions are as follows. `A_O(B)` is `admSet`: the pairs
  with `eta > 0`, beta in `sgdClass = {0}` or `momClass = [0,1)`, and every `stepRadius < 1`.
  `S_O(B)` is `Sfun`, an `sInf` of `1/Lmin` over `admSet`. `E_O(B)` is `Efun = B * Sfun`.
  `S_O` and `E_O` are `Sinf` and `Einf`, an `sInf` over integers `B >= 1`, and `B_O` is
  `Bcrit`. The admissible sets are nonempty (`sgd_point_mem`). What is proved:
  - (i) exactly (`helps_critical_i`, at `kappa_V > 1`);
  - (ii) for SGD exactly, and `E_mom <= E_SGD` (`helps_critical_ii`);
  - the momentum lower bound of (ii) with `c_kappa = max(1 - 4/sqrt kappa_V, 1/sqrt 5)`
    (`helps_critical_ii_mom'`, `kappa_V > 16`);
  - (iii) for SGD, the ratio bounds with `c_kappa`, and the closing claim that the left
    side is at least `sqrt(kappa_V)/19` (`helps_critical_iii_sgd`,
    `helps_critical_iii_ratio'`, `Bratio_ge'`, `Bratio_ge_div19`);
  - the finite-`B` lower bounds and `S_O(B) -> 1/lambda_O` (`helps_critical_finiteB`);
  - the remark on `E_mom = E_SGD` (`Bratio_of_Einf_eq`).

  The route for `c_kappa` is `phi(m) >= sqrt(1-m)` (`neg_log_one_sub_le_div_sqrt`), then
  `m <= m_kappa = 4/(1+sqrt(1+kappa_V))` (`min_le_Mk`), `1 - m_kappa > 1/5` and
  `m_kappa < 4/sqrt kappa_V` (`Mk_props`, `cK_le_sqrt_one_sub`); the monotonicity of `phi`
  is not needed. The `sqrt(kappa_V)/19` claim uses `d >= 0` only. The earlier weaker forms
  with `1 - 4/sqrt(kappa_V)` alone (`helps_critical_ii_mom`, `Bratio_ge`,
  `helps_critical_iii_ratio`) remain as lemmas. The module needs no Jury hypothesis.

Supporting entries: their statements were dropped from the tex, but the Lean proofs
are kept and other entries use them.

- `lem:helps-rate`: the stability equivalence `u < 1` iff `rho < 1` in
  `Helps/Stability.lean`, used by `lem:helps-vocab` (i). On the Lean side it is
  partial, since the fixed point and the `limsup` rate were never formalized.
- `lem:helps-roots`: cubic root continuity in `Helps/RootPerturbation.lean`.
- `lem:helps-transfer`: the uniform `C eps^(4/3)` transfer in `Helps/Transfer.lean`,
  the quantitative form of the "`r/eps = r_c + o(1)` on compacts" step in KE's
  proofs. `helps_transfer_box` holds on `{Delta <= D, u_n <= U}`.
- `cor:helps-speedup`: `cor_helps_speedup`, now cited under `lem:speedup`.

The proofs of `lem:helps-rate` and of `rem:stab-large-w` use a generating-function
identity for the squared kick response. The 2x2 Jury criterion
`External.JuryStability` is an explicit hypothesis.

Not registered: KE's new statements `lem:chi_roots`, `lem:step_speed`,
`lem:step_spectrum`, `lem:small_delta`, `rem:schedule`, `lem:vocab_rows` and
`prop:vocab_full` (alias `rem:vocab`), and the remark `rem:helps-numerics`. Some of
them are already partly proved:

- `lem:step_speed` by `beta_le_stepRadius`;
- `lem:chi_roots` (c) for `u` in `(0,1)` by `continuumPerronRate_quarter_cube`;
- in `prop:vocab_full` (ii), the SGD and tuned-`beta` limits by
  `prop:helps-critical` (i) and `helps_critical_finiteB`. The fixed-`beta` formula,
  the `B - 1 <= B_x` threshold of (i) and the "about" forms of (iii) are not
  formalized.

The integration renamed the Vocabulary copy of `neg_log_one_sub_le` to
`neg_log_one_sub_le_vocab`, because it clashed with the identical lemma in
`Limits.lean`.

Trust boundary: unchanged. There are no paper-specific axioms and no `sorry`.
`Audit.lean` admits only `propext`, `Classical.choice` and `Quot.sound`. Every V2
declaration named in `obligations.json` is resolved by `#check`.

Verification after the 2026-10-05 re-pin passed. The `momentum_helps.tex` snapshot
is byte-identical to the merged revised appendix, with sha256 `f8c99009...8c32`;
the earlier snapshot was `3bdf52f5...de74c`. Results:

- 358 imported modules and 2,558 authored theorem declarations;
- 5,924 audited declarations, of which 4,989 are kernel theorems;
- 599 source-obligation references;
- 29 v1 and 3 v2 frozen source hashes.

`scripts/coverage.py` now reads an optional `tex_status: "supporting"` (with
`supporting_note`) from `obligations.json`. It reports such an entry as `supporting`
and keeps its Lean-side status in `lean_status`. It also mirrors `kind`, `title`
and `tex_labels` into `coverage.json`.

Coverage:

- 35 entries complete or complete with corrections;
- 4 partial: `cor:recursion`, `prop:W2`, `cor:samplecost` and `lem:helps-vocab`;
- 4 supporting: `lem:helps-rate`, `lem:helps-roots`, `lem:helps-transfer` and
  `cor:helps-speedup`;
- 2 assumptions: `ass:G` and `ass:W2`;
- 2 `v1_superseded`: `ass:S` and `ass:W`;
- 1 definition.

## V2 merged appendix (2026-10-05)

Sources, frozen in `source/v2/manifest.json` and checked by `scripts/verify.py`:

- `source/v2/momentum_helps.tex`, section "Benefits of momentum", after the merge with
  KE's section and the harmonization pass (sha256 `90c5bcc8...5c07`, byte-identical to
  `paper/appendix/momentum_helps.tex`). The harmonization defines one decay rate
  `Lambda := -ln rho(T)`, merges `lem:step_speed` and `lem:helps-onecopy` (`beta in [0,1)`),
  moves `lem:helps-sgd` to `app:rates`, adds `lem:helps-vocab` (v), the limit in
  `prop:helps-critical` (i), absolute bounds on `B_mom` in (iii) and the fixed-`beta` part
  (iv), and makes `prop:vocab_full` follow and cite `prop:helps-critical`.
- `source/v2/chunks/{01,02,03,04,05,07,08}_*.tex`: copies of the live appendix chunks
  (`paper/appendix/unified/chunks/`), which state the master reduction and the renewal
  section for `beta in [0,1)`. They are listed under `required_live_chunks` in the
  manifest, and `verify.py` fails if one of them has no hash. The v1 snapshot in
  `source/` (including `source/chunks/`) is frozen and unchanged.

### Modules

New modules in `SparseSGD/Scaling/Helps/` (namespace `SparseSGD.Scaling.Helps`), all
imported by `Helps/All.lean`:

| Module | Content |
| --- | --- |
| `ChiRoots` | `lem:chi_roots` (a)-(e) for `u in [0,1)`, `u = 0` included; (d) with the constant 18 for `Delta <= 1/50` |
| `StepSpeed` | `rho(F)` as `meanRadius`; `lem:step_speed` = `lem:helps-onecopy` for `beta in [0,1)`; `rem:retention-cap` (a); the Step 6 facts (symmetry, monotonicity) |
| `StepSpectrum` | `lem:step_spectrum`: the cubic `q`, eigenvalues `1 + eps z`, `|b_i| <= 1 + (16/3) Delta + eps Delta^2`, `q - chi` |
| `SmallDeltaSlowRoot`, `SmallDeltaFactor`, `SmallDelta` | `lem:small_delta`: slow-root bracket, factorization and fast roots, `|theta| <= 25(eps+Delta)`, LS form |
| `SampleCostAbove` | `cor:sample_cost` (i), case `s -> 0` of (ii), `rem:sgd_cost` |
| `SampleCost` | `cor:sample_cost` (ii) case `s -> infinity`, uniformity in `s` and the co-scaling form; `rem:sgd_cost`; co-scaling clauses of `lem:helps-vocab` (iii) and `prop:vocab_full` (i) |
| `Schedule` | `rem:schedule`: Chung's lemma and `k R_k -> varsigma^2 d/(Bp)` |
| `FixedFloor` | `prop:fixed_floor` = `lem:speedup`: the limit for `u in [0,1)`, (i) with the equality case, (ii) at `u = 0`, the exact counterpart, critical damping against `2 eta`, the paragraph after the proof |
| `VocabRows` | `lem:vocab_rows`: row decoupling in law, row recursion, excess loss |
| `VocabFull` | `prop:vocab_full` = `rem:vocab` (i)-(iii) and the remark after it |

Extended in place (new declarations appended, no existing signature changed):
`Vocabulary` (`lem:helps-vocab` (iii) for `beta in [0,1)` and (v), bundle
`lem_helps_vocab_v2`) and `CriticalBatch` (`prop:helps-critical` (i) limit, (iii) absolute
bounds, (iv), bundle `prop_helps_critical_v2`).

New directory `SparseSGD/Discrete/General/` (namespace `SparseSGD`, suffix `_v2`), imported
by `General/All.lean` and from `SparseSGD.lean`:

| Module | Content |
| --- | --- |
| `Renewal` | `lem:L2`, `cor:stab` (i)-(iii), `cor:lift` (ii) and rank at most one, for `beta in [0,1)` |
| `Tikhonov` | `cor:tikhonov` for every `eps in (0,1]` (`cor_tikhonov_v2`) |

### Coverage against the current tex

| Label | Status | Lean |
| --- | --- | --- |
| `app:rates` (definition of `Lambda`) | defined | `perStepRate`, `stepRadius`, `continuumPerronRate`; `Lambda = eps r_c (1+o(1))` by `helps_transfer`, `helps_transfer_compact` |
| `lem:chi_roots` | complete | `lem_chi_roots` |
| `lem:helps-sgd` | complete | `lem_helps_sgd`, `ls_beta_zero_sup` |
| `lem:step_speed` = `lem:helps-onecopy` | complete | `lem_step_speed`, `perStepRate_le_curvature_cap` |
| `lem:step_spectrum` | complete | `mem_stepRoots_iff_spectrumQ`, `abs_spectrumB_le`, `spectrumQ_sub_chi` |
| `lem:small_delta` | complete | `lem_small_delta`, `lsRate_small_delta` |
| `lem:ray` | complete | `lem_ray_bundle` |
| `cor:sample_cost` = `cor:samplecost` | complete | `lsNfold_ge_retention`; `samplecost_below`, `cor_samplecost`, `samplecost_above`, `cor_sample_cost_uniform`, `cor_sample_cost_tendsto` |
| `lem:sgd-cost` (alias `rem:sgd_cost`) | complete | `lsNfoldSGD_eq`, `lsNfoldSGD_mono`, `lsNfoldSGD_le_max`, `samplecost_ge_sgd_uniform` |
| `rem:crit_single` | complete | `hyperbola_relation` (the other sentences are readings, not claims) |
| `prop:fixed_floor` = `lem:speedup` | complete with corrections MF-1, MF-2 | `fixed_floor_limit_noise`, `fixed_floor_limit_total`, `speedupRatio_eq_two_iff`, `speedupRatio_quarter_all`, `fixed_floor_exact_counterpart`, `critical_damping_vs_double_lr`, `speedup_expansion_fixed_floor` |
| `rem:schedule` | remark, not required | `schedule_risk_asymptotic`; the Cramér–Rao/minimax sentence is not formalized |
| `lem:vocab_rows` | complete | `vocab_row_moment_trajectory_explicit`, `vocab_excess_loss_expectation` |
| `lem:helps-vocab` (i)-(v) | complete | `lem_helps_vocab_v2`, `helps_vocab_iii_coscaling` |
| `lem:helps-twocurv` | complete | `twocurv_real`, `rhoMax_ge_twocurv` |
| `prop:helps-critical` (i)-(iv) | complete | `prop_helps_critical_v2` |
| `prop:vocab_full` = `rem:vocab` | complete | `prop_vocab_full`, `vocab_full_i_coscaling` |
| `lem:L1` | complete | raw-oracle declarations (arbitrary real `beta`) |
| `lem:L2` | complete | `stable_kernel_masses_v2`, `kickResponse_beta_zero`, `normalized_kernel_*_v2` |
| `cor:stab` | complete | `trajectory_risk_*_v2`, `freeRisk_pos_v2`, `beta_zero_dark_start` |
| `lem:retention-cap` (alias `rem:retention-cap`, part (a)) | complete | `meanRadius_sq_le_stepRadius`, `meanRadius_sq_eq_beta_iff`, `perStepRate_le_neg_log_beta` |
| `rem:retention-cold` (part (b)) | remark, not required | limsup bound not formalized; ingredient `beta_le_meanRadius_sq` |
| `lem:stab-all` (alias `rem:stab-large-w`) | complete | `lem_stab_all_large_w`, `lem_stab_all`, `stepRadius_lt_one_iff` |
| `cor:tikhonov` | complete | `cor_tikhonov_v2` |
| `cor:lift` | v1_restricted | identities and (ii) for `beta in [0,1)`; matched form of (i) only for `1/2 <= beta` |
| `lem:helps-rate`, `lem:helps-roots`, `lem:helps-transfer`, `cor:helps-speedup` | supporting | dropped from the tex; Lean proofs kept |

Partial and restricted items, and why:

- `rem:schedule`: the closing sentence (the risk `varsigma^2 d/N` is that of least squares
  on the active samples, the Cramér–Rao bound and asymptotically the minimax risk) is an
  imported statistics claim without a citation; it is not formalized. The numerical check
  `1.0028` is a numerical remark and is not registered.
- `rem:retention-cap` (b), `limsup_k R_k^(1/k) >= rho(F)^2` from the cold start, is not
  formalized (Cauchy–Hadamard on the generating function of `e_1^T F^k e_1`).
- `cor:lift` (i), matched form `R_k = X(k ebar)^2`: the live tex states it for
  `beta in (0,1)`, Lean for `1/2 <= beta` only (`noiseFree_risk_squareRootLift_grid`). The
  matched-coordinate layer is shared with `thm:M` and keeps `1/2 <= beta`.

Not registered: the numerical remarks (`rem:helps-numerics`, the vocabulary numerics and
loss-curve paragraphs, the bigram experiment); in the discussion after
`prop:helps-critical`, the floor sentence `R_infinity = varsigma^2 d/(d+2)`.

### The momentum range `beta in [0,1)`

The live chunks state the master reduction and the renewal section for `beta in [0,1)`.
In Lean:

- Hold for `beta in [0,1)`: `lem:L1` (the raw-oracle declarations take an arbitrary real
  `beta`); `lem:L2` and `cor:stab` (`Discrete/General/Renewal`, with the new (iii)
  hypothesis `0 < s.R ∨ (0 < beta ∧ s ≠ 0)` and the counterexample
  `beta_zero_dark_start`); `cor:tikhonov` (`cor_tikhonov_v2`, `C = 538/margin + 8`);
  `cor:lift` (ii) and its noise-free identities; `rem:retention-cap` (a); and in the
  appendix `lem:step_speed`, `lem:helps-vocab` (iii), `prop:helps-critical` (iv).
- Remain at `1/2 <= beta`: the v1 declarations `stable_kernel_masses`,
  `trajectory_risk_*`, `cor_tikhonov`, `smallDelta_*` and the 25 `Comparison/*` and
  `Scaling/*` modules that depend on them. Their signatures are frozen, and the comparison
  theorem and its corollaries legitimately need `beta >= 1/2`: the live tex keeps
  `beta >= 1/2` for `thm:M`, `cor:regular`, `cor:resonance`, `cor:window` and `cor:curv`
  (`ebar <= log 2` in Steps 3 and 4 of the proof of `thm:M`).
- At `1/2 <= beta` in Lean but `beta in (0,1)` in the live tex: the matched form of
  `cor:lift` (i) (registered `v1_restricted`) and `def:matched`, `lem:match`, `lem:embed`,
  which stay registered against the v1 chunk. Relaxing the matched layer is a follow-up.

Registry. `obligations.json` gives each relaxed entry `source` (the live chunk),
`v1_source` and a `beta_range` note. A subclaim proved by a relaxed declaration is
`complete`, lists it under `relaxed_by` and keeps the old declarations under
`v1_declarations`. A subclaim proved only in the v1 range is `v1_restricted`.
`scripts/coverage.py` reports an entry `v1_restricted` when all its subclaims are proved
and some only for `1/2 <= beta`. `scripts/verify.py` also resolves every `relaxed_by` and
`v1_declarations` name by `#check`.

### Tex corrections (genuine; see `CORRECTIONS.md`, "V2 merged appendix")

- MF-1, `prop:fixed_floor`: "let `eps -> 0` with `(Delta,u)` fixed" is empty at `u = 0`
  (the total feedback is at least `u_c > 0`); read it with `u_n = u` fixed, or the total feedback
  tending to `u`. To apply.
- MF-2, the exact counterpart after `prop:fixed_floor`: add `u = u_n + eta p/2 < 1`. To
  apply.

### Verification

`python3 scripts/verify.py` passed after the promotion of `rem:stab-large-w`,
`rem:retention-cap` (a) and `rem:sgd_cost` to lemmas (2026-10-05): 373 imported modules,
2,866 authored theorem declarations, 6,586 audited declarations (5,587 theorems) with
only `propext`, `Classical.choice` and `Quot.sound`, 849 source-obligation references
resolved, 29 v1 and 10 v2 frozen source hashes (7 of them live chunks). Coverage: 44
complete numbered results (including corrected statements), 2 partial numbered results
(`cor:recursion`, `prop:W2`), 1 `v1_restricted` (`cor:lift`), 4 supporting,
2 `v1_superseded`; 3 remarks (discussion, not required): `rem:crit_single` fully proved,
`rem:retention-cold` and `rem:schedule` recorded as not required.

## Matched layer for β ∈ (0,1) (2026-10-06)

The live tex states `def:matched`, `lem:match`, `lem:embed` and the matched form of `cor:lift`
(i) for `β ∈ (0,1)`. The v1 matched-coordinate layer (`Comparison/ExactMatching`,
`Comparison/ExactEmbedding`, part of `Comparison/SquareRootLift`) assumed `1/2 ≤ β`, but used
it only to obtain `0 < β`. The new directory `SparseSGD/Comparison/General/` restates it for
`0 < β < 1` as new declarations with suffix `_v2`. Its modules are imported by `General/All.lean`,
which `SparseSGD.lean` imports.

| Module | Content |
| --- | --- |
| `Matching` | `lem:match`: 9 declarations, from `matchedMeanFlow_invariants_v2` to `exact_matching_existsUnique_v2` |
| `Embedding` | `lem:embed`: 16 declarations, through the v2 renewal lemmas of `Discrete/General/Renewal` |
| `SquareRootLift` | `cor:lift` (i), matched form: `noiseFree_risk_squareRootLift_grid_v2`, `comparisonFlow_squareRootLift_rank_v2`, and two supporting declarations |

Each `_v2` statement is the v1 statement with `1/2 ≤ β` replaced by `0 < β`.

Registry changes:

- `def:matched`, `lem:match` and `lem:embed` are re-sourced to the live chunk 03
  (`v2/chunks/03_master_theorem.tex`), with `relaxed_by` and `v1_declarations`.
- `cor:lift` is complete; it is no longer `v1_restricted`.
- `squareRootLift_defect` and `squareRootLift_oscillator_defect` keep `1/2 ≤ β`. The live
  statement of (ii) is proved by `trajectory_risk_defect_sup_bound_v2`.

Verification passed with:

- 377 modules and 2,895 authored theorem declarations;
- 6,635 audited declarations (5,633 theorems), using only the standard axioms;
- 862 source-obligation references;
- 29 v1 and 10 v2 frozen source hashes.

Coverage: 45 complete numbered results, 2 partial (`cor:recursion`, `prop:W2`), 0 v1-restricted.

## `prop:W2` (iii) for the drift recursion (2026-10-06)

`Logistic/V2/WindowDrift` defines `windowDriftMap r h eps Phi`. It is the tame drift
recursion of `lem:LRdrift`, with the tame coefficients of `lem:B` (`nu = 0`, `rho = 1`), in
the window variables `(theta, eta m, R, eta^2 V, eta C)` with `h = eta eps p`.
`windowDriftMap_conj` proves that it is conjugate to `tameDriftMap r eps (h/eps^2) Phi 0 1` by
the scaling `diag(1, h/eps, 1, (h/eps)^2, h/eps)`. The module also proves:

- `windowDriftMap_zero`: at `eps = 0` it is `windowMap`;
- `windowDriftMap_fixed`: its fixed points satisfy `m = 0`, `alpha theta = r`,
  `c = -h alpha R/(2-eps)` and `v = 2 h alpha R/(2-eps)` exactly;
- `windowDrift_fixedPoint_tendsto`: they converge to the window fixed point when
  `(theta, R)` does.

`Logistic/V2/WindowDriftJacobian` gives:

- the explicit Jacobian (`hasFDerivAt_windowDriftMap`), which is continuous in `(eps, x)` and
  equal to `J0` at `eps = 0`;
- `two_lt_windowUpper` and `prop_W2_iii_above_interval`, an eigenvalue below `-1` for every
  `w` in `(w_c, 2)`;
- `prop_W2_iii_drift`, statement (iii) for the drift recursion with no hypothesis on
  `J_eps`.

`prop:W2` is complete. `cor:recursion` is the only partial numbered result.

Verification passed with:

- 379 modules and 2,909 authored theorem declarations;
- 6,668 audited declarations (5,662 theorems), using only the standard axioms;
- 871 source-obligation references;
- 29 v1 and 10 v2 frozen source hashes.

Coverage: 46 complete numbered results and 1 partial.

## Orchestration

The coordinator owns interfaces, imports, configuration and integration. Three
workers at a time own disjoint files. Default: gpt-6-luna (medium); failed proof
attempts escalate to gpt-6.1-sol (high), then gpt-6-astra (high). Each assignment
has a bounded lemma family and a compilation check. Workers cannot add assumptions
or alter the shared interface without coordinator review.

## Least-squares process entry points

`SparseSGD/Probability/LeastSquares/Public.lean` exports
`leastSquares_process_memLp`, `leastSquares_conditional_oracle`, and
`leastSquares_conditional_gradient`. They construct the oracle from the actual
product sample law; they do not assume conditional moment identities.
`leastSquares_moment_trajectory` in `Trajectory.lean` identifies all three raw
integrated moments `(R,V,C)` with `Params.trajectory` for every iteration.

The batch size is positive. The oracle allows `0 ≤ p ≤ 1`; the normalized
trajectory requires `p > 0`. Label noise is centered with finite second moment,
and the initial joint law has square-integrable error and scaled momentum
`q = ηm`, independent of the future batch stream. No independence between the
initial error and momentum is required. `params_explicit` gives the manuscript's
parameters. The algebraic statements allow arbitrary real `β,η`, including the
manuscript's domain `η > 0`, `1/2 ≤ β < 1`.

`BoundaryCases.lean` checks zero/full sampling, batch size one and zero label
variance; `Process.lean` checks that an empty batch still applies momentum.
This milestone uses no cited external theorem assumptions.

`SparseSGD/Examples/LeastSquares.lean` instantiates the actual sampled-process
theorem with `d = B = p = 1`, zero label noise, deterministic unit initial error,
zero momentum, `β = 3/4` and `η = 1/4`. Lean verifies the one-step moments
`(R,V,C) = (227/256, 3/256, 13/256)`.
