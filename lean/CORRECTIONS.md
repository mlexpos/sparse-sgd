# Statement audit

No corrected claim is considered proved until its declaration is recorded here.

## Obligations identified during planning

- Proposition D(v): `0 < theta*/r < 1` alone does not give a uniform positive
  lower bound, as needed for the asserted two-sided asymptotic comparison.
  Proved repair for bounded loads in `SparseSGD/Logistic/Bounds.lean`: if
  `0 ≤ Phi ≤ P`, then `r / exp(P/2) ≤ theta*` and
  `Phi / exp(P/2) ≤ Phi * theta* / r ≤ Phi`. For a fixed cap P this supplies
  uniform comparability. `equilibriumBulk_integerBatch_comparable` and
  `equilibriumBulk_fixedBatch_comparable` now establish the dimension-dependent
  comparison for actual natural-valued batch families with an eventual load cap.
  Status: corrected bounded-load claim proved.
- Corollary on curvature: the absolute `O(epsilonBar)` error requires control
  of the initial energy and additive forcing appearing in the preceding window
  estimate. Status: proved with the initial-energy and forcing factor retained in
  `ls_curvature_cells_risk` and `ls_curvature_cells_energy`.
- Power-law batch sizes must be integer-valued for probabilistic models.
  Rounding may alter quantitative rates; separate exact admissible families from
  asymptotic equivalence. Status: proved by the integer-family, resonance,
  load-limit and phase-cell modules; the exact rates are recorded below.
- Logistic drift permits a signed multiplicative coefficient. The algebraic
  recursion therefore has no positivity restriction; positivity is a separate
  hypothesis for renewal and stability arguments. Status: reflected in definitions.

## Full-paper implementation decisions

The user approved proving documented corrections while preserving the source
snapshot, and preserving S/W as explicit hypotheses.

- Matching at `|cos(theta)| = 1` is valid: the critical response is
  `-(ebar/4) * exp(-ebar/2)`, which is nonzero. The proof must handle this
  branch explicitly; it must not exclude these parameters.
- Discrete instability and strict continuum rank growth retain the standing PSD,
  nonnegative-load and positive-curvature assumptions. A determinant derivative
  identity alone does not prove strict rank growth.
- Logistic increment estimates will be stated on bounded stopped neighborhoods,
  with explicit bounds on signal, bulk energy and scaled momentum. Tameness alone
  does not justify the asserted uniform constants; the squared-gradient terms
  inside the signal/bulk frame also require bounds. Status: proved in `process_tame_matchedIncrement_dual_condLExp`,
  `lrIncrementVariance_le_source` and `lrIncrementScale_le_source`.
- The finite-horizon fluid result must prove its Jacobian-product and bootstrap
  conditions; cell-2 initial fast layers cannot be omitted by assuming all
  coordinates move on the slow clock. Status: proved in
  `cor_fluid_tame_cell_two_warm` and `cor_fluid_tame_cells_three_four`.
  The proof uses exact bounded powers of the free momentum map and a
  perturbation estimate; it does not assume slow motion of the initial layer.
- KL expansions retain `epsilon_B` alongside the small-load remainder. An
  `O(Phi)` relative error requires a separately established `epsilon_B = O(Phi)`.
  Finite-parameter fixed points also retain the `w,u_n` errors. Status:
  proved in `PopulationEquilibrium` and `FixedPoint` with those terms explicit.
- S does not, by itself, assert variational stability of every Jacobian product.
  W remains an explicit conditional input; neither is an external standard theorem.

- The abstract fluid theorem uses a deterministic reference initial state with
  almost-sure equality of the random initial state, so its Jacobian products are
  deterministic. For the non-strict radius condition, the Taylor and increment
  hypotheses must hold on closed balls; alternatively require a strict interior
  radius margin. Open balls and the source's non-strict bound do not suffice at
  equality. Status: proved by `SparseSGD.Logistic.fluid_limit_normingFamily` and its
  sup-norm specialization `fluid_limit_supNorm`.

- Proposition D's raw covariance limit requires a vanishing rare-class probability
  and bounded curvature-weighted bulk energy, or a comparable condition. The
  exact identity `C = -(1-beta) A R/(1+beta)` does not follow to zero from
  `w = eta (1-beta) A` tending to zero alone when eta also varies.
  `tame_fixedPoint_covariance_tendsto` proves the corrected rare-class limit.
  `actual_tame_fixedPoint_signal` and `actual_tame_fixedPoint_bulk` prove explicit
  finite-parameter errors with constants 16 and 48 once `epsilon_B ≤ 1/12`;
  the bulk error retains `epsilon_B + w + |u_n|`.
- The long-window remark's strict separation of the slow and oscillatory rates
  requires positive noise load. At zero noise their clean decay rates coincide.
  The estimates in `Scaling/Window.lean` cover zero noise without asserting strict
  separation; `window_continuum_rate_bound` gives the actual spectral-rate error.

- Lemma B variance derivatives at variance zero are right derivatives on
  `[0,infinity)`. The second pure-variance derivative of A keeps its
  `(1/4) p alpha` main term, just as the first keeps `(1/2) p alpha`.
  `tame_scalarJets_first_second` and the actual scalar coefficient derivative
  identities prove the clarified first/second-order estimates.

- With a floor-rounded growing integer batch (`sigma > 0`), the resonance
  proof must include a relative batch error of order `d^(-sigma)`. Its
  generally valid rate is therefore `d^(-min(gamma,1,sigma))`; the printed
  rate needs `sigma >= min(gamma,1)` or exact admissible powers. For `sigma=0`,
  the realized fixed positive integer batch replaces the real prefactor in
  all limiting constants. Negative sigma cannot give the stated natural-valued
  batch power law. Qualitative phase exponents are unchanged. Quantitative
  rounding estimates are proved in `Scaling/IntegerRounding.lean`, `Resonance.lean`
  and `ResonanceFixed.lean`.

The LR increment variance bound also needs a bounded effective learning step on the stopped neighborhood. The centered squared bulk gradient includes the linear cross term `2 eta² A <theta_bulk, delta g>`. Its variance scales as `eta⁴ p³ R/B`, which is not uniformly absorbed by the displayed `eta² p/B` term if `eta p` is unbounded. The formal concentration application retains an effective-step bound (or the corresponding explicit coefficient factor); the intended small-step cells satisfy this extra condition. This is separate from bounding the state neighborhood.

The non-boundary lemma means that the three bookkeeping cuts introduce no additional phase boundary. Its literal final sentence needs qualification: genuine boundaries can intersect these cuts. For example, kappa = sigma intersects resonance at gamma = 1; crossing that intersection can change the cell. The gamma = 0 edge uses fixed momentum, and sigma = 0 uses the realized positive integer batch. The formal scaling statements keep the same exact parameter formulas and distinguish these actual boundaries.

The quantitative LR34 trajectory bound uses a common normalized initial state for the recursion and reference ODE. If they differ, their initial discrepancy must be retained in the error bound; the formal source endpoint requires equality. Its small-error and parameter-neighborhood conditions are explicit eventual hypotheses, and compact containment of the iterates is proved.


The finite-horizon fluid probability bound retains the linear Bernstein term
`M log(10 N / delta)` as well as the square-root variance term. The source proof
explicitly invokes `eta = o(sqrt(d / log d))` to discard this term, but the
corollary statement omits this condition. A polynomial horizon is also needed
to replace the confidence logarithm by `O(log d)`. The actual process theorem
`actual_matched_fluid_source_radius` retains the full finite bound. Its constants
refer to a bounded stopped neighborhood and the actual dimension/batch identity;
`lrIncrementVariance_min_clock_bound` proves the source min-clock variance bound.
`actual_matched_fluid_sqrt_dimension` proves the pure square-root rate under
explicit load, horizon and step-size bounds; `fluid_power_learning_absorption`
discharges absorption for power-law learning rates with alpha > -1/2, and
`fluidGridHorizon_eventually_le_polynomial` proves the actual polynomial horizon.
These conditions are explicit rather than inferred from tameness alone.

The logistic Gaussian variance coordinate is `q = theta^2 + R`, which is
nonnegative on physical states. Taylor estimates at `q=0` use derivatives within
the closed half-line. `fluid_limit_normingFamily_on_process` requires the Taylor
bound only between the physical process and deterministic reference states;
`rectangle_taylor_bound` and `variance_lift_taylor_bound` justify this formulation
without asserting smoothness at negative variance.

Assumptions S and W are explicit proposition-valued interfaces, not proved
results or added Lean axioms. `SourceAssumptionS` quantifies global exponential
attraction of physical states to the actual canonical dynamic-alpha equilibrium,
with uniform constants on compact positive-curvature parameter sets. It does not
assert variational stability. `SourceAssumptionW` makes the informal window claim
precise for actual drift recursions, actual fixed points and matched bulk-energy
units. Its input records vanishing tame error and noise load, bounded forcing
and initial energy, small adjacent coefficient changes, and local stability,
Nyquist and internal-resonance margins. It existentially supplies continuous
coefficient interpolations agreeing with the actual retention grid; its averaged
equations and all-time comparison are assumptions. These hypotheses delimit the
formal interpretation of the source's informal window statement. Neither S nor W
is used to prove the finite-horizon fluid bound in cells 2--4.

The cell fluid corollary is formalized for fixed teacher norm, a finite limiting
load, a fixed finite horizon and controlled deterministic initial data. In cell
2, arbitrary bounded matched momentum is allowed; the common effective initial
slow state is `(theta - beta*Y, R - 2*beta*U + beta^2*V)` in matched coordinates.
In cells 3--4, the common initial state is fixed in the normalized dynamic
coordinates and satisfies the physical covariance inequalities. The actual
random chain and its deterministic drift start at the same state. These initial
conditions make explicit the data on which the uniform constants depend.

For fixed, nonvanishing rare-class probabilities (`kappa=0`), “tame regime” is
made quantitative: `cor_fluid_tame_cell_two_warm` and
`cor_fluid_tame_cells_three_four` prove the existence of a positive probability
cap before choosing the dimension-indexed family. The cap depends on the fixed
teacher, load, horizon, initial data and polynomial horizon exponent; probabilities
below that cap give the same square-root concentration rate. The cap is not
claimed to be uniform over unbounded horizons or initial data. Vanishing
probabilities eventually satisfy every such cap. The deterministic reference
bounds, global existence on the needed finite interval, physical-state
preservation, derivative bounds and stochastic bootstrap are all proved. No
path-containment assumption or S/W hypothesis is used in these final endpoints.
The constants in the displayed rate may depend on these fixed data; no uniformity
over unbounded teacher norms or loads is asserted merely by displaying the factor
`(1+Phi)^3*(1+r^2)`.

The actual power-law specializations use natural-valued rounded batches and the
floor of the minimum-clock horizon. The fixed-probability regular wrapper fixes
`delta>0` first and sets `epsilonStar=etaStar*pStar/delta`; its rarity cap is thus
chosen before `pStar`, rather than depending circularly on the probability through
the limiting clock ratio. Positive teacher norm is required eventually in the
dimension, since dimension zero contains only the zero vector.
