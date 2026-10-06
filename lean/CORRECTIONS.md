# Statement audit

> **Notation (2026-10-05).** Entries here record corrections in the manuscript notation of
> their date: `Δ` (now the stiffness `ω²`), `w` (now `λ`), `u`, `u_n`, `u_c`, "load" (now the
> feedback `H`, `H_n`, `H_c`), "additive load" (now the ambient temperature `φ`), and the LR
> curvature factor `α` (now `ϱ`). See `NOTATION.md`.

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

## V2 drafts (revised appendix)

Sources: `source/v2/lr5_global_stability.tex` and `source/v2/lr_windows.tex`,
frozen on 2026-10-04 with hashes in `source/v2/manifest.json`. The Lean status of
each fix is given after it. The IDs V2-1 to V2-8 are the ones that `obligations.json`
refers to.

### Corrections and gaps

- **V2-1, `prop:S`, eq:LR5-dissipation and the coercivity step.** The identity
  `L' = -Y^2 - (V-b)^2/V - b^2 C^2/(QV)` holds on `{Q > 0}`, where physicality
  gives `R, V > 0`. Fix: write "Along \eqref{eq:LR5}, on $\{Q>0\}$," and add
  "when $\Phi^*=0$ the identity reads $\mathcal L'=-Y^2-V$ on all physical states".
  Lean: `V2.hasDerivAt_lyapunov` (with `0 < Q`, `0 < V`),
  `V2.hasDerivAt_lyapunov_zero_load` and `V2.dissipation_zero_load`. The lower
  bound `V2.lyapunov_lower_bound` and the compact sublevel sets
  `V2.lyapunov_sublevel_bounds` are proved under the same hypotheses. Proved.
  Applied to the tex on 2026-10-04.
- **V2-2, `prop:S` (iii), first sentence of the proof.** Continuity of the
  eigenvalues does not by itself give a neighbourhood and rate that are uniform
  over `P`. Fix: "By (ii), and since $y^*$ depends continuously on
  $(\Delta^*,\Phi^*,r)$ (the positive root of Proposition~\ref{prop:D} is
  continuous, by strict monotonicity of its scalar equation), so does the Jacobian. A
  quadratic Lyapunov matrix for the Jacobian at one parameter remains one, with
  half the rate, at nearby parameters. The field is $C^1$ jointly in parameters
  and state, so the remainder is $o(|y-y^*|)$ locally uniformly in the
  parameters." In the next sentence, "the same holds, with the same time" should
  read "the solution is within the local-stability radius at the same time $T$".
  Later times then follow from local stability. Lean:
  `V2.positiveRoot_continuousOn`, `V2.canonicalEquilibrium_continuousOn`,
  `V2.certificate_robust`, `V2.dynamicField_remainder_uniform`,
  `V2.prop_S_iii_proportional` and `V2.prop_S_iii`. Proved.
  Applied to the tex on 2026-10-04.
- **V2-3, `prop:W1`, hypotheses.** Fix: "Let $\Phi^*>0$" becomes "Let
  $\Phi^*>0$ and $r>0$, so that $\theta^*>0$". The definition $a=r/\theta^*$
  and the proof that $s_j$ is well defined both use $\theta^*\ne0$: the quartic
  at $a(1+\theta^{*2})$ equals $-a^2R^*\theta^{*2}$. Lean: `V2.freqQuartic_signal`,
  and `V2.oscillatory_eigenvalue_asymptotics` and `V2.five_eigenvalues` assume
  `θ ≠ 0`. Their equilibrium specialisations discharge this from `r > 0`
  (`V2.equilibrium_params_pos`). Proved.
  Applied to the tex on 2026-10-04.
- **V2-4, `prop:W1` proof, "Its characteristic polynomial is $-i\nu$ times
  ...".** Lean proves
  `det(λI - Ω) = λ(λ^4 + a(5+θ*^2+R*)λ^2 + a^2(4+4θ*^2+R*))`, which at `λ = iν` is
  `+iν` times the displayed quadratic in `ν^2`. Fix: "With
  $\det(\lambda I-\Omega)$, the characteristic polynomial at $\lambda=i\nu$ is
  $i\nu$ times ...". The roots are unchanged. Lean: `V2.omega_charpoly`. Proved.
- **V2-5, `cor:recursion`, uniqueness of the fixed point.** The proof gives
  uniqueness in the fixed ball $\mathcal N$, whose radius does not depend on
  $\varepsilon$. This is stronger than uniqueness within distance
  $M\delta_\varepsilon$. Fix: "has a fixed point $y^*_\varepsilon$ within
  distance $M\delta_\varepsilon$ of $y^*$, unique in a neighbourhood of $y^*$
  independent of $\varepsilon$". Lean: `V2.cor_recursion_tame` and
  `V2.cor_recursion_tame'`, with uniqueness in `closedBall y* s` and
  `C varrho0 ≤ s`. Proved for the tame coefficients.
  Applied to the tex on 2026-10-04.
- **V2-6, `cor:recursion`, uniformity in $(\Delta^*,\Phi^*,r)$.** The statement
  says that $M,c,\Gamma$ depend only on $K$ and on compact bounds for the
  parameters. The proof works at one parameter: it takes $P$ with
  $A^\top P+PA=-I$ for that $A$. Fix: add "By the robustness of $P$ used in
  Proposition~\ref{prop:S}(iii), $P$, $s_0$ and $c_0$ can be chosen uniformly
  on a compact parameter set, and $T_0$ is uniform there by
  Proposition~\ref{prop:S}(iii)". Lean: not formalized.
  `V2.cor_recursion_tame` fixes `(r, Δ*, Φ*)`. Its constants are uniform over
  the tube `|δ-Δ*| ≤ Δ*/2`, `ρ ∈ [0,1]`, `varrho ≤ varrho0` around that point,
  and they depend only on `(r, Δ*, Φ*, K)`.
  Applied to the tex on 2026-10-04.
- **V2-7, `prop:W2`, scope of $R^*>0$.** Parts (ii) and (iii) need $R^*>0$, but
  the statement attaches $R^*>0$ only to $0<w_c<2$. At $R^*=0$,
  $\mathsf d(w)=4(w-3+\theta^{*2})^2$ vanishes at $w=3-\theta^{*2}$. This lies
  in $(0,w_c)$ when, for example, $\theta^{*2}=2$, and there $\mathsf p$ has a
  double root, so simplicity fails. Fix: "Let $R^*>0$. Then $0<w_c<2$, and
  ...". In (ii), also name the eigenvalues: $1$ and two conjugate pairs on the unit
  circle with real parts $m_-/2<m_+/2$. Lean: `V2.windowD_pos`,
  `V2.window_roots_inside` and `V2.prop_W2_ii` (all with `0 < R`). The `R → 0+`
  limit of `w_c` is `V2.w_c_limit`. Proved.
  Applied to the tex on 2026-10-04.
- **V2-8, `prop:W2` (iii), last step of the proof.** "The Jacobian of the drift
  recursion at its fixed point is within $O(\varepsilon)$ of $J_0$" is
  asserted, not proved. It needs two facts. First, the fixed point of the drift
  recursion, in the scaled variables, converges to $\hat x^*$. Second, the
  damping and noise terms dropped in \eqref{eq:window-map} are $O(\varepsilon)$
  in $C^1$ near $\hat x^*$, by Lemma~\ref{lem:B}. Fix: state these two facts,
  with a reference. For persistence, convergence $J_\varepsilon\to J_0$ is
  enough, and no rate is needed. Lean: the persistence step is
  `V2.real_eigenvalue_persistence` and `V2.prop_W2_iii`, with entrywise
  `J_ε → J0` as a hypothesis. The convergence itself is not formalized.
  Applied to the tex on 2026-10-04.
  Formalized on 2026-10-06 (`Logistic/V2/WindowDrift`, `WindowDriftJacobian`):
  `prop_W2_iii_drift` proves (iii) for the tame drift recursion, with no hypothesis on
  `J_ε`. The fixed point is located exactly, not through Proposition D: `m = 0`,
  `alpha theta = r`, `c = -h alpha R/(2-eps)` and `v = 2 h alpha R/(2-eps)`.

### Sharpenings (optional, the tex is correct as stated)

- `prop:W1`, $\lambda_0$: the error is $O(\Delta^{*-1})$, because
  $\chi(\epsilon,\epsilon\lambda)/\epsilon$ has no $O(\epsilon)$ term
  (`V2.real_eigenvalue_asymptotics_sharp`). The oscillatory eigenvalues keep
  $O(\Delta^{*-1/2})$.
- `prop:W1`, trace identity: the limit formulas satisfy
  $\lambda_0+2\mu_1+2\mu_2=-4$ exactly (`V2.lambda_mu_trace`). The
  $O(\Delta^{*-1/2})$ term enters only when they are compared with the actual
  eigenvalues, whose sum is exactly $\operatorname{tr}A=-4$
  (`V2.five_eigenvalues`, `V2.trace_corollary`).

### Implementer notes not carried over

Some implementer notes described an earlier draft, and the frozen v2 tex already
contains what they asked for:
- the coefficient $\mathsf c_2$ is displayed;
- `cor:recursion` already writes $\Psi_\varepsilon=y+\varepsilon b+\varepsilon e_\varepsilon$ and uses the additive term $M\varepsilon\delta_\varepsilon$;
- the continuity argument for $m_\pm>-2$ in `prop:W2` is valid as written.

The following were dropped because they concern only how the Lean statements
are packaged:
- the tube hypotheses `|δ-Δ*| ≤ Δ*/2`, `ρ ∈ [0,1]` and `varrho ≤ 1`, which hold
  eventually along the path;
- the two-sided `HasDerivAt` at `t = 0`;
- certificates `(P, c)` in place of `A^T P + P A = -I`;
- statements on arbitrary balls.

## V2 momentum-helps (revised appendix, "When momentum helps")

Source: `source/v2/momentum_helps.tex` (section `sec:helps-app`), frozen on
2026-10-04 and re-frozen on 2026-10-05 after the tex merge with KE's version, with
its hash in `source/v2/manifest.json`. The Lean modules are in
`SparseSGD/Scaling/Helps/`.

### Re-pin of 2026-10-05 (merged tex)

Each registered label was compared with the merged text:

- Kept, with notation-only changes (`\mathcal L -> \mathcal T`, `log -> ln`,
  `V, kappa_V, p_1, p_V -> |\mathcal V|, kappa_{\mathcal V}, p_max, p_min`):
  `lem:helps-sgd`, `lem:helps-onecopy`, `lem:helps-twocurv` and
  `prop:helps-critical`. All four remain complete.
- `lem:helps-vocab`: kept, but the merge rewrote the last claim of (iii). Its
  hypotheses "`beta >= 1/2`, `eps -> 0`, `s -> nu0` in `(0, infinity)`, error
  `1 - O(eps^(1/3))`" became "the parameters of copy `|V|` vary along a
  co-scaling ray with `gamma > 0`, error `1 + o(1)`". On such a ray
  `s = 2 eps/(p eta_+)` converges in `[0, infinity]`.
  - `helps_vocab_asymptotic` implies the new claim when `s -> s0` in
    `(0, infinity)`.
  - For `s <= 1 - eps` the claim is a two-line consequence of
    `perStepRate_le_neg_log_beta`, but there is no Lean statement for it.
  - For `s -> infinity` it is not formalized.
  - Status: partial.
- `lem:ray`, now KE's statement. Lean implies it: `rayRate = mu*`,
  `nu * rayDelta = e*`, and `one_sub_two_rayDelta` gives `Delta* = (1 - e*^2)/2`.
  Status: complete.
- `cor:samplecost`, now KE's `cor:sample_cost`.
  - (i) follows from `perStepRate_le_neg_log_beta`, pointwise in `eta`.
  - (ii) is formalized only on the resonance line: the uniform `O(eps^(1/3))`
    form on `s in [s0/2, 2 s0]` implies her `o(1)` when `s -> s0` in
    `(0, infinity)`.
  - It does not cover the cases `s -> infinity` (her proof uses `lem:small_delta`)
    and `s -> 0`.
  - The old Lean result was proved on `{u_n <= c Delta}` with `c = nu0`, which on
    the ray is `u_n <= nu Delta/2`. That restriction is harmless and is not the
    gap. The gap is that `nu0` must be a fixed positive number.
  - Status: partial.
- `lem:speedup`, now KE's `prop:fixed_floor`. Lean implies it for `u_n` in `(0,1)`,
  which always holds for LS (see MH-2): `cor_helps_speedup` gives the ratio limit,
  `lem_speedup` gives (i) and (ii). Status: complete.
- Dropped from the tex, now `supporting`: `lem:helps-rate`, `lem:helps-roots`,
  `lem:helps-transfer` and `cor:helps-speedup`. Their Lean proofs are kept; see the
  `supporting_note` fields in `obligations.json`.

Every statement of the section that is registered here (`lem:helps-sgd`,
`lem:helps-rate`, `lem:helps-roots`, `lem:helps-transfer`, `lem:ray`,
`cor:samplecost`, `lem:speedup`, `cor:helps-speedup`, `lem:helps-onecopy` and
`lem:helps-vocab`, and in the final snapshot `lem:helps-twocurv` and
`prop:helps-critical`) was found true as written in the 2026-10-04 snapshot, under
Assumption G. No statement needed an extra hypothesis. `prop:helps-critical` is
fully formalized; it was partial until the `c_kappa` branch and the
`sqrt(kappa_V)/19` claim were added. For the 2026-10-05 merged snapshot, see the
re-pin section above and MH-2.

### Corrections to apply

- **MH-1, proof of `lem:helps-vocab` (ii), first sentence** ("with
  $x_V:=2\eta p_V(1-u_V)\in(0,1]$"). Replace $(0,1]$ by $(0,1)$. Under the
  stability of copy $V$, Lemma~\ref{lem:helps-sgd} gives
  $0<x_V\le p_V\eta_+(p_V)/2<1$, so $\Lambda_V$ is finite. The next sentence
  already uses this bound. The statement is unaffected. Lean: `sgd_radius_eq`.
  Status: applied in the merged tex of 2026-10-05, which reads "so
  $x_{|\mathcal V|}\in(0,1)$".
- **MH-2, `prop:fixed_floor` (i) (KE), optional clarification.** Part (i) says that
  the `eps -> 0` ratio `r_c(Delta,u)/(2 Delta (1-u))` is less than 2. This fails
  with equality at `u = 0`, `Delta = 1/4`. There `r_c = 1` by `lem:chi_roots` (b),
  so the ratio is `1/(1/2) = 2`, and the proof's `chi(-c) < 0` becomes
  `chi(-c) = 0`, since `c = 1` and `u = 0`. For LS at a fixed learning rate
  `u_n = eta(d+2-p)/(2B) > 0`, so the proposition is true in its intended scope.
  Lean proves it for `u_n` in `(0,1)` (`speedupRatio_lt_two`). A clarification
  would read "for $u>0$" or "at most $2$, with equality only at $u=0$,
  $\Delta=\frac14$". "For every $\beta$" is vacuous in the `eps -> 0` limit and
  could be dropped. Status: optional, for KE.

### Checked and not carried over

The implementers proposed other notes. They are not errors in the tex:

- *`w >= 0` in `lem:helps-sgd`, `phi >= 0` in `cor:helps-speedup`, `beta >= 0` in
  `rem:retention-cap` (a).* Each follows from the stated hypotheses. Assumption G has
  `cA > 0` and `vadd >= 0`, so `w > 0` and `phi >= 0`, and the section uses
  `beta in [0,1)` throughout.
- *`lem:helps-transfer`, Step 4 constant `4M^2`.* The inequality
  $|\log(1+x)-x|\le x^2$ for $|x|\le\frac12$ is true, and so is the bound
  $\frac12\eps^2M^2+\frac12x^2\le4M^2\eps^2$. Lean gets `6M^2` only because
  Mathlib has the `2x^2` form.
- *`lem:helps-transfer`, Step 5 (`4 Delta u_c <= 2 D^2 eps^2`).* This is correct as
  written.
- *`lem:speedup` (i) at `u = 0`.* The 2026-10-04 statement fixed $u\in(0,1)$. KE's
  `prop:fixed_floor`, which now carries the label, does not; see MH-2.
- *`lem:helps-rate` and `lem:helps-vocab`, `Lambda = +infinity` when
  `rho(L) = 0`.* The tex defines $\Lambda\in(-\infty,\infty]$. For the LS copies,
  $\rho(\mathcal L_j)>0$: for $\beta>0$ since $\rho\ge\beta$, and for $\beta=0$
  since $u_{n,j}>0$. So $\Lambda_{\min}$ is finite. Lean writes
  `Lmin = -log max_j rho(L_j)` only because `Real.log 0 = 0`.
- *`cor:samplecost` and `lem:helps-vocab` (iii), "vary so that $\eps\to0$".*
  For the 2026-10-04 statements, the uniform Lean form, with `eps0` and `C`
  depending only on `nu0`, implies the claim, and $\beta\ge\frac12$ is redundant.
  The merged tex states both claims along a co-scaling ray with $\gamma>0$, so $s$
  may also tend to $0$ or $\infty$. The Lean form covers only $s\to s_0\in(0,\infty)$;
  see the re-pin section above. This is a formalization gap, not a tex error: KE's
  proof of `cor:sample_cost` (ii) treats all three cases.
- *`lem:helps-onecopy`, strict inequality.* Lean proves the non-strict final bound,
  and the tex's strict intermediate step is correct.

- *`prop:helps-critical`, hypotheses.* The Lean statements take `p_1 >= ... >= p_V > 0`
  (`hanti`, `hp`), integer `B >= 1`, and `kappa_V > 1` everywhere except the momentum
  lower bounds of (ii) and (iii), which take `kappa_V > 16`. This matches the
  discussion after the proposition. No Jury hypothesis is used.
- *`prop:helps-critical` (iii), "$d\ge1$" in the closing claim.* The claim
  $\ge\sqrt{\kappa_V}/19$ also holds for $d=0$: then $p_V/(d+2)<\frac1{32}$ and
  $\frac18\cdot\frac1{\sqrt5}\cdot\frac{255}{256}\cdot\frac{31}{32}>\frac1{19}$. The
  tex is correct as written. Formalized as `Bratio_ge_div19` (it uses `d >= 0` only).
- *`lem:helps-twocurv`, form.* Lean states it through
  $\rho(\mathcal L_j)\ge\rho(F_j)^2$, which is the form the proposition uses, and in
  in a real-variable form (`twocurv_real`). The real-variable form is the tex
  statement with $r=\max(\rho(F_1),\rho(F_V))$ given by its defining properties, and
  the reduction "we may assume $r<1$" becomes the hypothesis $r<1$.

### Optional proof alternatives (the tex proofs are correct)

- `prop:helps-critical`, Step 3. The monotonicity of $x/\log(1+x)$ can be replaced
  by Bernoulli's inequality $(1+a)^B\ge1+Ba$. Lean: `bernoulli_aux`,
  `sgd_B_div_Lmin`.
- `prop:helps-critical`, Step 1. For the momentum class, the comparison
  $\lambda_{\mathrm{SGD}}\le\lambda_{\mathrm{mom}}$ at $\beta=0$ is not needed,
  because the bound $\ge(\sqrt\kappa-1)/(\sqrt\kappa+1)$ of
  `lem:helps-twocurv` already holds at $\beta=0$. Lean: `Lmin_le_lamMom`.

- `lem:speedup` (iii). The implicit function theorem can be replaced by a real-root
  bracket. Put $q=2(1-u)\Delta+2(1-u)(1-3u)\Delta^2$ and
  $c_3=32u^3-60u^2+32u-4$. Then
  $\chi(-q+t\Delta^3)=\Delta^3P(t,\Delta,u)$ with $P(t,0,u)=2(t-c_3)$, so the
  sign of $\chi$ changes between $t=c_3-1$ and $t=c_3+1$ for small $\Delta$.
  The root found lies above $-\frac13$, and there $\chi'>0$, so it is the
  rightmost root. Lean: `spectrumPolynomial_bracket_signs`, `speedup_expansion`.
- `rem:stab-large-w`, "$u<1$ implies stability". For $|z|\ge1$,
  $p_0(z)\sum_nx_nz^{-(n+1)}=z(z+\beta)$, where $x_n$ is the squared kick
  response. A root of the noisy polynomial with $|z|\ge1$ would therefore give
  $1\le\tilde u$. This holds for every $\beta\in[0,1)$. Lean:
  `kickSq_generating_function`, `stepRadius_lt_one_of_totalLoad_lt_one`.
- `lem:helps-transfer`, Step 2. With the closed-form characteristic polynomial
  $Q_\eps=\chi(\cdot;\Delta,u_n)+\eps(r_2\mu^2+r_1\mu+r_0)$, only a bound
  $u_n\le U$ is needed, not $u_n\le c\Delta$, and the matrices $A,G$ can be
  dropped. Lean: `transferRemainder_eq`, `helps_transfer_box`.
- `lem:helps-vocab` (iv)(b). Gelfand's formula can be replaced by the
  factorisation of the noise-free characteristic polynomial,
  $(z-\beta)(z^2-((1+\beta-w)^2-2\beta)z+\beta^2)$. Lean:
  `stepRadius_noiseFree_eq_beta_iff`.

## V2 merged appendix (2026-10-05)

Sources: `source/v2/momentum_helps.tex` after the harmonization pass (sha256
`90c5bcc8...5c07`), and the live appendix chunks `source/v2/chunks/` (01, 02, 03, 04, 05,
07, 08), which relax the momentum range of the master reduction and of the renewal
section to `beta in [0,1)`. Every label of the merged section and of the relaxed chunk
statements was compared with what Lean proves; see the README section of the same name
for the coverage table.

### Corrections to apply

- **MF-1, `prop:fixed_floor` (= `lem:speedup`), statement: "let $\eps\to0$ with
  $(\Delta,u)$ fixed".** For $\eps>0$ the total load of the momentum chain is
  $u=u_n+u_c\ge u_c=\eps^2\Delta/(2(2-\eps))>0$, because $u_n\ge0$. So no chain has total
  load $u=0$, and at $u=0$ the limit is taken over an empty family. Replace by "Fix
  $\Delta>0$ and $u\in[0,1)$, and let $\eps\to0$ with $\Delta$ and the noise load $u_n=u$
  fixed (equivalently, with the total load tending to $u$)". The limit
  $r_c(\Delta,u)/(2\Delta(1-u))$ and parts (i), (ii) are unchanged. Lean:
  `fixed_floor_limit_noise` (fixed `u_n in [0,1)`, `u_n = 0` included) and
  `fixed_floor_limit_total` (total load held at `u in (0,1)`). Status: applied to the tex on 2026-10-05.
- **MF-2, paragraph after the proof of `prop:fixed_floor` (the exact counterpart).** "For
  every $\beta$, every $u_n$ and $4\eta p<1$, ... So the ratio is at most
  $2/((1-u)(1-4\eta p))$" needs the SGD load $u=u_n+\eta p/2<1$. For $u\ge1$ the SGD rate
  $-\ln(1-2\eta p(1-u))$ is $\le0$, so the ratio is not bounded by the displayed
  expression (whose denominator is then $\le0$): with $u_n<1\le u_n+\eta p/2$ and
  $u_n+u_c<1$ the momentum chain is stable and SGD is not. Replace "every $u_n$" by "every
  $u_n$ with $u=u_n+\eta p/2<1$". Lean: `fixed_floor_exact_counterpart` (hypothesis
  `u_n + eps Delta/2 < 1`). Status: applied to the tex on 2026-10-05.

`MH-2` (above) is applied: the harmonized `prop:fixed_floor` (i) reads "at most $2$, with
equality only if $u=0$ and $\Delta=\frac14$", which Lean proves for all `u in [0,1)`
(`speedupRatio_le_two`, `speedupRatio_eq_two_iff`).

No statement of the relaxed chunks needed a correction. `cor:stab` (iii) already carries
the new hypothesis "$(\Sigma_0)_{11}>0$, or $\beta>0$ and $\Sigma_0\ne0$", and Lean proves
that it is needed at $\beta=0$ (`beta_zero_dark_start`).

### Checked and not carried over

The implementers proposed further notes. None is a mathematical error in the tex:

- *`lem:step_spectrum`, "$\eps\ne2$", "$\eps>0$", "$u\in[0,1]$".* The lemma sets
  $\beta=1-\eps$ with $\beta\in[0,1)$ and $u\in[0,1)$, so $\eps\in(0,1]$. Lean carries
  `eps != 0`, `eps != 2` because its identities are stated for real `eps`.
- *`lem:step_speed` (i), $\Lambda\le\ebar$ at $\beta=0$.* The tex value is
  $\ln(1/0)=+\infty$ and $\Lambda\in(-\infty,\infty]$, so the bound is vacuous and correct.
  Lean's `Real.log 0 = 0` cannot express it; the clause is formalized for `beta > 0`.
- *`lem:step_speed` (i), equality $\rho(\mathcal T)=\rho(F)^2$ for $u_n=0$ holds for every
  $\beta\ge0$.* True (`stepRadius_noiseFree_eq_meanRadius_sq`), but the lemma's range
  $\beta\in[0,1)$ is all the section uses.
- *`prop:helps-critical` (iv), "$S_\beta=\inf_BS_\beta(B)$" needs $\mathcal A_\beta(B)\ne\emptyset$.*
  The proof's preamble gets nonemptiness for every class from `lem:helps-vocab` (i). In
  Lean that direction is the Jury criterion, an explicit hypothesis, hence `jury` in
  `Sfun_fixed_ge`, `Sinf_fixed_eq`; the limit `Sfun_fixed_tendsto` needs none.
- *`prop:vocab_full` (ii), $S_\beta\le A_\beta$ under $\Delta_\beta\le\frac14$.* It uses
  that $\Delta_\beta\le\frac14$ implies $\kappa_{\mathcal V}\ge\kappa_\beta$, which is shown
  in Step 6 of the proof of `prop:helps-critical` (Lean: `kappaBeta_le_of_delta`).
- *`prop:vocab_full` (i), per-token learning rates.* Lean proves the bound for every
  $B\ge1$ with no stability hypothesis (`vocab_full_per_token`); the tex statement is the
  case $B-1\le B_\times$, as written.
- *`cor:sample_cost` (ii) and the co-scaling clauses of `lem:helps-vocab` (iii) and
  `prop:vocab_full` (i).* Lean proves quantitative, uniform forms (`samplecost_below` with
  `eps <= 1/50`, `s >= 100`, `C = 408`; `cor_sample_cost_uniform` with `eps0(delta)`
  depending on nothing else). These sharpen the tex's $o(1)$ statements; they are not
  corrections.
- *`rem:schedule`, last sentence (Cramér–Rao bound, minimax risk).* An imported
  statistics claim with no citation; not formalized (registered as pending). A citation
  would help the reader but is not a mathematical correction.
- *`lem:small_delta`, proof of $q(-t_+)<0$.* Lean uses the cruder $t_+\le0.68\,a_0$; the
  tex's $a_2(1+4a_0)^2/a_1^2<1.5$ is also correct ($3.024\cdot1.32^2/1.97^2<1.36$).
- *`lem:chi_roots` (d).* Lean replaces the implicit function theorem by an explicit
  bracket, with constant $18$ for $\Delta\le\frac1{50}$; the tex proof is correct.

### Beta-range relaxation (live chunks)

Proved for `beta in [0,1)` by new declarations (the v1 declarations, with
`1/2 <= beta`, keep their signatures): `lem:L2` (`stable_kernel_masses_v2`,
`kickResponse_beta_zero`, the `normalized_kernel_*_v2` lemmas,
`mean_powers_tendsto_zero_beta_zero`), `cor:stab` (`trajectory_risk_*_v2`, with the new
hypothesis of (iii) as `0 < s.R ∨ (0 < beta ∧ s ≠ 0)`), `cor:tikhonov`
(`cor_tikhonov_v2`), `cor:lift` (ii) (`trajectory_risk_defect_sup_bound_v2`) and rank at
most one (`noiseFree_rankOne_rank_le_one`), `rem:retention-cap` (a)
(`meanRadius_sq_le_stepRadius`). `lem:L1` needed nothing: the raw-oracle declarations take
an arbitrary real `beta`.

Still `1/2 <= beta` in Lean where the live tex has `beta in (0,1)`: the matched form of
`cor:lift` (i), registered `v1_restricted`, and the matched-parameter layer behind
`def:matched`, `lem:match`, `lem:embed` (still registered against the v1 chunk, where
`1/2 <= beta`). The live tex itself keeps `beta >= 1/2` for `thm:M` and everything
derived from it (`cor:regular`, `cor:resonance`, `cor:window`, `cor:curv`), so those
entries are consistent.
