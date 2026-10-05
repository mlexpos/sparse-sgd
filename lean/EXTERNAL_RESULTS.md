# External result boundary

`SparseSGD.External.JuryStability` is the first explicit external interface.
It states the two-dimensional Jury criterion in the equivalent linear-dynamics
form: the three inequalities imply that matrix powers tend to zero. The theorem
`mean_powers_tendsto_zero` verifies those inequalities for the paper's mean matrix.
It takes the interface as an argument; there is no global axiom asserting it.

The V2 momentum-helps stability statements also consume `External.JuryStability`
as an explicit argument `jury`, never as an axiom. In `Scaling/Helps/Stability.lean`
these are `kickSq_hasSum_of_stable`, `kickSq_hasSum_mul`, `kickSq_charPoly_ne_zero`,
`kickSq_generating_function`, `stepRadius_lt_one_of_totalLoad_lt_one`,
`stepRadius_lt_one_iff`, `perStepRate_pos_iff` and `perStepRate_pos_iff_of_beta_pos`.
Through them it reaches `copy_stable_iff_lt_critical` and `all_stable_iff_lt_min` in
`Scaling/Helps/Vocabulary.lean`, which is the `if` direction of `lem:helps-vocab` (i). The
interface is used only for the mean 2x2 block `F`, to turn the Jury inequalities into
`F^n -> 0`. That gives summability of the squared kick response and hence `u < 1 =>
rho(L) < 1` (`lem:helps-rate`, a supporting entry since the 2026-10-05 tex merge, and
`rem:stab-large-w`). The converse directions, and
`Scaling/Helps/CriticalBatch.lean` (`lem:helps-twocurv`, `prop:helps-critical`), do not use
it. There, admissibility is the definition `stepRadius < 1`, and the admissible sets are
nonempty because of the explicit point `(1/(d+2), 0)` (`sgd_point_mem`).

Additions of the V2 merged appendix (2026-10-05), all with `jury` as an explicit argument:
- `Discrete/General/Renewal.lean` and `Discrete/General/Tikhonov.lean`: the `_v2` forms of
  `lem:L2`, `cor:stab`, `cor:lift` (ii) and `cor:tikhonov` for `beta in [0,1)`, exactly
  where the v1 forms used it. `mean_powers_tendsto_zero_beta_zero` proves the `beta = 0`
  case of `F^n -> 0` directly, without the interface.
- `Scaling/Helps/Vocabulary.lean`: `lem_helps_vocab_v2` (through `all_stable_iff_lt_min`).
- `Scaling/Helps/SampleCostAbove.lean`: `lsLamStar_pos`, hence `lsNfold_ge_retention`
  (`cor:sample_cost` (i)): some learning rate is stable, so `Lambda* > 0`.
- `Scaling/Helps/CriticalBatch.lean` (v2 additions): `admSet_fixed_nonempty`,
  `Sfun_fixed_ge`, `Sinf_fixed_eq`, `prop_helps_critical_v2`: the
  fixed-`beta` admissible set is nonempty at every `B`, the tex's appeal to
  `lem:helps-vocab` (i). The limit `Sfun_fixed_tendsto` does not use it.
- `Scaling/Helps/VocabFull.lean` (`vocab_full_Sinf_le_fixed`, `vocab_full_tendsto_fixed`,
  `vocab_full_remark`, `prop_vocab_full`) and `vocab_full_i_coscaling` in
  `Scaling/Helps/SampleCost.lean`, for the same nonemptiness.

`SparseSGD.External.GaussianSteinCertificate d` is an explicit hypothesis for
the cited standard Gaussian Stein identities. It is quantified over arbitrary
scalar test functions, shifts, vectors, and coordinates of the actual standard
product Gaussian. The first identity requires a continuous first derivative;
the second requires continuous first and second derivatives. Each derivative is
linked to its test function by `HasDerivAt`, and the displayed integrands must
be integrable. The logistic specializations prove the sigmoid calculus; the
drift application must also prove the required integrability. This interface
does not assume a logistic mean, variance, drift, or limiting conclusion.

Before introducing any interface below, write its precise mathematical statement,
verify its applicability to the quoted use, and record its Lean declaration here.
The manuscript's claims are not substitutes for these generic external results.

| Citation in snapshot | Permitted role | Interface status |
|---|---|---|
| Elaydi (2005), Theorem 2.37 | Jury criterion for discrete linear stability | `SparseSGD.External.JuryStability`; explicit hypothesis (also consumed by `Scaling/Helps/Stability`, `lem:helps-vocab` (i), the fixed-`beta` parts of `prop:helps-critical` (iv) and `prop:vocab_full`, `cor:sample_cost` (i), and the `_v2` renewal statements of `Discrete/General`) |
| Horn–Johnson (2013), Theorem 6.1.1 and §6.1 | Gershgorin localization and component eigenvalue counts | Proved directly in the project; no external interface used |
| Stein (1981) | First and second Gaussian integration-by-parts identities | `SparseSGD.External.GaussianSteinCertificate`; explicit hypothesis |
| Boucheron–Lugosi–Massart (2013), §2.4, Corollary 2.11, Theorem 2.10 | Precisely stated concentration and moment-to-MGF bounds | `SparseSGD.External.MartingaleBernsteinCertificate`; conditional MGF-to-tail; `SparseSGD.External.BernsteinMomentsCertificate` supplies scalar raw-moments to centered-MGF |
| Freedman (1975) | Martingale tail bound, only with its actual hypotheses | `SparseSGD.External.MartingaleBernsteinCertificate`; explicit hypothesis |
| Hairer–Nørsett–Wanner (1993), §II.3 | Applicable discrete Grönwall estimate | Prefer Mathlib |
| Khalil (2002), Theorem 11.1 | Applicable singular-perturbation theorem | Proved directly by quantitative slow tracking; no external interface used |
| Perko (2001), §3.9 Theorem 1 and §3.7 Theorem 2 | Bendixson and Poincaré–Bendixson | Proved directly in the project; no external interface used |
| Feller (1968), Chapter XIII | Background on renewal; no blanket assumption of paper-specific renewal claims | Renewal identities proved directly; no external interface used |

Assumption G is a model hypothesis. Its least-squares conditional identities are
now proved from the actual sampling law in `Probability/LeastSquares/Public.lean`,
with positive sampling probability for the manuscript's positive-curvature domain.
This branch uses Mathlib's probability and integration theorems and introduces no
external theorem interface or additional axiom. Assumptions
S and W are explicit manuscript conjectural inputs and must be visible hypotheses
of any result using them. They are defined in `Logistic/SourceAssumptions.lean`; neither is used as a
proof premise in the finite-horizon results. Their precise domains and the
interpretation of window averaging are recorded in `CORRECTIONS.md`.

`SparseSGD.External.MartingaleBernsteinCertificate Ω` is the reusable scalar
conditional Bernstein inequality. For a probability space, a filtration and
adapted real increments whose two-sided nonnegative conditional exponential
moments are bounded by `exp(t²v/(2(1-|t|M)))`, it bounds the strict absolute-sum
tail above `sqrt(2KvL)+2ML` by `2 exp(-L)`. It includes zero variance/scale and
requires `v,M ≥ 0`, `L > 0`. The certificate contains no logistic, stopping,
Jacobian, or fluid-limit conclusion. `fluid_limit_normingFamily` proves those
steps and the source probability bound. Nonnegative conditional expectation
ensures the MGF assumption is meaningful without presupposing integrability.

`SparseSGD.External.BernsteinMomentsCertificate X` states the cited BLM scalar moment implication: for a probability law and measurable integrable f, integrable absolute moments bounded by n! a c^n for every n >= 2 imply exponential integrability and a centered MGF bound with variance factor 8 a c² and scale 2c, for |t| 2c < 1. This is an explicit theorem parameter, not an axiom. Actual logistic rare moments, iid batch averaging and full-history conditional transport are proved in `IncrementMoments`, `IncrementLinearMGF` and `IncrementConditional`.

`SparseSGD.External.HoeffdingCertificate X` is the standard scalar Hoeffding lemma (BLM 2013): a centered measurable integrable variable bounded in absolute value by one has an everywhere integrable exponential and MGF at most exp(t²/2).

`SparseSGD.External.GaussianQuadraticCertificate` supplies only standard Gaussian integral facts: the centered squared norm under the actual d-dimensional standard Gaussian has MGF at most exp(d t²/(1-2|t|)) for 2|t|<1, and a scalar standard Gaussian satisfies E[G² exp(G²/4)] <= 4. The first is the standard chi-square sub-gamma estimate discussed in BLM §2.4; the latter follows from an elementary Gaussian integral (its exact value is 2 sqrt 2). Independence of weighted Gaussian sums, all logistic rare moments, random residual-weight averaging, and the compound quadratic application are proved outside the certificate. These are explicit hypotheses, not added Lean axioms.
