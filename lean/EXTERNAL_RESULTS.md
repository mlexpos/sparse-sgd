# External result boundary

`SparseSGD.External.JuryStability` is the first explicit external interface.
It states the two-dimensional Jury criterion in the equivalent linear-dynamics
form: the three inequalities imply that matrix powers tend to zero. The theorem
`mean_powers_tendsto_zero` verifies those inequalities for the paper's mean matrix.
It takes the interface as an argument; there is no global axiom asserting it.

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
| Elaydi (2005), Theorem 2.37 | Jury criterion for discrete linear stability | `SparseSGD.External.JuryStability`; explicit hypothesis |
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
