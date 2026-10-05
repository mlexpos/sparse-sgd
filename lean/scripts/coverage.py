"""Refresh conservative source coverage from the project module inventory."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]
components = {
    "lem:L1": (["Probability/Orthogonality", "Probability/GramStep", "Probability/MomentReduction", "Discrete/Algebra", "Probability/LeastSquares/Trajectory", "Probability/LeastSquares/Public", "Probability/RawOracle"],
        "General source oracle L2 propagation and exact moment reduction; actual sparse Gaussian least-squares specialization also complete."),
    "eq:LSoracle": (["Probability/GaussianMoments", "Probability/GaussianProduct", "Probability/GaussianNorm", "Probability/Batch", "Probability/LeastSquares/SingleSample", "Probability/LeastSquares/IndependentBatch", "Probability/LeastSquares/BatchOracle", "Probability/LeastSquares/Freshness", "Probability/LeastSquares/Dynamic", "Probability/LeastSquares/SourceOracle", "Probability/LeastSquares/Public", "Probability/LeastSquares/BoundaryCases"],
        "Complete for the stated sparse Gaussian sample law: independent centered L2 label noise, actual iid minibatch averaging, all-time L2 propagation and conditional mean/variance in the gradient-history filtration. B > 0; oracle includes p = 0 and p = 1."),
    "lem:L2": (["Discrete/Renewal", "Discrete/Chebyshev", "Discrete/Lyapunov", "Discrete/KernelMass", "Discrete/StableKernel", "Discrete/General/Renewal"],
        "Renewal, kick response (trigonometric for beta > 0, -(1-w)^n at beta = 0) and kernel masses for beta in [0,1) (General/Renewal), with the explicit cited Jury hypothesis."),
    "cor:stab": (["Discrete/Loads", "Discrete/Equilibrium", "Discrete/Positivity", "Discrete/RenewalBounds", "Discrete/RiskBound", "Discrete/FreeRisk", "Discrete/Stability", "Discrete/General/Renewal"],
        "Threshold, uniform bound, geometric convergence and necessity for beta in [0,1) (General/Renewal, the _v2 declarations)."),
    "cor:tikhonov": (["Scaling/SmallDeltaKernel", "Scaling/SmallDeltaForcing", "Scaling/SmallDeltaExponential", "Scaling/Tikhonov", "Discrete/General/Tikhonov"],
        "Uniform small-Delta comparison for every eps in (0,1] (cor_tikhonov_v2); the v1 cor_tikhonov keeps 1/2 <= beta."),
    "rem:retention-cap": (["Scaling/Helps/ExactRate", "Scaling/Helps/StepSpeed"],
        "v2 live chunk: (a) rho(L) >= rho(F)^2 >= beta with the equality case, beta in [0,1); (b) the limsup bound is pending."),
    "lem:L3": (["Continuum/Algebra", "Continuum/Differential", "Continuum/Spectrum", "Continuum/Hurwitz", "Continuum/Eigenfunctionals", "Continuum/Energy", "Continuum/Flow"],
        "Explicit all-time ODE solution, field/derivative identities, exact characteristic-root threshold and energy bounds; renewal, kernel mass/variation, exponential decay, modal inversion and strict rank growth remain."),
    "lem:match": (["Comparison/Similarity"],
        "Algebra conditional on trace/determinant; matrix-exponential matching and uniqueness remain."),
    "lem:embed": (["Comparison/Embedding"],
        "Exact transformed covariance step and risk preservation; exponential matching and kernel normalization remain."),
    "lem:quad": (["Comparison/Geometric", "Comparison/QuadratureBound"],
        "Exact finite and infinite identities; compact-strip quantitative bound remains."),
    "cor:lift": (["Discrete/Algebra", "Discrete/RenewalBounds", "Discrete/RiskBound", "Discrete/FreeRisk", "Comparison/SquareRootLift", "Discrete/General/Renewal"],
        "Noise-free identities and rank at most one for beta in [0,1); defect (ii) for beta in [0,1); matched oscillator form of (i) for 1/2 <= beta only."),
    "cor:curv": (["Discrete/Loads", "Scaling/CurvatureLimit", "Scaling/CurvatureWindow"], "Actual parameter limits, matched-curvature asymptotics, full trajectory/local-average comparison and limiting rate ordering; error retains energy and forcing size."),
    "phase-dictionary": (["Scaling/Exponents", "Scaling/IntegerFamilies"], "Exponent classification and admissible integer families proved; analytic cell limits remain."),
    "cor:window": (["Scaling/Window"], "Actual all-time slow/oscillatory comparison, risk reconstruction, finite local averaging and actual Perron-rate estimate."),
    "lem:B": (["Logistic/TameCoefficients", "Logistic/ScalarCoefficients", "Logistic/TameCoefficientDerivatives"], "Actual coefficients and every first/second derivative proved; variance-zero uses right derivatives and pure-variance A derivatives retain their exponential main terms."),
    "cor:regular": (["Scaling/RegularLimit", "Scaling/RegularUniformConstants"], "Full all-time quantitative rate over compact positive curvature sets; uniform semigroup decay and actual matrix covariance error."),
    "prop:D": (["Logistic/Equilibrium", "Logistic/Bounds"],
        "Scalar root, quantitative actual fixed-point asymptotics, bounded-load integer-family comparability, small-load expansion and Jacobian proved. Corrected actual population-loss/KL expansion is proved at fixed r, retaining tameness and finite-load errors."),
    "thm:A": (["Logistic/StoppedFluid", "Logistic/FluidTheorem", "External/MartingaleBernstein"],
        "Full arbitrary-norm finite-family fluid bound, using the explicit standard scalar Bernstein certificate. Deterministic reference and closed-neighborhood corrections are recorded."),
    # v2 (revised appendix, source/v2/).
    "prop:S": (["Logistic/V2/Lyapunov", "Logistic/V2/PositiveDeterminant", "Logistic/V2/Barbalat", "Logistic/V2/GlobalConvergence", "Logistic/V2/Hurwitz", "Logistic/V2/LyapunovCertificate", "Logistic/V2/UniformRate", "Logistic/V2/All"],
        "v2: free-energy Lyapunov function and dissipation identity, global existence and LaSalle-type convergence, Hurwitz Jacobian, uniform exponential rate on compact initial data and parameters."),
    "prop:W1": (["Logistic/V2/LargeDeltaAlgebra", "Logistic/V2/LargeDeltaPerturbation"],
        "v2: exact algebra of Omega, D, H, S and the Rayleigh shifts; large-Delta eigenvalue asymptotics via the explicit characteristic polynomial."),
    "cor:recursion": (["Logistic/V2/RecursionContraction", "Logistic/V2/RecursionTame", "Logistic/V2/All"],
        "v2: abstract drift-recursion contraction and its tame-coefficient instantiation at a fixed base point; actual coefficients and uniformity over compact parameter sets remain."),
    "prop:W2": (["Logistic/V2/WindowMapAlgebra", "Logistic/V2/WindowUnitCircle"],
        "v2: window-map Jacobian, determinants, palindromic factorization, unit-circle spectrum below w_c and period doubling; the drift-recursion Jacobian limit remains a hypothesis."),
    "ass:W2": (["Logistic/V2/All"], "v2 assumption, stated as an explicit Prop structure (not an axiom)."),
    # v2 momentum-helps appendix (source/v2/momentum_helps.tex; snapshot of 2026-10-05,
    # after the merge with KE's section and the harmonization pass). Entries with
    # tex_status "supporting" in obligations.json have no tex statement any more; their
    # Lean proofs are kept.
    "app:rates": (["Scaling/Helps/StepMatrix", "Scaling/Helps/Transfer", "Scaling/Helps/FixedFloor"],
        "v2: Lambda := -ln rho(T) (perStepRate, stepRadius), r_c (continuumPerronRate) and Lambda = eps r_c (1+o(1))."),
    "lem:chi_roots": (["Scaling/Helps/CubicRoots", "Scaling/Helps/ChiRoots"],
        "v2: (a)-(e) for Delta > 0, u in [0,1), u = 0 included; (d) with the explicit constant 18 for Delta <= 1/50."),
    "lem:step_spectrum": (["Scaling/Helps/Transfer", "Scaling/Helps/StepSpectrum"],
        "v2: explicit cubic q, eigenvalues 1 + eps z, |b_i| <= 1 + (16/3) Delta + eps Delta^2, q - chi."),
    "lem:small_delta": (["Scaling/Helps/SmallDeltaSlowRoot", "Scaling/Helps/SmallDeltaFactor", "Scaling/Helps/SmallDelta"],
        "v2: Lambda = 2 eta p (1-u)(1+theta), |theta| <= 25(eps+Delta), for eps, Delta <= 1/50."),
    "rem:sgd_cost": (["Scaling/Helps/Limits", "Scaling/Helps/SampleCostAbove", "Scaling/Helps/SampleCost"],
        "v2: SGD's exact sample cost, monotone in B, <= (1+eps) max(N_stab, N_mem); momentum N_1 >= (1-delta) max."),
    "rem:crit_single": (["Scaling/Helps/Ray", "Scaling/Helps/Limits"],
        "v2: the hyperbola (N_1 - N_stab)(N_1 - N_mem) = N_stab N_mem / 2 for the leading-order N_1."),
    "rem:schedule": (["Scaling/Helps/Schedule"],
        "v2: Chung's lemma and k R_k -> varsigma^2 d/(Bp) at beta = 0, eta_k = 1/(pk); the statistical interpretation is pending."),
    "lem:vocab_rows": (["Scaling/Helps/VocabRows"],
        "v2: rows decouple in law, row recursion (L1) with p = p_j, excess loss (1/2) sum_j p_j R_j."),
    "prop:vocab_full": (["Scaling/Helps/CriticalBatch", "Scaling/Helps/VocabFull", "Scaling/Helps/SampleCost"],
        "v2: (i) SGD iff B-1 <= B_x with closed-form S, per-token rates, momentum factor, co-scaling clause; (ii), (iii) and the remark after it."),
    "lem:helps-sgd": (["Scaling/Helps/StepMatrix", "Scaling/Helps/ExactRate", "Scaling/Helps/All"],
        "v2: beta = 0 radius |1-2w(1-u)|, stability iff u < 1, rate formula and LS supremum."),
    "lem:helps-rate": (["Scaling/Helps/StepMatrix", "Scaling/Helps/Stability"],
        "v2, supporting (dropped from tex): Lambda > 0 iff u < 1 (Jury hypothesis explicit)."),
    "lem:helps-roots": (["Scaling/Helps/RootPerturbation"],
        "v2, supporting (dropped from tex): root matching and extremal real parts/moduli for monic cubics."),
    "lem:helps-transfer": (["Scaling/Helps/StepMatrix", "Scaling/Helps/RootPerturbation", "Scaling/Helps/Transfer", "Scaling/Helps/All"],
        "v2, supporting (dropped from tex): retention-clock conjugation, transfer cubic, uniform C eps^(4/3) bounds."),
    "lem:ray": (["Scaling/Helps/CubicRoots", "Scaling/Helps/Ray", "Scaling/Helps/All"],
        "v2, KE's lem:ray: supremum mu*(s) of r_c along the ray, unique maximizer Delta* = (1-e*^2)/2."),
    "cor:samplecost": (["Scaling/Helps/ExactRate", "Scaling/Helps/Ray", "Scaling/Helps/Limits", "Scaling/Helps/SampleCostAbove", "Scaling/Helps/SampleCost"],
        "v2, cor:sample_cost: (i) via the retention cap; (ii) in all three cases s -> infinity, s -> s0, s -> 0, uniformly in s, and along every sequence with eps -> 0."),
    "lem:speedup": (["Scaling/Helps/CubicRoots", "Scaling/Helps/SpeedupExpansion", "Scaling/Helps/Limits", "Scaling/Helps/ChiRoots", "Scaling/Helps/FixedFloor", "Scaling/Helps/All"],
        "v2, prop:fixed_floor: eps -> 0 ratio limit (u in [0,1), corrected reading), (i) <= 2 with the equality case, (ii) for u in [0,1), exact counterpart, critical damping against 2 eta, small-Delta expansion."),
    "cor:helps-speedup": (["Scaling/Helps/Limits"], "v2, supporting (dropped from tex): uniform on compact K, with explicit floors."),
    "lem:helps-onecopy": (["Scaling/Helps/ExactRate", "Scaling/Helps/StepSpeed"],
        "v2, lem:step_speed = lem:helps-onecopy (beta in [0,1)): beta <= rho(F)^2 <= rho(T), equality for u_n = 0, Lambda <= ebar (beta > 0), Lambda <= -log(1-4 eps Delta)."),
    "lem:helps-vocab": (["Scaling/Helps/Vocabulary", "Scaling/Helps/Limits", "Scaling/Helps/SampleCost"],
        "v2: (i)-(v): stability window, small- and large-batch bounds (beta in [0,1) in (iii)), co-scaling clause for every s, noise-free attainment, the large-batch limit and the exact SGD optimum (v)."),
    "lem:helps-twocurv": (["Scaling/Helps/CriticalBatch", "Scaling/Helps/StepSpeed"],
        "v2: real-variable two-curvature bound and its transfer to the radius of L via rho(L_j) >= rho(F_j)^2."),
    "prop:helps-critical": (["Scaling/Helps/CriticalBatch", "Scaling/Helps/Vocabulary", "Scaling/Helps/StepSpeed", "Scaling/Helps/All"],
        "v2: (i) with the limit S_O(B) -> S_O, (ii), (iii) with the absolute bounds on B_mom, (iv) for every fixed beta in [0,1); kappa_V > 1 globally and kappa_V > 16 on the momentum lower bounds."),
}
# Subclaim statuses accepted as complete, and the status of a subclaim whose only Lean
# proof is the v1 form restricted to 1/2 <= beta while the live (v2) tex states it for
# beta in [0,1) or (0,1). A subclaim relaxed by a new declaration is "complete": its
# "declarations" certify the live statement, "relaxed_by" names the relaxed declarations
# and "v1_declarations" keeps the old 1/2 <= beta ones.
RESTRICTED = "v1_restricted"
inventory = []
for path in sorted((ROOT / "SparseSGD").rglob("*.lean")):
    text = path.read_text()
    declarations = re.findall(r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected)\s+)?(?:theorem|lemma)\s+([^\s(:]+)", text, re.M)
    inventory.append(dict(module="SparseSGD." + str(path.relative_to(ROOT / "SparseSGD").with_suffix("")).replace("/", "."),
                          file=str(path.relative_to(ROOT)), theorem_names=declarations))
claims = json.loads((ROOT / "coverage.json").read_text())
obligations = json.loads((ROOT / "obligations.json").read_text())
by_label = {entry["label"]: entry for entry in obligations}
if len(by_label) != len(obligations) or set(by_label) != {c["label"] for c in claims}:
    raise SystemExit("Source claims and obligation registry disagree")
accepted = {"complete", "complete_corrected", "defined", "assumption", "v1_superseded"}
for claim in claims:
    entry = by_label[claim["label"]]
    subclaims = entry["subclaims"]
    if not subclaims or len({s["id"] for s in subclaims}) != len(subclaims):
        raise SystemExit(f"Missing or duplicate subclaims: {claim['label']}")
    for subclaim in subclaims:
        if subclaim["status"] in accepted | {RESTRICTED} and not subclaim["declarations"]:
            raise SystemExit(f"Completed obligation without declaration: {claim['label']}/{subclaim['id']}")
        if subclaim["status"] == "complete_corrected" and not subclaim.get("correction"):
            raise SystemExit(f"Missing correction reference: {claim['label']}/{subclaim['id']}")
        if subclaim["status"] == RESTRICTED and not subclaim.get("remaining"):
            raise SystemExit(f"v1_restricted subclaim without remaining: {claim['label']}/{subclaim['id']}")
        relaxed = subclaim.get("relaxed_by", [])
        if relaxed and (subclaim["status"] not in accepted
                        or not set(relaxed) <= set(subclaim["declarations"])
                        or not subclaim.get("v1_declarations")):
            raise SystemExit(f"Inconsistent relaxed_by: {claim['label']}/{subclaim['id']}")
    statuses = {s["status"] for s in subclaims}
    if "v1_superseded" in statuses:
        # v1 source assumptions replaced in v2; the kind stays "assumption".
        if statuses != {"v1_superseded"} or not claim.get("superseded_by"):
            raise SystemExit(f"Inconsistent v1_superseded entry: {claim['label']}")
        claim["status"] = "v1_superseded"
    elif statuses <= accepted:
        if claim["kind"] == "assumption":
            claim["status"] = "assumption"
        elif claim["kind"] == "definition":
            claim["status"] = "defined"
        else:
            claim["status"] = "complete_corrected" if "complete_corrected" in statuses else "complete"
    elif statuses <= accepted | {RESTRICTED}:
        # Every subclaim is proved, but some only in the v1 range 1/2 <= beta.
        claim["status"] = RESTRICTED
    elif "partial" in statuses or statuses & (accepted | {RESTRICTED}):
        claim["status"] = "partial"
    else:
        claim["status"] = "pending"
    claim["subclaims"] = subclaims
    claim["declarations"] = list(dict.fromkeys(name for s in subclaims for name in s["declarations"]))
    if claim["label"] in components:
        modules, note = components[claim["label"]]
        claim["component_modules"] = ["SparseSGD." + m.replace("/", ".")
            for m in modules if (ROOT / "SparseSGD" / (m + ".lean")).exists()]
    claim["remaining"] = "" if claim["status"] in accepted else " ".join(
        s.get("remaining", "") for s in subclaims if s["status"] not in accepted).strip()
    # Registry metadata kept in obligations.json is mirrored into coverage.json.
    for key in ("kind", "title"):
        claim[key] = entry[key]
    if entry.get("source"):
        claim["source"] = entry["source"]
    for key in ("tex_labels", "supporting_note", "lean_status", "lean_remaining",
                "v1_source", "beta_range"):
        claim.pop(key, None)
    for key in ("tex_labels", "v1_source", "beta_range"):
        if entry.get(key):
            claim[key] = entry[key]
    # A "supporting" entry: the statement was dropped from the frozen tex, but its
    # Lean proofs are kept because surviving statements build on them. It is not a
    # source obligation any more; the Lean-side status is kept for reference.
    if entry.get("tex_status") is not None:
        if entry["tex_status"] != "supporting" or not entry.get("supporting_note"):
            raise SystemExit(f"Invalid tex_status entry: {claim['label']}")
        claim["lean_status"] = claim["status"]
        claim["lean_remaining"] = claim["remaining"]
        claim["status"] = "supporting"
        claim["supporting_note"] = entry["supporting_note"]
        claim["remaining"] = ""
(ROOT / "coverage.json").write_text(json.dumps(claims, indent=2)+"\n")
(ROOT / "declarations.json").write_text(json.dumps(inventory, indent=2)+"\n")
print(f"{len(inventory)} modules; {sum(len(x['theorem_names']) for x in inventory)} authored theorem declarations.")
print(f"{sum(c['status'] in {'complete', 'complete_corrected'} for c in claims)} complete (including corrected statements) and {sum(c['status']=='partial' for c in claims)} partial source entries; {sum(c['status']=='pending' for c in claims)} pending; {sum(c['status']==RESTRICTED for c in claims)} v1-restricted (proved only for 1/2 <= beta where the live tex has beta in [0,1)); {sum(c['status']=='v1_superseded' for c in claims)} v1 assumptions superseded in v2; {sum(c['status']=='supporting' for c in claims)} supporting entries (dropped from the frozen tex, Lean proofs kept). Source assumptions remain explicit.")
