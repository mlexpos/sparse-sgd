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
    "lem:L2": (["Discrete/Renewal", "Discrete/Chebyshev", "Discrete/Lyapunov", "Discrete/KernelMass", "Discrete/StableKernel"],
        "Finite renewal, Chebyshev response and stable kernel masses using explicit cited Jury hypothesis; pole classification and exponential decay estimate remain."),
    "cor:stab": (["Discrete/Loads", "Discrete/Equilibrium", "Discrete/Positivity", "Discrete/RenewalBounds", "Discrete/RiskBound", "Discrete/FreeRisk"],
        "Load equivalence, fixed point, positivity and instantiated uniform risk bound; geometric convergence and necessity remain."),
    "lem:L3": (["Continuum/Algebra", "Continuum/Differential", "Continuum/Spectrum", "Continuum/Hurwitz", "Continuum/Eigenfunctionals", "Continuum/Energy", "Continuum/Flow"],
        "Explicit all-time ODE solution, field/derivative identities, exact characteristic-root threshold and energy bounds; renewal, kernel mass/variation, exponential decay, modal inversion and strict rank growth remain."),
    "lem:match": (["Comparison/Similarity"],
        "Algebra conditional on trace/determinant; matrix-exponential matching and uniqueness remain."),
    "lem:embed": (["Comparison/Embedding"],
        "Exact transformed covariance step and risk preservation; exponential matching and kernel normalization remain."),
    "lem:quad": (["Comparison/Geometric", "Comparison/QuadratureBound"],
        "Exact finite and infinite identities; compact-strip quantitative bound remains."),
    "cor:lift": (["Discrete/Algebra", "Discrete/RenewalBounds", "Discrete/RiskBound", "Discrete/FreeRisk"],
        "Discrete rank-one covariance/risk identities and full supremum defect bound (ii); matched oscillator in (i) remains."),
    "cor:curv": (["Discrete/Loads", "Scaling/CurvatureLimit", "Scaling/CurvatureWindow"], "Actual parameter limits, matched-curvature asymptotics, full trajectory/local-average comparison and limiting rate ordering; error retains energy and forcing size."),
    "phase-dictionary": (["Scaling/Exponents", "Scaling/IntegerFamilies"], "Exponent classification and admissible integer families proved; analytic cell limits remain."),
    "cor:window": (["Scaling/Window"], "Actual all-time slow/oscillatory comparison, risk reconstruction, finite local averaging and actual Perron-rate estimate."),
    "lem:B": (["Logistic/TameCoefficients", "Logistic/ScalarCoefficients", "Logistic/TameCoefficientDerivatives"], "Actual coefficients and every first/second derivative proved; variance-zero uses right derivatives and pure-variance A derivatives retain their exponential main terms."),
    "cor:regular": (["Scaling/RegularLimit", "Scaling/RegularUniformConstants"], "Full all-time quantitative rate over compact positive curvature sets; uniform semigroup decay and actual matrix covariance error."),
    "prop:D": (["Logistic/Equilibrium", "Logistic/Bounds"],
        "Scalar root, quantitative actual fixed-point asymptotics, bounded-load integer-family comparability, small-load expansion and Jacobian proved. Corrected actual population-loss/KL expansion is proved at fixed r, retaining tameness and finite-load errors."),
    "thm:A": (["Logistic/StoppedFluid", "Logistic/FluidTheorem", "External/MartingaleBernstein"],
        "Full arbitrary-norm finite-family fluid bound, using the explicit standard scalar Bernstein certificate. Deterministic reference and closed-neighborhood corrections are recorded."),
}
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
accepted = {"complete", "complete_corrected", "defined", "assumption"}
for claim in claims:
    entry = by_label[claim["label"]]
    subclaims = entry["subclaims"]
    if not subclaims or len({s["id"] for s in subclaims}) != len(subclaims):
        raise SystemExit(f"Missing or duplicate subclaims: {claim['label']}")
    for subclaim in subclaims:
        if subclaim["status"] in accepted and not subclaim["declarations"]:
            raise SystemExit(f"Completed obligation without declaration: {claim['label']}/{subclaim['id']}")
        if subclaim["status"] == "complete_corrected" and not subclaim.get("correction"):
            raise SystemExit(f"Missing correction reference: {claim['label']}/{subclaim['id']}")
    statuses = {s["status"] for s in subclaims}
    if statuses <= accepted:
        if claim["kind"] == "assumption":
            claim["status"] = "assumption"
        elif claim["kind"] == "definition":
            claim["status"] = "defined"
        else:
            claim["status"] = "complete_corrected" if "complete_corrected" in statuses else "complete"
    elif "partial" in statuses or statuses & accepted:
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
(ROOT / "coverage.json").write_text(json.dumps(claims, indent=2)+"\n")
(ROOT / "declarations.json").write_text(json.dumps(inventory, indent=2)+"\n")
print(f"{len(inventory)} modules; {sum(len(x['theorem_names']) for x in inventory)} authored theorem declarations.")
print(f"{sum(c['status'] in {'complete', 'complete_corrected'} for c in claims)} complete (including corrected statements) and {sum(c['status']=='partial' for c in claims)} partial source entries; {sum(c['status']=='pending' for c in claims)} pending. Source assumptions remain explicit.")
