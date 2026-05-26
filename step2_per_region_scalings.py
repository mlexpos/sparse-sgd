"""Per-region asymptotic verification (six regions: A, B, C, D, E, F).

Reuses the matrix construction, characteristic-polynomial machinery, and
constraint-derivation pipeline in ``core`` to verify, for each of the six
regions of the (kappa, gamma) phase plane defined in
appendix section ``sec:phase_regions``, that:

  - c_3 leading exponent matches the predicted closed form
  - c_1 c_2 > c_3 leading exponent matches the predicted closed form
  - c_1 > 0 and c_2 > 0 are not the binding constraints
  - The maximal alpha (i.e., the binding eta_max) reduces to a single
    closed-form expression after applying the regime's resonance condition.

The six regions:

  Region A   : kappa <= sigma - 1
  Region B  : sigma - 1 < kappa <= sigma,  gamma <  1 - sigma + kappa
  Region C  : sigma - 1 < kappa <= sigma,  gamma >  1 - sigma + kappa
  Region D   : kappa > sigma,               gamma <= kappa - sigma
  Region E  : kappa > sigma,               kappa - sigma < gamma < 1 - sigma + kappa
  Region F  : kappa > sigma,               gamma > 1 - sigma + kappa

Run with:

    python step2_per_region_scalings.py
"""

from __future__ import annotations

import os
import sys
from typing import Optional

import sympy as sp

# Make ``core`` importable when this script is run from the project root.
_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

import core  # noqa: E402

Regime = core.Regime
RegimeReport = core.RegimeReport


# --- Extend atom inference with the two resonance patterns -----------------
#
# ``core.infer_atoms_from_conditions`` matches a fixed set of condition
# string patterns. We add two more for the resonance line
# ``gamma = 1 - sigma + kappa``, which we need to drive simplification of
# ``Max(alpha_c3, alpha_c1c2)`` within Regions B/C/E/F.
_core_infer = core.infer_atoms_from_conditions


def _infer_atoms_with_resonance(regime, k, s, gamma):
    atoms = _core_infer(regime, k, s, gamma)
    conds_norm = [core._normalize_condition(c)
                  for c in getattr(regime, "conditions", [])]
    for c in conds_norm:
        # Strip whitespace to be permissive about formatting.
        c_compact = c.replace(" ", "")
        # gamma < 1 - sigma + kappa  ⇒  (1 + kappa - sigma - gamma) >= 0
        if c_compact in ("gamma<1-sigma+kappa", "gamma<1+kappa-sigma",
                         "gamma<kappa-sigma+1", "gamma<-sigma+kappa+1"):
            atoms["1+κ-σ-γ"] = 1 + k - s - gamma
        # gamma > 1 - sigma + kappa  ⇒  (gamma + sigma - kappa - 1) >= 0
        if c_compact in ("gamma>1-sigma+kappa", "gamma>1+kappa-sigma",
                         "gamma>kappa-sigma+1", "gamma>-sigma+kappa+1"):
            atoms["γ+σ-κ-1"] = gamma + s - k - 1
    return atoms


# Monkey-patch: internal calls inside ``core`` resolve via core's namespace,
# so this redirects every downstream consumer to the extended inference.
core.infer_atoms_from_conditions = _infer_atoms_with_resonance


# --- Extend test-value dispatch with the new region names ------------------
#
# ``core.determine_sign_in_regime`` falls back to numerical evaluation at a
# regime-specific test point pulled from ``get_test_values(regime_name)``.
# For our new region names, that lookup would return ``{}`` and the sign of
# any non-trivial expression would come back as ``None``, breaking
# leading-term selection. We therefore extend the dispatch with concrete
# test points satisfying each region's full set of conditions (including
# the resonance inequality, where applicable).
_kappa = sp.Symbol("kappa", real=True, nonnegative=True)
_sigma = sp.Symbol("sigma", real=True, nonnegative=True)
_gamma = sp.Symbol("gamma", real=True, nonnegative=True)

_REGION_TEST_VALUES = {
    # Region A: kappa <= sigma - 1 (so sigma >= kappa + 1).
    "region_A": {_kappa: sp.Rational(1, 4), _sigma: sp.Rational(3, 2),
                 _gamma: sp.Rational(1, 2)},
    # Region B: sigma-1 < kappa <= sigma, gamma < 1 - sigma + kappa.
    # With kappa=3/10, sigma=1/2: 1-sigma+kappa = 4/5; pick gamma = 2/5.
    "region_B": {_kappa: sp.Rational(3, 10), _sigma: sp.Rational(1, 2),
                  _gamma: sp.Rational(2, 5)},
    # Region C: same kappa, sigma; gamma > 1 - sigma + kappa = 4/5; pick gamma = 6/5.
    "region_C": {_kappa: sp.Rational(3, 10), _sigma: sp.Rational(1, 2),
                  _gamma: sp.Rational(6, 5)},
    # Region D: kappa > sigma, gamma <= kappa - sigma.
    "region_D": {_kappa: sp.Rational(4, 5), _sigma: sp.Rational(3, 10),
                 _gamma: sp.Rational(1, 5)},
    # Region E: kappa=4/5, sigma=3/10. kappa - sigma = 1/2 and 1 - sigma + kappa = 3/2.
    # Need 1/2 < gamma < 3/2; pick gamma = 4/5.
    "region_E": {_kappa: sp.Rational(4, 5), _sigma: sp.Rational(3, 10),
                  _gamma: sp.Rational(4, 5)},
    # Region F: same kappa, sigma; need gamma > 3/2; pick gamma = 2.
    "region_F": {_kappa: sp.Rational(4, 5), _sigma: sp.Rational(3, 10),
                  _gamma: sp.Integer(2)},
}

_core_get_test_values = core.get_test_values


def _get_test_values_extended(regime_name):
    if regime_name in _REGION_TEST_VALUES:
        return _REGION_TEST_VALUES[regime_name]
    return _core_get_test_values(regime_name)


core.get_test_values = _get_test_values_extended


# --- Define the 6 regions --------------------------------------------------
#
# Substitutions are inherited from the corresponding "primitive group"
# substitutions exported by ``core``: Regions B and C share the
# dense-typical substitutions; Regions E and F share the
# sparse-sparsity-limited substitutions.
def _region(name, conditions, parent_subs):
    return Regime(
        name=name,
        description=f"({name}) -- see appendix Section sec:phase_regions",
        conditions=conditions,
        substitutions=dict(parent_subs),  # shallow copy
    )


REGIONS = {
    "region_A": _region(
        "region_A",
        ["κ ≤ σ", "σ ≥ κ + 1"],
        core.DENSE_RARE_SUBS,
    ),
    "region_B": _region(
        "region_B",
        ["κ ≤ σ", "σ < κ + 1", "γ < 1 - σ + κ"],
        core.DENSE_TYPICAL_SUBS,
    ),
    "region_C": _region(
        "region_C",
        ["κ ≤ σ", "σ < κ + 1", "γ > 1 - σ + κ"],
        core.DENSE_TYPICAL_SUBS,
    ),
    "region_D": _region(
        "region_D",
        ["κ > σ", "γ ≤ κ - σ"],
        core.SPARSE_DECAY_LIMITED_SUBS,
    ),
    "region_E": _region(
        "region_E",
        ["κ > σ", "γ > κ - σ", "γ < 1 - σ + κ"],
        core.SPARSE_SPARSITY_LIMITED_SUBS,
    ),
    "region_F": _region(
        "region_F",
        ["κ > σ", "γ > κ - σ", "γ > 1 - σ + κ"],
        core.SPARSE_SPARSITY_LIMITED_SUBS,
    ),
}


# --- Resolve Max(alpha_c3, alpha_c1c2) using region atoms ------------------
def _resolve_max(a: Optional[sp.Expr], b: Optional[sp.Expr],
                 region) -> Optional[sp.Expr]:
    """Pick whichever of a, b is provably >= the other given region atoms."""
    if a is None and b is None:
        return None
    if a is None:
        return b
    if b is None:
        return a

    diff = core._canon(a - b)
    k, s, gamma = core.symbols_in_expr(diff)
    atoms = _infer_atoms_with_resonance(region, k, s, gamma)

    ok_ab, _ = core.prove_nonneg_by_atoms(a - b, atoms, k, s, gamma)
    if ok_ab is True:
        return a
    ok_ba, _ = core.prove_nonneg_by_atoms(b - a, atoms, k, s, gamma)
    if ok_ba is True:
        return b
    # Could not resolve; fall back to symbolic Max.
    return sp.Max(a, b)


def build_region_report(entries, region):
    """Like core.build_regime_report, but with simplified alpha_star."""
    base = core.build_regime_report(entries, region)
    alpha_star = _resolve_max(base.alpha_c3, base.alpha_c1c2, region)
    eta_scaling = ("N/A" if alpha_star is None
                   else f"d^({core._eta_power_from_alpha(alpha_star)})")
    fields = vars(base).copy()
    fields["alpha_star"] = alpha_star
    fields["eta_scaling"] = eta_scaling
    return RegimeReport(**fields)


REGION_ORDER = ["region_A", "region_B", "region_C",
                "region_D", "region_E", "region_F"]


def run_six_region_verification():
    entries = core.build_matrix_entries()
    return [build_region_report(entries, REGIONS[k]) for k in REGION_ORDER]


def _bool_str(x):
    if x is True:
        return "PASS"
    if x is False:
        return "FAIL"
    return "?"


def main():
    reports = run_six_region_verification()

    print()
    print("=" * 110)
    print(f"{'Region':<12} {'c3':<6} {'c1c2':<8} "
          f"{'c1≤c3':<8} {'c2≤c3':<8} {'eta_max scaling':<40} "
          f"{'Max?':<6}")
    print("-" * 110)

    overall_ok = True
    any_unresolved = False
    for rep in reports:
        c3s = "PASS" if rep.c3_matches else "FAIL"
        c12 = "PASS" if rep.c1c2_matches else "FAIL"
        c1t = _bool_str(rep.c1_leq)
        c2t = _bool_str(rep.c2_leq)
        eta = str(rep.eta_scaling)
        unresolved = "Max" in eta
        if unresolved:
            any_unresolved = True
        print(f"{rep.regime_name:<12} {c3s:<6} {c12:<8} "
              f"{c1t:<8} {c2t:<8} {eta:<40} "
              f"{'YES' if unresolved else '-':<6}")
        if not (rep.c3_matches and rep.c1c2_matches and
                rep.c1_leq is True and rep.c2_leq is True):
            overall_ok = False

    print("=" * 110)
    print(f"OVERALL VERDICT: {'✓ PASS' if overall_ok else '✗ FAIL'}")
    if any_unresolved:
        print("WARNING: one or more regions has an unresolved Max(...) in eta_max.")
        print("         The resonance condition was not enough to determine which "
              "ceiling binds.")
    print()

    if overall_ok and not any_unresolved:
        print("All six regions resolve to a single closed-form eta_max.")

    sys.exit(0 if (overall_ok and not any_unresolved) else 1)


if __name__ == "__main__":
    main()
