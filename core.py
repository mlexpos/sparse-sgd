"""Core machinery for Hurwitz-based stability verification.

This module provides the symbolic pipeline used by
``step2_per_region_scalings.py`` to verify per-regime asymptotic stability
of the 3x3 ODE linearization governing sparse-momentum training:

    d/dt [R, V, C]^T = A_batch [R, V, C]^T

Main pieces:
  - ``Term`` / ``TermList``: polynomial-like arithmetic over (eta, d)
    scaling exponents with signs.
  - ``Regime``: a parameter regime with substitution dict mapping derived
    exponents (psi, nu, mu, kappa_eff, gamma_chi, delta_minus1_g_exp)
    to expressions in the primary parameters (kappa, sigma, gamma).
  - ``build_matrix_entries``: returns the 9 entries of A_batch as TermLists.
  - ``compute_c1`` / ``compute_c2`` / ``compute_c3``: the three Hurwitz
    coefficients via trace / sum-of-principal-minors / negative determinant.
  - Leading-term analysis (``analyze_all_groups``, ``find_leading_term_in_group``)
    that locates the dominant exponent at each (eta-power, sign) bucket.
  - Constraint derivations (``derive_c3_constraint``,
    ``derive_c1c2_gt_c3_constraint``, etc.) that solve for alpha_min.
  - ``build_regime_report``: packages all of the above into a RegimeReport
    carrying alpha_c3, alpha_c1c2, the verification matches against the
    expected closed forms (gamma_chi + psi and nu - psi), the nonneg
    proofs that c1 and c2 are not binding, and the implied eta_max scaling.
  - Atom-based nonnegativity certificate search used to discharge
    regime-inequality proofs (``prove_nonneg_by_atoms``,
    ``leq_with_regime_proof``).

The substitution content for the four "primitive group" regimes referenced
by the six-region verifier is exported as named constants
(``DENSE_TYPICAL_SUBS``, ``DENSE_RARE_SUBS``, ``SPARSE_DECAY_LIMITED_SUBS``,
``SPARSE_SPARSITY_LIMITED_SUBS``).
"""

from __future__ import annotations

import itertools
import re
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

import sympy as sp
from sympy import simplify


# =============================================================================
# Symbolic variables
# =============================================================================

# Primary parameters (user-controlled)
kappa, sigma, gamma = sp.symbols('kappa sigma gamma', real=True, nonnegative=True)
alpha = sp.symbols('alpha', real=True)  # learning rate exponent (can be negative)

# Derived exponents (will be substituted per-regime)
psi, nu, mu, kappa_eff, gamma_chi = sp.symbols(
    'psi nu mu kappa_eff gamma_chi', real=True
)

# Dedicated exponent for drift viscosity delta_{-1,g}
delta_minus1_g_exp = sp.Symbol('delta_minus1_g_exp', real=True)


# =============================================================================
# Term and TermList: polynomial-like arithmetic over scaling exponents
# =============================================================================

@dataclass
class Term:
    """A single (eta-power, d-exponent, sign) term with an optional label.

    Attributes:
        eta_power: Power of eta (learning rate) in this term.
        d_exponent: Exponent of d in the scaling (symbolic expression).
        sign: +1 or -1 indicating the sign of the coefficient.
        label: Optional string describing the term's origin.
    """
    eta_power: int
    d_exponent: sp.Expr
    sign: int  # +1 or -1
    label: str = ""

    def __post_init__(self):
        assert self.sign in [1, -1], f"Sign must be +1 or -1, got {self.sign}"
        if not isinstance(self.d_exponent, sp.Expr):
            self.d_exponent = sp.sympify(self.d_exponent)

    def __repr__(self):
        sign_str = "+" if self.sign == 1 else "-"
        label_str = f" [{self.label}]" if self.label else ""
        return f"Term(eta^{self.eta_power}, d^({self.d_exponent}), {sign_str}){label_str}"

    def __neg__(self):
        return Term(self.eta_power, self.d_exponent, -self.sign, self.label)

    def __mul__(self, other: 'Term') -> 'Term':
        new_eta = self.eta_power + other.eta_power
        new_exp = simplify(self.d_exponent + other.d_exponent)
        new_sign = self.sign * other.sign
        new_label = f"({self.label})*({other.label})" if self.label and other.label else ""
        return Term(new_eta, new_exp, new_sign, new_label)


class TermList:
    """A sum of terms, i.e., a polynomial in eta with d-dependent coefficients.

    Matrix entries, minors, and Hurwitz coefficients are all TermLists.
    """

    def __init__(self, terms: List[Term] = None):
        self.terms = terms if terms is not None else []

    def __repr__(self):
        if not self.terms:
            return "TermList(empty)"
        lines = [f"TermList with {len(self.terms)} terms:"]
        by_eta = {}
        for t in self.terms:
            by_eta.setdefault(t.eta_power, []).append(t)
        for eta_pow in sorted(by_eta.keys()):
            lines.append(f"  eta^{eta_pow}: {len(by_eta[eta_pow])} terms")
        return "\n".join(lines)

    def __iter__(self):
        return iter(self.terms)

    def __len__(self):
        return len(self.terms)

    def __neg__(self) -> 'TermList':
        return TermList([-t for t in self.terms])

    def __add__(self, other: 'TermList') -> 'TermList':
        return TermList(self.terms + other.terms)

    def __sub__(self, other: 'TermList') -> 'TermList':
        return self + (-other)

    def __mul__(self, other: 'TermList') -> 'TermList':
        new_terms = []
        for t1 in self.terms:
            for t2 in other.terms:
                new_terms.append(t1 * t2)
        return TermList(new_terms)

    def filter_by_eta(self, eta_power: int) -> 'TermList':
        return TermList([t for t in self.terms if t.eta_power == eta_power])

    def filter_by_sign(self, sign: int) -> 'TermList':
        return TermList([t for t in self.terms if t.sign == sign])

    def get_eta_powers(self) -> List[int]:
        return sorted(set(t.eta_power for t in self.terms))

    def count_by_eta_and_sign(self) -> dict:
        counts = {}
        for t in self.terms:
            key = (t.eta_power, t.sign)
            counts[key] = counts.get(key, 0) + 1
        return counts


def term(eta_power: int, d_exponent, sign: int, label: str = "") -> TermList:
    """Create a TermList containing a single term."""
    return TermList([Term(eta_power, sp.sympify(d_exponent), sign, label)])


# =============================================================================
# Regime: parameter regime with derived-exponent substitutions
# =============================================================================

@dataclass
class Regime:
    """A parameter regime with specific substitutions for derived exponents."""
    name: str
    description: str
    conditions: List[str]                      # human-readable
    substitutions: Dict[sp.Symbol, sp.Expr]    # derived exponent -> expression

    def substitute(self, expr: sp.Expr) -> sp.Expr:
        """Apply regime-specific substitutions to an expression."""
        return simplify(expr.subs(self.substitutions))

    def __repr__(self):
        cond_str = " AND ".join(self.conditions)
        return f"Regime({self.name}: {cond_str})"


# -----------------------------------------------------------------------------
# Substitution tables for the four "primitive group" regimes.
#
# Each entry encodes the regime-specific values of the derived exponents
# (kappa_eff, psi, nu, mu, gamma_chi, delta_minus1_g_exp) in terms of
# (kappa, sigma, gamma).
# -----------------------------------------------------------------------------

# Dense regime with typical variance scaling (diagonal dominates chi).
#   Conditions: kappa <= sigma, sigma < kappa + 1.
DENSE_TYPICAL_SUBS: Dict[sp.Symbol, sp.Expr] = {
    kappa_eff: 0,
    psi: kappa,                     # min(kappa, sigma) = kappa since kappa <= sigma
    nu: gamma,                        # max(0, gamma - 0) = gamma
    mu: 0,                          # min(gamma, 0) = 0
    gamma_chi: 1 - kappa - sigma,   # 1 - psi - sigma
    delta_minus1_g_exp: 0,          # super-polynomially small; polynomial upper bound = 0
}

# Dense regime with rare/coherent variance scaling (cross-term dominates chi).
#   Conditions: kappa <= sigma, sigma >= kappa + 1.
DENSE_RARE_SUBS: Dict[sp.Symbol, sp.Expr] = {
    kappa_eff: 0,
    psi: kappa,
    nu: gamma,
    mu: 0,
    gamma_chi: -2 * kappa,          # coherent / cross-term dominance
    delta_minus1_g_exp: 0,
}

# Sparse regime with transient memory (decay faster than active-update rate).
#   Conditions: kappa > sigma, gamma <= kappa - sigma.
SPARSE_DECAY_LIMITED_SUBS: Dict[sp.Symbol, sp.Expr] = {
    kappa_eff: kappa - sigma,
    psi: sigma,                     # min(kappa, sigma) = sigma since kappa > sigma
    nu: 0,                          # max(0, gamma - kappa_eff) = 0 since gamma <= kappa_eff
    mu: gamma,                        # min(gamma, kappa_eff) = gamma
    gamma_chi: 1 - 2 * sigma,       # chi always typical in sparse
    # delta_{-1,g} ~ P/((P+eps)(P+2eps)) ~ d^{2 gamma - kappa_eff}
    delta_minus1_g_exp: 2 * gamma - (kappa - sigma),
}

# Sparse regime with persistent memory (active-update rate slower than decay).
#   Conditions: kappa > sigma, gamma > kappa - sigma.
SPARSE_SPARSITY_LIMITED_SUBS: Dict[sp.Symbol, sp.Expr] = {
    kappa_eff: kappa - sigma,
    psi: sigma,
    nu: gamma - kappa + sigma,        # max(0, gamma - kappa_eff)
    mu: kappa - sigma,              # min(gamma, kappa_eff) = kappa_eff
    gamma_chi: 1 - 2 * sigma,
    # delta_{-1,g} ~ 1/P ~ d^{kappa_eff}
    delta_minus1_g_exp: kappa - sigma,
}


# =============================================================================
# Test values (concrete (kappa, sigma, gamma) points satisfying each regime)
# =============================================================================

def get_test_values(regime_name: str) -> Dict[sp.Symbol, sp.Expr]:
    """Return concrete test values for (kappa, sigma, gamma) satisfying
    the named regime's conditions. Used for numerical sign disambiguation
    in ``determine_sign_in_regime``.
    """
    test_values = {
        "dense_typical": {
            kappa: sp.Rational(3, 10), sigma: sp.Rational(1, 2), gamma: sp.Rational(4, 5)
        },
        # kappa=0.3 <= sigma=0.5, and sigma=0.5 < kappa+1=1.3

        "dense_rare": {
            kappa: sp.Rational(1, 4), sigma: sp.Rational(3, 2), gamma: sp.Rational(1, 2)
        },
        # kappa=0.25 <= sigma=1.5, and sigma=1.5 >= kappa+1=1.25

        "sparse_decay_limited": {
            kappa: sp.Rational(4, 5), sigma: sp.Rational(3, 10), gamma: sp.Rational(1, 5)
        },
        # kappa=0.8 > sigma=0.3, and gamma=0.2 <= kappa-sigma=0.5

        "sparse_sparsity_limited": {
            kappa: sp.Rational(4, 5), sigma: sp.Rational(3, 10), gamma: sp.Rational(4, 5)
        },
        # kappa=0.8 > sigma=0.3, and gamma=0.8 > kappa-sigma=0.5
    }
    return test_values.get(regime_name, {})


# =============================================================================
# Matrix A_batch: 9 entries as TermLists
# =============================================================================

# Exponent for delta_{-1,g}: kept as a symbol so Regime.substitute selects
# the regime-dependent value.
DELTA_MINUS1_G_EXP = delta_minus1_g_exp

# Convenience: exponent for higher-order drift moments
#   (delta_theta^{(2)}, delta_{theta,g}, delta_g^{(2)})
MU2 = 2 * mu


def build_matrix_entries():
    """Build all 9 matrix entries as TermLists.

    Returns a dict keyed by entry name (e.g. 'a_R', 'b_V', 'c_C').

    The matrix structure is:
        A = | a_R  a_V  a_C |   (Row for dR/dt)
            | b_R  b_V  b_C |   (Row for dV/dt)
            | c_R  c_V  c_C |   (Row for dC/dt)

    Key scaling relationships:
        epsilon = 1-beta ~ d^{-gamma}
        phi_1 ~ d^{-psi}
        chi = (d+2) phi_2 + phi_3 ~ d^{gamma_chi}
        1 - barbeta_1, 1 - barbeta_2 ~ d^{-nu}

    Drift / product coefficients:
        First-moment drift:      delta_theta, delta_g, delta_{-1,theta} ~ d^{mu}
        Higher-order drift:      delta_theta^{(2)}, delta_{theta,g}, delta_g^{(2)} ~ d^{2 mu}

    Drift viscosity delta_{-1,g} := E[beta^K b(K)]:
        - sparse_decay_limited:    ~ d^{2 gamma - kappa_eff}
        - sparse_sparsity_limited: ~ d^{kappa_eff}
        - dense regimes:           super-polynomially suppressed; modeled as d^0
          (conservative polynomial upper bound).

    Notation: delta_theta^{(2)} means E[a(K)^2], delta_g^{(2)} means
    E[b(K)^2], and delta_{theta,g} means E[a(K) b(K)]. These are NOT the
    same as (delta_theta)^2, (delta_g)^2, or delta_theta * delta_g.
    """
    entries = {}

    # ---------------- Row 1: dR/dt coefficients (error evolution) ------------

    # a_R = -2 eta epsilon phi_1 + eta^2 epsilon^2 chi
    entries['a_R'] = (
        term(1, -alpha - gamma - psi, -1, "a_R^(1)  -2 eta eps phi1") +
        term(2, -2 * alpha - 2 * gamma + gamma_chi, +1, "a_R^(2)  +eta^2 eps^2 chi")
    )

    # a_V = eta^2 delta_theta^{(2)} - 2 eta^3 eps phi_1 delta_{theta,g}
    #       + eta^4 eps^2 chi delta_g^{(2)}
    entries['a_V'] = (
        term(2, -2 * alpha + MU2, +1, "a_V^(1)  +eta^2 d_theta^(2)") +
        term(3, -3 * alpha - gamma - psi + MU2, -1,
             "a_V^(2)  -2 eta^3 eps phi1 d_{theta,g}") +
        term(4, -4 * alpha - 2 * gamma + gamma_chi + MU2, +1,
             "a_V^(3)  +eta^4 eps^2 chi d_g^(2)")
    )

    # a_C = -2 eta delta_theta + 2 eta^2 eps phi_1 (delta_g + delta_theta)
    #       - 2 eta^3 eps^2 chi delta_g
    entries['a_C'] = (
        term(1, -alpha + mu, -1, "a_C^(1)  -2 eta d_theta") +
        term(2, -2 * alpha - gamma - psi + mu, +1,
             "a_C^(2)  +2 eta^2 eps phi1(d_g+d_theta)") +
        term(3, -3 * alpha - 2 * gamma + gamma_chi + mu, -1,
             "a_C^(3)  -2 eta^3 eps^2 chi d_g")
    )

    # ---------------- Row 2: dV/dt coefficients (momentum energy) ------------

    # b_R = epsilon^2 chi
    entries['b_R'] = term(0, -2 * gamma + gamma_chi, +1, "b_R^(1)  +eps^2 chi")

    # b_V = (barbeta_2 - 1) - 2 eta eps phi_1 delta_{-1,g}
    #       + eta^2 eps^2 chi delta_g^{(2)}
    entries['b_V'] = (
        term(0, -nu, -1, "b_V^(1)  (barbeta2-1)<0") +
        term(1, -alpha - gamma - psi + DELTA_MINUS1_G_EXP, -1,
             "b_V^(2)  -2 eta eps phi1 d_{-1,g}") +
        term(2, -2 * alpha - 2 * gamma + gamma_chi + MU2, +1,
             "b_V^(3)  +eta^2 eps^2 chi d_g^(2)")
    )

    # b_C = 2 eps barbeta_1 phi_1 - 2 eta eps^2 chi delta_g
    entries['b_C'] = (
        term(0, -gamma - psi, +1, "b_C^(1)  +2 eps barbeta1 phi1") +
        term(1, -alpha - 2 * gamma + gamma_chi + mu, -1,
             "b_C^(2)  -2 eta eps^2 chi d_g")
    )

    # ---------------- Row 3: dC/dt coefficients (correlation) ----------------

    # c_R = eps phi_1 - eta eps^2 chi
    entries['c_R'] = (
        term(0, -gamma - psi, +1, "c_R^(1)  +eps phi1") +
        term(1, -alpha - 2 * gamma + gamma_chi, -1, "c_R^(2)  -eta eps^2 chi")
    )

    # c_V = -eta delta_{-1,theta} + eta^2 eps phi_1 (delta_{theta,g} + delta_{-1,g})
    #       - eta^3 eps^2 chi delta_g^{(2)}
    # Note: delta_{theta,g} and delta_{-1,g} are kept as separate eta^2 terms
    # so their dominance can be resolved regime-by-regime.
    entries['c_V'] = (
        term(1, -alpha + mu, -1, "c_V^(1)  -eta d_{-1,theta}") +
        term(2, -2 * alpha - gamma - psi + MU2, +1,
             "c_V^(2a) +eta^2 eps phi1 d_{theta,g}") +
        term(2, -2 * alpha - gamma - psi + DELTA_MINUS1_G_EXP, +1,
             "c_V^(2b) +eta^2 eps phi1 d_{-1,g}") +
        term(3, -3 * alpha - 2 * gamma + gamma_chi + MU2, -1,
             "c_V^(3)  -eta^3 eps^2 chi d_g^(2)")
    )

    # c_C = (barbeta_1 - 1) - eta eps phi_1 (delta_g + delta_theta + barbeta_1)
    #       + 2 eta^2 eps^2 chi delta_g
    entries['c_C'] = (
        term(0, -nu, -1, "c_C^(1)  (barbeta1-1)<0") +
        term(1, -alpha - gamma - psi + mu, -1,
             "c_C^(2)  -eta eps phi1(d_g+d_theta+barbeta1)") +
        term(2, -2 * alpha - 2 * gamma + gamma_chi + mu, +1,
             "c_C^(3)  +2 eta^2 eps^2 chi d_g")
    )

    return entries


# =============================================================================
# Hurwitz coefficients c1, c2, c3
# =============================================================================

def compute_c1(entries):
    """Compute c_1 = -tr(A) = -(a_R + b_V + c_C). Returns a TermList."""
    trace = entries['a_R'] + entries['b_V'] + entries['c_C']
    return -trace


def compute_principal_minors(entries):
    """Compute the three principal 2x2 minors M_11, M_22, M_33.

    Returns dict with M_11, M_22, M_33 as TermLists, where:
        M_11 = b_V * c_C - b_C * c_V  (delete row 1, col 1)
        M_22 = a_R * c_C - a_C * c_R  (delete row 2, col 2)
        M_33 = a_R * b_V - a_V * b_R  (delete row 3, col 3)
    """
    return {
        'M_11': entries['b_V'] * entries['c_C'] - entries['b_C'] * entries['c_V'],
        'M_22': entries['a_R'] * entries['c_C'] - entries['a_C'] * entries['c_R'],
        'M_33': entries['a_R'] * entries['b_V'] - entries['a_V'] * entries['b_R'],
    }


def compute_c2(entries):
    """Compute c_2 = M_11 + M_22 + M_33 (sum of principal 2x2 minors)."""
    minors = compute_principal_minors(entries)
    c2 = minors['M_11'] + minors['M_22'] + minors['M_33']
    if not isinstance(c2, TermList):
        raise TypeError(f"Expected TermList, got {type(c2)}")
    return c2


def compute_cofactors(entries):
    """Compute the three cofactors used to expand det(A) along row 1.

    Returns dict with:
        M_1 = b_V * c_C - b_C * c_V  (cofactor of a_R)
        M_2 = b_R * c_C - b_C * c_R  (cofactor of a_V)
        M_3 = b_R * c_V - b_V * c_R  (cofactor of a_C)
    """
    return {
        'M_1': entries['b_V'] * entries['c_C'] - entries['b_C'] * entries['c_V'],
        'M_2': entries['b_R'] * entries['c_C'] - entries['b_C'] * entries['c_R'],
        'M_3': entries['b_R'] * entries['c_V'] - entries['b_V'] * entries['c_R'],
    }


def compute_determinant(entries):
    """Compute det(A) via cofactor expansion along row 1.

    det(A) = a_R * M_1 - a_V * M_2 + a_C * M_3.
    Returns (det_A, cofactors).
    """
    cofactors = compute_cofactors(entries)
    det_A = (entries['a_R'] * cofactors['M_1'] -
             entries['a_V'] * cofactors['M_2'] +
             entries['a_C'] * cofactors['M_3'])
    return det_A, cofactors


def compute_c3(entries):
    """Compute c_3 = -det(A). Returns (c3_termlist, cofactors)."""
    det_A, cofactors = compute_determinant(entries)
    return -det_A, cofactors


# =============================================================================
# Leading-term analysis
# =============================================================================

def substitute_regime(expr, regime):
    """Apply regime-specific substitutions and simplify.

    Args:
        expr: A sympy expression possibly containing (psi, nu, mu, kappa_eff,
            gamma_chi, delta_minus1_g_exp).
        regime: A Regime object with substitutions dict.

    Returns:
        Simplified expression in terms of (kappa, sigma, gamma, alpha).
    """
    return simplify(expr.subs(regime.substitutions))


def determine_sign_in_regime(expr, regime_name):
    """Determine the sign of an expression (in kappa, sigma, gamma, alpha)
    given regime constraints.

    Returns:
        +1 if expr > 0 in this regime
        -1 if expr < 0 in this regime
        0 if expr == 0 in this regime
        None if sign cannot be determined (depends on specific parameter values)
    """
    expr = simplify(expr)

    if expr.is_number:
        if expr > 0:
            return +1
        elif expr < 0:
            return -1
        else:
            return 0

    if expr == 0:
        return 0

    free_syms = expr.free_symbols
    if alpha in free_syms:
        # Sign depends on the learning-rate exponent - cannot determine
        return None

    # Simple symbolic patterns
    if expr == -gamma:
        return -1
    if expr == gamma:
        return +1
    if expr == -kappa:
        return -1
    if expr == -sigma:
        return -1

    # For more complex expressions, evaluate at the regime's test point
    test_vals = get_test_values(regime_name)
    if test_vals:
        try:
            if not free_syms.issubset(set(test_vals.keys())):
                return None
            numerical_val = float(expr.subs(test_vals))
            if abs(numerical_val) < 1e-10:
                return 0
            elif numerical_val > 0:
                return +1
            else:
                return -1
        except (TypeError, ValueError):
            return None

    return None


@dataclass
class LeadingTermResult:
    """Result of leading-term analysis for a single (eta-power, sign) group."""
    eta_power: int
    sign: int
    num_terms: int
    leading_term: Optional[Term]
    leading_exponent_raw: Optional[sp.Expr]      # Before regime substitution
    leading_exponent_subst: Optional[sp.Expr]    # After regime substitution
    tied_terms: List[Term]

    def sign_str(self):
        return "+" if self.sign == +1 else "-"

    def __repr__(self):
        if self.leading_term is None:
            return f"eta^{self.eta_power} {self.sign_str()}: (no terms)"
        return f"eta^{self.eta_power} {self.sign_str()}: d^({self.leading_exponent_subst})"


def find_leading_term_in_group(terms: List[Term], regime: 'Regime') -> LeadingTermResult:
    """Find the leading term among a group of same-sign, same-eta-power terms.

    The leader is the term with the largest (least negative) d-exponent after
    regime substitution. Pairwise comparisons use ``determine_sign_in_regime``.
    """
    if not terms:
        return LeadingTermResult(
            eta_power=0, sign=0, num_terms=0,
            leading_term=None, leading_exponent_raw=None,
            leading_exponent_subst=None, tied_terms=[]
        )

    eta_power = terms[0].eta_power
    sign = terms[0].sign

    subst_data = []
    for t in terms:
        exp_subst = substitute_regime(t.d_exponent, regime)
        subst_data.append((t, t.d_exponent, exp_subst))

    leaders = [subst_data[0]]

    for item in subst_data[1:]:
        t, exp_raw, exp_subst = item
        leader_t, leader_raw, leader_subst = leaders[0]

        diff = simplify(exp_subst - leader_subst)
        sign_of_diff = determine_sign_in_regime(diff, regime.name)

        if sign_of_diff == +1:
            leaders = [item]
        elif sign_of_diff == 0:
            leaders.append(item)
        # sign_of_diff in (-1, None) => keep current leader

    leading_t, leading_raw, leading_subst = leaders[0]
    tied = [item[0] for item in leaders]

    return LeadingTermResult(
        eta_power=eta_power,
        sign=sign,
        num_terms=len(terms),
        leading_term=leading_t,
        leading_exponent_raw=leading_raw,
        leading_exponent_subst=leading_subst,
        tied_terms=tied,
    )


def analyze_all_groups(
    termlist: TermList, regime: 'Regime'
) -> Dict[Tuple[int, int], LeadingTermResult]:
    """Analyze every (eta-power, sign) group in a TermList.

    Returns a dict mapping (eta_power, sign) -> LeadingTermResult.
    """
    results = {}

    for eta_pow in termlist.get_eta_powers():
        terms_at_eta = termlist.filter_by_eta(eta_pow)

        for sign in [+1, -1]:
            sign_terms = terms_at_eta.filter_by_sign(sign).terms
            if sign_terms:
                result = find_leading_term_in_group(sign_terms, regime)
                results[(eta_pow, sign)] = result

    return results


# =============================================================================
# Constraint derivation
# =============================================================================

@dataclass
class StabilityConstraint:
    """Result of deriving a single Routh-Hurwitz constraint alpha > alpha_min."""
    condition_name: str             # e.g., "c_3 > 0"
    regime_name: str
    is_stable_always: bool          # True if no constraint needed
    is_unstable_always: bool        # True if never stable
    alpha_min: Optional[sp.Expr]    # Constraint: alpha > alpha_min
    alpha_min_simplified: Optional[sp.Expr]
    derivation_steps: List[str]

    def __repr__(self):
        if self.is_stable_always:
            return f"{self.condition_name} in {self.regime_name}: Always satisfied"
        if self.is_unstable_always:
            return f"{self.condition_name} in {self.regime_name}: Never satisfied"
        return f"{self.condition_name} in {self.regime_name}: alpha > {self.alpha_min_simplified}"


def derive_alpha_bound(
    leading_pos: LeadingTermResult,
    leading_neg: LeadingTermResult,
    condition_name: str,
    regime: 'Regime',
) -> StabilityConstraint:
    """Derive alpha > alpha_min from leading positive/negative exponents.

    The d-exponents already encode the -k*alpha contribution from eta^k, so
    stability simply requires e_pos > e_neg; we solve this for alpha.
    """
    steps = []

    if leading_pos is None or leading_pos.leading_term is None:
        steps.append("No positive terms found")
        return StabilityConstraint(
            condition_name=condition_name,
            regime_name=regime.name,
            is_stable_always=False,
            is_unstable_always=True,
            alpha_min=None,
            alpha_min_simplified=None,
            derivation_steps=steps,
        )

    if leading_neg is None or leading_neg.leading_term is None:
        steps.append("No negative terms found")
        steps.append("Condition satisfied for all eta")
        return StabilityConstraint(
            condition_name=condition_name,
            regime_name=regime.name,
            is_stable_always=True,
            is_unstable_always=False,
            alpha_min=None,
            alpha_min_simplified=None,
            derivation_steps=steps,
        )

    eta_pos = leading_pos.eta_power
    eta_neg = leading_neg.eta_power
    e_pos = leading_pos.leading_exponent_subst
    e_neg = leading_neg.leading_exponent_subst

    steps.append(f"Leading positive: eta^{eta_pos} with exponent e+ = {e_pos}")
    steps.append(f"Leading negative: eta^{eta_neg} with exponent e- = {e_neg}")
    steps.append("")
    steps.append("Note: Exponents already include -k*alpha from eta^k scaling")
    steps.append(f"Total d-scaling of positive term: d^{{{e_pos}}}")
    steps.append(f"Total d-scaling of negative term: d^{{{e_neg}}}")
    steps.append("")
    steps.append("For stability (positive dominates): e+ > e-")
    steps.append(f"  {e_pos} > {e_neg}")

    diff = simplify(e_pos - e_neg)
    steps.append(f"  e+ - e- = {diff}")
    steps.append(f"  Need: {diff} > 0")

    if alpha not in diff.free_symbols:
        sign = determine_sign_in_regime(diff, regime.name)
        if sign == +1:
            steps.append(f"  {diff} > 0 is always true")
            steps.append("  -> Always stable (no constraint on alpha)")
            return StabilityConstraint(
                condition_name=condition_name,
                regime_name=regime.name,
                is_stable_always=True,
                is_unstable_always=False,
                alpha_min=None,
                alpha_min_simplified=None,
                derivation_steps=steps,
            )
        elif sign == -1:
            steps.append(f"  {diff} > 0 is never true")
            steps.append("  -> Always unstable")
            return StabilityConstraint(
                condition_name=condition_name,
                regime_name=regime.name,
                is_stable_always=False,
                is_unstable_always=True,
                alpha_min=None,
                alpha_min_simplified=None,
                derivation_steps=steps,
            )
        else:
            steps.append(f"  Cannot determine sign of {diff}")
            return StabilityConstraint(
                condition_name=condition_name,
                regime_name=regime.name,
                is_stable_always=False,
                is_unstable_always=False,
                alpha_min=None,
                alpha_min_simplified=None,
                derivation_steps=steps,
            )

    # diff contains alpha: solve for the constraint
    coeff_alpha = diff.coeff(alpha)
    rest = simplify(diff - coeff_alpha * alpha)

    steps.append("")
    steps.append("Solving for alpha:")
    steps.append(f"  {diff} > 0")
    steps.append(f"  {coeff_alpha}*alpha + ({rest}) > 0")

    if coeff_alpha == 0:
        steps.append("  No alpha dependence (unexpected)")
        return StabilityConstraint(
            condition_name=condition_name,
            regime_name=regime.name,
            is_stable_always=False,
            is_unstable_always=False,
            alpha_min=None,
            alpha_min_simplified=None,
            derivation_steps=steps,
        )
    elif coeff_alpha > 0:
        alpha_min = simplify(-rest / coeff_alpha)
        steps.append(f"  {coeff_alpha}*alpha > {-rest}")
        steps.append(f"  alpha > {alpha_min}")
        return StabilityConstraint(
            condition_name=condition_name,
            regime_name=regime.name,
            is_stable_always=False,
            is_unstable_always=False,
            alpha_min=alpha_min,
            alpha_min_simplified=simplify(alpha_min),
            derivation_steps=steps,
        )
    else:  # coeff_alpha < 0
        alpha_max = simplify(-rest / coeff_alpha)
        steps.append(f"  {coeff_alpha}*alpha > {-rest}")
        steps.append(f"  alpha < {alpha_max}  (inequality flips due to negative coefficient)")
        steps.append("  This gives an UPPER bound on alpha, not lower bound")
        steps.append("  -> System is stable for SMALL alpha (large learning rate)")
        steps.append("  This is unusual and may indicate an error")
        return StabilityConstraint(
            condition_name=condition_name,
            regime_name=regime.name,
            is_stable_always=False,
            is_unstable_always=False,
            alpha_min=None,
            alpha_min_simplified=None,
            derivation_steps=steps,
        )


def _leading_pos_neg_at_lowest_eta(results):
    """Helper: from analyze_all_groups output, return (leading_pos, leading_neg)
    at the lowest eta-power that has positive / negative terms respectively.
    """
    pos_keys = [(eta, s) for (eta, s) in results.keys() if s == +1]
    neg_keys = [(eta, s) for (eta, s) in results.keys() if s == -1]

    if not pos_keys:
        leading_pos = None
    else:
        min_eta_pos = min(eta for eta, _ in pos_keys)
        leading_pos = results[(min_eta_pos, +1)]

    if not neg_keys:
        leading_neg = None
    else:
        min_eta_neg = min(eta for eta, _ in neg_keys)
        leading_neg = results[(min_eta_neg, -1)]

    return leading_pos, leading_neg


def derive_c3_constraint(entries, regime: 'Regime') -> StabilityConstraint:
    """Derive the c_3 > 0 constraint for a given regime."""
    c3, _ = compute_c3(entries)
    results = analyze_all_groups(c3, regime)
    leading_pos, leading_neg = _leading_pos_neg_at_lowest_eta(results)
    return derive_alpha_bound(leading_pos, leading_neg, "c_3 > 0", regime)


def derive_c1_constraint(entries, regime: 'Regime') -> StabilityConstraint:
    """Derive the c_1 > 0 constraint for a given regime.

    c_1 = -tr(A) = -(a_R + b_V + c_C).
    """
    c1 = compute_c1(entries)
    results = analyze_all_groups(c1, regime)
    leading_pos, leading_neg = _leading_pos_neg_at_lowest_eta(results)
    return derive_alpha_bound(leading_pos, leading_neg, "c_1 > 0", regime)


def derive_c2_constraint(entries, regime: 'Regime') -> StabilityConstraint:
    """Derive the c_2 > 0 constraint for a given regime.

    c_2 = M_11 + M_22 + M_33 (sum of principal 2x2 minors).
    """
    c2 = compute_c2(entries)
    results = analyze_all_groups(c2, regime)
    leading_pos, leading_neg = _leading_pos_neg_at_lowest_eta(results)
    return derive_alpha_bound(leading_pos, leading_neg, "c_2 > 0", regime)


def derive_c1c2_gt_c3_constraint(entries, regime: 'Regime') -> StabilityConstraint:
    """Derive the c_1 c_2 > c_3 constraint for a given regime.

    Strategy:
      1. Find leading scaling of c_1 (typically O(eta^0), exponent ~ -nu)
      2. Find leading scaling of c_2 (typically O(eta^0), exponent ~ -2 nu)
      3. Find leading scaling of c_3 (typically O(eta^1), exponent ~ -alpha - 2 nu - psi)
      4. For c_1 c_2 > c_3: exponent(c_1) + exponent(c_2) > exponent(c_3).
    """
    steps = []

    c1 = compute_c1(entries)
    c2 = compute_c2(entries)
    c3, _ = compute_c3(entries)

    c1_results = analyze_all_groups(c1, regime)
    c2_results = analyze_all_groups(c2, regime)
    c3_results = analyze_all_groups(c3, regime)

    steps.append("Finding leading scalings for c_1, c_2, c_3...")

    c1_eta0_pos = c1_results.get((0, +1))
    if c1_eta0_pos:
        c1_leading_exp = c1_eta0_pos.leading_exponent_subst
        steps.append(f"c_1 leading: eta^0 positive, exponent = {c1_leading_exp}")
    else:
        steps.append("WARNING: No O(eta^0) positive terms in c_1")
        c1_leading_exp = None

    c2_eta0_pos = c2_results.get((0, +1))
    if c2_eta0_pos:
        c2_leading_exp = c2_eta0_pos.leading_exponent_subst
        steps.append(f"c_2 leading: eta^0 positive, exponent = {c2_leading_exp}")
    else:
        steps.append("WARNING: No O(eta^0) positive terms in c_2")
        c2_leading_exp = None

    c3_eta1_pos = c3_results.get((1, +1))
    if c3_eta1_pos:
        c3_leading_exp = c3_eta1_pos.leading_exponent_subst
        steps.append(f"c_3 leading: eta^1 positive, exponent = {c3_leading_exp}")
    else:
        steps.append("WARNING: No O(eta^1) positive terms in c_3")
        c3_leading_exp = None

    if c1_leading_exp is None or c2_leading_exp is None or c3_leading_exp is None:
        return StabilityConstraint(
            condition_name="c_1 c_2 > c_3",
            regime_name=regime.name,
            is_stable_always=False,
            is_unstable_always=False,
            alpha_min=None,
            alpha_min_simplified=None,
            derivation_steps=steps + ["Cannot derive constraint: missing leading terms"],
        )

    # For c_1 c_2 > c_3: exponent(c_1) + exponent(c_2) > exponent(c_3)
    lhs = simplify(c1_leading_exp + c2_leading_exp)
    rhs = c3_leading_exp

    steps.append("\nFor c_1 c_2 > c_3:")
    steps.append(f"  exp(c_1) + exp(c_2) = {c1_leading_exp} + {c2_leading_exp} = {lhs}")
    steps.append(f"  exp(c_3) = {rhs}")
    steps.append(f"  Need: {lhs} > {rhs}")

    diff = simplify(lhs - rhs)
    steps.append(f"  Difference: {diff}")

    coeff_alpha = diff.coeff(alpha)
    rest = simplify(diff - coeff_alpha * alpha)

    steps.append(f"  Coefficient of alpha: {coeff_alpha}")
    steps.append(f"  Constant part: {rest}")

    if coeff_alpha == 0:
        sign = determine_sign_in_regime(diff, regime.name)
        if sign == +1:
            steps.append("  No alpha dependence, diff > 0: Always satisfied")
            return StabilityConstraint(
                condition_name="c_1 c_2 > c_3",
                regime_name=regime.name,
                is_stable_always=True,
                is_unstable_always=False,
                alpha_min=None,
                alpha_min_simplified=None,
                derivation_steps=steps,
            )
        elif sign == -1:
            steps.append("  No alpha dependence, diff < 0: Never satisfied")
            return StabilityConstraint(
                condition_name="c_1 c_2 > c_3",
                regime_name=regime.name,
                is_stable_always=False,
                is_unstable_always=True,
                alpha_min=None,
                alpha_min_simplified=None,
                derivation_steps=steps,
            )

    if coeff_alpha > 0:
        alpha_min = simplify(-rest / coeff_alpha)
        steps.append(f"  For diff > 0: alpha > {alpha_min}")
    else:
        steps.append("  Coefficient of alpha is negative: gives upper bound, not lower")
        alpha_min = None

    return StabilityConstraint(
        condition_name="c_1 c_2 > c_3",
        regime_name=regime.name,
        is_stable_always=False,
        is_unstable_always=False,
        alpha_min=alpha_min,
        alpha_min_simplified=simplify(alpha_min) if alpha_min else None,
        derivation_steps=steps,
    )


# =============================================================================
# Canonicalization and atom-based nonnegativity certificates
# =============================================================================

def _canon(expr: Optional[sp.Expr]) -> Optional[sp.Expr]:
    """Canonical form for symbolic comparison: expand then together."""
    if expr is None:
        return None
    return sp.together(sp.expand(expr))


def _is_zero(expr: sp.Expr) -> bool:
    return bool(_canon(expr) == 0)


def _eq_expr(a: Optional[sp.Expr], b: Optional[sp.Expr]) -> bool:
    if a is None or b is None:
        return False
    return _is_zero(_canon(a - b))


def _eta_power_from_alpha(alpha_expr: sp.Expr) -> sp.Expr:
    """Convert an alpha_min value to the corresponding d-exponent of eta_max.

    Since eta ~ d^{-alpha}, the maximal eta scales as d^{-alpha_min}.
    """
    return _canon(-alpha_expr)


def _max_alpha(a: Optional[sp.Expr], b: Optional[sp.Expr]) -> Optional[sp.Expr]:
    if a is None and b is None:
        return None
    if a is None:
        return b
    if b is None:
        return a
    return sp.Max(a, b)


# Symbol-name sets used to recover (kappa, sigma, gamma) from an arbitrary
# expression's free_symbols.
KAPPA_NAMES = {"kappa", "κ"}
SIGMA_NAMES = {"sigma", "σ"}
GAMMA_NAMES = {"gamma", "γ"}


def symbols_in_expr(expr: sp.Expr) -> Tuple[sp.Symbol, sp.Symbol, sp.Symbol]:
    """Return (kappa_sym, sigma_sym, gamma_sym) chosen from expr.free_symbols
    by name. Falls back to the canonical module-level symbols.
    """
    syms = list(expr.free_symbols)
    k_sym = next((s for s in syms if s.name in KAPPA_NAMES), None) or kappa
    s_sym = next((s for s in syms if s.name in SIGMA_NAMES), None) or sigma
    g_sym = next((s for s in syms if s.name in GAMMA_NAMES), None) or gamma
    return k_sym, s_sym, g_sym


# Global assumption: gamma >= 0.
GAMMA_NONNEG = True


def _normalize_condition(cond: str) -> str:
    """Normalize a regime-condition string: ASCII inequalities and names,
    collapsed whitespace.
    """
    c = (cond.replace("≤", "<=").replace("≥", ">=")
             .replace("κ", "kappa").replace("σ", "sigma").replace("γ", "gamma"))
    c = re.sub(r"\s+", " ", c.strip())
    return c


def infer_atoms_from_conditions(
    regime, k: sp.Symbol, s: sp.Symbol, gamma: sp.Symbol
) -> Dict[str, sp.Expr]:
    """Infer a set of nonnegative "atoms" from regime.conditions strings.

    Recognized condition patterns (after normalization):
      kappa <= sigma             => (sigma - kappa) >= 0
      kappa > sigma              => (kappa - sigma) >= 0
      sigma < kappa + 1          => (kappa + 1 - sigma) >= 0
      sigma >= kappa + 1         => (sigma - kappa - 1) >= 0
      gamma <= kappa - sigma    => (kappa - sigma - gamma) >= 0
      gamma > kappa - sigma     => (gamma + sigma - kappa) >= 0

    The global assumption gamma >= 0 also contributes an atom when GAMMA_NONNEG.
    """
    atoms: Dict[str, sp.Expr] = {}
    if GAMMA_NONNEG:
        atoms["γ"] = gamma

    conds = getattr(regime, "conditions", [])
    conds_norm = [_normalize_condition(c) for c in conds]

    for c in conds_norm:
        if "kappa <= sigma" in c:
            atoms["σ-κ"] = s - k
        if "kappa > sigma" in c:
            atoms["κ-σ"] = k - s

        if "sigma < kappa + 1" in c or "sigma < kappa+1" in c:
            atoms["κ+1-σ"] = k + 1 - s

        if "sigma >= kappa + 1" in c or "sigma >= kappa+1" in c:
            atoms["σ-κ-1"] = s - k - 1

        if "gamma <= kappa - sigma" in c or "gamma <= kappa-sigma" in c:
            atoms["κ-σ-γ"] = k - s - gamma

        if "gamma > kappa - sigma" in c or "gamma > kappa-sigma" in c:
            atoms["γ+σ-κ"] = gamma + s - k

    return atoms


def fallback_atoms_by_name(
    regime, k: sp.Symbol, s: sp.Symbol, gamma: sp.Symbol
) -> Dict[str, sp.Expr]:
    """Hardcoded atom sets for the four named primitive regimes.

    Invoked by ``leq_with_regime_proof`` as a safety net; for unknown regime
    names (e.g. the six-region names) this returns only {gamma} under
    GAMMA_NONNEG, which is a no-op on top of ``infer_atoms_from_conditions``.
    """
    name = getattr(regime, "name", "")
    atoms = {"γ": gamma} if GAMMA_NONNEG else {}
    if name == "dense_typical":
        atoms.update({"σ-κ": s - k, "κ+1-σ": k + 1 - s})
    elif name == "dense_rare":
        atoms.update({"σ-κ": s - k, "σ-κ-1": s - k - 1})
    elif name == "sparse_decay_limited":
        atoms.update({"κ-σ": k - s, "κ-σ-γ": k - s - gamma})
    elif name == "sparse_sparsity_limited":
        atoms.update({"κ-σ": k - s, "γ+σ-κ": gamma + s - k})
    return atoms


def prove_nonneg_by_atoms(
    diff: sp.Expr, atoms: Dict[str, sp.Expr],
    k: sp.Symbol, s: sp.Symbol, gamma: sp.Symbol,
) -> Tuple[Optional[bool], str]:
    """Try to prove diff >= 0 by writing it as a nonnegative combination:

        diff = c0 + sum_i c_i * atom_i

    where each c_i is either a nonnegative number, or an affine expression
    (a*gamma + b) with a, b >= 0 (using gamma >= 0). Atoms themselves are
    assumed >= 0 by regime/global assumptions.

    Searches over subsets of atoms up to size 3 and solves the linear system.

    Returns:
        (True, explanation)  - certificate found
        (None, explanation)  - no certificate found (not a contradiction)
    """
    diff = _canon(diff)

    if diff == 0:
        return (True, "diff == 0")
    if diff.is_number:
        return (bool(diff >= 0), f"numeric diff={diff}")

    def vec(expr: sp.Expr) -> sp.Matrix:
        expr = _canon(expr)
        P = sp.Poly(expr, k, s, gamma, domain="EX")
        for m in P.monoms():
            if sum(m) >= 2:
                raise ValueError(f"Nonlinear monomial {m} in expr={expr}")
        c1 = P.coeff_monomial((0, 0, 0))
        ck = P.coeff_monomial((1, 0, 0))
        cs = P.coeff_monomial((0, 1, 0))
        cl = P.coeff_monomial((0, 0, 1))
        return sp.Matrix([c1, ck, cs, cl])

    b = vec(diff)
    e0 = sp.Matrix([1, 0, 0, 0])

    atom_items = list(atoms.items())
    atom_vecs = [(name, at, vec(at)) for name, at in atom_items]

    def coeff_nonneg(c: sp.Expr) -> bool:
        c = sp.simplify(c)
        if c.is_number:
            return bool(c >= 0)
        # allow a*gamma + b with a, b >= 0 numbers
        P = sp.Poly(c, gamma, domain="EX")
        if P.degree() <= 1:
            a = sp.simplify(P.coeff_monomial((1,)))
            bb = sp.simplify(P.coeff_monomial((0,)))
            return bool(a.is_number and bb.is_number and a >= 0 and bb >= 0)
        return False

    max_subset = min(3, len(atom_vecs))
    for r in range(0, max_subset + 1):
        for subset in itertools.combinations(atom_vecs, r):
            Vcols = [e0] + [x[2] for x in subset]
            V = sp.Matrix.hstack(*Vcols)
            if V.rank() < V.shape[1]:
                continue
            try:
                c = V.LUsolve(b)
            except Exception:
                continue

            c0 = sp.simplify(c[0])
            if not coeff_nonneg(c0):
                continue

            ok = True
            parts = [f"{c0}"]
            for j, (nm, _, _) in enumerate(subset, start=1):
                cj = sp.simplify(c[j])
                if not coeff_nonneg(cj):
                    ok = False
                    break
                parts.append(f"{cj}*({nm})")

            if ok:
                return (True, "diff = " + " + ".join(parts))

    return (None, "no certificate found from inferred atoms "
                  "(may need more atoms or finer regimes)")


def leq_with_regime_proof(
    alpha_ci: Optional[sp.Expr], alpha_c3: Optional[sp.Expr], regime,
) -> Tuple[Optional[bool], Optional[sp.Expr], str, Dict[str, sp.Expr]]:
    """Try to prove alpha_min(c_i) <= alpha_min(c_3) using regime atoms.

    Returns (result, diff, explanation, atom_set) where:
      - result is True/False/None
      - diff = alpha_c3 - alpha_ci (canonical form) or None
    """
    if alpha_ci is None or alpha_c3 is None:
        return (None, None, "missing expressions", {})

    diff = _canon(alpha_c3 - alpha_ci)
    k, s, gamma_sym = symbols_in_expr(diff)

    atoms = infer_atoms_from_conditions(regime, k, s, gamma_sym)
    fb = fallback_atoms_by_name(regime, k, s, gamma_sym)
    for kk, vv in fb.items():
        atoms.setdefault(kk, vv)

    ok, expl = prove_nonneg_by_atoms(diff, atoms, k, s, gamma_sym)
    return (ok, diff, expl, atoms)


# =============================================================================
# Expected closed forms and regime report
# =============================================================================

def expected_alpha_min_c3(regime) -> sp.Expr:
    """Paper's closed form for c_3 > 0: alpha_min = gamma_chi + psi."""
    return _canon((gamma_chi + psi).subs(regime.substitutions))


def expected_alpha_min_c1c2(regime) -> sp.Expr:
    """Paper's closed form for c_1 c_2 > c_3: alpha_min = nu - psi."""
    return _canon((nu - psi).subs(regime.substitutions))


@dataclass
class RegimeReport:
    """Full verification report for a single regime/region.

    Fields bundle the derived alpha_min values, pass/fail verdicts against
    the closed forms (gamma_chi + psi and nu - psi), the nonbinding proofs
    for c_1 and c_2, and the implied eta_max scaling.
    """
    regime_name: str
    conditions: str

    alpha_c3: Optional[sp.Expr]
    alpha_c1: Optional[sp.Expr]
    alpha_c2: Optional[sp.Expr]
    alpha_c1c2: Optional[sp.Expr]

    c3_matches: bool
    c1c2_matches: bool

    c1_leq: Optional[bool]
    c2_leq: Optional[bool]
    c1_diff: Optional[sp.Expr]
    c2_diff: Optional[sp.Expr]
    c1_expl: str
    c2_expl: str

    alpha_star: Optional[sp.Expr]
    switch_expr: Optional[sp.Expr]
    eta_scaling: str


def build_regime_report(entries, regime) -> RegimeReport:
    """Build the complete verification report for a single regime.

    Derives c_1, c_2, c_3, and c_1 c_2 > c_3 constraints; checks them
    against the paper's closed forms; certifies that c_1 and c_2 are not
    binding relative to c_3; and reports alpha_star = max(alpha_c3, alpha_c1c2)
    along with the implied eta_max ~ d^{-alpha_star} scaling.
    """
    c3_con = derive_c3_constraint(entries, regime)
    c1_con = derive_c1_constraint(entries, regime)
    c2_con = derive_c2_constraint(entries, regime)
    c1c2_con = derive_c1c2_gt_c3_constraint(entries, regime)

    alpha_c3 = _canon(c3_con.alpha_min_simplified)
    alpha_c1 = _canon(c1_con.alpha_min_simplified)
    alpha_c2 = _canon(c2_con.alpha_min_simplified)
    alpha_c1c2 = _canon(c1c2_con.alpha_min_simplified)

    exp_c3 = expected_alpha_min_c3(regime)
    exp_c1c2 = expected_alpha_min_c1c2(regime)

    c3_ok = _eq_expr(alpha_c3, exp_c3)
    c1c2_ok = _eq_expr(alpha_c1c2, exp_c1c2)

    c1_leq, c1_diff, c1_expl, _c1_atoms = leq_with_regime_proof(alpha_c1, alpha_c3, regime)
    c2_leq, c2_diff, c2_expl, _c2_atoms = leq_with_regime_proof(alpha_c2, alpha_c3, regime)

    switch_expr = None
    if alpha_c1c2 is not None and alpha_c3 is not None:
        switch_expr = _canon(alpha_c1c2 - alpha_c3)

    alpha_star = _max_alpha(alpha_c3, alpha_c1c2)
    eta_scaling = "N/A" if alpha_star is None else f"d^({_eta_power_from_alpha(alpha_star)})"

    return RegimeReport(
        regime_name=getattr(regime, "name", "regime"),
        conditions=", ".join(getattr(regime, "conditions", [])),

        alpha_c3=alpha_c3,
        alpha_c1=alpha_c1,
        alpha_c2=alpha_c2,
        alpha_c1c2=alpha_c1c2,

        c3_matches=c3_ok,
        c1c2_matches=c1c2_ok,

        c1_leq=c1_leq,
        c2_leq=c2_leq,
        c1_diff=c1_diff,
        c2_diff=c2_diff,
        c1_expl=c1_expl,
        c2_expl=c2_expl,

        alpha_star=alpha_star,
        switch_expr=switch_expr,
        eta_scaling=eta_scaling,
    )
