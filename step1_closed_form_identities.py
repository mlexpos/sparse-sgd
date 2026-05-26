"""Symbolic verification of the closed-form leading-order expansion of c_3.

The Routh--Hurwitz coefficient c_3 = -det(A) is claimed in the paper's
stability appendix to satisfy

    c_3 = 2 eta epsilon B_1 (1 - bar_beta_2) [(1 - bar_beta_1) + delta_theta]
                                                                    + O(eta^2)
        = 2 eta B_1 (1 - bar_beta_1)(1 - bar_beta_2) + O(eta^2)

where the second equality uses the epsilon-cancellation identity:

    (1 - bar_beta_1) + delta_theta = (1 - bar_beta_1) / epsilon.

This script verifies BOTH steps symbolically by:
  1. Building the 3x3 ODE coefficient matrix A from the full-ODE
     matrix-entries section of the ODE-derivation appendix, in the full
     closed-form algebra (no asymptotic decomposition).
  2. Computing -det(A), extracting eta-power coefficients, and checking
     - eta^0 coefficient is zero,
     - eta^1 coefficient equals the Step 1 closed form,
     - the Step 1 form simplifies to the clean form via epsilon-cancellation.

It also prints the fully-collected eta^2 closed form, which the stability
appendix gives in a footnote and references this script as the symbolic
verification.
"""

import sympy as sp


# --- Free symbols ---------------------------------------------------------
# eta and beta are the dynamical parameters; P, p, B, d are model parameters.
# We treat P (= P_batch) as a free symbol with Q = 1 - P, rather than expanding
# P = 1 - (1-p)^B, to keep simplifications tractable.
eta, beta = sp.symbols("eta beta", positive=True)
P, p, B, d = sp.symbols("P p B d", positive=True)
Q = 1 - P
eps = 1 - beta


# --- Retention factors and drift coefficients (closed forms from the
#     setup appendix: retention factors, drift coefficients, squared-drift
#     coefficients, and product terms).
beta1 = P * beta / (1 - Q * beta)
beta2 = P * beta**2 / (1 - Q * beta**2)

dth = beta / (1 - Q * beta)                                  # delta_theta
dg = Q * beta / (1 - Q * beta)                               # delta_g
dth2 = beta**2 * (1 + Q * beta) / ((1 - Q * beta) * (1 - Q * beta**2))
dg2 = Q * dth2                                               # delta_g^(2)
dm1th = P * beta**2 / ((1 - Q * beta) * (1 - Q * beta**2))   # delta_{-1, theta}
dm1g = P * Q * beta**3 / ((1 - Q * beta) * (1 - Q * beta**2))
dthg = Q * beta**2 * (1 + beta) / ((1 - Q * beta) * (1 - Q * beta**2))


# --- Batch scaling factors (from the batch-scaling-factors section of the
#     ODE-derivation appendix).
B1 = p / P
Bdiag = p / (B * P)
Bcross = p**2 * (B - 1) / (B * P)
B2 = (d + 2) * Bdiag + Bcross


# --- Matrix entries (from the full-ODE matrix-entries section of the
#     ODE-derivation appendix).
a_R = -2 * eta * eps * B1 + eta**2 * eps**2 * B2
a_V = (
    eta**2 * dth2
    - 2 * eta**3 * eps * B1 * dthg
    + eta**4 * eps**2 * B2 * dg2
)
a_C = (
    -2 * eta * dth
    + 2 * eta**2 * eps * B1 * (dg + dth)
    - 2 * eta**3 * eps**2 * B2 * dg
)

b_R = eps**2 * B2
b_V = (beta2 - 1) - 2 * eta * eps * B1 * dm1g + eta**2 * eps**2 * B2 * dg2
b_C = 2 * eps * beta1 * B1 - 2 * eta * eps**2 * B2 * dg

c_R = eps * B1 - eta * eps**2 * B2
c_V = (
    -eta * dm1th
    + eta**2 * eps * B1 * (dthg + dm1g)
    - eta**3 * eps**2 * B2 * dg2
)
c_C = (
    (beta1 - 1)
    - eta * eps * B1 * (dg + dth + beta1)
    + 2 * eta**2 * eps**2 * B2 * dg
)

A = sp.Matrix([
    [a_R, a_V, a_C],
    [b_R, b_V, b_C],
    [c_R, c_V, c_C],
])


# --- Compute the characteristic polynomial coefficients and split by eta.
# Recall c_1 = -tr(A), c_2 = sum of principal 2x2 minors, c_3 = -det(A).
c1 = sp.expand(-A.trace())
c2_raw = sum(
    A.minor(i, i) for i in range(3)
)  # sum of principal 2x2 minors
c2 = sp.expand(c2_raw)
c3 = sp.expand(-A.det())

c1_eta0 = sp.simplify(c1.coeff(eta, 0))
c2_eta0 = sp.simplify(c2.coeff(eta, 0))
c3_eta0 = sp.simplify(c3.coeff(eta, 0))
c3_eta1 = sp.simplify(c3.coeff(eta, 1))
c3_eta2 = sp.simplify(c3.coeff(eta, 2))


def check(label, expr, expected):
    diff = sp.simplify(sp.together(expr - expected))
    ok = diff == 0
    status = "PASS" if ok else "FAIL"
    print(f"  [{status}] {label}")
    if not ok:
        print(f"    diff = {diff}")
    return ok


print("Verifying closed-form leading-order expansion of c_3:")
print()

# Sanity check: no eta^0 term.
all_ok = True
all_ok &= check("c_3 has no constant term in eta", c3_eta0, sp.Integer(0))

# Step 1: eta^1 coefficient equals the Step 1 closed form.
expected_step1 = 2 * eps * B1 * (1 - beta2) * ((1 - beta1) + dth)
all_ok &= check(
    "eta^1 coefficient equals Step 1 closed form "
    "(2 eps B1 (1 - bar_beta_2) [(1 - bar_beta_1) + delta_theta])",
    c3_eta1,
    expected_step1,
)

# Step 2: applying the epsilon-cancellation identity collapses the Step 1
# form directly to the clean form (the explicit eps in front cancels against
# the 1/eps that emerges from (1 - bar_beta_1) + delta_theta).
expected_clean = 2 * B1 * (1 - beta1) * (1 - beta2)
all_ok &= check(
    "Step 1 form collapses to clean form via epsilon-cancellation "
    "(2 B1 (1 - bar_beta_1)(1 - bar_beta_2))",
    expected_step1,
    expected_clean,
)

# Bonus: the epsilon-cancellation identity directly.
all_ok &= check(
    "epsilon-cancellation identity: (1 - bar_beta_1) + delta_theta "
    "== (1 - bar_beta_1) / epsilon",
    (1 - beta1) + dth,
    (1 - beta1) / eps,
)

# The cubic-coefficient scaling lemma (in the Vieta appendix) claims that at
# leading order in eta:
#   c_1 = (1 - bar_beta_1) + (1 - bar_beta_2) + O(eta)
#   c_2 = (1 - bar_beta_1)(1 - bar_beta_2) + O(eta)
all_ok &= check(
    "c_1 leading eta^0 term equals (1 - bar_beta_1) + (1 - bar_beta_2) "
    "(cubic-coefficient scaling lemma)",
    c1_eta0,
    (1 - beta1) + (1 - beta2),
)
all_ok &= check(
    "c_2 leading eta^0 term equals (1 - bar_beta_1)(1 - bar_beta_2) "
    "(cubic-coefficient scaling lemma)",
    c2_eta0,
    (1 - beta1) * (1 - beta2),
)

# Sign check on the eta^2 coefficient of c_3: the appendix asserts this term
# is negative ("c_3 = ... - eta^2 B_2 (1 - bar_beta_2)(...) + O(eta^3)" with
# the (...) being a strictly positive O(1) combination).  We check the sign
# at a representative interior point, since the symbolic expression is
# rational in (P, p, B, beta, d).
sample = {P: sp.Rational(1, 2), p: sp.Rational(1, 10),
          B: 4, beta: sp.Rational(9, 10), d: 100}
sign_at_sample = sp.sign(c3_eta2.subs(sample))
all_ok &= check(
    "eta^2 coefficient of c_3 is negative at a representative interior point "
    "(P=1/2, p=1/10, B=4, beta=9/10, d=100)",
    sign_at_sample,
    sp.Integer(-1),
)

# Verify the eta^2 coefficient matches the closed form given in the stability
# appendix footnote.  We construct that closed form as a sympy expression and
# check symbolically that it equals c3_eta2.  If the constructed form below
# is wrong (typo, sign error, etc.) the check FAILs and the script exits with
# non-zero.  The constructed form uses a free symbol Q so it pretty-prints in
# the same shape as the appendix; we substitute Q -> 1-P before comparing.
Q_appendix = sp.Symbol("Q", positive=True)
appendix_footnote_form = (
    -p * (1 - beta)**2 * (B * p * (1 - beta) + (1 + beta) * (d + 2 - p))
    / (B * P * (1 - Q_appendix * beta) * (1 - Q_appendix * beta**2))
)
all_ok &= check(
    "eta^2 coefficient of c_3 equals the appendix-footnote closed form "
    "-p (1-beta)^2 [B p (1-beta) + (1+beta) (d+2-p)] / "
    "[B P (1-Q beta) (1-Q beta^2)]",
    c3_eta2,
    appendix_footnote_form.subs(Q_appendix, 1 - P),
)

# Show the closed form as it appears in the appendix footnote.  The check
# above verifies (with Q := 1-P) that this expression equals c3_eta2
# symbolically, so what we pretty-print here is the same quantity sympy
# computed from -det(A) -- just regrouped to match the appendix's
# (1-beta) / (1+beta) factorization for readability.
print()
print("Closed-form eta^2 coefficient of c_3 (as in the appendix footnote):")
print()
sp.pprint(appendix_footnote_form)
print()

if all_ok:
    print("All checks PASSED.")
    raise SystemExit(0)
else:
    print("One or more checks FAILED.")
    raise SystemExit(1)
