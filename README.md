# SymPy verification

Symbolic verification of the algebraic and asymptotic claims in the
Everett & Paquette 2026 paper on Routh--Hurwitz stability of the
second-moment ODE.

## Setup

```bash
pip install -r requirements.txt
```

Requires Python 3.10+.

## Running

```bash
python step1_closed_form_identities.py
python step2_per_region_scalings.py
```

Each script returns exit code 0 on success, non-zero on failure, and prints
a per-check PASS/FAIL summary.

## Expected output

### `step1_closed_form_identities.py`

```
Verifying closed-form leading-order expansion of c_3:

  [PASS] c_3 has no constant term in eta
  [PASS] eta^1 coefficient equals Step 1 closed form (2 eps B1 (1 - bar_beta_2) [(1 - bar_beta_1) + delta_theta])
  [PASS] Step 1 form collapses to clean form via epsilon-cancellation (2 B1 (1 - bar_beta_1)(1 - bar_beta_2))
  [PASS] epsilon-cancellation identity: (1 - bar_beta_1) + delta_theta == (1 - bar_beta_1) / epsilon
  [PASS] c_1 leading eta^0 term equals (1 - bar_beta_1) + (1 - bar_beta_2) (cubic-coefficient scaling lemma)
  [PASS] c_2 leading eta^0 term equals (1 - bar_beta_1)(1 - bar_beta_2) (cubic-coefficient scaling lemma)
  [PASS] eta^2 coefficient of c_3 is negative at a representative interior point (P=1/2, p=1/10, B=4, beta=9/10, d=100)
  [PASS] eta^2 coefficient of c_3 equals the appendix-footnote closed form -p (1-beta)^2 [B p (1-beta) + (1+beta) (d+2-p)] / [B P (1-Q beta) (1-Q beta^2)]

Closed-form eta^2 coefficient of c_3 (as in the appendix footnote):

          2
-p⋅(1 - β) ⋅(B⋅p⋅(1 - β) + (β + 1)⋅(d - p + 2))
────────────────────────────────────────────────
                         ⎛     2    ⎞
          B⋅P⋅(-Q⋅β + 1)⋅⎝- Q⋅β  + 1⎠

All checks PASSED.
```

### `step2_per_region_scalings.py`

```
==============================================================================================================
Region       c3     c1c2     c1≤c3    c2≤c3    eta_max scaling                          Max?
--------------------------------------------------------------------------------------------------------------
region_A     PASS   PASS     PASS     PASS     d^(-gamma + kappa)                       -
region_B     PASS   PASS     PASS     PASS     d^(sigma - 1)                            -
region_C     PASS   PASS     PASS     PASS     d^(-gamma + kappa)                       -
region_D     PASS   PASS     PASS     PASS     d^(sigma - 1)                            -
region_E     PASS   PASS     PASS     PASS     d^(sigma - 1)                            -
region_F     PASS   PASS     PASS     PASS     d^(-gamma + kappa)                       -
==============================================================================================================
OVERALL VERDICT: ✓ PASS

All six regions resolve to a single closed-form eta_max.
```

## Files

The verification splits into two scripts at complementary levels of
abstraction, sharing a common machinery module:

### `core.py`

Term-algebra machinery (the `Term`/`TermList` classes), the `Regime` class,
the 3x3 matrix-entry construction, characteristic-polynomial computation
(`c_1 = -Tr(A)`, `c_2` = sum of principal 2x2 minors, `c_3 = -det(A)`),
leading-term analysis, and the per-regime constraint-derivation pipeline.

Also exports four named constants
(`DENSE_TYPICAL_SUBS`, `DENSE_RARE_SUBS`, `SPARSE_DECAY_LIMITED_SUBS`,
`SPARSE_SPARSITY_LIMITED_SUBS`) that encode the regime-specific asymptotic
substitutions for the four "primitive groups" in the (kappa, gamma) phase
plane. These are reused by `step2_per_region_scalings.py` to define the six
finer regions of the paper.

Not a verification entry point on its own -- it has no module-level
executable code.

### `step1_closed_form_identities.py` (closed-form algebra)

Builds `A` as a `3x3` matrix of full rational expressions in
`(beta, P_batch, p, B, d)` and computes `c_1`, `c_2`, `c_3` symbolically.
Verifies the exact algebraic identities used as inputs to the stability
and Vieta arguments:

- `c_3` has no `eta^0` term.
- `c_3`'s `eta^1` coefficient equals
  `2 eps B_1 (1 - bar_beta_2) [(1 - bar_beta_1) + delta_theta]`
  (the pre-cancellation form of the leading-order `c_3` expansion).
- That collapses to `2 B_1 (1 - bar_beta_1)(1 - bar_beta_2)` via
  the epsilon-cancellation identity.
- `c_1^(0) = (1 - bar_beta_1) + (1 - bar_beta_2)` and
  `c_2^(0) = (1 - bar_beta_1)(1 - bar_beta_2)`, the inputs to
  the cubic-coefficient scaling lemma in the Vieta appendix.
- `c_3^(2)` is negative at a representative interior point; the script
  also prints its factored closed form, which the appendix gives in a
  footnote and cites this script as the symbolic verification.

Independent of `core.py` -- uses SymPy directly in closed-form algebra.

### `step2_per_region_scalings.py` (per-region scaling consequences)

Imports machinery from `core.py` and defines six `Regime` objects
(`region_A`, `region_B`, `region_C`, `region_D`, `region_E`, `region_F`)
matching the appendix's six-region partition of the (kappa, gamma) phase
plane. For each region it:

- Identifies the leading-order positive and negative terms in each
  Routh--Hurwitz coefficient `c_1`, `c_2`, `c_3`.
- Solves for `alpha_min` in each Routh--Hurwitz inequality (where
  `eta ~ d^(-alpha)`).
- Verifies `alpha_c1 <= alpha_c3` and `alpha_c2 <= alpha_c3`, confirming
  `c_1`, `c_2` are never binding.
- Reports `alpha_star = max(alpha_c3, alpha_c1c2)` resolved to a single
  closed-form `d`-monomial via the region's resonance condition (no
  symbolic `Max` left in the output).

The compact summary at the end of the script's output reproduces
the per-region `eta_max` table in the stability appendix cell-by-cell.

`step2_per_region_scalings.py` monkey-patches two functions in `core`:
`infer_atoms_from_conditions` (to recognize the two resonance-line
condition patterns `gamma < 1 - sigma + kappa` and
`gamma > 1 - sigma + kappa`) and `get_test_values` (to provide concrete
test points for the six region names, needed by `core`'s numerical
sign-resolution fallback). Both are small extensions that leave the
underlying machinery unchanged.

## Pipeline

The two entry-point scripts compose into a single end-to-end verification
chain:

1. `step1_closed_form_identities.py` certifies the **exact algebraic identities**
   used as inputs to the Vieta classification and stability analysis.
2. `step2_per_region_scalings.py` then certifies the **per-region scaling
   conclusions** that flow from those identities under the co-scaling
   ansatz.

Together they mechanize the chain from the full-ODE matrix entries
through the per-region `eta_max` rows of the paper's phase diagram.
