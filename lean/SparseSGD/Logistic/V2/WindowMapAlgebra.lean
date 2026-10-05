import SparseSGD.Logistic.DynamicField
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # v2: the undamped per-step window map (prop:W2 (i), eq:window-map)

Coordinates `(theta, utilde, R, vtilde, ctilde)` are indexed as in `DynamicState`
(indices `0,1,2,3,4`).  The window map is the one-step map of cells 7-8 in the
regime `lambda = eta eps p`, `eps -> 0`.  Everything here is algebra: the map, its
fixed point, the Jacobian `J0` at the fixed point, `det J0`, `det (J0 -+ 1)`, the
characteristic polynomial, and the scalar inequalities behind the window ceiling `w_c`.
-/
namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic
noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-- eq:window-map: one undamped step of size `h`; `alpha` is evaluated at the old state.
Order `(theta, utilde, R, vtilde, ctilde)`. -/
def windowMap (r h : ℝ) (x : DynamicState) : DynamicState :=
  ![x 0 - (x 1 + h * (dynamicAlpha r x * x 0 - r)),
    x 1 + h * (dynamicAlpha r x * x 0 - r),
    x 2 - 2 * (x 4 + h * dynamicAlpha r x * x 2)
      + (x 3 + 2 * h * dynamicAlpha r x * x 4 + h ^ 2 * dynamicAlpha r x ^ 2 * x 2),
    x 3 + 2 * h * dynamicAlpha r x * x 4 + h ^ 2 * dynamicAlpha r x ^ 2 * x 2,
    x 4 + h * dynamicAlpha r x * x 2
      - (x 3 + 2 * h * dynamicAlpha r x * x 4 + h ^ 2 * dynamicAlpha r x ^ 2 * x 2)]

/-- The candidate fixed point `(theta, 0, R, wR, -wR/2)`. -/
def windowFixedPoint (theta R w : ℝ) : DynamicState :=
  ![theta, 0, R, w * R, -(w * R) / 2]

/-- v2 prop:W2 (i): the point `(theta, 0, R, wR, -wR/2)` is fixed by the window map when
`a = alpha(theta,R)`, `a theta = r`, `w = h a`. -/
theorem windowMap_fixed (r h theta R a w : ℝ)
    (ha : dynamicAlpha r (windowFixedPoint theta R w) = a)
    (hr : a * theta = r) (hw : w = h * a) :
    windowMap r h (windowFixedPoint theta R w) = windowFixedPoint theta R w := by
  have e : windowMap r h (windowFixedPoint theta R w) =
      ![theta - (0 + h * (a * theta - r)), 0 + h * (a * theta - r),
        R - 2 * (-(w * R) / 2 + h * a * R) + (w * R + 2 * h * a * (-(w * R) / 2) + h ^ 2 * a ^ 2 * R),
        w * R + 2 * h * a * (-(w * R) / 2) + h ^ 2 * a ^ 2 * R,
        -(w * R) / 2 + h * a * R - (w * R + 2 * h * a * (-(w * R) / 2) + h ^ 2 * a ^ 2 * R)] := by
    simp only [windowMap, windowFixedPoint, ha] at *
    simp
  rw [e]
  have h0 : a * theta - r = 0 := by rw [hr]; ring
  have hha : h * a = w := hw.symm
  ext i
  fin_cases i <;> simp [windowFixedPoint, h0] <;> subst hha <;> ring

/-- (D2) The Jacobian of the window map at its fixed point (independent of `a`). -/
def windowJacobian (theta R w : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1 - w * (1 + theta ^ 2), -1, -theta * w / 2, 0, 0;
     w * (1 + theta ^ 2), 1, theta * w / 2, 0, 0;
     R * theta * w * (w - 2), 0, R * w ^ 2 / 2 - R * w + w ^ 2 - 2 * w + 1, 1, 2 * w - 2;
     R * theta * w ^ 2, 0, w ^ 2 * (R + 2) / 2, 1, 2 * w;
     R * theta * w * (1 - w), 0, w * (R - R * w + 2 - 2 * w) / 2, -1, 1 - 2 * w]


/-- Scalar `A = 2 + 2 theta^2 + R`. -/
def windowA (theta R : ℝ) : ℝ := 2 + 2 * theta ^ 2 + R
/-- Scalar `B = 3 + theta^2 + R`. -/
def windowB (theta R : ℝ) : ℝ := 3 + theta ^ 2 + R
/-- `Q(w) = A w^2 - 4 B w + 16`. -/
def windowQ (theta R w : ℝ) : ℝ := windowA theta R * w ^ 2 - 4 * windowB theta R * w + 16
/-- Coefficient `b` of the palindromic quartic. -/
def windowCoefB (theta R w : ℝ) : ℝ :=
  -((2 + R) * w ^ 2 - 2 * (5 + R + theta ^ 2) * w + 8) / 2
/-- Coefficient `c` of the palindromic quartic. -/
def windowCoefC (theta R w : ℝ) : ℝ :=
  6 - 2 * (5 + R + theta ^ 2) * w + 2 * (3 + R + 2 * theta ^ 2) * w ^ 2
    - (2 + 2 * theta ^ 2 + R) * w ^ 3 / 2
/-- `p(m) = m^2 + b m + c - 2` (with `m = z + 1/z`). -/
def windowP (theta R w m : ℝ) : ℝ := m ^ 2 + windowCoefB theta R w * m + windowCoefC theta R w - 2
/-- `D(w)`, the discriminant factor. -/
def windowD (theta R w : ℝ) : ℝ :=
  R ^ 2 * (w - 2) ^ 2 + 4 * R * (w - 2) * (w - 3 - theta ^ 2) + 4 * (w - 3 + theta ^ 2) ^ 2

/-- v2 prop:W2 (i): `det J0 = 1`. -/
theorem windowJacobian_det (theta R w : ℝ) : (windowJacobian theta R w).det = 1 := by
  simp [windowJacobian, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Helper for v2 prop:W2 (i): the shifted matrix `J0 - z` written out entrywise. -/
theorem windowJacobian_sub_smul_one (theta R w z : ℝ) :
    windowJacobian theta R w - z • (1 : Matrix (Fin 5) (Fin 5) ℝ) =
    !![1 - w * (1 + theta ^ 2) - z, -1, -theta * w / 2, 0, 0;
     w * (1 + theta ^ 2), 1 - z, theta * w / 2, 0, 0;
     R * theta * w * (w - 2), 0, R * w ^ 2 / 2 - R * w + w ^ 2 - 2 * w + 1 - z, 1, 2 * w - 2;
     R * theta * w ^ 2, 0, w ^ 2 * (R + 2) / 2, 1 - z, 2 * w;
     R * theta * w * (1 - w), 0, w * (R - R * w + 2 - 2 * w) / 2, -1, 1 - 2 * w - z] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [windowJacobian]

/-- Helper for v2 prop:W2 (i): `det (J0 - z) = (1-z)(z^4 + b z^3 + c z^2 + b z + 1)`. -/
theorem windowJacobian_det_sub_smul_one (theta R w z : ℝ) :
    (windowJacobian theta R w - z • (1 : Matrix (Fin 5) (Fin 5) ℝ)).det =
      (1 - z) * (z ^ 4 + windowCoefB theta R w * z ^ 3 + windowCoefC theta R w * z ^ 2
        + windowCoefB theta R w * z + 1) := by
  rw [windowJacobian_sub_smul_one]
  simp [windowCoefB, windowCoefC, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring


/-- v2 prop:W2 (i): `det (J0 - 1) = 0`. -/
theorem windowJacobian_det_sub_one (theta R w : ℝ) :
    (windowJacobian theta R w - 1).det = 0 := by
  have h := windowJacobian_det_sub_smul_one theta R w 1
  simpa using h

/-- v2 prop:W2 (i): `det (J0 + 1) = -(w-2) Q(w)`. -/
theorem windowJacobian_det_add_one (theta R w : ℝ) :
    (windowJacobian theta R w + 1).det = -(w - 2) * windowQ theta R w := by
  have h := windowJacobian_det_sub_smul_one theta R w (-1)
  have e : windowJacobian theta R w - (-1 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ)
      = windowJacobian theta R w + 1 := by simp
  rw [e] at h
  rw [h]
  simp only [windowCoefB, windowCoefC, windowQ, windowA, windowB]
  ring

/-- v2 prop:W2 (i): the characteristic polynomial of `J0` over `C`,
`det (z - J0) = (z-1)(z^4 + b z^3 + c z^2 + b z + 1)`. -/
theorem window_charpoly (theta R w : ℝ) (z : ℂ) :
    (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) - (windowJacobian theta R w).map Complex.ofReal).det =
      (z - 1) * (z ^ 4 + (windowCoefB theta R w : ℂ) * z ^ 3 + (windowCoefC theta R w : ℂ) * z ^ 2
        + (windowCoefB theta R w : ℂ) * z + 1) := by
  have e : z • (1 : Matrix (Fin 5) (Fin 5) ℂ) - (windowJacobian theta R w).map Complex.ofReal =
    !![z - (1 - (w:ℂ) * (1 + (theta:ℂ) ^ 2)), 1, (theta:ℂ) * w / 2, 0, 0;
     -((w:ℂ) * (1 + (theta:ℂ) ^ 2)), z - 1, -((theta:ℂ) * w / 2), 0, 0;
     -((R:ℂ) * theta * w * (w - 2)), 0,
       z - ((R:ℂ) * w ^ 2 / 2 - R * w + w ^ 2 - 2 * w + 1), -1, -(2 * (w:ℂ) - 2);
     -((R:ℂ) * theta * w ^ 2), 0, -((w:ℂ) ^ 2 * (R + 2) / 2), z - 1, -(2 * (w:ℂ));
     -((R:ℂ) * theta * w * (1 - w)), 0, -((w:ℂ) * (R - R * w + 2 - 2 * w) / 2), 1,
       z - (1 - 2 * (w:ℂ))] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [windowJacobian] <;> ring
  rw [e]
  simp [windowCoefB, windowCoefC, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-! ### Scalar identities -/

/-- v2 prop:W2 (i): `p(-2) = (2-w) Q(w)/2`. -/
theorem windowP_neg_two (theta R w : ℝ) :
    windowP theta R w (-2) = (2 - w) * windowQ theta R w / 2 := by
  simp only [windowP, windowCoefB, windowCoefC, windowQ, windowA, windowB]; ring

/-- v2 prop:W2 (i): `p(2) = w^2 (2(4+4 theta^2+R) - A w)/2`. -/
theorem windowP_two (theta R w : ℝ) :
    windowP theta R w 2 = w ^ 2 * (2 * (4 + 4 * theta ^ 2 + R) - windowA theta R * w) / 2 := by
  simp only [windowP, windowCoefB, windowCoefC, windowA]; ring

/-- v2 prop:W2 (i): the discriminant `b^2 - 4(c-2) = w^2 D(w)/4`. -/
theorem window_discriminant (theta R w : ℝ) :
    windowCoefB theta R w ^ 2 - 4 * (windowCoefC theta R w - 2) = w ^ 2 * windowD theta R w / 4 := by
  simp only [windowCoefB, windowCoefC, windowD]; ring

/-- v2 prop:W2 (i): `b + 4 = (w/2)(2(5+R+theta^2) - (2+R) w)`. -/
theorem windowCoefB_add_four (theta R w : ℝ) :
    windowCoefB theta R w + 4 = (w / 2) * (2 * (5 + R + theta ^ 2) - (2 + R) * w) := by
  simp only [windowCoefB]; ring

/-- v2 prop:W2 (i): `Q(0) = 16`. -/
theorem windowQ_zero (theta R : ℝ) : windowQ theta R 0 = 16 := by
  simp [windowQ]

/-- v2 prop:W2 (i): `Q(2) = -4R`. -/
theorem windowQ_two (theta R : ℝ) : windowQ theta R 2 = -4 * R := by
  simp only [windowQ, windowA, windowB]; ring

/-- v2 prop:W2 (i): `B^2 - 4A = (theta^2-1)^2 + R^2 + 2R(1+theta^2)`. -/
theorem windowB_sq_sub (theta R : ℝ) :
    windowB theta R ^ 2 - 4 * windowA theta R =
      (theta ^ 2 - 1) ^ 2 + R ^ 2 + 2 * R * (1 + theta ^ 2) := by
  simp only [windowA, windowB]; ring

/-! ### Inequalities -/

/-- v2 prop:W2 (i): `D(w) > 0` for `0 < w < 2`, `R > 0`. -/
theorem windowD_pos (theta R w : ℝ) (hR : 0 < R) (hw2 : w < 2) : 0 < windowD theta R w := by
  have hs : 0 < 2 - w := by linarith
  have e : windowD theta R w = R ^ 2 * (2 - w) ^ 2 + 4 * R * (2 - w) * (1 + (2 - w) + theta ^ 2)
      + 4 * (theta ^ 2 - 1 - (2 - w)) ^ 2 := by
    simp only [windowD]; ring
  rw [e]
  have h1 : 0 < R ^ 2 * (2 - w) ^ 2 := by positivity
  have h2 : 0 ≤ 4 * R * (2 - w) * (1 + (2 - w) + theta ^ 2) := by
    have : 0 ≤ 1 + (2 - w) + theta ^ 2 := by positivity
    positivity
  have h3 : 0 ≤ 4 * (theta ^ 2 - 1 - (2 - w)) ^ 2 := by positivity
  linarith

/-- v2 prop:W2 (i): `p(2) > 0` for `0 < w < 2`, `R > 0`. -/
theorem windowP_two_pos (theta R w : ℝ) (hR : 0 < R) (hw0 : 0 < w) (hw2 : w < 2) :
    0 < windowP theta R w 2 := by
  rw [windowP_two]
  have hA : 0 < windowA theta R := by simp only [windowA]; positivity
  have : 0 < 2 * (4 + 4 * theta ^ 2 + R) - windowA theta R * w := by
    simp only [windowA]; nlinarith [sq_nonneg theta]
  positivity

/-- v2 prop:W2 (i): `b + 4 > 0` for `0 < w < 2`, `R > 0`. -/
theorem windowCoefB_add_four_pos (theta R w : ℝ) (hR : 0 < R) (hw0 : 0 < w) (hw2 : w < 2) :
    0 < windowCoefB theta R w + 4 := by
  rw [windowCoefB_add_four]
  have : 0 < 2 * (5 + R + theta ^ 2) - (2 + R) * w := by nlinarith [sq_nonneg theta]
  positivity

/-- The ceiling `w_c = 2 (B - sqrt (B^2 - 4A)) / A` (smaller root of `Q`). -/
def windowCritical (theta R : ℝ) : ℝ :=
  2 * (windowB theta R - Real.sqrt (windowB theta R ^ 2 - 4 * windowA theta R)) / windowA theta R

/-- The larger root of `Q`. -/
def windowUpper (theta R : ℝ) : ℝ :=
  2 * (windowB theta R + Real.sqrt (windowB theta R ^ 2 - 4 * windowA theta R)) / windowA theta R

/-- Helper for v2 prop:W2 (i): `A > 0`. -/
theorem windowA_pos (theta R : ℝ) (hR : 0 ≤ R) : 0 < windowA theta R := by
  simp only [windowA]; positivity

/-- Helper for v2 prop:W2 (i): `sqrt (B^2 - 4A) > 0` for `R > 0`. -/
theorem windowSqrt_pos (theta R : ℝ) (hR : 0 < R) :
    0 < Real.sqrt (windowB theta R ^ 2 - 4 * windowA theta R) := by
  apply Real.sqrt_pos.mpr
  rw [windowB_sq_sub]; positivity

/-- `Q(w) = A (w - w_c)(w - w_+)`. -/
theorem windowQ_factor (theta R w : ℝ) (hR : 0 < R) :
    windowQ theta R w = windowA theta R * (w - windowCritical theta R) * (w - windowUpper theta R) := by
  have hA := (windowA_pos theta R hR.le).ne'
  have hs := Real.sq_sqrt (show 0 ≤ windowB theta R ^ 2 - 4 * windowA theta R by
    rw [windowB_sq_sub]; positivity)
  simp only [windowCritical, windowUpper]
  generalize Real.sqrt (windowB theta R ^ 2 - 4 * windowA theta R) = s at hs ⊢
  rw [← sub_eq_zero]
  field_simp
  simp only [windowQ]
  linear_combination 4 * hs

/-- v2 prop:W2 (i): `Q(w_c) = 0`. -/
theorem windowQ_critical (theta R : ℝ) (hR : 0 < R) : windowQ theta R (windowCritical theta R) = 0 := by
  rw [windowQ_factor theta R _ hR]; ring

/-- v2 prop:W2 (i): `0 < w_c`. -/
theorem windowCritical_pos (theta R : ℝ) (hR : 0 < R) : 0 < windowCritical theta R := by
  have hA := windowA_pos theta R hR.le
  have hs := Real.sq_sqrt (show 0 ≤ windowB theta R ^ 2 - 4 * windowA theta R by
    rw [windowB_sq_sub]; positivity)
  have hs0 := (windowSqrt_pos theta R hR).le
  have hB : 0 < windowB theta R := by simp only [windowB]; positivity
  unfold windowCritical
  apply div_pos _ hA
  have : Real.sqrt (windowB theta R ^ 2 - 4 * windowA theta R) < windowB theta R := by
    nlinarith
  linarith

/-- v2 prop:W2 (i): `w_c < 2`. -/
theorem windowCritical_lt_two (theta R : ℝ) (hR : 0 < R) : windowCritical theta R < 2 := by
  have hA := windowA_pos theta R hR.le
  unfold windowCritical
  rw [div_lt_iff₀ hA]
  have key : windowB theta R - windowA theta R <
      Real.sqrt (windowB theta R ^ 2 - 4 * windowA theta R) := by
    apply Real.lt_sqrt_of_sq_lt
    have : windowB theta R - windowA theta R = 1 - theta ^ 2 := by
      simp only [windowA, windowB]; ring
    rw [windowB_sq_sub, this]; nlinarith [sq_nonneg (theta ^ 2 - 1), mul_pos hR (show 0 < 1 + theta ^ 2 by positivity)]
  linarith

/-- `w_c < w_+`. -/
theorem windowCritical_lt_upper (theta R : ℝ) (hR : 0 < R) :
    windowCritical theta R < windowUpper theta R := by
  have hA := windowA_pos theta R hR.le
  have hs := windowSqrt_pos theta R hR
  unfold windowCritical windowUpper
  apply div_lt_div_of_pos_right _ hA
  linarith

/-- v2 prop:W2 (i): `Q > 0` on `[0, w_c)`. -/
theorem windowQ_pos_of_lt (theta R w : ℝ) (hR : 0 < R) (hw : w < windowCritical theta R) :
    0 < windowQ theta R w := by
  rw [windowQ_factor theta R w hR]
  have hA := windowA_pos theta R hR.le
  have h1 : w - windowCritical theta R < 0 := by linarith
  have h2 : w - windowUpper theta R < 0 := by linarith [windowCritical_lt_upper theta R hR]
  have := mul_pos_of_neg_of_neg h1 h2
  rw [mul_assoc]; positivity

/-- v2 prop:W2 (i): `Q < 0` just above `w_c`, on `(w_c, w_c + eta)`. -/
theorem windowQ_neg_above (theta R : ℝ) (hR : 0 < R) :
    ∃ eta > 0, ∀ w, windowCritical theta R < w → w < windowCritical theta R + eta →
      windowQ theta R w < 0 := by
  refine ⟨windowUpper theta R - windowCritical theta R,
    by linarith [windowCritical_lt_upper theta R hR], ?_⟩
  intro w h1 h2
  rw [windowQ_factor theta R w hR]
  have hA := windowA_pos theta R hR.le
  have h1' : 0 < w - windowCritical theta R := by linarith
  have h2' : w - windowUpper theta R < 0 := by linarith
  have := mul_neg_of_pos_of_neg h1' h2'
  rw [mul_assoc]
  exact mul_neg_of_pos_of_neg hA this


/-- v2 prop:W2 (limits at `R -> 0`): `Q = 2 (w-2) ((1+theta^2) w - 4)` at `R = 0`. -/
theorem windowQ_R_zero (theta w : ℝ) :
    windowQ theta 0 w = 2 * (w - 2) * ((1 + theta ^ 2) * w - 4) := by
  simp only [windowQ, windowA, windowB]; ring

/-- v2 prop:W2 (limits at `R -> 0`): `w_c(theta, 0) = min (2, 4/(1+theta^2))`. -/
theorem windowCritical_R_zero (theta : ℝ) :
    windowCritical theta 0 = min 2 (4 / (1 + theta ^ 2)) := by
  have hp : 0 < 1 + theta ^ 2 := by positivity
  have e : windowB theta 0 ^ 2 - 4 * windowA theta 0 = (theta ^ 2 - 1) ^ 2 := by
    simp only [windowA, windowB]; ring
  have hA : windowA theta 0 = 2 * (1 + theta ^ 2) := by simp only [windowA]; ring
  unfold windowCritical
  rw [e, Real.sqrt_sq_eq_abs, hA]
  have hB : windowB theta 0 = 3 + theta ^ 2 := by simp only [windowB]; ring
  rw [hB]
  rcases le_or_gt 1 (theta ^ 2) with h | h
  · rw [abs_of_nonneg (by linarith)]
    have h4 : 4 / (1 + theta ^ 2) ≤ 2 := by
      rw [div_le_iff₀ hp]; linarith
    rw [min_eq_right h4]
    field_simp; ring
  · rw [abs_of_neg (by linarith)]
    have h4 : 2 ≤ 4 / (1 + theta ^ 2) := by
      rw [le_div_iff₀ hp]; linarith
    rw [min_eq_left h4]
    field_simp; ring

/-- v2 prop:W2 (limits at `R -> 0`): `w_c(theta, R) -> min (2, 4/(1+theta^2))`
as `R -> 0+`. -/
theorem w_c_limit (theta : ℝ) :
    Filter.Tendsto (fun R => windowCritical theta R) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (min 2 (4 / (1 + theta ^ 2)))) := by
  have hc : ContinuousAt (fun R => windowCritical theta R) 0 := by
    unfold windowCritical windowA windowB
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simp; positivity
  have := hc.tendsto
  rw [windowCritical_R_zero] at this
  exact this.mono_left nhdsWithin_le_nhds


/-! ### The derivative at the fixed point -/

/-- The derivative of `dynamicAlpha`: `d alpha = alpha (theta d theta + (1/2) dR)`. -/
theorem hasFDerivAt_dynamicAlpha_window (r : ℝ) (x : DynamicState) :
    HasFDerivAt (dynamicAlpha r)
      (dynamicAlpha r x • (x 0 • (ContinuousLinearMap.proj 0 : DynamicState →L[ℝ] ℝ) +
        (1 / 2 : ℝ) • (ContinuousLinearMap.proj 2 : DynamicState →L[ℝ] ℝ))) x := by
  have h0 : HasFDerivAt (fun y : DynamicState => y 0)
      (ContinuousLinearMap.proj 0 : DynamicState →L[ℝ] ℝ) x := hasFDerivAt_apply 0 x
  have h2 : HasFDerivAt (fun y : DynamicState => y 2)
      (ContinuousLinearMap.proj 2 : DynamicState →L[ℝ] ℝ) x := hasFDerivAt_apply 2 x
  have hsum : HasFDerivAt (fun y : DynamicState => y 0 ^ 2 + y 2 - r ^ 2)
      ((2 * x 0) • (ContinuousLinearMap.proj 0 : DynamicState →L[ℝ] ℝ) +
        (ContinuousLinearMap.proj 2 : DynamicState →L[ℝ] ℝ)) x := by
    have := ((h0.pow 2).add h2).sub_const (r ^ 2)
    convert this using 1
    ext v; simp
  have hin : HasFDerivAt (fun y : DynamicState => (y 0 ^ 2 + y 2 - r ^ 2) / 2)
      ((1 / 2 : ℝ) • ((2 * x 0) • (ContinuousLinearMap.proj 0 : DynamicState →L[ℝ] ℝ) +
        (ContinuousLinearMap.proj 2 : DynamicState →L[ℝ] ℝ))) x := by
    have := hsum.const_smul (1 / 2 : ℝ)
    convert this using 1
    funext y; simp; ring
  have := hin.exp
  exact this.congr_fderiv (by ext v; simp [dynamicAlpha]; ring)


/-- v2 prop:W2 (i), eq:window-map: the derivative of the window map at the fixed point
`(theta, 0, R, wR, -wR/2)` is the matrix `J0 = windowJacobian theta R w`
(here `d alpha / d theta = alpha theta`, `d alpha / d R = alpha / 2`). -/
theorem hasFDerivAt_windowMap (r h theta R a w : ℝ)
    (ha : dynamicAlpha r (windowFixedPoint theta R w) = a)
    (hr : a * theta = r) (hw : w = h * a) :
    HasFDerivAt (windowMap r h)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (windowJacobian theta R w)))
      (windowFixedPoint theta R w) := by
  have hA := hasFDerivAt_dynamicAlpha_window r (windowFixedPoint theta R w)
  rw [ha] at hA
  have hP : ∀ i : Fin 5, HasFDerivAt (fun y : DynamicState => y i)
      (ContinuousLinearMap.proj i : DynamicState →L[ℝ] ℝ) (windowFixedPoint theta R w) :=
    fun i => hasFDerivAt_apply i _
  have hg := (hA.mul (hP 0)).sub_const r
  have hU := (hP 1).add (hg.const_mul h)
  have hVn := ((hP 3).add ((hA.const_mul (2 * h)).mul (hP 4))).add
    (((hA.pow 2).const_mul (h ^ 2)).mul (hP 2))
  have hCm := (hP 4).add ((hA.const_mul h).mul (hP 2))
  rw [ha] at hg hU hVn hCm
  subst hw
  subst hr
  refine hasFDerivAt_pi'.2 fun i => ?_
  fin_cases i
  · exact ((hP 0).sub hU).congr_fderiv (by
      ext v; simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
        windowJacobian, windowFixedPoint]; ring)
  · exact hU.congr_fderiv (by
      ext v; simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
        windowJacobian, windowFixedPoint]; ring)
  · exact (((hP 2).sub (hCm.const_mul 2)).add hVn).congr_fderiv (by
      ext v; simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
        windowJacobian, windowFixedPoint]; ring)
  · exact hVn.congr_fderiv (by
      ext v; simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
        windowJacobian, windowFixedPoint]; ring)
  · exact (hCm.sub hVn).congr_fderiv (by
      ext v; simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
        windowJacobian, windowFixedPoint]; ring)

end
end SparseSGD.Logistic.V2
