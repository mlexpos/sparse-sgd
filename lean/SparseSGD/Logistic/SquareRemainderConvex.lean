import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open Set

namespace SparseSGD.Logistic

def squareExpRemainder (A x : ℝ) : ℝ := Real.exp (A*x^2)-1-A*x^2

theorem squareExpRemainder_hasDerivAt (A x : ℝ) :
    HasDerivAt (squareExpRemainder A) (2*A*x*(Real.exp (A*x^2)-1)) x := by
  unfold squareExpRemainder
  have hq : HasDerivAt (fun y : ℝ => A*y^2) (2*A*x) x := by
    convert (hasDerivAt_pow 2 x).const_mul A using 1 <;> ring
  have h := ((Real.hasDerivAt_exp (A*x^2)).comp x hq).sub_const 1 |>.sub hq
  convert h using 1
  · funext y
    dsimp [Function.comp_def]
  · ring

theorem squareExpRemainder_deriv (A x : ℝ) :
    deriv (squareExpRemainder A) x = 2*A*x*(Real.exp (A*x^2)-1) :=
  (squareExpRemainder_hasDerivAt A x).deriv

theorem squareExpRemainder_deriv_hasDerivAt (A x : ℝ) :
    HasDerivAt (deriv (squareExpRemainder A))
      (2*A*(Real.exp (A*x^2)-1)+4*A^2*x^2*Real.exp (A*x^2)) x := by
  have heq : deriv (squareExpRemainder A) = fun y : ℝ => 2*A*y*(Real.exp (A*y^2)-1) := funext (squareExpRemainder_deriv A)
  rw [heq]
  have hq : HasDerivAt (fun y : ℝ => A*y^2) (2*A*x) x := by
    convert (hasDerivAt_pow 2 x).const_mul A using 1 <;> ring
  have hsub : HasDerivAt (fun y : ℝ => Real.exp (A*y^2)-1) (2*A*x*Real.exp (A*x^2)) x := by
    have h := ((Real.hasDerivAt_exp (A*x^2)).comp x hq).sub_const 1
    simpa [Function.comp_def, mul_comm] using h
  have hmul := hsub.mul ((hasDerivAt_id x).const_mul (2*A))
  convert hmul using 1
  · funext y
    simp [id]
    ring
  · simp [id]
    ring

theorem squareExpRemainder_deriv2 (A x : ℝ) :
    deriv^[2] (squareExpRemainder A) x =
      2*A*(Real.exp (A*x^2)-1)+4*A^2*x^2*Real.exp (A*x^2) := by
  change deriv (deriv (squareExpRemainder A)) x = _
  exact (squareExpRemainder_deriv_hasDerivAt A x).deriv

theorem squareExpRemainder_continuous (A : ℝ) : Continuous (squareExpRemainder A) := by
  unfold squareExpRemainder
  exact (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))).sub continuous_const |>.sub (continuous_const.mul (continuous_id.pow 2))

theorem squareExpRemainder_nonneg (A x : ℝ) (hA : 0 ≤ A) :
    0 ≤ squareExpRemainder A x := by
  unfold squareExpRemainder
  have harg : 0 ≤ A*x^2 := mul_nonneg hA (sq_nonneg _)
  have h := Real.add_one_le_exp (A*x^2)
  linarith

theorem squareExpRemainder_convex (A : ℝ) (hA : 0 ≤ A) :
    ConvexOn ℝ Set.univ (squareExpRemainder A) := by
  apply convexOn_of_deriv2_nonneg convex_univ
  · exact (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))).sub continuous_const |>.sub (continuous_const.mul (continuous_id.pow 2)) |>.continuousOn
  · intro x hx
    exact (squareExpRemainder_hasDerivAt A x).differentiableAt.differentiableWithinAt
  · intro x hx
    exact (squareExpRemainder_deriv_hasDerivAt A x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [squareExpRemainder_deriv2]
    have hxexp : 1 ≤ Real.exp (A*x^2) := by
      have := Real.add_one_le_exp (A*x^2)
      have hxarg : 0 ≤ A*x^2 := mul_nonneg hA (sq_nonneg _)
      linarith
    positivity

end SparseSGD.Logistic
