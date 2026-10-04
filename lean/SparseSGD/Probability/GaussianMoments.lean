import SparseSGD.Foundations
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.MGFAnalytic

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SparseSGD.Probability

/-- Every nonnegative integer moment of a real Gaussian is integrable. -/
theorem gaussianReal_integrable_pow (mean : ℝ) (variance : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (ProbabilityTheory.gaussianReal mean variance) := by
  exact integrable_pow_of_mem_interior_integrableExpSet
    (X := fun x : ℝ => x) (by simp) n

theorem gaussianReal_standard_second_moment :
    ∫ x : ℝ, x ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) = 1 := by
  calc
    ∫ x : ℝ, x ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) =
        Var[(fun x : ℝ => x); ProbabilityTheory.gaussianReal 0 1] := by
      rw [variance_eq_integral measurable_id'.aemeasurable]
      simp [integral_id_gaussianReal]
    _ = 1 := by simp

/-- The fourth derivative at zero of the standard-normal moment-generating function. -/
private theorem standard_mgf_fourth_derivative :
    iteratedDeriv 4 (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 = 3 := by
  have h0 (t : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (s ^ 2 / 2))
      (t * Real.exp (t ^ 2 / 2)) t := by
    convert (((hasDerivAt_id t).pow 2).div_const 2).exp using 1 <;>
      ((try funext s); simp; try ring)
  have h1 (t : ℝ) : HasDerivAt (fun s : ℝ => s * Real.exp (s ^ 2 / 2))
      ((1 + t ^ 2) * Real.exp (t ^ 2 / 2)) t := by
    convert (hasDerivAt_id t).mul (h0 t) using 1 <;>
      ((try funext s); simp; try ring)
  have h2 (t : ℝ) : HasDerivAt (fun s : ℝ => (1 + s ^ 2) * Real.exp (s ^ 2 / 2))
      ((3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) t := by
    convert ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).pow 2)).mul (h0 t)
      using 1 <;> ((try funext s); simp; try ring)
  have h3 (t : ℝ) : HasDerivAt (fun s : ℝ => (3 * s + s ^ 3) * Real.exp (s ^ 2 / 2))
      ((3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2)) t := by
    convert (((hasDerivAt_id t).const_mul 3).add ((hasDerivAt_id t).pow 3)).mul (h0 t)
      using 1 <;> ((try funext s); simp; try ring)
  have hd0 : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
      fun t => t * Real.exp (t ^ 2 / 2) := funext (fun t => (h0 t).deriv)
  have hd1 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := funext (fun t => (h1 t).deriv)
  have hd2 : deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := funext (fun t => (h2 t).deriv)
  have hd3 : deriv (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) :=
    funext (fun t => (h3 t).deriv)
  norm_num [iteratedDeriv_succ', hd0, hd1, hd2, hd3, iteratedDeriv_zero]

theorem gaussianReal_standard_fourth_moment :
    ∫ x : ℝ, x ^ 4 ∂(ProbabilityTheory.gaussianReal 0 1) = 3 := by
  calc
    ∫ x : ℝ, x ^ 4 ∂(ProbabilityTheory.gaussianReal 0 1) =
        iteratedDeriv 4 (mgf (fun x : ℝ => x) (ProbabilityTheory.gaussianReal 0 1)) 0 := by
      rw [iteratedDeriv_mgf_zero (by simp)]
      rfl
    _ = 3 := by
      rw [mgf_fun_id_gaussianReal]
      simpa using standard_mgf_fourth_derivative

theorem gaussianReal_standard_fourth_integrable :
    Integrable (fun x : ℝ => x ^ 4) (ProbabilityTheory.gaussianReal 0 1) :=
  gaussianReal_integrable_pow 0 1 4

end SparseSGD.Probability
