import SparseSGD.Probability.GaussianExponential
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Probability
noncomputable section

theorem gaussian_inner_map {d : ℕ} (theta : EuclideanSpace ℝ (Fin d)) :
    (standardGaussianProduct d).map (fun z => inner ℝ theta (WithLp.toLp 2 z)) =
      gaussianReal 0 (‖theta‖^2).toNNReal := by
  change (standardGaussianProduct d).map ((innerSL ℝ theta) ∘ WithLp.toLp 2) = _
  rw [← Measure.map_map (innerSL ℝ theta).continuous.measurable
    (WithLp.measurable_toLp 2 (Fin d → ℝ))]
  rw [standardGaussianProduct, map_pi_eq_stdGaussian, IsGaussian.map_eq_gaussianReal]
  simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm]

theorem gaussian_inner_add_map {d : ℕ} (theta : EuclideanSpace ℝ (Fin d)) (c : ℝ) :
    (standardGaussianProduct d).map (fun z => inner ℝ theta (WithLp.toLp 2 z)+c) =
      gaussianReal c (‖theta‖^2).toNNReal := by
  change (standardGaussianProduct d).map ((fun x : ℝ => x+c) ∘
    (fun z => inner ℝ theta (WithLp.toLp 2 z))) = _
  rw [← Measure.map_map (by fun_prop : Measurable (fun x : ℝ => x+c)) (by fun_prop),
    gaussian_inner_map, gaussianReal_map_add_const, zero_add]

/-- Scalar Gaussian averaging, including the degenerate variance-zero case. -/
def gaussianAverage (f : ℝ → ℝ) (c q : ℝ) : ℝ :=
  ∫ z : ℝ, f (Real.sqrt q*z+c) ∂gaussianReal 0 1

theorem gaussian_sqrt_add_map (c q : ℝ) (hq : 0 ≤ q) :
    (gaussianReal 0 1).map (fun z => Real.sqrt q*z+c) = gaussianReal c q.toNNReal := by
  change (gaussianReal 0 1).map ((fun x : ℝ => x+c) ∘ (fun z => Real.sqrt q*z)) = _
  rw [← Measure.map_map (by fun_prop : Measurable (fun x : ℝ => x+c))
    (by fun_prop : Measurable (fun z : ℝ => Real.sqrt q*z)),
    gaussianReal_map_const_mul, gaussianReal_map_add_const]
  simp only [mul_zero, zero_add, mul_one]
  apply congrArg (gaussianReal c)
  apply NNReal.eq
  simp only [NNReal.coe_mk, Real.sq_sqrt hq, Real.coe_toNNReal q hq]

theorem gaussianAverage_eq_integral (f : ℝ → ℝ) (hf : Continuous f)
    (c q : ℝ) (hq : 0 ≤ q) :
    gaussianAverage f c q = ∫ z, f z ∂gaussianReal c q.toNNReal := by
  rw [← gaussian_sqrt_add_map c q hq,
    integral_map (by fun_prop) hf.aestronglyMeasurable]
  rfl

theorem gaussian_projected_average {d : ℕ} (theta : EuclideanSpace ℝ (Fin d))
    (c : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z, f (inner ℝ theta (WithLp.toLp 2 z)+c) ∂standardGaussianProduct d) =
      gaussianAverage f c (‖theta‖^2) := by
  rw [gaussianAverage_eq_integral f hf c _ (sq_nonneg _), ← gaussian_inner_add_map theta c,
    integral_map (by fun_prop) hf.aestronglyMeasurable]

end
end SparseSGD.Probability
