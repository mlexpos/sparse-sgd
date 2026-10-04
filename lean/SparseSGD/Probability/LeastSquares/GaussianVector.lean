import SparseSGD.Probability.LeastSquares.Model
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory
open scoped ENNReal


namespace SparseSGD.Probability.LeastSquares
noncomputable section

local instance : ENNReal.HolderTriple 4 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]⟩

theorem euclidean_norm_sq_eq_sum {d : ℕ} (x : Vec d) :
    ‖x‖ ^ 2 = ∑ i : Fin d, (x i) ^ 2 := by
  simpa [EuclideanSpace, Real.norm_eq_abs, sq_abs] using
    (PiLp.norm_sq_eq_of_L2 (fun _ : Fin d => ℝ) x)

theorem euclidean_inner_eq_sum {d : ℕ} (x y : Vec d) :
    inner ℝ x y = ∑ i : Fin d, x i * y i := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp [inner, mul_comm]

/-- Every Gaussian coordinate has each finite absolute moment. -/
theorem gaussian_coord_memLp {d : ℕ} (i : Fin d) (q : ℝ≥0∞) (hq : q ≠ ∞) :
    MemLp (fun x : Fin d → ℝ => x i) q (standardGaussianProduct d) := by
  exact (memLp_id_gaussianReal' (μ := 0) (v := 1) q hq).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i)

theorem gaussian_inner_memLp {d : ℕ} (e : Vec d) (q : ℝ≥0∞) (hq : q ≠ ∞) :
    MemLp (fun x : Fin d → ℝ => inner ℝ (WithLp.toLp 2 x : Vec d) e) q
      (standardGaussianProduct d) := by
  simp only [euclidean_inner_eq_sum]
  exact memLp_finsetSum Finset.univ (fun i _ => (gaussian_coord_memLp i q hq).mul_const (e i))

theorem gaussian_norm_sq_memLp_two (d : ℕ) :
    MemLp (fun x : Fin d → ℝ => ‖WithLp.toLp 2 x‖ ^ 2) 2
      (standardGaussianProduct d) := by
  simp only [euclidean_norm_sq_eq_sum]
  apply memLp_finsetSum Finset.univ
  intro i hi
  convert
    ((gaussian_coord_memLp i 4 (by norm_num)).mul
      (gaussian_coord_memLp i 4 (by norm_num)) : MemLp _ 2 _) using 1
  funext x
  simp only [Pi.mul_apply, pow_two]

/-- The expected squared norm of the Gaussian feature is the dimension. -/
theorem gaussian_norm_sq_integral (d : ℕ) :
    ∫ x : Fin d → ℝ, ‖WithLp.toLp 2 x‖ ^ 2 ∂standardGaussianProduct d = d := by
  simp only [euclidean_norm_sq_eq_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => (gaussian_coord_memLp i 2 (by norm_num)).integrable_sq)]
  simp only [pow_two, standardGaussianProduct_covariance, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem standardGaussianProduct_euclidean_norm_inner_sq {d : ℕ} (e : Vec d) :
    ∫ x : Fin d → ℝ,
      ‖WithLp.toLp 2 x‖ ^ 2 * (inner ℝ (WithLp.toLp 2 x : Vec d) e) ^ 2
        ∂SparseSGD.Probability.standardGaussianProduct d =
      (d + 2) * ‖e‖ ^ 2 := by
  have h := SparseSGD.Probability.standardGaussianProduct_norm_inner_sq
    (fun j => e j)
  convert h using 1 <;> simp [euclidean_norm_sq_eq_sum, euclidean_inner_eq_sum]

end
end SparseSGD.Probability.LeastSquares
