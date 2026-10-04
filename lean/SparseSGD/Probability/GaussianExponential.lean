import SparseSGD.Probability.LeastSquares.GaussianVector

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Probability
noncomputable section

theorem gaussian_exp_sum_integrable {d : ℕ} (a : Fin d → ℝ) :
    Integrable (fun z : Fin d → ℝ => Real.exp (∑ i, a i*z i))
      (standardGaussianProduct d) := by
  simp_rw [Real.exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (a i))

theorem gaussian_exp_sum_integral {d : ℕ} (a : Fin d → ℝ) :
    (∫ z : Fin d → ℝ, Real.exp (∑ i, a i*z i) ∂standardGaussianProduct d) =
      Real.exp ((∑ i, (a i)^2)/2) := by
  simp_rw [Real.exp_sum]
  rw [standardGaussianProduct, integral_fintype_prod_eq_prod (fun i x => Real.exp (a i*x))]
  have H (i : Fin d) : (∫ x : ℝ, Real.exp (a i*x) ∂gaussianReal 0 1) =
      Real.exp ((a i)^2/2) := by
    simpa [mgf] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) (a i)
  simp_rw [H]
  rw [← Real.exp_sum, Finset.sum_div]

theorem gaussian_exp_inner_integrable {d : ℕ}
    (theta : EuclideanSpace ℝ (Fin d)) (c k : ℝ) :
    Integrable (fun z : Fin d → ℝ =>
      Real.exp (k*(inner ℝ theta (WithLp.toLp 2 z)+c))) (standardGaussianProduct d) := by
  have H := (gaussian_exp_sum_integrable (fun i => k*theta i)).mul_const (Real.exp (k*c))
  convert H using 1
  funext z
  rw [← Real.exp_add, LeastSquares.euclidean_inner_eq_sum]
  congr 1
  change k*((∑ i, theta i*z i)+c) = (∑ i, (k*theta i)*z i)+k*c
  simp only [mul_add, Finset.mul_sum, mul_assoc]

theorem gaussian_exp_inner_integral {d : ℕ}
    (theta : EuclideanSpace ℝ (Fin d)) (c k : ℝ) :
    (∫ z : Fin d → ℝ, Real.exp (k*(inner ℝ theta (WithLp.toLp 2 z)+c))
      ∂standardGaussianProduct d) = Real.exp (k*c+k^2*‖theta‖^2/2) := by
  have heq (z : Fin d → ℝ) :
      Real.exp (k*(inner ℝ theta (WithLp.toLp 2 z)+c)) =
        Real.exp (∑ i, (k*theta i)*z i)*Real.exp (k*c) := by
    rw [← Real.exp_add, LeastSquares.euclidean_inner_eq_sum]
    congr 1
    change k*((∑ i, theta i*z i)+c) = (∑ i, (k*theta i)*z i)+k*c
    simp only [mul_add, Finset.mul_sum, mul_assoc]
  simp_rw [heq]
  rw [integral_mul_const, gaussian_exp_sum_integral, ← Real.exp_add,
    LeastSquares.euclidean_norm_sq_eq_sum]
  congr 1
  simp only [mul_pow, ← Finset.mul_sum]
  ring

end
end SparseSGD.Probability
