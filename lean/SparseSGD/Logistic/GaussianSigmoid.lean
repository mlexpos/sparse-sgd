import SparseSGD.Logistic.SigmoidBounds
import SparseSGD.Probability.GaussianExponential

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section

@[fun_prop] theorem sigma_continuous : Continuous sigma :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_sigma x).continuousAt

@[fun_prop] theorem sigmaPrime_continuous : Continuous sigmaPrime :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_sigmaPrime x).continuousAt

@[fun_prop] theorem sigmaSecond_continuous : Continuous sigmaSecond := by
  unfold sigmaSecond
  fun_prop

@[fun_prop] theorem sigmaSqSecond_continuous : Continuous sigmaSqSecond := by
  unfold sigmaSqSecond
  fun_prop

@[fun_prop] theorem oneMinusSigmaSqSecond_continuous : Continuous oneMinusSigmaSqSecond := by
  unfold oneMinusSigmaSqSecond
  fun_prop

private abbrev gaussianLaw (d : ℕ) := SparseSGD.Probability.standardGaussianProduct d

theorem gaussian_integral_abs_bound {d : ℕ} (theta : Vec d) (c k C : ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f)
    (hbound : ∀ z, |f z| ≤ C*Real.exp (k*(inner ℝ theta (WithLp.toLp 2 z)+c))) :
    Integrable f (gaussianLaw d) ∧
      |∫ z, f z ∂gaussianLaw d| ≤ C*Real.exp (k*c+k^2*‖theta‖^2/2) := by
  have hi := (SparseSGD.Probability.gaussian_exp_inner_integrable theta c k).const_mul C
  have hfi : Integrable f (gaussianLaw d) := hi.mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hbound z))
  refine ⟨hfi, ?_⟩
  calc
    _ ≤ ∫ z, |f z| ∂gaussianLaw d := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f
    _ ≤ ∫ z, C*Real.exp (k*(inner ℝ theta (WithLp.toLp 2 z)+c)) ∂gaussianLaw d :=
      integral_mono hfi.abs hi (hbound)
    _ = _ := by rw [integral_const_mul, SparseSGD.Probability.gaussian_exp_inner_integral]

theorem gaussian_sigma_integral_bound {d : ℕ} (theta : Vec d) (c : ℝ) :
    Integrable (fun z => sigma (inner ℝ theta (WithLp.toLp 2 z)+c)) (gaussianLaw d) ∧
    |∫ z, sigma (inner ℝ theta (WithLp.toLp 2 z)+c) ∂gaussianLaw d| ≤
      Real.exp (c+‖theta‖^2/2) := by
  simpa using gaussian_integral_abs_bound theta c 1 1 _
    (by fun_prop)
    (fun z => by rw [abs_of_pos (sigma_pos _)]; simpa using sigma_le_exp _)

theorem gaussian_sigmaPrime_integral_bound {d : ℕ} (theta : Vec d) (c : ℝ) :
    Integrable (fun z => sigmaPrime (inner ℝ theta (WithLp.toLp 2 z)+c)) (gaussianLaw d) ∧
    |∫ z, sigmaPrime (inner ℝ theta (WithLp.toLp 2 z)+c) ∂gaussianLaw d| ≤
      Real.exp (c+‖theta‖^2/2) := by
  simpa using gaussian_integral_abs_bound theta c 1 1 _
    (by fun_prop)
    (fun z => by rw [abs_of_pos (sigmaPrime_pos _)]; simpa using sigmaPrime_le_exp _)

theorem gaussian_sigmaPrime_error_bound {d : ℕ} (theta : Vec d) (c : ℝ) :
    |(∫ z, sigmaPrime (inner ℝ theta (WithLp.toLp 2 z)+c) ∂gaussianLaw d)-
      Real.exp (c+‖theta‖^2/2)| ≤ 2*Real.exp (2*c+2*‖theta‖^2) := by
  have H := gaussian_integral_abs_bound theta c 2 2
    (fun z => sigmaPrime (inner ℝ theta (WithLp.toLp 2 z)+c)-
      Real.exp (inner ℝ theta (WithLp.toLp 2 z)+c))
    (by fun_prop) (fun z => sigmaPrime_exp_error _)
  have he := SparseSGD.Probability.gaussian_exp_inner_integrable theta c 1
  simp only [one_mul] at he
  rw [integral_sub (gaussian_sigmaPrime_integral_bound theta c).1 he] at H
  have heq := SparseSGD.Probability.gaussian_exp_inner_integral theta c 1
  simp only [one_mul, one_pow] at heq
  rw [heq] at H
  have he : (2:ℝ)^2*‖theta‖^2/2 = 2*‖theta‖^2 := by ring
  simpa only [he] using H.2

theorem gaussian_sigma_sq_integral_bound {d : ℕ} (theta : Vec d) (c : ℝ) :
    Integrable (fun z => sigma (inner ℝ theta (WithLp.toLp 2 z)+c)^2) (gaussianLaw d) ∧
    |∫ z, sigma (inner ℝ theta (WithLp.toLp 2 z)+c)^2 ∂gaussianLaw d| ≤
      Real.exp (2*c+2*‖theta‖^2) := by
  have H := gaussian_integral_abs_bound theta c 2 1
    (fun z => sigma (inner ℝ theta (WithLp.toLp 2 z)+c)^2)
    (by fun_prop)
    (fun z => by rw [abs_of_nonneg (sq_nonneg _)]; simpa using sigma_sq_le_exp _)
  have he : (2:ℝ)^2*‖theta‖^2/2 = 2*‖theta‖^2 := by ring
  simpa only [he, one_mul] using H

theorem gaussian_oneMinusSigma_sq_error_bound {d : ℕ} (theta : Vec d) (c : ℝ) :
    |(∫ z, (1-sigma (inner ℝ theta (WithLp.toLp 2 z)+c))^2 ∂gaussianLaw d)-1| ≤
      2*Real.exp (c+‖theta‖^2/2) := by
  have H := gaussian_integral_abs_bound theta c 1 2
    (fun z => (1-sigma (inner ℝ theta (WithLp.toLp 2 z)+c))^2-1)
    (by fun_prop) (fun z => by simpa using oneMinusSigma_sq_error _)
  have hi : Integrable (fun z => (1-sigma (inner ℝ theta (WithLp.toLp 2 z)+c))^2) (gaussianLaw d) := by
    convert H.1.add (integrable_const (1 : ℝ)) using 1
    funext z
    simp
  rw [integral_sub hi (integrable_const (1 : ℝ))] at H
  simpa using H.2

theorem gaussian_sigmaSqSecond_integral_bound {d : ℕ} (theta : Vec d) (c : ℝ) :
    Integrable (fun z => sigmaSqSecond (inner ℝ theta (WithLp.toLp 2 z)+c)) (gaussianLaw d) ∧
    |∫ z, sigmaSqSecond (inner ℝ theta (WithLp.toLp 2 z)+c) ∂gaussianLaw d| ≤
      4*Real.exp (2*c+2*‖theta‖^2) := by
  have H := gaussian_integral_abs_bound theta c 2 4 _
    (by fun_prop)
    (fun z => sigmaSqSecond_abs_le_exp _)
  have he : (2:ℝ)^2*‖theta‖^2/2 = 2*‖theta‖^2 := by ring
  simpa only [he, one_mul] using H

theorem gaussian_oneMinusSigmaSqSecond_integral_bound {d : ℕ} (theta : Vec d) (c : ℝ) :
    Integrable (fun z => oneMinusSigmaSqSecond (inner ℝ theta (WithLp.toLp 2 z)+c)) (gaussianLaw d) ∧
    |∫ z, oneMinusSigmaSqSecond (inner ℝ theta (WithLp.toLp 2 z)+c) ∂gaussianLaw d| ≤
      2*Real.exp (c+‖theta‖^2/2) := by
  simpa using gaussian_integral_abs_bound theta c 1 2 _
    (by fun_prop)
    (fun z => by simpa using oneMinusSigmaSqSecond_abs_le_exp _)

end
end SparseSGD.Logistic
