import SparseSGD.Logistic.Coefficients
import SparseSGD.External.GaussianStein

open MeasureTheory

namespace SparseSGD.Logistic
noncomputable section

private theorem hasDerivAt_sigmaSq (t : ℝ) :
    HasDerivAt (fun x => sigma x ^ 2) (2 * sigma t * sigmaPrime t) t := by
  have h := hasDerivAt_sigma t
  convert (h.pow 2) using 1 <;> ring_nf

private theorem continuous_sigma : Continuous sigma := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hasDerivAt_sigma t).continuousAt

private theorem continuous_sigmaPrime : Continuous sigmaPrime := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hasDerivAt_sigmaPrime t).continuousAt

private theorem continuous_sigmaSecond : Continuous sigmaSecond := by
  unfold sigmaSecond
  have hσ := continuous_sigma
  have hp := continuous_sigmaPrime
  have hσ' := continuous_sigma
  fun_prop

private theorem continuous_sigmaSqSecond : Continuous sigmaSqSecond := by
  unfold sigmaSqSecond
  have hσ := continuous_sigma
  have hp := continuous_sigmaPrime
  have hs := continuous_sigmaSecond
  fun_prop

private theorem continuous_oneMinusSigmaSqSecond : Continuous oneMinusSigmaSqSecond := by
  unfold oneMinusSigmaSqSecond
  have hσ := continuous_sigma
  have hp := continuous_sigmaPrime
  have hs := continuous_sigmaSecond
  fun_prop

private theorem continuous_two_sigma_sigmaPrime :
    Continuous (fun t => 2 * sigma t * sigmaPrime t) := by
  have hσ := continuous_sigma
  have hp := continuous_sigmaPrime
  fun_prop

private theorem continuous_negative_residual_prime :
    Continuous (fun t => -2 * (1 - sigma t) * sigmaPrime t) := by
  have hσ := continuous_sigma
  have hp := continuous_sigmaPrime
  fun_prop

private theorem hasDerivAt_sigmaSq_deriv (t : ℝ) :
    HasDerivAt (fun x => 2 * sigma x * sigmaPrime x) (sigmaSqSecond t) t := by
  have hσ := hasDerivAt_sigma t
  have hp := hasDerivAt_sigmaPrime t
  convert ((hσ.mul hp).const_mul 2) using 1 <;> dsimp [sigmaSqSecond] <;> ring_nf

private theorem hasDerivAt_oneMinusSigmaSq (t : ℝ) :
    HasDerivAt (fun x => (1 - sigma x) ^ 2) (-2 * (1 - sigma t) * sigmaPrime t) t := by
  have h := (hasDerivAt_sigma t).const_sub 1
  convert (h.pow 2) using 1 <;> ring_nf

private theorem hasDerivAt_oneMinusSigmaSq_deriv (t : ℝ) :
    HasDerivAt (fun x => -2 * (1 - sigma x) * sigmaPrime x)
      (oneMinusSigmaSqSecond t) t := by
  have hσ := hasDerivAt_sigma t
  have hp := hasDerivAt_sigmaPrime t
  have h := (hσ.const_sub 1).mul hp
  convert h.const_mul (-2) using 1 <;> dsimp [oneMinusSigmaSqSecond] <;> ring_nf

/-- First-order Gaussian Stein identity specialized to the logistic link.
Integrability is explicit, so callers can discharge it from the bounded
sigmoid and Gaussian coordinate moments. -/
theorem logistic_first_order (H : SparseSGD.External.GaussianSteinCertificate d)
    (θ : Fin d → ℝ) (c : ℝ) (i : Fin d)
    (hProd : Integrable (fun z : Fin d → ℝ => sigma (∑ j, θ j * z j + c) * z i)
      (SparseSGD.Probability.standardGaussianProduct d))
    (hDeriv : Integrable (fun z : Fin d → ℝ => sigmaPrime (∑ j, θ j * z j + c))
      (SparseSGD.Probability.standardGaussianProduct d)) :
    (∫ z, sigma (∑ j, θ j * z j + c) * z i
      ∂SparseSGD.Probability.standardGaussianProduct d) =
      θ i * ∫ z, sigmaPrime (∑ j, θ j * z j + c)
        ∂SparseSGD.Probability.standardGaussianProduct d := by
  exact H.first_order θ c sigma sigmaPrime i hasDerivAt_sigma continuous_sigmaPrime hProd hDeriv

/-- First-order identity for the class-one gradient residual `sigma - 1`. -/
theorem logistic_positive_class_first_order
    (H : SparseSGD.External.GaussianSteinCertificate d)
    (θ : Fin d → ℝ) (c : ℝ) (i : Fin d)
    (hProd : Integrable (fun z : Fin d → ℝ =>
      (sigma (∑ j, θ j * z j + c) - 1) * z i)
      (SparseSGD.Probability.standardGaussianProduct d))
    (hDeriv : Integrable (fun z : Fin d → ℝ => sigmaPrime (∑ j, θ j * z j + c))
      (SparseSGD.Probability.standardGaussianProduct d)) :
    (∫ z, (sigma (∑ j, θ j * z j + c) - 1) * z i
      ∂SparseSGD.Probability.standardGaussianProduct d) =
      θ i * ∫ z, sigmaPrime (∑ j, θ j * z j + c)
        ∂SparseSGD.Probability.standardGaussianProduct d := by
  exact H.first_order θ c (fun t => sigma t - 1) sigmaPrime i
    (fun t => (hasDerivAt_sigma t).sub_const 1) continuous_sigmaPrime hProd hDeriv

/-- Second-order Gaussian Stein identity for the positive-class squared
logistic residual. -/
theorem logistic_positive_residual_second_order
    (H : SparseSGD.External.GaussianSteinCertificate d)
    (θ : Fin d → ℝ) (c : ℝ) (i j : Fin d)
    (hProd : Integrable (fun z : Fin d → ℝ =>
      sigma (∑ k, θ k * z k + c) ^ 2 * z i * z j)
      (SparseSGD.Probability.standardGaussianProduct d))
    (hVal : Integrable (fun z : Fin d → ℝ => sigma (∑ k, θ k * z k + c) ^ 2)
      (SparseSGD.Probability.standardGaussianProduct d))
    (hSecond : Integrable (fun z : Fin d → ℝ =>
      sigmaSqSecond (∑ k, θ k * z k + c))
      (SparseSGD.Probability.standardGaussianProduct d)) :
    (∫ z, sigma (∑ k, θ k * z k + c) ^ 2 * z i * z j
      ∂SparseSGD.Probability.standardGaussianProduct d) =
      (if i = j then ∫ z, sigma (∑ k, θ k * z k + c) ^ 2
        ∂SparseSGD.Probability.standardGaussianProduct d else 0) +
      θ i * θ j * ∫ z, sigmaSqSecond (∑ k, θ k * z k + c)
        ∂SparseSGD.Probability.standardGaussianProduct d := by
  exact H.second_order θ c (fun t => sigma t ^ 2) (fun t => 2 * sigma t * sigmaPrime t)
    sigmaSqSecond i j (fun t => hasDerivAt_sigmaSq t)
    (fun t => hasDerivAt_sigmaSq_deriv t)
    continuous_two_sigma_sigmaPrime
    continuous_sigmaSqSecond
    hProd hVal hSecond

/-- Second-order Gaussian Stein identity for the negative-class squared
logistic residual. -/
theorem logistic_negative_residual_second_order
    (H : SparseSGD.External.GaussianSteinCertificate d)
    (θ : Fin d → ℝ) (c : ℝ) (i j : Fin d)
    (hProd : Integrable (fun z : Fin d → ℝ =>
      (1 - sigma (∑ k, θ k * z k + c)) ^ 2 * z i * z j)
      (SparseSGD.Probability.standardGaussianProduct d))
    (hVal : Integrable (fun z : Fin d → ℝ =>
      (1 - sigma (∑ k, θ k * z k + c)) ^ 2)
      (SparseSGD.Probability.standardGaussianProduct d))
    (hSecond : Integrable (fun z : Fin d → ℝ =>
      oneMinusSigmaSqSecond (∑ k, θ k * z k + c))
      (SparseSGD.Probability.standardGaussianProduct d)) :
    (∫ z, (1 - sigma (∑ k, θ k * z k + c)) ^ 2 * z i * z j
      ∂SparseSGD.Probability.standardGaussianProduct d) =
      (if i = j then ∫ z, (1 - sigma (∑ k, θ k * z k + c)) ^ 2
        ∂SparseSGD.Probability.standardGaussianProduct d else 0) +
      θ i * θ j * ∫ z, oneMinusSigmaSqSecond (∑ k, θ k * z k + c)
        ∂SparseSGD.Probability.standardGaussianProduct d := by
  exact H.second_order θ c (fun t => (1 - sigma t) ^ 2)
    (fun t => -2 * (1 - sigma t) * sigmaPrime t) oneMinusSigmaSqSecond i j
    (fun t => hasDerivAt_oneMinusSigmaSq t)
    (fun t => hasDerivAt_oneMinusSigmaSq_deriv t)
    continuous_negative_residual_prime
    continuous_oneMinusSigmaSqSecond hProd hVal hSecond

end
end SparseSGD.Logistic
