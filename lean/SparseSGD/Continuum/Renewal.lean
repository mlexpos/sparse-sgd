import SparseSGD.Continuum.CovarianceFlow

open scoped Matrix.Norms.Operator

namespace SparseSGD

noncomputable section

/-- Risk transported by the free oscillator from the initial covariance. -/
def continuumFreeRisk (delta : ℝ) (s : Moments) (t : ℝ) : ℝ :=
  (continuumMeanFlow delta t * s.cov * (continuumMeanFlow delta t).transpose) 0 0

/-- The free response of the first coordinate to a kick in the second coordinate. -/
def continuumImpulseResponse (delta t : ℝ) : ℝ := continuumMeanFlow delta t 0 1

/-- Scalar renewal kernel of the continuum second-moment equation. -/
def continuumRenewalKernel (delta t : ℝ) : ℝ :=
  2 / delta * continuumImpulseResponse delta t ^ 2

/-- A positive oscillator parameter gives a nonnegative renewal kernel. -/
theorem continuumRenewalKernel_nonneg {delta : ℝ} (hd : 0 < delta) (t : ℝ) :
    0 ≤ continuumRenewalKernel delta t :=
  mul_nonneg (div_nonneg (by norm_num) hd.le) (sq_nonneg _)

/-- The scalar renewal identity at time zero for the instantiated continuum flow. -/
theorem continuumFlow_renewal_initial (delta u phi : ℝ) (s : Moments) :
    (continuumFlow delta u phi s 0).R = s.R := by
  simp [continuumFlow_initial]

/-- The risk entry of the transported noise covariance is the scalar renewal integrand. -/
theorem continuumCovarianceSource_response (delta u phi : ℝ) (s : Moments) (t : ℝ) :
    (continuumMeanFlow delta t * continuumCovarianceSource delta u phi s *
        (continuumMeanFlow delta t).transpose) 0 0 =
      continuumRenewalKernel delta t * (u * s.R + phi) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  simp [continuumCovarianceSource, continuumKickCovariance, continuumRenewalKernel,
    continuumImpulseResponse]
  ring

/-- The concrete matrix-exponential continuum flow satisfies the scalar renewal equation. -/
theorem continuumFlow_renewal (delta u phi : ℝ) (s : Moments) (t : ℝ) :
    (continuumFlow delta u phi s t).R = continuumFreeRisk delta s t +
      ∫ x in (0 : ℝ)..t, continuumRenewalKernel delta (t - x) *
        (u * (continuumFlow delta u phi s x).R + phi) := by
  let L : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ :=
    ((LinearMap.proj 0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)).comp
      (LinearMap.proj 0 : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
  let A := L.toContinuousLinearMap
  have hint : Continuous (fun x => continuumMeanFlow delta (t - x) *
      continuumCovarianceSource delta u phi (continuumFlow delta u phi s x) *
      (continuumMeanFlow delta (t - x)).transpose) := by
    have hP : Continuous (fun x : ℝ => continuumMeanFlow delta (t - x)) :=
      (continuumMeanFlow_continuous delta).comp (continuous_const.sub continuous_id)
    have hQ : Continuous (fun x => continuumCovarianceSource delta u phi
        (continuumFlow delta u phi s x)) := by
      exact (continuous_const.mul
        ((continuous_const.mul (continuumFlow_R_continuous delta u phi s)).add continuous_const)).smul
          continuous_const
    exact (hP.mul hQ).mul hP.matrix_transpose
  have h := congrArg A (continuumCovarianceFlow_variation_of_constants delta u phi s t)
  rw [map_add] at h
  have hcomm : A (∫ x in (0 : ℝ)..t, continuumMeanFlow delta (t - x) *
      continuumCovarianceSource delta u phi (continuumFlow delta u phi s x) *
      (continuumMeanFlow delta (t - x)).transpose) =
      ∫ x in (0 : ℝ)..t, A (continuumMeanFlow delta (t - x) *
        continuumCovarianceSource delta u phi (continuumFlow delta u phi s x) *
        (continuumMeanFlow delta (t - x)).transpose) := by
    convert (A.intervalIntegral_comp_comm (μ := MeasureTheory.volume)
      (hint.intervalIntegrable 0 t)).symm using 1
  rw [hcomm] at h
  change (continuumFlow delta u phi s t).R = continuumFreeRisk delta s t +
    ∫ x in (0 : ℝ)..t, (continuumMeanFlow delta (t - x) *
      continuumCovarianceSource delta u phi (continuumFlow delta u phi s x) *
      (continuumMeanFlow delta (t - x)).transpose) 0 0 at h
  simp_rw [continuumCovarianceSource_response] at h
  exact h

end
end SparseSGD
