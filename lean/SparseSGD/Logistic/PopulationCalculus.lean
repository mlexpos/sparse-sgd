import SparseSGD.Logistic.PopulationLoss
import SparseSGD.Logistic.Drift

open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1200000

def sampleHessian {d : ℕ} (p : unitInterval) (mu theta : Vec d) (a : Sample d) : Vec d →L[ℝ] Vec d :=
  sigmaPrime (inner ℝ theta (feature mu a)+bias p mu) •
    (innerSL ℝ (feature mu a)).smulRight (feature mu a)

theorem hasFDerivAt_gradient {d : ℕ} (p : unitInterval) (mu theta : Vec d) (a : Sample d) :
    HasFDerivAt (fun theta => gradient p mu theta a) (sampleHessian p mu theta a) theta := by
  let x := feature mu a
  have hi : HasFDerivAt (fun theta : Vec d => inner ℝ theta x+bias p mu)
      (innerSL ℝ x) theta := by
    simpa only [coe_innerSL_apply,real_inner_comm] using
      ((innerSL ℝ x).hasFDerivAt.add_const (bias p mu))
  have h := (((hasDerivAt_sigma (inner ℝ theta x+bias p mu)).comp_hasFDerivAt theta hi).sub_const
      (labelReal a.1)).smul_const x
  convert h using 1
  · rfl
  · ext v
    simp only [sampleHessian,smul_apply,ContinuousLinearMap.smulRight_apply]
    simp [x,smul_smul]

theorem sampleHessian_norm_bound {d : ℕ} (p : unitInterval) (mu theta : Vec d) (a : Sample d) :
    ‖sampleHessian p mu theta a‖ ≤ ‖feature mu a‖^2 := by
  apply (sampleHessian p mu theta a).opNorm_le_bound (sq_nonneg _)
  intro v
  simp only [sampleHessian,smul_apply,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,norm_smul,Real.norm_eq_abs]
  have hsig := sigmaPrime_abs_le_one (inner ℝ theta (feature mu a)+bias p mu)
  have hin : |inner ℝ (feature mu a) v| ≤ ‖feature mu a‖*‖v‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (feature mu a) v
  calc
    |sigmaPrime (inner ℝ theta (feature mu a)+bias p mu)| *
        (|inner ℝ (feature mu a) v| * ‖feature mu a‖) ≤
        |inner ℝ (feature mu a) v| * ‖feature mu a‖ :=
      mul_le_of_le_one_left (by positivity) hsig
    _ ≤ (‖feature mu a‖*‖v‖)*‖feature mu a‖ :=
      mul_le_mul_of_nonneg_right hin (norm_nonneg _)
    _ = _ := by ring

theorem measurable_sampleHessian {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    Measurable (sampleHessian p mu theta) := by
  have hx := measurable_feature d mu
  have hp : Continuous sigmaPrime :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_sigmaPrime x).continuousAt
  have hz : Measurable (fun a : Sample d => inner ℝ theta (feature mu a)+bias p mu) :=
    (measurable_const.inner hx).add measurable_const
  have hr : Measurable (fun a : Sample d => (innerSL ℝ (feature mu a)).smulRight (feature mu a)) := by
    change Measurable (fun a => (ContinuousLinearMap.smulRightL ℝ (Vec d) (Vec d))
      (innerSL ℝ (feature mu a)) (feature mu a))
    have heval : Continuous (fun z : (Vec d →L[ℝ] (Vec d →L[ℝ] Vec d)) × Vec d => z.1 z.2) :=
      continuous_fst.clm_apply continuous_snd
    exact heval.measurable.comp
      (((ContinuousLinearMap.smulRightL ℝ (Vec d) (Vec d)).continuous.measurable.comp
        ((innerSL ℝ).continuous.measurable.comp hx)).prodMk hx)
  exact (hp.measurable.comp hz).smul hr

def populationHessian {d : ℕ} (p : unitInterval) (mu theta : Vec d) : Vec d →L[ℝ] Vec d :=
  ∫ a : Sample d, sampleHessian p mu theta a ∂sampleLaw d p

theorem hasFDerivAt_populationGradient {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    HasFDerivAt (populationGradient p mu) (populationHessian p mu theta) theta := by
  have hg : Integrable (gradient p mu theta) (sampleLaw d p) :=
    (gradient_memLp_two d p mu theta).integrable (by norm_num)
  have hgm : ∀ theta, AEStronglyMeasurable (gradient p mu theta) (sampleLaw d p) := by
    intro theta
    exact ((measurable_gradient d p mu).comp
      (f := fun a : Sample d => (theta,a)) (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hbound : Integrable (fun a : Sample d => ‖feature mu a‖^2) (sampleLaw d p) :=
    (memLp_two_iff_integrable_sq_norm (sample_feature_memLp_two d p mu).aestronglyMeasurable).mp
      (sample_feature_memLp_two d p mu)
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (H := Vec d) (E := Vec d)
    (F := fun theta a => gradient p mu theta a) (F' := fun theta a => sampleHessian p mu theta a)
    (bound := fun a => ‖feature mu a‖^2) (s := Set.univ) (μ := sampleLaw d p) (x₀ := theta)
    Filter.univ_mem (Filter.Eventually.of_forall hgm) hg
    (measurable_sampleHessian p mu theta).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a theta _ => sampleHessian_norm_bound p mu theta a)
    hbound (Filter.Eventually.of_forall fun a theta _ => hasFDerivAt_gradient p mu theta a)
  convert h using 1 <;> rfl

theorem populationHessian_quadratic {d : ℕ} (p : unitInterval) (mu theta v : Vec d) :
    inner ℝ v (populationHessian p mu theta v) =
      ∫ a : Sample d, sigmaPrime (inner ℝ theta (feature mu a)+bias p mu) *
        (inner ℝ v (feature mu a))^2 ∂sampleLaw d p := by
  have hb : Integrable (fun a : Sample d => ‖feature mu a‖^2) (sampleLaw d p) :=
    (memLp_two_iff_integrable_sq_norm (sample_feature_memLp_two d p mu).aestronglyMeasurable).mp
      (sample_feature_memLp_two d p mu)
  have hi : Integrable (sampleHessian p mu theta) (sampleLaw d p) :=
    hb.mono' (measurable_sampleHessian p mu theta).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => sampleHessian_norm_bound p mu theta a)
  rw [populationHessian,ContinuousLinearMap.integral_apply hi v]
  have hiv : Integrable (fun a : Sample d => sampleHessian p mu theta a v) (sampleLaw d p) :=
    (ContinuousLinearMap.apply ℝ (Vec d) v).integrable_comp hi
  rw [← integral_inner (𝕜 := ℝ) hiv v]
  congr 1
  funext a
  simp only [sampleHessian,smul_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,
    real_inner_smul_right,real_inner_comm (feature mu a) v]
  ring

/-- The vector in the population integral is the actual Hilbert-space gradient. -/
theorem hasGradientAt_populationLoss {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    HasGradientAt (populationLoss p mu) (populationGradient p mu theta) theta := by
  apply hasGradientAt_iff_hasFDerivAt.2
  convert hasFDerivAt_populationLoss p mu theta using 1
  ext v
  rfl

/-- The population gradient has the exact Gaussian Stein coefficient form. -/
theorem populationGradient_eq_coefficients {d : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d)
    (p : unitInterval) (mu theta : Vec d) :
    populationGradient p mu theta = coefA p mu theta • theta + coefB p mu theta • mu :=
  gradient_integral H p mu theta

theorem populationHessian_quadratic_nonneg {d : ℕ} (p : unitInterval) (mu theta v : Vec d) :
    0 ≤ inner ℝ v (populationHessian p mu theta v) := by
  rw [populationHessian_quadratic]
  exact integral_nonneg fun a => mul_nonneg (sigmaPrime_pos _).le (sq_nonneg _)

theorem populationGradient_differentiable {d : ℕ} (p : unitInterval) (mu : Vec d) :
    Differentiable ℝ (populationGradient p mu) :=
  fun theta => (hasFDerivAt_populationGradient p mu theta).differentiableAt

@[fun_prop] theorem populationGradient_continuous {d : ℕ} (p : unitInterval) (mu : Vec d) :
    Continuous (populationGradient p mu) := (populationGradient_differentiable p mu).continuous

end
end SparseSGD.Logistic
