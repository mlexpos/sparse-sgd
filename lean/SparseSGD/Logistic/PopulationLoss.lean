import SparseSGD.Logistic.Moments
import Mathlib.Analysis.Calculus.ParametricIntegral

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1200000

/-- The logistic softplus function. -/
def softplus (t : ℝ) : ℝ := Real.log (1 + Real.exp t)

/-- Softplus has the logistic link as its actual derivative. -/
theorem hasDerivAt_softplus (t : ℝ) : HasDerivAt softplus (sigma t) t := by
  have hd := ((Real.hasDerivAt_exp t).const_add 1).log
    (show 1+Real.exp t ≠ 0 by positivity)
  change HasDerivAt (fun t : ℝ => Real.log (1+Real.exp t)) (sigma t) t
  simpa only [sigma] using hd

@[fun_prop] theorem softplus_continuous : Continuous softplus :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_softplus t).continuousAt

theorem softplus_nonneg (t : ℝ) : 0 ≤ softplus t := by
  unfold softplus
  exact Real.log_nonneg (by linarith [Real.exp_pos t])

theorem softplus_lipschitz : LipschitzWith 1 softplus := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (hasDerivAt_softplus t).differentiableAt)
  intro t
  rw [(hasDerivAt_softplus t).deriv,← NNReal.coe_le_coe]
  simp only [coe_nnnorm,NNReal.coe_one,Real.norm_eq_abs,abs_of_pos (sigma_pos t)]
  exact (sigma_lt_one t).le

theorem softplus_abs_bound (t : ℝ) : |softplus t| ≤ Real.log 2+|t| := by
  have h := softplus_lipschitz.dist_le_mul t 0
  simp only [Real.dist_eq,NNReal.coe_one,one_mul,sub_zero] at h
  have h0 : softplus 0 = Real.log 2 := by norm_num [softplus]
  rw [h0] at h
  rw [abs_of_nonneg (softplus_nonneg t)]
  linarith [le_abs_self (softplus t-Real.log 2)]

def sampleLoss {d : ℕ} (p : unitInterval) (mu theta : Vec d) (a : Sample d) : ℝ :=
  let z := inner ℝ theta (feature mu a) + bias p mu
  softplus z - labelReal a.1 * z

theorem measurable_sampleLoss {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    Measurable (sampleLoss p mu theta) := by
  have hz : Measurable (fun a : Sample d => inner ℝ theta (feature mu a)+bias p mu) :=
    (measurable_const.inner (measurable_feature d mu)).add measurable_const
  exact (softplus_continuous.measurable.comp hz).sub
    ((measurable_labelReal.comp measurable_fst).mul hz)

theorem sampleLoss_abs_bound {d : ℕ} (p : unitInterval) (mu theta : Vec d) (a : Sample d) :
    |sampleLoss p mu theta a| ≤ Real.log 2+2*|inner ℝ theta (feature mu a)+bias p mu| := by
  let z := inner ℝ theta (feature mu a)+bias p mu
  have hy : |labelReal a.1| ≤ 1 := by cases a.1 <;> norm_num [labelReal]
  have hl := softplus_abs_bound z
  change |softplus z-labelReal a.1*z| ≤ _
  have hprod : |labelReal a.1*z| ≤ |z| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg z) hy
  linarith [abs_sub (softplus z) (labelReal a.1*z)]

/-- Integrability is with respect to the actual Bernoulli-Gaussian law. -/
theorem sampleLoss_integrable {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    Integrable (sampleLoss p mu theta) (sampleLaw d p) := by
  have hf := (sample_feature_memLp_two d p mu).integrable (by norm_num)
  have hz : Integrable (fun a : Sample d => inner ℝ theta (feature mu a)+bias p mu)
      (sampleLaw d p) := (hf.const_inner theta).add (integrable_const _)
  apply ((integrable_const (Real.log 2)).add (hz.abs.const_mul 2)).mono'
    (measurable_sampleLoss p mu theta).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun a => by
    simpa only [Real.norm_eq_abs,Pi.add_apply] using sampleLoss_abs_bound p mu theta a

/-- The actual per-sample derivative is the covector represented by its gradient. -/
theorem hasFDerivAt_sampleLoss {d : ℕ} (p : unitInterval) (mu theta : Vec d) (a : Sample d) :
    HasFDerivAt (fun theta => sampleLoss p mu theta a)
      (innerSL ℝ (gradient p mu theta a)) theta := by
  let x := feature mu a
  have hi : HasFDerivAt (fun theta : Vec d => inner ℝ theta x+bias p mu)
      (innerSL ℝ x) theta := by
    simpa only [coe_innerSL_apply,real_inner_comm] using ((innerSL ℝ x).hasFDerivAt.add_const (bias p mu))
  have h := ((hasDerivAt_softplus (inner ℝ theta x+bias p mu)).comp_hasFDerivAt theta hi).sub
    (hi.const_mul (labelReal a.1))
  convert h using 1
  · rfl
  · ext v
    simp only [sub_apply,smul_apply,smul_eq_mul,
      innerSL_apply_apply,gradient,real_inner_smul_left]
    dsimp [x]
    ring

theorem sampleLoss_derivative_norm_bound {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (a : Sample d) : ‖innerSL ℝ (gradient p mu theta a)‖ ≤ ‖feature mu a‖ := by
  rw [innerSL_apply_norm,gradient,norm_smul,Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (logistic_residual_abs_le_one _ _)

/-- Source population risk under the model's actual Bernoulli-Gaussian mixture law. -/
def populationLoss {d : ℕ} (p : unitInterval) (mu theta : Vec d) : ℝ :=
  ∫ a : Sample d, sampleLoss p mu theta a ∂sampleLaw d p

/-- Actual population gradient, defined by integrating the sample gradient. -/
def populationGradient {d : ℕ} (p : unitInterval) (mu theta : Vec d) : Vec d :=
  ∫ a : Sample d, gradient p mu theta a ∂sampleLaw d p

/-- Differentiation of the actual population integral is justified by the
integrable Gaussian feature norm, uniformly in the parameter. -/
theorem hasFDerivAt_populationLoss {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    HasFDerivAt (populationLoss p mu) (innerSL ℝ (populationGradient p mu theta)) theta := by
  have hg : Integrable (gradient p mu theta) (sampleLaw d p) :=
    (gradient_memLp_two d p mu theta).integrable (by norm_num)
  have hgm : Measurable (gradient p mu theta) :=
    (measurable_gradient d p mu).comp
      (f := fun a : Sample d => (theta,a)) (measurable_const.prodMk measurable_id)
  have hderivmeas : AEStronglyMeasurable (fun a : Sample d => innerSL ℝ (gradient p mu theta a))
      (sampleLaw d p) :=
    ((innerSL ℝ : Vec d →L[ℝ] (Vec d →L[ℝ] ℝ)).continuous.measurable.comp hgm).aestronglyMeasurable
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (H := Vec d) (E := ℝ)
    (F := fun theta a => sampleLoss p mu theta a)
    (F' := fun theta a => innerSL ℝ (gradient p mu theta a))
    (bound := fun a => ‖feature mu a‖) (s := Set.univ)
    (μ := sampleLaw d p) (x₀ := theta) (Filter.univ_mem)
    (Filter.Eventually.of_forall fun theta => (measurable_sampleLoss p mu theta).aestronglyMeasurable)
    (sampleLoss_integrable p mu theta) hderivmeas
    (Filter.Eventually.of_forall fun a theta _ => sampleLoss_derivative_norm_bound p mu theta a)
    ((sample_feature_memLp_two d p mu).integrable (by norm_num)).norm
    (Filter.Eventually.of_forall fun a theta _ => hasFDerivAt_sampleLoss p mu theta a)
  have hcomm := (innerSL ℝ : Vec d →L[ℝ] (Vec d →L[ℝ] ℝ)).integral_comp_comm hg
  rw [hcomm] at h
  convert h using 1 <;> rfl

/-- In particular the genuine population risk is differentiable everywhere. -/
theorem populationLoss_differentiable {d : ℕ} (p : unitInterval) (mu : Vec d) :
    Differentiable ℝ (populationLoss p mu) :=
  fun theta => (hasFDerivAt_populationLoss p mu theta).differentiableAt

@[fun_prop] theorem populationLoss_continuous {d : ℕ} (p : unitInterval) (mu : Vec d) :
    Continuous (populationLoss p mu) := (populationLoss_differentiable p mu).continuous

/-- Excess source risk, measured relative to the Bayes parameter `mu`. -/
def excessLoss {d : ℕ} (p : unitInterval) (mu theta : Vec d) : ℝ :=
  populationLoss p mu theta - populationLoss p mu mu

end
end SparseSGD.Logistic
