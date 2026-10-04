import SparseSGD.Logistic.IncrementMoments

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

private theorem global_gaussian_shift_bound {d : ℕ} (theta u : Vec d) (b Q L : ℝ)
    (hθ : ‖theta‖ ≤ Q) (hu : ‖u‖ ≤ L) :
    Real.exp (2*b+‖(2 : ℝ) • theta+u‖^2/2) ≤
      Real.exp (2*b+2*‖theta‖^2)*Real.exp (2*Q*L+L^2/2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hQ : 0 ≤ Q := (norm_nonneg _).trans hθ
  have hL : 0 ≤ L := (norm_nonneg _).trans hu
  have hi : inner ℝ theta u ≤ Q*L :=
    (real_inner_le_norm _ _).trans (mul_le_mul hθ hu (norm_nonneg _) hQ)
  have hu2 : ‖u‖^2 ≤ L^2 := by nlinarith [norm_nonneg u]
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_pow, real_inner_smul_left]
  nlinarith

/-- A Gaussian-scale rare envelope valid at every real tilt, unlike the
local factorial moment bound used for linear Bernstein estimates. -/
theorem tame_global_residualExpAbs_bound {d : ℕ} (p : unitInterval)
    (mu theta u : Vec d) (Q L : ℝ)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (hθ : ‖theta‖ ≤ Q) (hu : ‖u‖ ≤ L) (hmu : |inner ℝ u mu| ≤ L) :
    (∫ a, residualExpAbs p mu theta u a ∂sampleLaw d p) ≤
      4*Real.exp (2*Q^2+2)*(p : ℝ)*Real.exp (L^2) := by
  have hQ : 0 ≤ Q := (norm_nonneg _).trans hθ
  have hL : 0 ≤ L := (norm_nonneg _).trans hu
  have h0 := global_gaussian_shift_bound theta u (bias p mu) Q L hθ hu
  have h1 := global_gaussian_shift_bound theta (-u) (bias p mu) Q L hθ (by simpa using hu)
  simp only [← sub_eq_add_neg] at h1
  have ht := (tame_exponential_controls p mu theta hp htame).1
  have hbase : (1-(p : ℝ))*Real.exp (2*bias p mu+2*‖theta‖^2) ≤ (p : ℝ) := by nlinarith
  have hzero : (1-(p : ℝ))*(Real.exp (2*bias p mu+‖(2 : ℝ) • theta+u‖^2/2)+
      Real.exp (2*bias p mu+‖(2 : ℝ) • theta-u‖^2/2)) ≤
      2*(p : ℝ)*Real.exp (2*Q*L+L^2/2) := by
    have hs := mul_le_mul_of_nonneg_left (add_le_add h0 h1) (sub_nonneg.mpr p.property.2)
    have hh := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (2*Q*L+L^2/2)).le
    nlinarith
  have htilt : Real.exp (2*Q*L+L^2/2) ≤ Real.exp (2*Q^2+2)*Real.exp (L^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (L-2*Q)]
  have hone : Real.exp (|inner ℝ u mu|+‖u‖^2/2) ≤ Real.exp (2*Q^2+2)*Real.exp (L^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hu2 : ‖u‖^2 ≤ L^2 := by nlinarith [norm_nonneg u]
    nlinarith [sq_nonneg (L-1), sq_nonneg Q]
  have hh := residualExpAbs_bound p mu theta u
  have hz := mul_le_mul_of_nonneg_left htilt (show 0 ≤ 2*(p : ℝ) by positivity)
  have ho := mul_le_mul_of_nonneg_left hone (show 0 ≤ 2*(p : ℝ) by positivity)
  nlinarith

/-- Every fixed polynomial degree has a rare Gaussian-scale global
exponential envelope for an actual normalized gradient projection. -/
theorem tame_global_projection_weighted_moment {d : ℕ} (p : unitInterval)
    (mu theta u : Vec d) (Q s : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (hθ : ‖theta‖ ≤ Q) (hu : ‖u‖ ≤ 1) (hmu : |inner ℝ u mu| ≤ 1) :
    Integrable (fun a => |inner ℝ u (gradient p mu theta a)|^n*
      Real.exp (|s| * |inner ℝ u (gradient p mu theta a)|)) (sampleLaw d p) ∧
    (∫ a, |inner ℝ u (gradient p mu theta a)|^n*
      Real.exp (|s| * |inner ℝ u (gradient p mu theta a)|) ∂sampleLaw d p) ≤
      (n.factorial : ℝ)*(4*Real.exp (2*Q^2+4))*(p : ℝ)*Real.exp (2*s^2) := by
  let v : Vec d := (|s|+1) • u
  have hL : 0 ≤ |s|+1 := by positivity
  have hv : ‖v‖ ≤ |s|+1 := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL]
    exact mul_le_of_le_one_right hL hu
  have hvm : |inner ℝ v mu| ≤ |s|+1 := by
    simp only [v, real_inner_smul_left, abs_mul, abs_of_nonneg hL]
    exact mul_le_of_le_one_right hL hmu
  have hpoint (a : Sample d) : |inner ℝ u (gradient p mu theta a)|^n*
      Real.exp (|s| * |inner ℝ u (gradient p mu theta a)|) ≤
      (n.factorial : ℝ)*residualExpAbs p mu theta v a := by
    let c := sigma (inner ℝ theta (feature mu a)+bias p mu)-labelReal a.1
    let x := inner ℝ u (feature mu a)
    have hc : |c| ≤ 1 := logistic_residual_abs_le_one _ _
    have hcp : |c|^n ≤ c^2 := by
      simpa only [sq_abs] using pow_le_pow_of_le_one (abs_nonneg c) hc hn
    have hx : |x|^n ≤ (n.factorial : ℝ)*Real.exp |x| := by
      have hh := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) n
      have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
      exact (div_le_iff₀ hf).mp hh |>.trans_eq (mul_comm _ _)
    have hcx : |c*x| ≤ |x| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg x) hc
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcx (abs_nonneg s))
    change |inner ℝ u (c • feature mu a)|^n*Real.exp (|s| * |inner ℝ u (c • feature mu a)|) ≤ _
    rw [real_inner_smul_right, abs_mul, mul_pow]
    have hh := mul_le_mul hcp hx (pow_nonneg (abs_nonneg x) n) (sq_nonneg c)
    have hh' := mul_le_mul hh he (Real.exp_pos _).le (by positivity : 0 ≤ c^2*((n.factorial : ℝ)*Real.exp |x|))
    have heq : (c^2*((n.factorial : ℝ)*Real.exp |x|))*Real.exp (|s| * |x|) =
        (n.factorial : ℝ)*residualExpAbs p mu theta v a := by
      dsimp [residualExpAbs, v]
      rw [real_inner_smul_left, abs_mul, abs_of_nonneg hL]
      have hex : Real.exp ((|s|+1)*|x|) = Real.exp |x| * Real.exp (|s| * |x|) := by
        rw [show (|s|+1)*|x| = |x|+|s| * |x| by ring, Real.exp_add]
      change _ = (n.factorial : ℝ)*(c^2*Real.exp ((|s|+1)*|x|))
      rw [hex]
      ring
    simpa only [c, x, abs_mul] using hh'.trans_eq heq
  have hrawI := (residualExpAbs_integrable p mu theta v).const_mul (n.factorial : ℝ)
  have hmeas : Measurable (fun a : Sample d => inner ℝ u (gradient p mu theta a)) :=
    measurable_const.inner ((measurable_gradient d p mu).comp
      (f := fun a : Sample d => (theta,a)) (measurable_const.prodMk measurable_id))
  have hi : Integrable (fun a => |inner ℝ u (gradient p mu theta a)|^n*
      Real.exp (|s| * |inner ℝ u (gradient p mu theta a)|)) (sampleLaw d p) := by
    apply hrawI.mono' ((hmeas.abs.pow_const n).mul
      (Real.measurable_exp.comp (measurable_const.mul hmeas.abs))).aestronglyMeasurable
    filter_upwards with a
    change ‖|inner ℝ u (gradient p mu theta a)|^n*
      Real.exp (|s| * |inner ℝ u (gradient p mu theta a)|)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpoint a
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi hrawI hpoint
  rw [integral_const_mul] at hh
  have he := tame_global_residualExpAbs_bound p mu theta v Q (|s|+1) hp htame hθ hv hvm
  have hex : Real.exp ((|s|+1)^2) ≤ Real.exp 2*Real.exp (2*s^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (|s|-1), sq_abs s]
  have hscaled := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ n.factorial by positivity)
  have hlast := mul_le_mul_of_nonneg_left hex
    (show 0 ≤ (n.factorial : ℝ)*(4*Real.exp (2*Q^2+2))*(p : ℝ) by positivity)
  have heq : (n.factorial : ℝ)*(4*Real.exp (2*Q^2+2))*(p : ℝ)*(Real.exp 2*Real.exp (2*s^2)) =
      (n.factorial : ℝ)*(4*Real.exp (2*Q^2+4))*(p : ℝ)*Real.exp (2*s^2) := by
    have hex : Real.exp (2*Q^2+2)*Real.exp 2 = Real.exp (2*Q^2+4) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (n.factorial : ℝ)*4*(Real.exp (2*Q^2+2)*Real.exp 2)*(p : ℝ)*Real.exp (2*s^2) := by ring
      _ = _ := by rw [hex]; ring
  nlinarith [hlast.trans_eq heq]

theorem feature_projection_exp_integrable {d : ℕ} (p : unitInterval) (mu u : Vec d) :
    Integrable (fun a : Sample d => Real.exp (inner ℝ u (feature mu a))) (sampleLaw d p) := by
  have hm : Measurable (fun a : Sample d => Real.exp (inner ℝ u (feature mu a))) :=
    Real.measurable_exp.comp (measurable_const.inner (measurable_feature d mu))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun y => ?_), integrable_bernoulliMeasure true false p _⟩
  cases y
  · simpa only [feature, labelReal, Bool.false_eq_true, ↓reduceIte, zero_add, add_zero, one_mul]
      using SparseSGD.Probability.gaussian_exp_inner_integrable u 0 1
  · simpa only [feature, labelReal, ↓reduceIte, inner_add_right, one_mul, add_comm]
      using SparseSGD.Probability.gaussian_exp_inner_integrable u (inner ℝ u mu) 1

theorem feature_projection_exp_integral {d : ℕ} (p : unitInterval) (mu u : Vec d) :
    (∫ a : Sample d, Real.exp (inner ℝ u (feature mu a)) ∂sampleLaw d p) =
      (1-(p : ℝ))*Real.exp (‖u‖^2/2)+(p : ℝ)*Real.exp (inner ℝ u mu+‖u‖^2/2) := by
  rw [sampleLaw, integral_prod _ (feature_projection_exp_integrable p mu u), integral_bernoulliMeasure]
  simp only [feature, labelReal, ↓reduceIte, Bool.false_eq_true, zero_add, inner_add_right, smul_eq_mul]
  rw [show (∫ z : Fin d → ℝ, Real.exp (inner ℝ u (WithLp.toLp 2 z))
    ∂SparseSGD.Probability.standardGaussianProduct d) = Real.exp (‖u‖^2/2) by
      simpa using SparseSGD.Probability.gaussian_exp_inner_integral u 0 1]
  have he (z : Fin d → ℝ) : Real.exp (inner ℝ u mu+inner ℝ u (WithLp.toLp 2 z)) =
      Real.exp (inner ℝ u (WithLp.toLp 2 z)+inner ℝ u mu) := by congr 1; ring
  simp_rw [he]
  rw [show (∫ z : Fin d → ℝ, Real.exp (inner ℝ u (WithLp.toLp 2 z)+inner ℝ u mu)
    ∂SparseSGD.Probability.standardGaussianProduct d) = Real.exp (inner ℝ u mu+‖u‖^2/2) by
      simpa using SparseSGD.Probability.gaussian_exp_inner_integral u (inner ℝ u mu) 1]
  ring

/-- The unweighted exponential factor needed when symmetrizing a rare
projection also has a global Gaussian-scale bound. -/
theorem normalized_projection_exp_abs_bound {d : ℕ} (p : unitInterval)
    (mu theta u : Vec d) (s : ℝ) (hu : ‖u‖ ≤ 1) (hmu : |inner ℝ u mu| ≤ 1) :
    Integrable (fun a => Real.exp (|s| * |inner ℝ u (gradient p mu theta a)|)) (sampleLaw d p) ∧
    (∫ a, Real.exp (|s| * |inner ℝ u (gradient p mu theta a)|) ∂sampleLaw d p) ≤
      2*Real.exp (1/2)*Real.exp (s^2) := by
  let v : Vec d := |s| • u
  have hpoint (a : Sample d) : Real.exp (|s| * |inner ℝ u (gradient p mu theta a)|) ≤
      Real.exp (inner ℝ v (feature mu a))+Real.exp (inner ℝ (-v) (feature mu a)) := by
    have hc := logistic_residual_abs_le_one (inner ℝ theta (feature mu a)+bias p mu) a.1
    have hh : |inner ℝ u (gradient p mu theta a)| ≤ |inner ℝ u (feature mu a)| := by
      rw [gradient, real_inner_smul_right, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hc
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hh (abs_nonneg s))
    have hv : |inner ℝ v (feature mu a)| = |s| * |inner ℝ u (feature mu a)| := by
      simp only [v, real_inner_smul_left, abs_mul, abs_abs]
    rw [← hv] at he
    exact he.trans (by simpa only [inner_neg_left] using exp_abs_le_sum (inner ℝ v (feature mu a)))
  have hmajor := (feature_projection_exp_integrable p mu v).add (feature_projection_exp_integrable p mu (-v))
  have hmeas : Measurable (fun a : Sample d => inner ℝ u (gradient p mu theta a)) :=
    measurable_const.inner ((measurable_gradient d p mu).comp
      (f := fun a : Sample d => (theta,a)) (measurable_const.prodMk measurable_id))
  have hi : Integrable (fun a => Real.exp (|s| * |inner ℝ u (gradient p mu theta a)|)) (sampleLaw d p) := by
    apply hmajor.mono' (Real.measurable_exp.comp (measurable_const.mul hmeas.abs)).aestronglyMeasurable
    filter_upwards with a
    change ‖Real.exp (|s| * |inner ℝ u (gradient p mu theta a)|)‖ ≤ _
    rw [Real.norm_eq_abs, Real.abs_exp]
    exact hpoint a
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi hmajor hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add (feature_projection_exp_integrable p mu v) (feature_projection_exp_integrable p mu (-v)),
    feature_projection_exp_integral, feature_projection_exp_integral] at hh
  have hv : ‖v‖ ≤ |s| := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_abs]
    exact mul_le_of_le_one_right (abs_nonneg s) hu
  have hvm : |inner ℝ v mu| ≤ |s| := by
    simp only [v, real_inner_smul_left, abs_mul, abs_abs]
    exact mul_le_of_le_one_right (abs_nonneg s) hmu
  have h0 : Real.exp (‖v‖^2/2) ≤ Real.exp (1/2)*Real.exp (s^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [norm_nonneg v, sq_abs s, sq_nonneg s]
  have h1 : Real.exp (inner ℝ v mu+‖v‖^2/2) ≤ Real.exp (1/2)*Real.exp (s^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [le_abs_self (inner ℝ v mu), norm_nonneg v, sq_abs s, sq_nonneg (|s|-1)]
  have h2 : Real.exp (inner ℝ (-v) mu+‖-v‖^2/2) ≤ Real.exp (1/2)*Real.exp (s^2) := by
    rw [← Real.exp_add, inner_neg_left, norm_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [neg_le_abs (inner ℝ v mu), norm_nonneg v, sq_abs s, sq_nonneg (|s|-1)]
  simp only [norm_neg] at hh
  have hz := mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr p.property.2)
  have ho := mul_le_mul_of_nonneg_left h1 p.property.1
  have ho' := mul_le_mul_of_nonneg_left h2 p.property.1
  simp only [norm_neg] at ho'
  nlinarith

end
end SparseSGD.Logistic
