import SparseSGD.Logistic.TameCoefficients
import SparseSGD.Probability.GaussianExponential

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

private abbrev γ (d : ℕ) := SparseSGD.Probability.standardGaussianProduct d
private abbrev Z {d : ℕ} (z : Fin d → ℝ) : Vec d := WithLp.toLp 2 z

theorem exp_abs_le_sum (x : ℝ) : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-x)]
  · rw [abs_of_nonpos hx]; linarith [Real.exp_pos x]

private def classZeroMajorant {d : ℕ} (theta u : Vec d) (b : ℝ) (z : Fin d → ℝ) : ℝ :=
  Real.exp (inner ℝ ((2 : ℝ) • theta + u) (Z z) + 2*b) +
    Real.exp (inner ℝ ((2 : ℝ) • theta - u) (Z z) + 2*b)

private theorem classZeroMajorant_integrable {d : ℕ} (theta u : Vec d) (b : ℝ) :
    Integrable (classZeroMajorant theta u b) (γ d) := by
  unfold classZeroMajorant
  apply Integrable.add
  · simpa only [one_mul] using SparseSGD.Probability.gaussian_exp_inner_integrable ((2 : ℝ) • theta + u) (2*b) 1
  · simpa only [one_mul] using SparseSGD.Probability.gaussian_exp_inner_integrable ((2 : ℝ) • theta - u) (2*b) 1

private theorem classZeroMajorant_integral {d : ℕ} (theta u : Vec d) (b : ℝ) :
    (∫ z, classZeroMajorant theta u b z ∂γ d) =
      Real.exp (2*b + ‖(2 : ℝ) • theta + u‖^2/2) +
        Real.exp (2*b + ‖(2 : ℝ) • theta - u‖^2/2) := by
  unfold classZeroMajorant
  rw [integral_add
    (by simpa only [one_mul] using SparseSGD.Probability.gaussian_exp_inner_integrable ((2 : ℝ) • theta + u) (2*b) 1)
    (by simpa only [one_mul] using SparseSGD.Probability.gaussian_exp_inner_integrable ((2 : ℝ) • theta - u) (2*b) 1)]
  simpa only [one_mul, one_pow] using congrArg₂ (· + ·)
    (SparseSGD.Probability.gaussian_exp_inner_integral ((2 : ℝ) • theta + u) (2*b) 1)
    (SparseSGD.Probability.gaussian_exp_inner_integral ((2 : ℝ) • theta - u) (2*b) 1)

private theorem classZeroMajorant_bound {d : ℕ} (theta u : Vec d) (b : ℝ) (z : Fin d → ℝ) :
    sigma (inner ℝ theta (Z z) + b)^2 * Real.exp |inner ℝ u (Z z)| ≤
      classZeroMajorant theta u b z := by
  have hs := sigma_sq_le_exp (inner ℝ theta (Z z) + b)
  calc
    _ ≤ Real.exp (2*(inner ℝ theta (Z z)+b)) *
      (Real.exp (inner ℝ u (Z z)) + Real.exp (-inner ℝ u (Z z))) :=
      mul_le_mul hs (exp_abs_le_sum _) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by
      simp only [classZeroMajorant, mul_add, ← Real.exp_add,
        inner_add_left, inner_sub_left, real_inner_smul_left]
      congr 1 <;> congr 1 <;> ring

theorem classZero_residual_exp_abs_integrable {d : ℕ} (theta u : Vec d) (b : ℝ) :
    Integrable (fun z : Fin d → ℝ => sigma (inner ℝ theta (Z z)+b)^2 *
      Real.exp |inner ℝ u (Z z)|) (γ d) := by
  apply (classZeroMajorant_integrable theta u b).mono'
  · exact (by fun_prop : Measurable (fun z : Fin d → ℝ =>
      sigma (inner ℝ theta (Z z)+b)^2 * Real.exp |inner ℝ u (Z z)|)).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact classZeroMajorant_bound theta u b z

/-- The class-zero exponential tilt is explicit. Its cost includes the
shift by twice the parameter vector. -/
theorem classZero_residual_exp_abs_bound {d : ℕ} (theta u : Vec d) (b : ℝ) :
    (∫ z : Fin d → ℝ, sigma (inner ℝ theta (Z z)+b)^2 * Real.exp |inner ℝ u (Z z)| ∂γ d) ≤
      Real.exp (2*b + ‖(2 : ℝ) • theta + u‖^2/2) +
        Real.exp (2*b + ‖(2 : ℝ) • theta - u‖^2/2) := by
  rw [← classZeroMajorant_integral]
  exact integral_mono (classZero_residual_exp_abs_integrable theta u b)
    (classZeroMajorant_integrable theta u b) (classZeroMajorant_bound theta u b)

private def classOneMajorant {d : ℕ} (u mu : Vec d) (z : Fin d → ℝ) : ℝ :=
  Real.exp (inner ℝ u (Z z) + |inner ℝ u mu|) +
    Real.exp (inner ℝ (-u) (Z z) + |inner ℝ u mu|)

private theorem classOneMajorant_integrable {d : ℕ} (u mu : Vec d) :
    Integrable (classOneMajorant u mu) (γ d) := by
  unfold classOneMajorant
  apply Integrable.add
  · simpa only [one_mul] using SparseSGD.Probability.gaussian_exp_inner_integrable u |inner ℝ u mu| 1
  · simpa only [one_mul] using SparseSGD.Probability.gaussian_exp_inner_integrable (-u) |inner ℝ u mu| 1

private theorem classOneMajorant_bound {d : ℕ} (theta u mu : Vec d) (b : ℝ) (z : Fin d → ℝ) :
    (sigma (inner ℝ theta (mu + Z z)+b)-1)^2 * Real.exp |inner ℝ u (mu + Z z)| ≤
      classOneMajorant u mu z := by
  have hc := logistic_residual_abs_le_one (inner ℝ theta (mu+Z z)+b) true
  simp only [labelReal, ↓reduceIte] at hc
  have hc2 : (sigma (inner ℝ theta (mu+Z z)+b)-1)^2 ≤ 1 := by
    nlinarith [abs_nonneg (sigma (inner ℝ theta (mu+Z z)+b)-1), sq_abs (sigma (inner ℝ theta (mu+Z z)+b)-1)]
  calc
    _ ≤ Real.exp |inner ℝ u (mu+Z z)| := mul_le_of_le_one_left (Real.exp_pos _).le hc2
    _ ≤ Real.exp (|inner ℝ u mu| + |inner ℝ u (Z z)|) := by
      apply Real.exp_le_exp.mpr
      rw [inner_add_right]
      exact abs_add_le _ _
    _ ≤ Real.exp |inner ℝ u mu| *
        (Real.exp (inner ℝ u (Z z)) + Real.exp (-inner ℝ u (Z z))) := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_left (exp_abs_le_sum _) (Real.exp_pos _).le
    _ = _ := by
      simp only [classOneMajorant, mul_add, ← Real.exp_add, inner_neg_left]
      congr 1 <;> congr 1 <;> ring

theorem classOne_residual_exp_abs_integrable {d : ℕ} (theta u mu : Vec d) (b : ℝ) :
    Integrable (fun z : Fin d → ℝ => (sigma (inner ℝ theta (mu+Z z)+b)-1)^2 *
      Real.exp |inner ℝ u (mu+Z z)|) (γ d) := by
  apply (classOneMajorant_integrable u mu).mono'
  · exact (by fun_prop : Measurable (fun z : Fin d → ℝ =>
      (sigma (inner ℝ theta (mu+Z z)+b)-1)^2 * Real.exp |inner ℝ u (mu+Z z)|)).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact classOneMajorant_bound theta u mu b z

theorem classOne_residual_exp_abs_bound {d : ℕ} (theta u mu : Vec d) (b : ℝ) :
    (∫ z : Fin d → ℝ, (sigma (inner ℝ theta (mu+Z z)+b)-1)^2 *
      Real.exp |inner ℝ u (mu+Z z)| ∂γ d) ≤
      2*Real.exp (|inner ℝ u mu| + ‖u‖^2/2) := by
  have hm : (∫ z, classOneMajorant u mu z ∂γ d) =
      2*Real.exp (|inner ℝ u mu|+‖u‖^2/2) := by
    unfold classOneMajorant
    rw [integral_add
      (by simpa only [one_mul] using SparseSGD.Probability.gaussian_exp_inner_integrable u |inner ℝ u mu| 1)
      (by simpa only [one_mul] using SparseSGD.Probability.gaussian_exp_inner_integrable (-u) |inner ℝ u mu| 1)]
    have h0 := SparseSGD.Probability.gaussian_exp_inner_integral u |inner ℝ u mu| 1
    have h1 := SparseSGD.Probability.gaussian_exp_inner_integral (-u) |inner ℝ u mu| 1
    simp only [one_mul, one_pow, norm_neg] at h0 h1
    rw [h0, h1]; ring
  rw [← hm]
  exact integral_mono (classOne_residual_exp_abs_integrable theta u mu b)
    (classOneMajorant_integrable u mu) (classOneMajorant_bound theta u mu b)

def residualExpAbs {d : ℕ} (p : unitInterval) (mu theta u : Vec d) (a : Sample d) : ℝ :=
  (sigma (inner ℝ theta (feature mu a)+bias p mu)-labelReal a.1)^2 *
    Real.exp |inner ℝ u (feature mu a)|

theorem residualExpAbs_integrable {d : ℕ} (p : unitInterval) (mu theta u : Vec d) :
    Integrable (residualExpAbs p mu theta u) (sampleLaw d p) := by
  have hm : Measurable (residualExpAbs p mu theta u) := by
    have hf := measurable_feature d mu
    have hl : Measurable (fun a : Sample d => labelReal a.1) := by
      unfold labelReal
      exact Measurable.ite (measurable_fst (measurableSet_singleton true)) measurable_const measurable_const
    have hs : Measurable (fun a : Sample d => sigma (inner ℝ theta (feature mu a)+bias p mu)) :=
      measurable_sigma.comp ((measurable_const.inner hf).add measurable_const)
    unfold residualExpAbs
    exact ((hs.sub hl).pow_const 2).mul (((measurable_const.inner hf).abs).exp)
  change Integrable _ ((bernoulliMeasure true false p).prod (γ d))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards with y
    cases y
    · simpa only [residualExpAbs, feature, labelReal, Bool.false_eq_true, ↓reduceIte,
        zero_add, sub_zero] using classZero_residual_exp_abs_integrable theta u (bias p mu)
    · simpa only [residualExpAbs, feature, labelReal, ↓reduceIte] using
        classOne_residual_exp_abs_integrable theta u mu (bias p mu)
  · exact integrable_bernoulliMeasure true false p _

theorem residualExpAbs_bound {d : ℕ} (p : unitInterval) (mu theta u : Vec d) :
    (∫ a, residualExpAbs p mu theta u a ∂sampleLaw d p) ≤
      (1-(p : ℝ)) *
        (Real.exp (2*bias p mu + ‖(2 : ℝ) • theta + u‖^2/2) +
          Real.exp (2*bias p mu + ‖(2 : ℝ) • theta - u‖^2/2)) +
      (p : ℝ) * (2*Real.exp (|inner ℝ u mu|+‖u‖^2/2)) := by
  rw [sampleLaw, integral_prod _ (residualExpAbs_integrable p mu theta u), integral_bernoulliMeasure]
  simp only [residualExpAbs, feature, labelReal, ↓reduceIte, Bool.false_eq_true, zero_add, sub_zero, smul_eq_mul]
  have h0 := mul_le_mul_of_nonneg_left
    (classZero_residual_exp_abs_bound theta u (bias p mu)) (sub_nonneg.mpr p.property.2)
  have h1 := mul_le_mul_of_nonneg_left
    (classOne_residual_exp_abs_bound theta u mu (bias p mu)) p.property.1
  linarith

private theorem increment_gaussian_shift_bound {d : ℕ} (theta u : Vec d) (b Q : ℝ)
    (hθ : ‖theta‖ ≤ Q) (hu : ‖u‖ ≤ 1) :
    Real.exp (2*b + ‖(2 : ℝ) • theta + u‖^2/2) ≤
      Real.exp (2*b+2*‖theta‖^2) * Real.exp (2*Q+1/2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hi : inner ℝ theta u ≤ Q := by
    calc
      _ ≤ ‖theta‖*‖u‖ := real_inner_le_norm _ _
      _ ≤ ‖theta‖ := mul_le_of_le_one_right (norm_nonneg _) hu
      _ ≤ Q := hθ
  have hu2 : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    mul_pow, real_inner_smul_left]
  nlinarith

/-- A rare exponential envelope for all polynomial moments of the actual
logistic gradient projection. `Q` bounds the parameter norm; the projection
is normalized so its class-one deterministic shift is at most one. -/
theorem tame_residualExpAbs_bound {d : ℕ} (p : unitInterval) (mu theta u : Vec d) (Q : ℝ)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (hθ : ‖theta‖ ≤ Q) (hu : ‖u‖ ≤ 1) (hmu : |inner ℝ u mu| ≤ 1) :
    (∫ a, residualExpAbs p mu theta u a ∂sampleLaw d p) ≤
      (2*(Real.exp (2*Q+1/2)+Real.exp (3/2)))*(p : ℝ) := by
  have h0 := increment_gaussian_shift_bound theta u (bias p mu) Q hθ hu
  have h0' := increment_gaussian_shift_bound theta (-u) (bias p mu) Q hθ (by simpa using hu)
  simp only [← sub_eq_add_neg] at h0'
  have ht := (tame_exponential_controls p mu theta hp htame).1
  have hbase : (1-(p : ℝ))*Real.exp (2*bias p mu+2*‖theta‖^2) ≤ (p : ℝ) := by
    nlinarith
  have hzero : (1-(p : ℝ))*
      (Real.exp (2*bias p mu+‖(2 : ℝ) • theta+u‖^2/2) +
        Real.exp (2*bias p mu+‖(2 : ℝ) • theta-u‖^2/2)) ≤
      2*(p : ℝ)*Real.exp (2*Q+1/2) := by
    have hsum := mul_le_mul_of_nonneg_left (add_le_add h0 h0')
      (sub_nonneg.mpr p.property.2)
    have hh := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (2*Q+1/2)).le
    nlinarith
  have hu2 : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hone : (p : ℝ)*(2*Real.exp (|inner ℝ u mu|+‖u‖^2/2)) ≤
      2*(p : ℝ)*Real.exp (3/2) := by
    have he : Real.exp (|inner ℝ u mu|+‖u‖^2/2) ≤ Real.exp (3/2) :=
      Real.exp_le_exp.mpr (by linarith)
    nlinarith
  have hh := residualExpAbs_bound p mu theta u
  linarith

theorem residual_projection_moment_pointwise {d : ℕ} (p : unitInterval) (mu theta u : Vec d)
    (n : ℕ) (hn : 2 ≤ n) (a : Sample d) :
    |inner ℝ u (gradient p mu theta a)|^n ≤
      (n.factorial : ℝ)*residualExpAbs p mu theta u a := by
  let c := sigma (inner ℝ theta (feature mu a)+bias p mu)-labelReal a.1
  let x := inner ℝ u (feature mu a)
  have hc : |c| ≤ 1 := logistic_residual_abs_le_one _ _
  have hc2 : |c|^n ≤ c^2 := by
    simpa only [sq_abs] using pow_le_pow_of_le_one (abs_nonneg c) hc hn
  have hx : |x|^n ≤ (n.factorial : ℝ)*Real.exp |x| := by
    have hh := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) n
    have hnf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    exact (div_le_iff₀ hnf).mp hh |>.trans_eq (mul_comm _ _)
  change |inner ℝ u (c • feature mu a)|^n ≤ (n.factorial : ℝ)*(c^2*Real.exp |x|)
  rw [real_inner_smul_right, abs_mul, mul_pow]
  calc
    _ ≤ c^2*((n.factorial : ℝ)*Real.exp |x|) :=
      mul_le_mul hc2 hx (pow_nonneg (abs_nonneg _) _) (sq_nonneg c)
    _ = _ := by ring

theorem residual_projection_moment_integrable {d : ℕ} (p : unitInterval) (mu theta u : Vec d)
    (n : ℕ) (hn : 2 ≤ n) :
    Integrable (fun a : Sample d => |inner ℝ u (gradient p mu theta a)|^n) (sampleLaw d p) := by
  apply ((residualExpAbs_integrable p mu theta u).const_mul (n.factorial : ℝ)).mono'
  · have hg : Measurable (fun a : Sample d => gradient p mu theta a) :=
      (measurable_gradient d p mu).comp (f := fun a : Sample d => (theta, a))
      (measurable_const.prodMk measurable_id)
    exact ((measurable_const.inner hg).abs.pow_const n).aestronglyMeasurable
  · filter_upwards with a
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact residual_projection_moment_pointwise p mu theta u n hn a

/-- All actual sample projection moments retain the rare-class factor `p`.
No Gaussian moment or increment estimate is assumed. -/
theorem tame_residual_projection_moments {d : ℕ} (p : unitInterval) (mu theta u : Vec d) (Q : ℝ)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (hθ : ‖theta‖ ≤ Q) (hu : ‖u‖ ≤ 1) (hmu : |inner ℝ u mu| ≤ 1)
    (n : ℕ) (hn : 2 ≤ n) :
    (∫ a : Sample d, |inner ℝ u (gradient p mu theta a)|^n ∂sampleLaw d p) ≤
      (n.factorial : ℝ)*(2*(Real.exp (2*Q+1/2)+Real.exp (3/2)))*(p : ℝ) := by
  have hh := integral_mono (residual_projection_moment_integrable p mu theta u n hn)
    ((residualExpAbs_integrable p mu theta u).const_mul (n.factorial : ℝ))
      (residual_projection_moment_pointwise p mu theta u n hn)
  rw [integral_const_mul] at hh
  have ht := mul_le_mul_of_nonneg_left
    (tame_residualExpAbs_bound p mu theta u Q hp htame hθ hu hmu)
      (show (0 : ℝ) ≤ n.factorial by positivity)
  nlinarith

def rareProjectionConstant (Q : ℝ) : ℝ := 2*(Real.exp (2*Q+1/2)+Real.exp (3/2))

theorem rareProjectionConstant_pos (Q : ℝ) : 0 < rareProjectionConstant Q := by
  unfold rareProjectionConstant
  positivity

/-- Unit directions have factorial moments with polynomial signal strength
`(1+‖mu‖)^n`; the constant depends only on the stopped parameter norm bound. -/
theorem tame_unit_gradient_projection_moments {d : ℕ} (p : unitInterval) (mu theta u : Vec d) (Q : ℝ)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (hθ : ‖theta‖ ≤ Q) (hu : ‖u‖ ≤ 1) (n : ℕ) (hn : 2 ≤ n) :
    (∫ a : Sample d, |inner ℝ u (gradient p mu theta a)|^n ∂sampleLaw d p) ≤
      (n.factorial : ℝ)*((p : ℝ)*rareProjectionConstant Q)*(1+r mu)^n := by
  let L := 1+r mu
  have hL : 0 < L := by dsimp [L, r]; positivity
  have hL1 : 1 ≤ L := by dsimp [L, r]; linarith [norm_nonneg mu]
  let w : Vec d := L⁻¹ • u
  have hw : ‖w‖ ≤ 1 := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    have hi : L⁻¹ ≤ 1 := (inv_le_one₀ hL).mpr hL1
    exact (mul_le_mul_of_nonneg_left hu (inv_pos.mpr hL).le).trans (by simpa using hi)
  have hwm : |inner ℝ w mu| ≤ 1 := by
    simp only [w, real_inner_smul_left, abs_mul, abs_of_pos (inv_pos.mpr hL)]
    calc
      _ ≤ L⁻¹*(‖u‖*‖mu‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm u mu) (inv_pos.mpr hL).le
      _ ≤ L⁻¹*r mu := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (norm_nonneg mu) hu) (inv_pos.mpr hL).le
      _ ≤ 1 := by rw [inv_mul_eq_div]; apply (div_le_iff₀ hL).mpr; dsimp [L]; linarith
  have hh := tame_residual_projection_moments p mu theta w Q hp htame hθ hw hwm n hn
  have hpoint (a : Sample d) : |inner ℝ u (gradient p mu theta a)|^n =
      L^n * |inner ℝ w (gradient p mu theta a)|^n := by
    have he : inner ℝ u (gradient p mu theta a) = L*inner ℝ w (gradient p mu theta a) := by
      simp only [w, real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
    rw [he, abs_mul, abs_of_pos hL, mul_pow]
  simp_rw [hpoint]
  rw [integral_const_mul]
  have hscaled := mul_le_mul_of_nonneg_left hh (pow_nonneg hL.le n)
  dsimp [L, rareProjectionConstant] at hscaled ⊢
  nlinarith

end
end SparseSGD.Logistic
