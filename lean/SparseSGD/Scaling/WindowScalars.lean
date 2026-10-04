import SparseSGD.Comparison.FunctionalComparison
import Mathlib.Analysis.Calculus.MeanValue

open Set

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

/-- An all-time perturbation estimate for two genuinely damped scalar modes. -/
theorem damped_exponential_difference (z w : ℂ) (m : ℝ) (hm : 0 < m)
    (hz : z.re ≤ -m) (hw : w.re ≤ -m) (t : ℝ) (ht : 0 ≤ t) :
    ‖Complex.exp (z*(t : ℂ))-Complex.exp (w*(t : ℂ))‖ ≤ ‖z-w‖/m := by
  let f := fun r : ℝ => Complex.exp ((z+(r : ℂ)*(w-z))*(t : ℂ))
  let f' := fun r : ℝ => ((w-z)*(t : ℂ))*f r
  have hd (r : ℝ) : HasDerivAt f (f' r) r := by
    simpa [f,f',id_eq,mul_comm,mul_left_comm,mul_assoc] using
      ((((hasDerivAt_id r).ofReal_comp.mul_const (w-z)).const_add z).mul_const (t : ℂ)).cexp
  have hbound (r : ℝ) (hr : r ∈ Ico 0 1) :
      ‖f' r‖ ≤ ‖w-z‖*t*Real.exp (-m*t) := by
    have hre : (z+(r : ℂ)*(w-z)).re ≤ -m := by
      simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        mul_zero,zero_mul,sub_zero,Complex.sub_re]
      nlinarith [mul_nonneg hr.1 (show 0 ≤ -m-w.re by linarith),
        mul_nonneg (show 0 ≤ 1-r by linarith [hr.2]) (show 0 ≤ -m-z.re by linarith)]
    dsimp only [f',f]
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht,Complex.norm_exp]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hre ht)) (by positivity)
  have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun r _ => (hd r).hasDerivWithinAt) hbound
  have hnorm : ‖Complex.exp (z*(t : ℂ))-Complex.exp (w*(t : ℂ))‖ ≤
      ‖z-w‖*t*Real.exp (-m*t) := by
    simpa [f,show z+(w-z) = w by ring,norm_sub_rev] using H
  have hte : t*Real.exp (-m*t) ≤ 1/m := by
    apply (le_div_iff₀ hm).2
    have H := Real.mul_exp_neg_le_exp_neg_one (m*t)
    rw [show -(m*t) = -m*t by ring] at H
    have H1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    nlinarith
  exact hnorm.trans (by simpa only [mul_assoc,div_eq_mul_inv,one_mul] using
    mul_le_mul_of_nonneg_left hte (norm_nonneg (z-w)))

theorem largeMode_parameter_shift (delta u a : ℝ) (hd : 1 ≤ delta)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ha : a^3+(4*delta-1)*a-4*delta*u = 0) :
    0 ≤ a-u ∧ a-u ≤ 1/(4*delta) := by
  have hs : a^2 ≤ 1 := by nlinarith
  have hprod : 4*delta*(a-u) = a*(1-a^2) := by nlinarith [ha]
  constructor
  · have H := mul_nonneg ha0 (show 0 ≤ 1-a^2 by linarith)
    nlinarith
  · apply (le_div_iff₀ (by linarith : 0 < 4*delta)).2
    have H := mul_le_mul_of_nonneg_left (show 1-a^2 ≤ 1 by nlinarith) ha0
    nlinarith

theorem largeMode_parameter_margin (delta u a margin : ℝ) (hd : 1 ≤ delta)
    (hm : 0 < margin) (hu : u ≤ 1-margin) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : a^3+(4*delta-1)*a-4*delta*u = 0) (hlarge : 1 ≤ 2*margin*delta) :
    a-1 ≤ -margin/2 := by
  have H := (largeMode_parameter_shift delta u a hd ha0 ha1 ha).2
  have H' := (le_div_iff₀ (by linarith : 0 < 4*delta)).1 H
  nlinarith

def windowOscillatoryRate (u omega : ℝ) : ℂ := -(1+u/2)+2*Complex.I*omega

theorem largeMode_oscillatory_rate_error (delta u a omega : ℝ) (hd : 4 ≤ delta)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ha : a^3+(4*delta-1)*a-4*delta*u = 0)
    (ho : 0 < omega) (hosq : omega^2 = delta-1/4) :
    ‖largeModeRootPlus delta a-windowOscillatoryRate u omega‖ ≤ 1/omega := by
  have hshift := largeMode_parameter_shift delta u a (by linarith) ha0 ha1 ha
  have hfreq := largeModeFrequency_deviation delta a omega (by linarith) ha0 ha1 ho hosq
  have how : omega ≤ delta := by nlinarith
  have H := Complex.norm_le_abs_re_add_abs_im (largeModeRootPlus delta a-windowOscillatoryRate u omega)
  have hre0 : (largeModeRootPlus delta a-windowOscillatoryRate u omega).re =
      -(1+a/2)+(1+u/2) := by simp [largeModeRootPlus,windowOscillatoryRate]
  have him0 : (largeModeRootPlus delta a-windowOscillatoryRate u omega).im =
      largeModeFrequency delta a-2*omega := by simp [largeModeRootPlus,windowOscillatoryRate]
  have hre : |-(1+a/2)+(1+u/2)| = (a-u)/2 := by
    rw [show -(1+a/2)+(1+u/2) = -(a-u)/2 by ring,abs_div,abs_neg,abs_of_nonneg hshift.1]
    norm_num
  rw [hre0,him0,hre,abs_of_nonneg hfreq.1] at H
  apply H.trans
  have h1 : 1/(4*delta) ≤ 1/(4*omega) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have h2 : (a-u)/2 ≤ 1/(8*omega) := by
    calc
      _ ≤ (1/(4*omega))/2 := div_le_div_of_nonneg_right (hshift.2.trans h1) (by norm_num)
      _ = _ := by ring
  have h3 : (a-u)/2+(largeModeFrequency delta a-2*omega) ≤
      1/(8*omega)+3/(16*omega) := add_le_add h2 hfreq.2
  exact h3.trans (by apply (le_div_iff₀ ho).2; field_simp [ho.ne']; norm_num)

end
end SparseSGD
