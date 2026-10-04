import SparseSGD.Comparison.ConvolutionQuadrature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1200000

theorem Params.matched_frequency_of_one_le (p : Params)
    (hb0 : 0 < p.beta) (hb1 : p.beta < 1) (hd : 1 ≤ p.matchedDelta) :
    ∃ omega : ℝ, 0 < omega ∧ omega^2 = p.matchedDelta-1/4 ∧
      omega*p.matchedStep = p.foldedAngle ∧ |p.traceCosine| ≤ 1 := by
  have hh := p.matchedStep_pos hb0 hb1
  have hc : |p.traceCosine| ≤ 1 := by
    by_contra H
    have he : p.matchedDelta ≤ 1/4 := by
      simp only [Params.matchedDelta, H, ite_false]
      linarith [sq_nonneg (Real.arcosh |p.traceCosine|/p.matchedStep)]
    linarith
  let omega := p.foldedAngle/p.matchedStep
  have hsq : omega^2 = p.matchedDelta-1/4 := by
    simp only [Params.matchedDelta, hc, ite_true]
    dsimp only [omega]
    ring
  have ho0 : 0 ≤ omega := div_nonneg p.foldedAngle_bounds.1 hh.le
  refine ⟨omega, by nlinarith, hsq, ?_, hc⟩
  exact div_mul_cancel₀ _ hh.ne'

/-- Closed form obtained from the already proved exact impulse mass. -/
theorem Params.sampledKernelMass_closed_form (p : Params)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))
    (jury : External.JuryStability) (omega : ℝ) (ho : 0 < omega)
    (hosq : omega^2 = p.matchedDelta-1/4)
    (hangle : omega*p.matchedStep = p.foldedAngle)
    (hc : |p.traceCosine| ≤ 1) :
    p.sampledKernelMass = (p.matchedDelta/omega^2)*(p.matchedStep/(1-p.beta))*
      (2*p.beta*(1+p.beta)*Real.sin p.foldedAngle^2 /
        ((1-p.beta)^2+4*p.beta*Real.sin p.foldedAngle^2)) := by
  have hb : 0 < p.beta := by linarith
  have hh := p.matchedStep_pos hb hb1
  have hd := p.matchedDelta_pos hb hb1 hw0 hw1
  have hs := (p.sampledImpulse_sq_hasSum hb0 hb1 hw0 hw1 jury).mul_left
    (p.matchedStep*(2/p.matchedDelta))
  have heq : p.sampledKernelMass = (p.matchedStep*(2/p.matchedDelta))*
      ((p.beta*p.matchingMatrix 1 1)^2/(2*p.w*p.eps*(1-p.curvature))) := by
    apply (p.sampledKernelMass_hasSum hb0 hb1 hw0 hw1 jury).unique
    convert hs using 1
    funext n
    dsimp [continuumRenewalKernel, Params.sampledImpulse]
    ring
  have hG : p.matchedMeanFlow 0 1 =
      Real.sqrt p.beta * (-p.matchedDelta*(Real.sin p.foldedAngle/omega)) := by
    have H := continuumMeanFlow_oscillatory p.matchedDelta omega p.matchedStep
      ho.ne' hosq hh.le
    change p.matchedMeanFlow = _ at H
    rw [H]
    simp only [oscillatorFormula, Matrix.smul_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]
    rw [p.exp_neg_half_matchedStep hb, mul_comm p.matchedStep omega, hangle]
  have hP : (p.beta*p.matchingMatrix 1 1)^2 =
      p.beta*p.matchedDelta^2*Real.sin p.foldedAngle^2/omega^2 := by
    have he : p.beta*p.matchingMatrix 1 1 = -p.matchingSign*p.matchedMeanFlow 0 1 := by
      change p.beta*((-p.matchingSign*p.matchedMeanFlow 0 1)/p.beta) = _
      exact mul_div_cancel₀ _ hb.ne'
    rw [he, hG]
    ring_nf
    rw [p.matchingSign_sq, Real.sq_sqrt hb.le]
    ring
  have hcos : Real.cos p.foldedAngle = |p.traceCosine| :=
    Real.cos_arccos (by linarith [abs_nonneg p.traceCosine]) hc
  have htrig : (1+p.beta-p.w)^2 =
      4*p.beta*(1-Real.sin p.foldedAngle^2) := by
    have H := Real.sin_sq_add_cos_sq p.foldedAngle
    rw [hcos, sq_abs, Params.traceCosine, div_pow, mul_pow,
      Real.sq_sqrt hb.le] at H
    have H' := (eq_div_iff (by positivity : (2:ℝ)^2*p.beta ≠ 0)).mp
      (show 1-Real.sin p.foldedAngle^2 =
        (1+p.beta-p.w)^2/((2:ℝ)^2*p.beta) by linarith)
    nlinarith
  have hden : 2*(1+p.beta)*p.w*(1-p.curvature) =
      (1-p.beta)^2+4*p.beta*Real.sin p.foldedAngle^2 := by
    unfold Params.curvature
    field_simp
    nlinarith [htrig]
  have heps : 0 < 1-p.beta := by linarith
  have hcurv : 0 < 1-p.curvature := by
    unfold Params.curvature
    rw [sub_pos, div_lt_iff₀ (by linarith : 0 < 2*(1+p.beta))]
    simpa using hw1
  rw [heq, hP, ← hden]
  unfold Params.eps
  field_simp
  <;> ring

/-- The exact sampled normalization stays uniformly away from zero throughout
the oscillatory region used by the eigenfunctional comparison. -/
theorem Params.sampledKernelMass_ge_one_fifth (p : Params)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))
    (jury : External.JuryStability) (hd : 1 ≤ p.matchedDelta) :
    1/5 ≤ p.sampledKernelMass := by
  have hb : 0 < p.beta := by linarith
  have hh := p.matchedStep_pos hb hb1
  obtain ⟨omega, ho, hosq, hangle, hc⟩ := p.matched_frequency_of_one_le hb hb1 hd
  have heps : 0 < 1-p.beta := by linarith
  have hepsh : 1-p.beta ≤ p.matchedStep := by
    have H := Real.log_le_sub_one_of_pos hb
    dsimp only [Params.matchedStep]
    linarith
  have hangle0 : 0 < p.foldedAngle := by rw [← hangle]; positivity
  have hsin : 0 < Real.sin p.foldedAngle := Real.sin_pos_of_pos_of_lt_pi
    hangle0 (by linarith [p.foldedAngle_bounds.2, Real.pi_pos])
  have hhalf : p.foldedAngle/2 ≤ Real.sin p.foldedAngle := by
    have H := Real.mul_le_sin p.foldedAngle_bounds.1 p.foldedAngle_bounds.2
    have hpi : (1:ℝ)/2 ≤ 2/Real.pi := by
      apply (le_div_iff₀ Real.pi_pos).mpr
      linarith [Real.pi_le_four]
    nlinarith [mul_le_mul_of_nonneg_right hpi p.foldedAngle_bounds.1]
  have hsquare : (1-p.beta)^2 ≤ (16/3)*Real.sin p.foldedAngle^2 := by
    have ha : p.foldedAngle^2 = omega^2*p.matchedStep^2 := by rw [← hangle, mul_pow]
    have ho3 : 3/4 ≤ omega^2 := by linarith
    have H := mul_le_mul_of_nonneg_right ho3 (sq_nonneg p.matchedStep)
    nlinarith [sq_nonneg (p.matchedStep-(1-p.beta)), sq_nonneg (Real.sin p.foldedAngle-p.foldedAngle/2)]
  have hratio : 1/5 ≤ 2*p.beta*(1+p.beta)*Real.sin p.foldedAngle^2 /
      ((1-p.beta)^2+4*p.beta*Real.sin p.foldedAngle^2) := by
    have hden : 0 < (1-p.beta)^2+4*p.beta*Real.sin p.foldedAngle^2 := by positivity
    apply (le_div_iff₀ hden).mpr
    have hbpoly : 16/3+4*p.beta ≤ 10*p.beta*(1+p.beta) := by nlinarith
    have H := mul_le_mul_of_nonneg_right hbpoly (sq_nonneg (Real.sin p.foldedAngle))
    nlinarith
  rw [p.sampledKernelMass_closed_form hb0 hb1 hw0 hw1 jury omega ho hosq hangle hc]
  have hf1 : 1 ≤ p.matchedDelta/omega^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ho)).mpr
    linarith
  have hf2 : 1 ≤ p.matchedStep/(1-p.beta) := (le_div_iff₀ heps).mpr (by simpa using hepsh)
  have hf : 1 ≤ p.matchedDelta/omega^2*(p.matchedStep/(1-p.beta)) :=
    one_le_mul_of_one_le_of_one_le hf1 hf2
  exact hratio.trans (le_mul_of_one_le_left (by linarith) hf)

end
end SparseSGD
