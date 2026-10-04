import SparseSGD.Comparison.LargeComparison

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

def comparisonDeltaThreshold (margin : ℝ) : ℝ :=
  max 4 (1/4+(22/margin)^2)

theorem Params.matchedStep_le_one (p : Params) (hb : 1/2 ≤ p.beta) :
    p.matchedStep ≤ 1 := by
  have hp : 0 < p.beta := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hp
  have hi : p.beta⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).2
    linarith
  unfold Params.matchedStep
  linarith

/-- In the large regime the actual matched parameters lie in the underdamped
branch, and the folded angle is exactly frequency times matched step. -/
theorem Params.large_matched_frequency (p : Params) (margin : ℝ) (hm : 0 < margin)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hD : comparisonDeltaThreshold margin ≤ p.matchedDelta) :
    ∃ omega : ℝ, 0 < omega ∧ omega^2 = p.matchedDelta-1/4 ∧
      omega*p.matchedStep = p.foldedAngle ∧ 22*p.matchedStep ≤ margin*omega := by
  have hh := p.matchedStep_pos (by linarith) hb1
  have hd4 : 4 ≤ p.matchedDelta := (le_max_left _ _).trans hD
  have hdlarge : 1/4+(22/margin)^2 ≤ p.matchedDelta := (le_max_right _ _).trans hD
  have hc : |p.traceCosine| ≤ 1 := by
    by_contra H
    have he : p.matchedDelta ≤ 1/4 := by
      unfold Params.matchedDelta
      rw [if_neg H]
      nlinarith [sq_nonneg (Real.arcosh |p.traceCosine|/p.matchedStep)]
    linarith
  let omega := p.foldedAngle/p.matchedStep
  have hosq : omega^2 = p.matchedDelta-1/4 := by
    simp only [Params.matchedDelta,hc,ite_true]
    dsimp only [omega]
    ring
  have ho0 : 0 ≤ omega := div_nonneg p.foldedAngle_bounds.1 hh.le
  have ho : 0 < omega := by nlinarith
  have holarge : 22/margin ≤ omega := by
    have hd : (22/margin)^2 ≤ omega^2 := by nlinarith
    have hr : 0 ≤ 22/margin := by positivity
    nlinarith
  have h22 : 22 ≤ margin*omega := by
    have H := (div_le_iff₀ hm).1 holarge
    simpa only [mul_comm] using H
  have hstep := p.matchedStep_le_one hb0
  refine ⟨omega,ho,hosq,?_,by nlinarith⟩
  exact div_mul_cancel₀ _ hh.ne'

/-- Uniform-in-time risk comparison at the actual matched parameters, across
all positive delta, with the paper's stability and Nyquist margins. -/
theorem moment_comparison_risk (margin : ℝ) (hm : 0 < margin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Params) (s : Moments),
      1/2 ≤ p.beta → p.beta < 1 → 0 < p.w → p.w < 2*(1+p.beta) →
      External.JuryStability → s.psd → 0 ≤ p.renormNoise →
      p.renormNoise ≤ 1-margin → 0 ≤ p.renormAdditive →
      (comparisonDeltaThreshold margin ≤ p.matchedDelta → p.foldedAngle ≤ Real.pi/2-margin) →
      ∀ k : ℕ,
      |(p.trajectory s k).R-(p.comparisonFlow s ((k : ℝ)*p.matchedStep)).R| ≤
        C*p.matchedStep*(p.comparisonInitialSize s+p.renormAdditive) := by
  obtain ⟨CL,hCL0,hCL⟩ := risk_comparison_large margin hm
  let CB := Real.sqrt (comparisonDeltaThreshold margin)*(1+6/margin)/margin
  let C := max CB (CL/margin^2)
  have hCB : 0 ≤ CB := by dsimp only [CB]; positivity
  refine ⟨C,le_trans hCB (le_max_left _ _),?_⟩
  intro p s hb0 hb1 hw0 hw1 jury hs hu0 hu hp hnyq k
  have hu1 : p.renormNoise < 1 := by linarith
  have hh := p.matchedStep_pos (by linarith) hb1
  have hd := p.matchedDelta_pos (by linarith) hb1 hw0 hw1
  have hs' := p.matchedMoments_psd s hs
  have hN : 0 ≤ p.comparisonInitialSize s+p.renormAdditive := by
    have hr := Moments.psd_R_nonneg hs'
    have hv := Moments.psd_V_nonneg hs'
    unfold Params.comparisonInitialSize
    positivity
  by_cases hD : comparisonDeltaThreshold margin ≤ p.matchedDelta
  · obtain ⟨omega,ho,hosq,hangle,hfreq⟩ := p.large_matched_frequency margin hm hb0 hb1 hD
    have hd4 : 4 ≤ p.matchedDelta := (le_max_left _ _).trans hD
    have H := hCL p s omega hb0 hb1 hw0 hw1 jury hs hu0 hu1 hp hd4 ho hosq
      (p.matchedStep_le_one hb0) (by rw [hangle]; exact hnyq hD) hfreq k
    let E := (p.matchedMoments s).R+p.matchedDelta*(p.matchedMoments s).V+p.renormAdditive
    have hE : 0 ≤ E := add_nonneg
      (add_nonneg (Moments.psd_R_nonneg hs') (mul_nonneg hd.le (Moments.psd_V_nonneg hs'))) hp
    have hEN : E ≤ p.comparisonInitialSize s+p.renormAdditive := by
      dsimp only [E,Params.comparisonInitialSize]
      linarith [abs_nonneg (p.matchedMoments s).C]
    have hgap : margin^2 ≤ (1-p.renormNoise)^2 := by nlinarith
    have H' := div_le_div_of_nonneg_left (show 0 ≤ CL*p.matchedStep*E by positivity)
      (sq_pos_of_pos hm) hgap
    apply H.trans
    change CL*p.matchedStep*E/(1-p.renormNoise)^2 ≤ _
    calc
      _ ≤ CL*p.matchedStep*E/margin^2 := H'
      _ ≤ CL*p.matchedStep*(p.comparisonInitialSize s+p.renormAdditive)/margin^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hEN (by positivity)) (sq_nonneg margin)
      _ = (CL/margin^2)*p.matchedStep*(p.comparisonInitialSize s+p.renormAdditive) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right CB _) hh.le) hN
  · have H := p.risk_comparison_bounded_margin hb0 hb1 hw0 hw1 jury s hs hu0 hp
      (comparisonDeltaThreshold margin) margin hm hu (le_of_not_ge hD) k
    exact H.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ (CL/margin^2)) hh.le) hN)

end
end SparseSGD
