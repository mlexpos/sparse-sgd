import SparseSGD.Scaling.WindowReconstruction

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

/-- The actual risk admits the two-scale expansion, uniformly over all steps. -/
theorem window_chain_risk_comparison (margin : ℝ) (hm : 0 < margin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Params) (s : Moments),
      1/2 ≤ p.beta → p.beta < 1 → 0 < p.w → p.w < 2*(1+p.beta) →
      External.JuryStability → s.psd → 0 ≤ p.renormNoise → p.renormNoise ≤ 1-margin →
      0 ≤ p.renormAdditive → windowDeltaThreshold margin ≤ p.matchedDelta →
      p.foldedAngle ≤ Real.pi/2-margin → ∀ k : ℕ,
      |(p.trajectory s k).R-(p.windowSlow s ((k : ℝ)*p.matchedStep)/2+
        (p.windowOsc s ((k : ℝ)*p.matchedStep)).re/2)| ≤
          C*(p.matchedStep+1/Real.sqrt p.matchedDelta)*(p.comparisonInitialSize s+p.renormAdditive) := by
  obtain ⟨C,hC,hbound⟩ := window_chain_energy_comparison margin hm
  refine ⟨2*C+16/margin,by positivity,?_⟩
  intro p s hb0 hb1 hw0 hw1 jury hs hu0 hu hp hD hnyq k
  have hd4 : 4 ≤ p.matchedDelta := (le_max_left _ _).trans ((le_max_left _ _).trans hD)
  have hd : 0 < p.matchedDelta := by linarith
  have hh := p.matchedStep_pos (by linarith) hb1
  let omega := Real.sqrt (p.matchedDelta-1/4)
  have ho : 0 < omega := Real.sqrt_pos.mpr (by linarith)
  have hosq : omega^2 = p.matchedDelta-1/4 := Real.sq_sqrt (by linarith)
  have hs' := p.matchedMoments_psd s hs
  let N := p.comparisonInitialSize s+p.renormAdditive
  have hN : 0 ≤ N := by
    have hr := Moments.psd_R_nonneg hs'
    have hv := Moments.psd_V_nonneg hs'
    dsimp only [N,Params.comparisonInitialSize]
    positivity
  have hsize := windowSize_margin_bound p.matchedDelta p.renormNoise p.renormAdditive margin
    (p.matchedMoments s) hd hm hu0 hu hp hs'
  change windowSize _ _ _ _ ≤ N/margin at hsize
  have hW : 0 ≤ windowSize p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s) := by
    have hr := Moments.psd_R_nonneg hs'
    have hv := Moments.psd_V_nonneg hs'
    dsimp only [windowSize]
    have hu1 : p.renormNoise < 1 := by linarith
    positivity
  obtain ⟨HS,HZ⟩ := hbound p s hb0 hb1 hw0 hw1 jury hs hu0 hu hp hD hnyq k
  obtain ⟨HSB,HZB⟩ := window_profile_bounds p.matchedDelta p.renormNoise p.renormAdditive omega
    (p.matchedMoments s) hd4 hu0 (by linarith) hp hs' ho hosq
    ((k : ℝ)*p.matchedStep) (by positivity)
  have H := window_risk_reconstruction_error p.matchedDelta omega
    (windowSize p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s))
    (C*(p.matchedStep+1/Real.sqrt p.matchedDelta)*N)
    (p.windowSlow s ((k : ℝ)*p.matchedStep)) (p.windowOsc s ((k : ℝ)*p.matchedStep))
    (p.matchedMoments (p.trajectory s k)) hd4 ho hosq hW (by positivity) HS HZ HSB HZB
  have hR : (p.matchedMoments (p.trajectory s k)).R = (p.trajectory s k).R :=
    p.matchedCovariance_first_entry (by linarith) hb1 hw0 hw1 _
  rw [hR] at H
  apply H.trans
  have hfreq := window_inverse_frequency_bound p.matchedDelta omega hd4 ho hosq
  have H' : 8*windowSize p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s)/omega ≤
      (16/margin)*(1/Real.sqrt p.matchedDelta)*N := by
    calc
      _ = 8*windowSize p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s)*(1/omega) := by ring
      _ ≤ 8*(N/margin)*(2/Real.sqrt p.matchedDelta) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 2*(C*(p.matchedStep+1/Real.sqrt p.matchedDelta)*N)+
        (16/margin)*(1/Real.sqrt p.matchedDelta)*N := by gcongr
    _ ≤ _ := by nlinarith only [mul_nonneg (show 0 ≤ 16/margin by positivity) (mul_nonneg hh.le hN)]

end
end SparseSGD
