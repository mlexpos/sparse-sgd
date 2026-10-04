import SparseSGD.Scaling.WindowRisk
import SparseSGD.Scaling.WindowAverages
import SparseSGD.Scaling.WindowRate

namespace SparseSGD
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1500000

/-- The finite local average of the actual matched chain, for every starting
step and every positive integer window length. -/
theorem window_chain_local_average (margin : ℝ) (hm : 0 < margin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Params) (s : Moments),
      1/2 ≤ p.beta → p.beta < 1 → 0 < p.w → p.w < 2*(1+p.beta) →
      External.JuryStability → s.psd → 0 ≤ p.renormNoise → p.renormNoise ≤ 1-margin →
      0 ≤ p.renormAdditive → windowDeltaThreshold margin ≤ p.matchedDelta →
      p.foldedAngle ≤ Real.pi/2-margin → ∀ k N : ℕ, 0 < N →
      |(∑ j ∈ Finset.range N, (p.trajectory s (k+j)).R)/(N : ℝ)-
        p.windowSlow s ((k : ℝ)*p.matchedStep)/2| ≤
          C*(p.matchedStep+1/Real.sqrt p.matchedDelta)*(p.comparisonInitialSize s+p.renormAdditive)+
          (4/margin)*(p.comparisonInitialSize s+p.renormAdditive)*
            ((N : ℝ)*p.matchedStep+1/((N : ℝ)*p.foldedAngle)) := by
  obtain ⟨C,hC,hbound⟩ := window_chain_risk_comparison margin hm
  refine ⟨C,hC,?_⟩
  intro p s hb0 hb1 hw0 hw1 jury hs hu0 hu hp hD hnyq k N hN
  have hd4 : 4 ≤ p.matchedDelta := (le_max_left _ _).trans ((le_max_left _ _).trans hD)
  have hd : 0 < p.matchedDelta := by linarith
  have hh := p.matchedStep_pos (by linarith) hb1
  obtain ⟨omega,ho,hosq,hangle,hfreq⟩ := p.large_matched_frequency margin hm hb0 hb1 ((le_max_left _ _).trans hD)
  have homega : omega = Real.sqrt (p.matchedDelta-1/4) := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ p.matchedDelta-1/4),Real.sqrt_nonneg (p.matchedDelta-1/4)]
  have htheta : 0 < p.foldedAngle := by rw [← hangle]; positivity
  have hu1 : p.renormNoise < 1 := by linarith
  have hs' := p.matchedMoments_psd s hs
  let M := p.comparisonInitialSize s+p.renormAdditive
  let W := windowSize p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s)
  let Z := oscillatoryEnergy p.matchedDelta (oscillatoryRoot omega) (p.matchedMoments s)
  let q := Complex.exp (windowOscillatoryRate p.renormNoise omega*(p.matchedStep : ℂ))
  have hW : 0 ≤ W := by
    have hr := Moments.psd_R_nonneg hs'
    have hv := Moments.psd_V_nonneg hs'
    dsimp only [W,windowSize]
    positivity
  have hWM : W ≤ M/margin := windowSize_margin_bound p.matchedDelta p.renormNoise p.renormAdditive margin
    (p.matchedMoments s) hd hm hu0 hu hp hs'
  have hM : 0 ≤ M := by
    have H := (le_div_iff₀ hm).1 hWM
    nlinarith
  have hZ : ‖Z‖ ≤ 2*W := by
    have H := window_initial_osc_bound p.matchedDelta omega (by linarith) hosq (p.matchedMoments s) hs'
    apply H.trans
    dsimp only [W,windowSize]
    have HF : 0 ≤ p.renormAdditive/(1-p.renormNoise) := by positivity
    linarith
  have hS : |slowEnergy p.matchedDelta (p.matchedMoments s)-2*p.renormAdditive/(1-p.renormNoise)| ≤ 2*W := by
    have H := window_initial_centered_bound p.matchedDelta p.renormNoise p.renormAdditive omega hd4 hu1 hp ho hosq
      (p.matchedMoments s) hs' 0
    change ‖(slowEnergy p.matchedDelta (p.matchedMoments s) : ℂ)-
      (slowEnergy p.matchedDelta (windowEquilibrium p.matchedDelta p.renormNoise p.renormAdditive) : ℂ)‖ ≤ _ at H
    simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,windowEquilibrium_slow _ _ _ hd.ne'] using H
  have hpower (j : ℕ) : p.windowOsc s ((j : ℝ)*p.matchedStep) = Z*q^j := by
    dsimp only [Params.windowOsc,Z,q]
    rw [← homega]
    exact windowOscillatoryProfile_power _ _ _ _ _ _
  have happrox (j : ℕ) : |(p.trajectory s j).R-(p.windowSlow s ((j : ℝ)*p.matchedStep)/2+(Z*q^j).re/2)| ≤
      C*(p.matchedStep+1/Real.sqrt p.matchedDelta)*M := by
    rw [← hpower]
    exact hbound p s hb0 hb1 hw0 hw1 jury hs hu0 hu hp hD hnyq j
  have hslow (j l : ℕ) : |p.windowSlow s (((j+l : ℕ) : ℝ)*p.matchedStep)-
      p.windowSlow s ((j : ℝ)*p.matchedStep)| ≤ (2*W)*((l : ℝ)*p.matchedStep) := by
    simpa only [Nat.cast_add,add_mul,Params.windowSlow] using
      windowSlowProfile_increment p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s)
        hu0 hu1 (2*W) hS ((j : ℝ)*p.matchedStep) ((l : ℝ)*p.matchedStep) (by positivity) (by positivity)
  obtain ⟨hq,hgap⟩ := window_multiplier_bounds p.renormNoise omega p.matchedStep p.foldedAngle
    hu0 hh.le htheta.le (by linarith) hangle
  have H := window_average_transfer (fun j => (p.trajectory s j).R)
    (fun j => p.windowSlow s ((j : ℝ)*p.matchedStep)) Z q
    (C*(p.matchedStep+1/Real.sqrt p.matchedDelta)*M) (2*W) p.matchedStep p.foldedAngle
    happrox hslow (by positivity) hh.le hq htheta hgap k N hN
  apply H.trans
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hpart1 : (2*W)*(N : ℝ)*p.matchedStep/2 ≤ (M/margin)*(N : ℝ)*p.matchedStep := by
    calc
      _ = W*(N : ℝ)*p.matchedStep := by ring
      _ ≤ _ := by gcongr
  have hpart2 : 2*‖Z‖/((N : ℝ)*p.foldedAngle) ≤ 4*(M/margin)/((N : ℝ)*p.foldedAngle) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ 2*(2*W) := by gcongr
      _ ≤ 2*(2*(M/margin)) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ C*(p.matchedStep+1/Real.sqrt p.matchedDelta)*M+
        (M/margin)*(N : ℝ)*p.matchedStep+4*(M/margin)/((N : ℝ)*p.foldedAngle) := by gcongr
    _ ≤ _ := by
      have HH : 0 ≤ (M/margin)*(N : ℝ)*p.matchedStep := by positivity
      change _ ≤ C*(p.matchedStep+1/Real.sqrt p.matchedDelta)*M+
        (4/margin)*M*((N : ℝ)*p.matchedStep+1/((N : ℝ)*p.foldedAngle))
      ring_nf at HH ⊢
      linarith only [HH]

end
end SparseSGD
