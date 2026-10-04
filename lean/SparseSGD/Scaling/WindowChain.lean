import SparseSGD.Scaling.WindowProfiles

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

def windowDeltaThreshold (margin : ℝ) : ℝ := max (comparisonDeltaThreshold margin) (1/(2*margin))
def Params.windowSlow (p : Params) (s : Moments) (t : ℝ) : ℝ :=
  windowSlowProfile p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s) t
def Params.windowOsc (p : Params) (s : Moments) (t : ℝ) : ℂ :=
  windowOscillatoryProfile p.matchedDelta p.renormNoise (Real.sqrt (p.matchedDelta-1/4)) (p.matchedMoments s) t

theorem windowOscillatoryProfile_grid (delta u omega h theta : ℝ) (s : Moments)
    (hangle : omega*h = theta) (k : ℕ) :
    windowOscillatoryProfile delta u omega s ((k : ℝ)*h) =
      oscillatoryEnergy delta (oscillatoryRoot omega) s*
        (Real.exp (-(1+u/2)*((k : ℝ)*h)) : ℂ)*Complex.exp (2*Complex.I*(k : ℂ)*(theta : ℂ)) := by
  have hc : (omega : ℂ)*(h : ℂ) = (theta : ℂ) := by exact_mod_cast hangle
  have he : windowOscillatoryRate u omega*((k : ℝ)*h : ℝ) =
      ((-(1+u/2)*((k : ℝ)*h) : ℝ) : ℂ)+2*Complex.I*(k : ℂ)*(theta : ℂ) := by
    unfold windowOscillatoryRate
    rw [← hc]
    push_cast
    ring
  unfold windowOscillatoryProfile
  rw [he,Complex.exp_add,← Complex.ofReal_exp]
  ring

/-- Actual chain slow energy and oscillation have a uniform long-window
approximation. No limiting regime or modal conclusion is an assumption. -/
theorem window_chain_energy_comparison (margin : ℝ) (hm : 0 < margin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Params) (s : Moments),
      1/2 ≤ p.beta → p.beta < 1 → 0 < p.w → p.w < 2*(1+p.beta) →
      External.JuryStability → s.psd → 0 ≤ p.renormNoise → p.renormNoise ≤ 1-margin →
      0 ≤ p.renormAdditive → windowDeltaThreshold margin ≤ p.matchedDelta →
      p.foldedAngle ≤ Real.pi/2-margin → ∀ k : ℕ,
      |slowEnergy p.matchedDelta (p.matchedMoments (p.trajectory s k))-
        p.windowSlow s ((k : ℝ)*p.matchedStep)| ≤
          C*(p.matchedStep+1/Real.sqrt p.matchedDelta)*(p.comparisonInitialSize s+p.renormAdditive) ∧
      ‖oscillatoryEnergy p.matchedDelta (oscillatoryRoot (Real.sqrt (p.matchedDelta-1/4)))
          (p.matchedMoments (p.trajectory s k))-p.windowOsc s ((k : ℝ)*p.matchedStep)‖ ≤
          C*(p.matchedStep+1/Real.sqrt p.matchedDelta)*(p.comparisonInitialSize s+p.renormAdditive) := by
  obtain ⟨CM,hCM0,hCM⟩ := moment_comparison_energyFunctional margin hm
  let CW := 2*(48+4/margin)/margin
  let C := CM+CW
  have hCW : 0 ≤ CW := by dsimp only [CW]; positivity
  refine ⟨C,add_nonneg hCM0 hCW,?_⟩
  intro p s hb0 hb1 hw0 hw1 jury hs hu0 hu hp hD hnyq k
  have hDc : comparisonDeltaThreshold margin ≤ p.matchedDelta := (le_max_left _ _).trans hD
  have hd4 : 4 ≤ p.matchedDelta := (le_max_left _ _).trans hDc
  have hd := p.matchedDelta_pos (by linarith) hb1 hw0 hw1
  have hh := p.matchedStep_pos (by linarith) hb1
  have hs' := p.matchedMoments_psd s hs
  have hlarge : 1 ≤ 2*margin*p.matchedDelta := by
    have H := (div_le_iff₀ (by positivity : 0 < 2*margin)).1 ((le_max_right _ _).trans hD)
    nlinarith
  obtain ⟨omega,ho,hosq,hangle,hfreq⟩ := p.large_matched_frequency margin hm hb0 hb1 hDc
  have he : omega = Real.sqrt (p.matchedDelta-1/4) := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ p.matchedDelta-1/4),
      Real.sqrt_nonneg (p.matchedDelta-1/4)]
  let N := p.comparisonInitialSize s+p.renormAdditive
  have hN : 0 ≤ N := by
    have hr := Moments.psd_R_nonneg hs'
    have hv := Moments.psd_V_nonneg hs'
    dsimp only [N,Params.comparisonInitialSize]
    positivity
  have hsize := windowSize_margin_bound p.matchedDelta p.renormNoise p.renormAdditive margin
    (p.matchedMoments s) hd hm hu0 hu hp hs'
  change windowSize _ _ _ _ ≤ N/margin at hsize
  have hfrequency := window_inverse_frequency_bound p.matchedDelta omega hd4 ho hosq
  have hcont (X : ℝ) (hX : X ≤ (48+4/margin)*windowSize p.matchedDelta p.renormNoise p.renormAdditive
      (p.matchedMoments s)/omega) : X ≤ CW*(1/Real.sqrt p.matchedDelta)*N := by
    apply hX.trans
    calc
      _ = (48+4/margin)*windowSize p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s)*(1/omega) := by ring
      _ ≤ (48+4/margin)*(N/margin)*(2/Real.sqrt p.matchedDelta) := by gcongr
      _ = _ := by dsimp only [CW]; ring
  have hcombine (X : ℝ) (hX : X ≤ CM*p.matchedStep*N+CW*(1/Real.sqrt p.matchedDelta)*N) :
      X ≤ C*(p.matchedStep+1/Real.sqrt p.matchedDelta)*N := by
    apply hX.trans
    calc
      _ ≤ C*p.matchedStep*N+C*(1/Real.sqrt p.matchedDelta)*N := by
        gcongr <;> dsimp only [C] <;> linarith
      _ = _ := by ring
  have HM := hCM p s omega hb0 hb1 hw0 hw1 jury hs hu0 hu hp (by linarith) ho hosq
    (fun _ => hnyq) k
  have HS := continuum_window_slow_bound p.matchedDelta p.renormNoise p.renormAdditive omega margin
    (p.matchedMoments s) hd4 hm hu0 hu hp hs' ho hosq hlarge ((k : ℝ)*p.matchedStep) (by positivity)
  have HZ := continuum_window_osc_bound p.matchedDelta p.renormNoise p.renormAdditive omega margin
    (p.matchedMoments s) hd4 hm hu0 hu hp hs' ho hosq hlarge ((k : ℝ)*p.matchedStep) (by positivity)
  constructor
  · have H0 := HM 0
    change ‖(slowEnergy p.matchedDelta (p.matchedMoments (p.trajectory s k)) : ℂ)-
      (slowEnergy p.matchedDelta (p.comparisonFlow s ((k : ℝ)*p.matchedStep)) : ℂ)‖ ≤ _ at H0
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at H0
    apply hcombine
    exact (abs_sub_le _ (slowEnergy p.matchedDelta (p.comparisonFlow s ((k : ℝ)*p.matchedStep))) _).trans
      (add_le_add H0 (hcont _ HS))
  · dsimp only [Params.windowOsc]
    rw [← he]
    apply hcombine
    exact (norm_sub_le_norm_sub_add_norm_sub _
      (oscillatoryEnergy p.matchedDelta (oscillatoryRoot omega) (p.comparisonFlow s ((k : ℝ)*p.matchedStep))) _).trans
      (add_le_add (HM 1) (hcont _ HZ))

theorem Params.windowOsc_grid (p : Params) (margin : ℝ) (hm : 0 < margin)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hD : windowDeltaThreshold margin ≤ p.matchedDelta) (s : Moments) (k : ℕ) :
    p.windowOsc s ((k : ℝ)*p.matchedStep) =
      oscillatoryEnergy p.matchedDelta (oscillatoryRoot (Real.sqrt (p.matchedDelta-1/4))) (p.matchedMoments s)*
        (Real.exp (-(1+p.renormNoise/2)*((k : ℝ)*p.matchedStep)) : ℂ)*
          Complex.exp (2*Complex.I*(k : ℂ)*(p.foldedAngle : ℂ)) := by
  obtain ⟨omega,ho,hosq,hangle,hfreq⟩ := p.large_matched_frequency margin hm hb0 hb1 ((le_max_left _ _).trans hD)
  have hd4 : 4 ≤ p.matchedDelta := (le_max_left _ _).trans ((le_max_left _ _).trans hD)
  have he : omega = Real.sqrt (p.matchedDelta-1/4) := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ p.matchedDelta-1/4),Real.sqrt_nonneg (p.matchedDelta-1/4)]
  dsimp only [Params.windowOsc]
  rw [← he]
  exact windowOscillatoryProfile_grid _ _ _ _ _ _ hangle k

end
end SparseSGD
