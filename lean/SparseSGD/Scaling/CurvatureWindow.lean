import SparseSGD.Scaling.CurvatureLimit

open Filter Topology
namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1000000

/-- Parameter hypotheses for the proved long-window corollary. -/
structure WindowParameters (p : Params) (margin : ℝ) : Prop where
  beta_lower : 1/2 ≤ p.beta
  beta_upper : p.beta < 1
  curvature_pos : 0 < p.w
  curvature_upper : p.w < 2*(1+p.beta)
  noise_nonneg : 0 ≤ p.renormNoise
  noise_margin : p.renormNoise ≤ 1-margin
  large : windowDeltaThreshold margin ≤ p.matchedDelta
  nyquist : p.foldedAngle ≤ Real.pi/2-margin

/-- Source curvature hypotheses imply the actual window hypotheses eventually,
with half the limiting margin. -/
theorem curvature_eventually_window (p : ℕ → Params) (w u margin : ℝ)
    (hb : Tendsto (fun n => (p n).beta) atTop (𝓝 1))
    (hw : Tendsto (fun n => (p n).w) atTop (𝓝 w))
    (hu : Tendsto (fun n => (p n).noise) atTop (𝓝 u))
    (hw0 : 0 < w) (hw4 : w < 4) (hm : 0 < margin)
    (hb1 : ∀ᶠ n in atTop, (p n).beta < 1)
    (hu0 : ∀ᶠ n in atTop, 0 ≤ (p n).noise)
    (hum : u/(1-w/4) ≤ 1-margin)
    (hnyq : 2*Real.sin margin ≤ |w-2|) :
    ∀ᶠ n in atTop, WindowParameters (p n) (margin/2) := by
  have hu0' : 0 ≤ u := ge_of_tendsto hu hu0
  have hur : 0 ≤ u/(1-w/4) := div_nonneg hu0' (by linarith)
  have hm1 : margin ≤ 1 := by linarith
  have hmpi : margin ≤ Real.pi/2 := by linarith [Real.pi_gt_three]
  have hangle := curvature_angle_margin w margin hm.le hmpi hnyq
  have hgap : Tendsto (fun n => 2*(1+(p n).beta)-(p n).w) atTop (𝓝 (4-w)) := by
    convert ((hb.const_add 1).const_mul 2).sub hw using 1 <;> norm_num
  have hnoise := curvature_noise_tendsto p w u hb hw hu hw4
  filter_upwards [hb.eventually (le_mem_nhds (show (1/2:ℝ)<1 by norm_num)),hb1,
    hw.eventually (lt_mem_nhds hw0),hgap.eventually (lt_mem_nhds (show (0:ℝ)<4-w by linarith)),
    hu0,(curvature_load_tendsto p w hb hw).eventually (gt_mem_nhds (show w/4<1 by linarith)),
    hnoise.eventually (ge_mem_nhds (show u/(1-w/4)<1-margin/2 by linarith)),
    (curvature_matchedDelta_tendsto_atTop p w hb hw hw0 hw4 hb1).eventually_ge_atTop (windowDeltaThreshold (margin/2)),
    (curvature_foldedAngle_tendsto p w hb hw).eventually
      (ge_mem_nhds (show Real.arccos |1-w/2|<Real.pi/2-margin/2 by linarith))]
    with n hbl hbu hwp hwu hnu hcu hnum hlarge hang
  exact ⟨hbl,hbu,hwp,by linarith,div_nonneg hnu (by linarith),hnum,hlarge,hang⟩

/-- Full actual-chain curvature-window estimate. The energy/forcing size is
retained, so no unrecorded uniform initial-data bound is required. -/
theorem curvature_window_comparison (p : ℕ → Params) (s : ℕ → Moments)
    (w u margin : ℝ) (jury : External.JuryStability)
    (hb : Tendsto (fun n => (p n).beta) atTop (𝓝 1))
    (hw : Tendsto (fun n => (p n).w) atTop (𝓝 w))
    (hu : Tendsto (fun n => (p n).noise) atTop (𝓝 u))
    (hw0 : 0 < w) (hw4 : w < 4) (hm : 0 < margin)
    (hb1 : ∀ᶠ n in atTop, (p n).beta < 1)
    (hu0 : ∀ᶠ n in atTop, 0 ≤ (p n).noise)
    (hp : ∀ᶠ n in atTop, 0 ≤ (p n).renormAdditive)
    (hs : ∀ n, (s n).psd) (hum : u/(1-w/4) ≤ 1-margin)
    (hnyq : 2*Real.sin margin ≤ |w-2|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ k : ℕ,
      |slowEnergy (p n).matchedDelta ((p n).matchedMoments ((p n).trajectory (s n) k))-
        (p n).windowSlow (s n) ((k : ℝ)*(p n).matchedStep)| ≤
          C*(p n).matchedStep*((p n).comparisonInitialSize (s n)+(p n).renormAdditive) ∧
      ‖oscillatoryEnergy (p n).matchedDelta (oscillatoryRoot (Real.sqrt ((p n).matchedDelta-1/4)))
          ((p n).matchedMoments ((p n).trajectory (s n) k))-
          (p n).windowOsc (s n) ((k : ℝ)*(p n).matchedStep)‖ ≤
          C*(p n).matchedStep*((p n).comparisonInitialSize (s n)+(p n).renormAdditive) ∧
      |((p n).trajectory (s n) k).R-((p n).windowSlow (s n) ((k : ℝ)*(p n).matchedStep)/2+
        ((p n).windowOsc (s n) ((k : ℝ)*(p n).matchedStep)).re/2)| ≤
          C*(p n).matchedStep*((p n).comparisonInitialSize (s n)+(p n).renormAdditive) := by
  have hm2 : 0 < margin/2 := half_pos hm
  obtain ⟨CE,hCE,HE⟩ := window_chain_energy_comparison (margin/2) hm2
  obtain ⟨CR,hCR,HR⟩ := window_chain_risk_comparison (margin/2) hm2
  obtain ⟨F,hF,HF⟩ := curvature_window_error_factor p w hb hw hw0 hw4 hb1
  refine ⟨(CE+CR)*F,by positivity,?_⟩
  filter_upwards [curvature_eventually_window p w u margin hb hw hu hw0 hw4 hm hb1 hu0 hum hnyq,hp,HF]
    with n hn hp hf
  intro k
  obtain ⟨he,hz⟩ := HE (p n) (s n) hn.beta_lower hn.beta_upper hn.curvature_pos hn.curvature_upper jury
    (hs n) hn.noise_nonneg hn.noise_margin hp hn.large hn.nyquist k
  have hr := HR (p n) (s n) hn.beta_lower hn.beta_upper hn.curvature_pos hn.curvature_upper jury
    (hs n) hn.noise_nonneg hn.noise_margin hp hn.large hn.nyquist k
  have hh := (p n).matchedStep_pos (by linarith [hn.beta_lower]) hn.beta_upper
  have hd := (p n).matchedDelta_pos (by linarith [hn.beta_lower]) hn.beta_upper hn.curvature_pos hn.curvature_upper
  have hpsd := (p n).matchedMoments_psd (s n) (hs n)
  have hN : 0 ≤ (p n).comparisonInitialSize (s n)+(p n).renormAdditive := by
    have hR := Moments.psd_R_nonneg hpsd
    have hV := Moments.psd_V_nonneg hpsd
    dsimp only [Params.comparisonInitialSize]
    positivity
  have hbound (D : ℝ) (hD : 0 ≤ D) (hDC : D ≤ CE+CR) :
      D*((p n).matchedStep+1/Real.sqrt (p n).matchedDelta)*
        ((p n).comparisonInitialSize (s n)+(p n).renormAdditive) ≤
      ((CE+CR)*F)*(p n).matchedStep*((p n).comparisonInitialSize (s n)+(p n).renormAdditive) := by
    calc
      _ ≤ D*(F*(p n).matchedStep)*((p n).comparisonInitialSize (s n)+(p n).renormAdditive) := by gcongr
      _ = D*F*(p n).matchedStep*((p n).comparisonInitialSize (s n)+(p n).renormAdditive) := by ring
      _ ≤ _ := by gcongr
  exact ⟨he.trans (hbound CE hCE (by linarith)),hz.trans (hbound CE hCE (by linarith)),
    hr.trans (hbound CR hCR (by linarith))⟩

/-- Local averaging in the curvature regime, with the matched-step error. -/
theorem curvature_window_local_average (p : ℕ → Params) (s : ℕ → Moments)
    (w u margin : ℝ) (jury : External.JuryStability)
    (hb : Tendsto (fun n => (p n).beta) atTop (𝓝 1))
    (hw : Tendsto (fun n => (p n).w) atTop (𝓝 w))
    (hu : Tendsto (fun n => (p n).noise) atTop (𝓝 u))
    (hw0 : 0 < w) (hw4 : w < 4) (hm : 0 < margin)
    (hb1 : ∀ᶠ n in atTop, (p n).beta < 1)
    (hu0 : ∀ᶠ n in atTop, 0 ≤ (p n).noise)
    (hp : ∀ᶠ n in atTop, 0 ≤ (p n).renormAdditive)
    (hs : ∀ n, (s n).psd) (hum : u/(1-w/4) ≤ 1-margin)
    (hnyq : 2*Real.sin margin ≤ |w-2|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ k N : ℕ, 0 < N →
      |(∑ j ∈ Finset.range N, ((p n).trajectory (s n) (k+j)).R)/(N : ℝ)-
        (p n).windowSlow (s n) ((k : ℝ)*(p n).matchedStep)/2| ≤
        C*(p n).matchedStep*((p n).comparisonInitialSize (s n)+(p n).renormAdditive)+
        (8/margin)*((p n).comparisonInitialSize (s n)+(p n).renormAdditive)*
          ((N : ℝ)*(p n).matchedStep+1/((N : ℝ)*(p n).foldedAngle)) := by
  obtain ⟨C,hC,HC⟩ := window_chain_local_average (margin/2) (half_pos hm)
  obtain ⟨F,hF,HF⟩ := curvature_window_error_factor p w hb hw hw0 hw4 hb1
  refine ⟨C*F,by positivity,?_⟩
  filter_upwards [curvature_eventually_window p w u margin hb hw hu hw0 hw4 hm hb1 hu0 hum hnyq,hp,HF]
    with n hn hp hf
  intro k N hN
  have H := HC (p n) (s n) hn.beta_lower hn.beta_upper hn.curvature_pos hn.curvature_upper jury
    (hs n) hn.noise_nonneg hn.noise_margin hp hn.large hn.nyquist k N hN
  have hh := (p n).matchedStep_pos (by linarith [hn.beta_lower]) hn.beta_upper
  have hd := (p n).matchedDelta_pos (by linarith [hn.beta_lower]) hn.beta_upper hn.curvature_pos hn.curvature_upper
  have hpsd := (p n).matchedMoments_psd (s n) (hs n)
  have hsize : 0 ≤ (p n).comparisonInitialSize (s n)+(p n).renormAdditive := by
    have hR := Moments.psd_R_nonneg hpsd
    have hV := Moments.psd_V_nonneg hpsd
    dsimp only [Params.comparisonInitialSize]
    positivity
  calc
    _ ≤ _ := H
    _ ≤ (C*(F*(p n).matchedStep))*((p n).comparisonInitialSize (s n)+(p n).renormAdditive)+
        (4/(margin/2))*((p n).comparisonInitialSize (s n)+(p n).renormAdditive)*
          ((N : ℝ)*(p n).matchedStep+1/((N : ℝ)*(p n).foldedAngle)) := by gcongr
    _ = _ := by ring

/-- The two limiting rates, before deciding which load vanishes. -/
theorem curvature_profile_rates_tendsto (p : ℕ → Params) (w u : ℝ)
    (hb : Tendsto (fun n => (p n).beta) atTop (𝓝 1))
    (hw : Tendsto (fun n => (p n).w) atTop (𝓝 w))
    (hu : Tendsto (fun n => (p n).noise) atTop (𝓝 u)) (hw4 : w < 4) :
    Tendsto (fun n => 1-(p n).renormNoise) atTop (𝓝 (1-u/(1-w/4))) ∧
    Tendsto (fun n => 1+(p n).renormNoise/2) atTop (𝓝 (1+u/(1-w/4)/2)) := by
  have h := curvature_noise_tendsto p w u hb hw hu hw4
  exact ⟨h.const_sub 1,(h.div_const 2).const_add 1⟩

/-- At positive curvature and noise, the rate lies strictly between the
ordinary load margin and one. -/
theorem curvature_switch_rate (w u : ℝ) (hw0 : 0 < w) (hw4 : w < 4)
    (hu0 : 0 < u) (hu1 : u+w/4 < 1) :
    1-(u+w/4) < 1-u/(1-w/4) ∧ 1-u/(1-w/4) < 1 := by
  have H := switch_rate_strict (⟨1,w,u,0⟩ : Params)
  simp only [Params.curvature,Params.totalLoad,Params.renormNoise] at H
  norm_num at H
  obtain ⟨h1,h2⟩ := H (by linarith) (by linarith) hu0 hu1
  constructor <;> linarith

theorem curvature_only_rate (w : ℝ) : 1-(0:ℝ)/(1-w/4)=1 := by simp

theorem noise_only_rate (u : ℝ) : 1-u/(1-(0:ℝ)/4)=1-u := by simp

end
end SparseSGD
