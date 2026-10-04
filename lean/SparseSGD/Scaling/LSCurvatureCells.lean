import SparseSGD.Scaling.LSLoadLimits

open Filter Topology MeasureTheory
namespace SparseSGD.Scaling
noncomputable section
set_option maxHeartbeats 1200000

/-- All window parameters and renormalized loads at the actual curvature ceiling. -/
theorem ls_curvature_cells_parameters
    (pStar kappa bStar sigma epsStar gamma etaStar alpha u margin : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (hb : 0 < bStar) (hs : 0 ≤ sigma)
    (he : 0 < epsStar) (hg : 0 < gamma) (heta : 0 < etaStar)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hw : -(alpha+gamma+kappa)=0)
    (hcell : (1-sigma-alpha<0 ∧ u=0) ∨
      (1-sigma-alpha=0 ∧ u=etaStar/(2*realizedBatchScale bStar sigma)))
    (hw4 : etaStar*epsStar*pStar<4) (hm : 0 < margin)
    (hum : u/(1-etaStar*epsStar*pStar/4) ≤ 1-margin)
    (hnyq : 2*Real.sin margin ≤ |etaStar*epsStar*pStar-2|) :
    let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
    (∀ᶠ d in atTop, WindowParameters (P d) (margin/2) ∧ 0 ≤ (P d).renormAdditive) ∧
      Tendsto (fun d => (P d).renormNoise) atTop (𝓝 (u/(1-etaStar*epsStar*pStar/4))) ∧
      Tendsto (fun d => (P d).renormAdditive) atTop
        (𝓝 ((SparseSGD.Probability.LeastSquares.labelVariance ν*u)/(1-etaStar*epsStar*pStar/4))) := by
  let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
  let w := etaStar*epsStar*pStar
  have hw0 : 0 < w := by dsimp [w]; positivity
  have halg := actualLSFamily_algebra pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp hb he hg heta hpd
  have hbeta := actualLSParams_beta_tendsto_one pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hg
  have hwlim := actualLSFamily_w_tendsto_critical pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp he heta hpd hw
  obtain ⟨hnoise,hadd⟩ := actualLSFamily_load_limits pStar kappa bStar sigma epsStar gamma etaStar alpha u p ν hp hk hb hs heta hpd hcell
  have hnu := curvature_noise_tendsto P w u hbeta hwlim hnoise hw4
  have hc := curvature_load_tendsto P w hbeta hwlim
  have hph : Tendsto (fun d => (P d).renormAdditive) atTop
      (𝓝 ((SparseSGD.Probability.LeastSquares.labelVariance ν*u)/(1-w/4))) :=
    hadd.div (tendsto_const_nhds.sub hc) (by dsimp [w]; linarith)
  have hb1 : ∀ᶠ d in atTop, (P d).beta<1 := halg.mono (fun _ hd => hd.2.1)
  have hn0 : ∀ᶠ d in atTop, 0 ≤ (P d).noise := halg.mono (fun _ hd => hd.2.2.2.2.2.1)
  refine ⟨?_,hnu,hph⟩
  filter_upwards [curvature_eventually_window P w u margin hbeta hwlim hnoise hw0 hw4 hm hb1 hn0 hum hnyq,
    halg,hc.eventually (eventually_lt_nhds (by dsimp [w]; linarith : w/4<1))] with d hd halg hc
  exact ⟨hd,(renorm_nonneg_of_curvature_lt_one (P d) halg.2.2.2.2.2.1 halg.2.2.2.2.2.2 hc).2⟩

/-- Cells 7 and 8: the actual LS two-scale risk bound has error of order one
matched step, with the initial-energy/forcing factor stated explicitly. -/
theorem ls_curvature_cells_risk
    (pStar kappa bStar sigma epsStar gamma etaStar alpha u margin : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (jury : External.JuryStability)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (hb : 0 < bStar) (hs : 0 ≤ sigma)
    (he : 0 < epsStar) (hg : 0 < gamma) (heta : 0 < etaStar)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hw : -(alpha+gamma+kappa)=0)
    (hcell : (1-sigma-alpha<0 ∧ u=0) ∨
      (1-sigma-alpha=0 ∧ u=etaStar/(2*realizedBatchScale bStar sigma)))
    (hw4 : etaStar*epsStar*pStar<4) (hm : 0 < margin)
    (hum : u/(1-etaStar*epsStar*pStar/4) ≤ 1-margin)
    (hnyq : 2*Real.sin margin ≤ |etaStar*epsStar*pStar-2|)
    (s : ℕ → Moments) (hsPSD : ∀ d, (s d).psd) :
    let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
    ∃ C ≥ 0,
      Tendsto (fun d => C*(P d).matchedStep) atTop (𝓝 0) ∧
      ∀ᶠ d in atTop, ∀ k : ℕ,
        |((P d).trajectory (s d) k).R-
          ((P d).windowSlow (s d) ((k : ℝ)*(P d).matchedStep)/2+
            ((P d).windowOsc (s d) ((k : ℝ)*(P d).matchedStep)).re/2)| ≤
          C*(P d).matchedStep*((P d).comparisonInitialSize (s d)+(P d).renormAdditive) := by
  let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
  let w := etaStar*epsStar*pStar
  have hw0 : 0 < w := by dsimp [w]; positivity
  have halg := actualLSFamily_algebra pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp hb he hg heta hpd
  have hbeta := actualLSParams_beta_tendsto_one pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hg
  have hwlim := actualLSFamily_w_tendsto_critical pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp he heta hpd hw
  obtain ⟨hnoise,_⟩ := actualLSFamily_load_limits pStar kappa bStar sigma epsStar gamma etaStar alpha u p ν hp hk hb hs heta hpd hcell
  have H := (ls_curvature_cells_parameters pStar kappa bStar sigma epsStar gamma etaStar alpha u margin p ν hp hk hb hs he hg heta hpd hw hcell hw4 hm hum hnyq).1
  have hb1 : ∀ᶠ d in atTop, (P d).beta<1 := halg.mono (fun _ hd => hd.2.1)
  have hn0 : ∀ᶠ d in atTop, 0 ≤ (P d).noise := halg.mono (fun _ hd => hd.2.2.2.2.2.1)
  obtain ⟨C,hC,HC⟩ := curvature_window_comparison P s w u margin jury hbeta hwlim hnoise hw0 hw4 hm hb1 hn0 (H.mono (fun _ hd => hd.2)) hsPSD hum hnyq
  refine ⟨C,hC,by simpa using (curvature_matchedStep_tendsto P hbeta).const_mul C,?_⟩
  filter_upwards [HC] with d hd
  exact fun k => (hd k).2.2

/-- The actual slow and oscillatory energies in cells 7 and 8. -/
theorem ls_curvature_cells_energy
    (pStar kappa bStar sigma epsStar gamma etaStar alpha u margin : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (jury : External.JuryStability)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (hb : 0 < bStar) (hs : 0 ≤ sigma)
    (he : 0 < epsStar) (hg : 0 < gamma) (heta : 0 < etaStar)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hw : -(alpha+gamma+kappa)=0)
    (hcell : (1-sigma-alpha<0 ∧ u=0) ∨
      (1-sigma-alpha=0 ∧ u=etaStar/(2*realizedBatchScale bStar sigma)))
    (hw4 : etaStar*epsStar*pStar<4) (hm : 0 < margin)
    (hum : u/(1-etaStar*epsStar*pStar/4) ≤ 1-margin)
    (hnyq : 2*Real.sin margin ≤ |etaStar*epsStar*pStar-2|)
    (s : ℕ → Moments) (hsPSD : ∀ d, (s d).psd) :
    let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
    ∃ C ≥ 0,
      Tendsto (fun d => C*(P d).matchedStep) atTop (𝓝 0) ∧
      ∀ᶠ d in atTop, ∀ k : ℕ,
        |slowEnergy (P d).matchedDelta ((P d).matchedMoments ((P d).trajectory (s d) k))-
          (P d).windowSlow (s d) ((k : ℝ)*(P d).matchedStep)| ≤
          C*(P d).matchedStep*((P d).comparisonInitialSize (s d)+(P d).renormAdditive) ∧
        ‖oscillatoryEnergy (P d).matchedDelta (oscillatoryRoot (Real.sqrt ((P d).matchedDelta-1/4)))
          ((P d).matchedMoments ((P d).trajectory (s d) k))-
          (P d).windowOsc (s d) ((k : ℝ)*(P d).matchedStep)‖ ≤
          C*(P d).matchedStep*((P d).comparisonInitialSize (s d)+(P d).renormAdditive) := by
  let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
  let w := etaStar*epsStar*pStar
  have hw0 : 0 < w := by dsimp [w]; positivity
  have halg := actualLSFamily_algebra pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp hb he hg heta hpd
  have hbeta := actualLSParams_beta_tendsto_one pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hg
  have hwlim := actualLSFamily_w_tendsto_critical pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp he heta hpd hw
  obtain ⟨hnoise,_⟩ := actualLSFamily_load_limits pStar kappa bStar sigma epsStar gamma etaStar alpha u p ν hp hk hb hs heta hpd hcell
  have H := (ls_curvature_cells_parameters pStar kappa bStar sigma epsStar gamma etaStar alpha u margin p ν hp hk hb hs he hg heta hpd hw hcell hw4 hm hum hnyq).1
  have hb1 : ∀ᶠ d in atTop, (P d).beta<1 := halg.mono (fun _ hd => hd.2.1)
  have hn0 : ∀ᶠ d in atTop, 0 ≤ (P d).noise := halg.mono (fun _ hd => hd.2.2.2.2.2.1)
  obtain ⟨C,hC,HC⟩ := curvature_window_comparison P s w u margin jury hbeta hwlim hnoise hw0 hw4 hm hb1 hn0 (H.mono (fun _ hd => hd.2)) hsPSD hum hnyq
  refine ⟨C,hC,by simpa using (curvature_matchedStep_tendsto P hbeta).const_mul C,?_⟩
  filter_upwards [HC] with d hd
  exact fun k => ⟨(hd k).1,(hd k).2.1⟩

end
end SparseSGD.Scaling
