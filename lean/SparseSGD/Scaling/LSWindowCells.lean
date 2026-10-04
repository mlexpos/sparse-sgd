import SparseSGD.Scaling.LSLoadLimits

open Filter Topology MeasureTheory
namespace SparseSGD.Scaling
noncomputable section
set_option maxHeartbeats 1200000

/-- Actual LS families in cells 5 and 6 satisfy the window hypotheses; the
error factor vanishes and the Nyquist margin follows from vanishing curvature. -/
theorem ls_small_curvature_window_parameters
    (pStar kappa bStar sigma epsStar gamma etaStar alpha u : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (hb : 0 < bStar) (hs : 0 ≤ sigma)
    (he : 0 < epsStar) (hg : 0 < gamma) (heta : 0 < etaStar)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hD : 0 < gamma-alpha-kappa) (hw : -(alpha+gamma+kappa)<0)
    (hcell : (1-sigma-alpha<0 ∧ u=0) ∨
      (1-sigma-alpha=0 ∧ u=etaStar/(2*realizedBatchScale bStar sigma)))
    (hu1 : u < 1) :
    let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
    ∃ margin > 0,
      (∀ᶠ d in atTop, WindowParameters (P d) margin ∧ 0 ≤ (P d).renormAdditive) ∧
      Tendsto (fun d => (P d).matchedStep+1/Real.sqrt (P d).matchedDelta) atTop (𝓝 0) ∧
      Tendsto (fun d => (P d).renormNoise) atTop (𝓝 u) ∧
      Tendsto (fun d => (P d).renormAdditive) atTop
        (𝓝 (SparseSGD.Probability.LeastSquares.labelVariance ν*u)) := by
  let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
  let D := lsDelta pStar etaStar epsStar kappa gamma alpha
  have hu0 : 0 ≤ u := by
    rcases hcell with ⟨_,hu⟩ | ⟨_,hu⟩
    · rw [hu]
    · rw [hu]
      exact (div_pos heta (mul_pos (by norm_num) (realizedBatchScale_pos bStar sigma hb))).le
  let margin := (1-u)/2
  have hm : 0 < margin := by dsimp [margin]; linarith
  have hmhalf : margin ≤ 1/2 := by dsimp [margin]; linarith
  have hum : u < 1-margin := by dsimp [margin]; linarith
  have halg := actualLSFamily_algebra pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp hb he hg heta hpd
  have hbeta := actualLSParams_beta_tendsto_one pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hg
  have heps : Tendsto (fun d => (P d).eps) atTop (𝓝 0) := by
    apply (scaledRetention_tendsto_zero epsStar gamma hg).congr'
    filter_upwards [halg] with d hd
    exact hd.2.2.1.symm
  have hwlim := actualLSFamily_w_tendsto_zero pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp he heta hpd hw
  have hc : Tendsto (fun d => (P d).curvature) atTop (𝓝 0) := by
    simpa using curvature_load_tendsto P 0 hbeta hwlim
  obtain ⟨hnoise,hadd⟩ := actualLSFamily_load_limits pStar kappa bStar sigma epsStar gamma etaStar alpha u p ν hp hk hb hs heta hpd hcell
  have hnu := renorm_load_tendsto _ _ u hnoise hc
  have hph := renorm_load_tendsto _ _ (SparseSGD.Probability.LeastSquares.labelVariance ν*u) hadd hc
  have hbnds : ∀ᶠ d in atTop, 1/2 ≤ (P d).beta ∧ (P d).beta<1 := halg.mono (fun _ hd => ⟨hd.1,hd.2.1⟩)
  have hDpos : ∀ᶠ d in atTop, 0 < D d := halg.mono (fun _ hd => hd.2.2.2.1)
  have hwD : ∀ᶠ d in atTop, (P d).w=D d*(P d).eps^2 := halg.mono (fun _ hd => hd.2.2.2.2.1)
  have hDlim := lsDelta_tendsto_atTop pStar etaStar epsStar kappa gamma alpha hp heta he hD
  have hmatch := small_step_matchedDelta_tendsto_atTop P D hbnds hDpos hDlim hwD hwlim heps
  have hstep := curvature_matchedStep_tendsto P hbeta
  have hinv : Tendsto (fun d => 1/Real.sqrt (P d).matchedDelta) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_div] using tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hmatch)
  have hang : Tendsto (fun d => (P d).foldedAngle) atTop (𝓝 0) := by
    simpa using curvature_foldedAngle_tendsto P 0 hbeta hwlim
  have hangle : 0 < Real.pi/2-margin := by linarith [Real.pi_gt_three]
  refine ⟨margin,hm,?_,by simpa using hstep.add hinv,hnu,hph⟩
  filter_upwards [halg,hc.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)),
    hnu.eventually (eventually_lt_nhds hum),hmatch.eventually_ge_atTop (windowDeltaThreshold margin),
    hang.eventually (eventually_lt_nhds hangle),hwlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))]
    with d hd hc hnu hlarge hang hwsmall
  obtain ⟨hb0,hb1,hepsEq,hDp,hwD,hn,ha⟩ := hd
  have hepsp := (Params.small_step_bounds (P d) hb0 hb1).1
  have hwp : 0 < (P d).w := by rw [hwD]; positivity
  obtain ⟨hn0,ha0⟩ := renorm_nonneg_of_curvature_lt_one (P d) hn ha hc
  exact ⟨⟨hb0,hb1,hwp,by linarith,hn0,hnu.le,hlarge,hang.le⟩,ha0⟩

/-- Cells 5 and 6: all-time two-scale risk approximation for actual integer
batch families. The initial-energy factor is retained explicitly. -/
theorem ls_window_cells_risk
    (pStar kappa bStar sigma epsStar gamma etaStar alpha u : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (jury : External.JuryStability)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (hb : 0 < bStar) (hs : 0 ≤ sigma)
    (he : 0 < epsStar) (hg : 0 < gamma) (heta : 0 < etaStar)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hD : 0 < gamma-alpha-kappa) (hw : -(alpha+gamma+kappa)<0)
    (hcell : (1-sigma-alpha<0 ∧ u=0) ∨
      (1-sigma-alpha=0 ∧ u=etaStar/(2*realizedBatchScale bStar sigma)))
    (hu1 : u < 1) (s : ℕ → Moments) (hsPSD : ∀ d, (s d).psd) :
    let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
    ∃ C ≥ 0,
      Tendsto (fun d => C*((P d).matchedStep+1/Real.sqrt (P d).matchedDelta)) atTop (𝓝 0) ∧
      ∀ᶠ d in atTop, ∀ k : ℕ,
        |((P d).trajectory (s d) k).R-
          ((P d).windowSlow (s d) ((k : ℝ)*(P d).matchedStep)/2+
            ((P d).windowOsc (s d) ((k : ℝ)*(P d).matchedStep)).re/2)| ≤
          C*((P d).matchedStep+1/Real.sqrt (P d).matchedDelta)*
            ((P d).comparisonInitialSize (s d)+(P d).renormAdditive) := by
  let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
  obtain ⟨margin,hm,H,hlim,_,_⟩ := ls_small_curvature_window_parameters pStar kappa bStar sigma epsStar gamma etaStar alpha u p ν hp hk hb hs he hg heta hpd hD hw hcell hu1
  obtain ⟨C,hC,HC⟩ := window_chain_risk_comparison margin hm
  refine ⟨C,hC,by simpa using hlim.const_mul C,?_⟩
  filter_upwards [H] with d hd
  intro k
  exact HC (P d) (s d) hd.1.beta_lower hd.1.beta_upper hd.1.curvature_pos hd.1.curvature_upper
    jury (hsPSD d) hd.1.noise_nonneg hd.1.noise_margin hd.2 hd.1.large hd.1.nyquist k

/-- The actual slow and oscillatory energies in cells 5 and 6. -/
theorem ls_window_cells_energy
    (pStar kappa bStar sigma epsStar gamma etaStar alpha u : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (jury : External.JuryStability)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (hb : 0 < bStar) (hs : 0 ≤ sigma)
    (he : 0 < epsStar) (hg : 0 < gamma) (heta : 0 < etaStar)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hD : 0 < gamma-alpha-kappa) (hw : -(alpha+gamma+kappa)<0)
    (hcell : (1-sigma-alpha<0 ∧ u=0) ∨
      (1-sigma-alpha=0 ∧ u=etaStar/(2*realizedBatchScale bStar sigma)))
    (hu1 : u < 1) (s : ℕ → Moments) (hsPSD : ∀ d, (s d).psd) :
    let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
    ∃ C ≥ 0,
      Tendsto (fun d => C*((P d).matchedStep+1/Real.sqrt (P d).matchedDelta)) atTop (𝓝 0) ∧
      ∀ᶠ d in atTop, ∀ k : ℕ,
        |slowEnergy (P d).matchedDelta ((P d).matchedMoments ((P d).trajectory (s d) k))-
          (P d).windowSlow (s d) ((k : ℝ)*(P d).matchedStep)| ≤
          C*((P d).matchedStep+1/Real.sqrt (P d).matchedDelta)*
            ((P d).comparisonInitialSize (s d)+(P d).renormAdditive) ∧
        ‖oscillatoryEnergy (P d).matchedDelta (oscillatoryRoot (Real.sqrt ((P d).matchedDelta-1/4)))
          ((P d).matchedMoments ((P d).trajectory (s d) k))-
          (P d).windowOsc (s d) ((k : ℝ)*(P d).matchedStep)‖ ≤
          C*((P d).matchedStep+1/Real.sqrt (P d).matchedDelta)*
            ((P d).comparisonInitialSize (s d)+(P d).renormAdditive) := by
  let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
  obtain ⟨margin,hm,H,hlim,_,_⟩ := ls_small_curvature_window_parameters pStar kappa bStar sigma epsStar gamma etaStar alpha u p ν hp hk hb hs he hg heta hpd hD hw hcell hu1
  obtain ⟨C,hC,HC⟩ := window_chain_energy_comparison margin hm
  refine ⟨C,hC,by simpa using hlim.const_mul C,?_⟩
  filter_upwards [H] with d hd
  intro k
  exact HC (P d) (s d) hd.1.beta_lower hd.1.beta_upper hd.1.curvature_pos hd.1.curvature_upper
    jury (hsPSD d) hd.1.noise_nonneg hd.1.noise_margin hd.2 hd.1.large hd.1.nyquist k

end
end SparseSGD.Scaling
