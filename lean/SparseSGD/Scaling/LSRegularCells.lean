import SparseSGD.Scaling.LSLearningFamily
import SparseSGD.Scaling.Resonance

open Filter Topology MeasureTheory
namespace SparseSGD.Scaling
noncomputable section
set_option maxHeartbeats 1200000

/-- The actual LS family in regular cells 3 and 4, for every admissible
integer batch exponent, converges uniformly over all minibatch steps. -/
theorem ls_regular_cells_all_batches
    (pStar kappa bStar sigma epsStar gamma etaStar alpha R u : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (jury : External.JuryStability)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (hb : 0 < bStar) (hs : 0 ≤ sigma)
    (he : 0 < epsStar) (hg : 0 < gamma) (heta : 0 < etaStar)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hD : gamma-alpha-kappa=0)
    (hcell : (1-sigma-alpha<0 ∧ u=0) ∨
      (1-sigma-alpha=0 ∧ u=etaStar/(2*realizedBatchScale bStar sigma)))
    (hR : 0 ≤ R) (hu1 : u < 1) :
    ∀ e > 0, ∀ᶠ d in atTop, ∀ k : ℕ,
      let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d
      |(P.trajectory ⟨R,0,0⟩ k).R-
        (continuumFlow (etaStar*pStar/epsStar) u
          (SparseSGD.Probability.LeastSquares.labelVariance ν*u)
          ⟨R,0,0⟩ ((k : ℝ)*P.matchedStep)).R| < e := by
  let D := etaStar*pStar/epsStar
  let variance := SparseSGD.Probability.LeastSquares.labelVariance ν
  let phi := variance*u
  let margin := (1-u)/2
  let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
  have hDp : 0 < D := by dsimp [D]; positivity
  have hu0 : 0 ≤ u := by
    rcases hcell with ⟨_,hu⟩ | ⟨_,hu⟩
    · rw [hu]
    · rw [hu]
      exact (div_pos heta (mul_pos (by norm_num) (realizedBatchScale_pos bStar sigma hb))).le
  have hvar : 0 ≤ variance := labelVariance_nonneg ν
  have hphi : 0 ≤ phi := mul_nonneg hvar hu0
  have hm : 0 < margin := by dsimp [margin]; linarith
  have huM : u < 1-margin := by dsimp [margin]; linarith
  obtain ⟨eps0,heps0,A,hA,Hmain⟩ := regular_cold_raw_rate D margin hDp hm
  have heps := scaledRetention_tendsto_zero epsStar gamma hg
  have halg := actualLSFamily_algebra pStar kappa bStar sigma epsStar gamma etaStar alpha
    p ν hp hb he hg heta hpd
  have htuple : ∀ᶠ d in atTop, P d=lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar alpha variance d := by
    filter_upwards [hpd,eventually_gt_atTop (0 : ℕ)] with d hd hd0
    have hp0 : (p d : ℝ) ≠ 0 := by rw [hd]; exact (scaledSparsity_pos_of_pos pStar kappa d hp hd0).ne'
    exact actualLSParams_eq_lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d hp0 hd
  obtain ⟨hnoiseRaw,haddRaw⟩ := ls_power_load_limits pStar kappa etaStar alpha bStar sigma variance u hp hk heta hb hs hcell
  have hnoise : Tendsto (fun d => (P d).noise) atTop (𝓝 u) := by
    apply hnoiseRaw.congr'
    filter_upwards [htuple] with d hd
    rw [hd]
    rfl
  have hadd : Tendsto (fun d => (P d).additive) atTop (𝓝 phi) := by
    apply haddRaw.congr'
    filter_upwards [htuple] with d hd
    rw [hd]
    rfl
  have hcurv : Tendsto (fun d => (P d).curvature) atTop (𝓝 0) :=
    actualLSParams_curvature_tendsto_zero pStar kappa bStar sigma epsStar gamma etaStar alpha
      p ν hp he heta hg hpd (by linarith)
  have hnu : Tendsto (fun d => (P d).renormNoise) atTop (𝓝 u) := renorm_load_tendsto _ _ u hnoise hcurv
  have hph : Tendsto (fun d => (P d).renormAdditive) atTop (𝓝 phi) := renorm_load_tendsto _ _ phi hadd hcurv
  have hraw : ∀ᶠ d in atTop, (P d).w=D*(P d).eps^2 ∧ (P d).eps=scaledRetention epsStar gamma d := by
    filter_upwards [halg,eventually_gt_atTop (0 : ℕ)] with d hd hd0
    refine ⟨?_,hd.2.2.1⟩
    rw [hd.2.2.2.2.1,lsDelta_resonant_constant pStar etaStar epsStar kappa gamma alpha hp heta he hD d hd0]
  have hepsP : Tendsto (fun d => (P d).eps) atTop (𝓝 0) := by
    apply heps.congr'
    filter_upwards [hraw] with d hd
    exact hd.2.symm
  have hwlim : Tendsto (fun d => (P d).w) atTop (𝓝 0) := by
    have H : Tendsto (fun d => D*(P d).eps^2) atTop (𝓝 0) := by simpa using (hepsP.pow 2).const_mul D
    apply H.congr'
    filter_upwards [hraw] with d hd
    exact hd.1.symm
  have herr : Tendsto (fun d => A*((P d).eps+|(P d).renormNoise-u|+|(P d).renormAdditive-phi|)*
      (R+(P d).renormAdditive+1)) atTop (𝓝 0) := by
    have Hnu : Tendsto (fun d => |(P d).renormNoise-u|) atTop (𝓝 0) := by simpa using (hnu.sub_const u).abs
    have Hph : Tendsto (fun d => |(P d).renormAdditive-phi|) atTop (𝓝 0) := by simpa using (hph.sub_const phi).abs
    simpa using (((hepsP.add Hnu).add Hph).const_mul A).mul ((hph.const_add R).add_const 1)
  intro e he
  filter_upwards [halg,hraw,hepsP.eventually (eventually_lt_nhds heps0),
    hwlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/16)),
    hcurv.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)),
    hnu.eventually (eventually_lt_nhds huM),herr.eventually (eventually_lt_nhds he)]
    with d halg hraw hepsSmall hwSmall hcSmall hnuSmall herror
  obtain ⟨hb0,hb1,hepsEq,hDelta,hwDelta,hn0,ha0⟩ := halg
  have hepspos := (Params.small_step_bounds (P d) hb0 hb1).1
  have hwpos : 0 < (P d).w := by rw [hraw.1]; positivity
  obtain ⟨hnu0,hph0⟩ := renorm_nonneg_of_curvature_lt_one (P d) hn0 ha0 hcSmall
  intro k
  exact (Hmain (P d) R u phi hb0 hb1 hwpos hwSmall.le hraw.1 hepsSmall.le jury hR
    hnu0 hnuSmall.le hu0 huM.le hph0 k).trans_lt herror

end
end SparseSGD.Scaling
