import SparseSGD.Scaling.LSFamily
import SparseSGD.Scaling.LearningLimit

open Filter Topology MeasureTheory
namespace SparseSGD.Scaling
noncomputable section
set_option maxHeartbeats 1200000

/-- Actual integer-batch LS families in cells 1 and 2 converge uniformly at all
learning-clock grid points. The exponent alternatives determine whether noise
survives, and the curve's forcing is the actual label variance. -/
theorem ls_learning_cells_uniform
    (pStar kappa bStar sigma epsStar gamma etaStar alpha R u : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (jury : External.JuryStability)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (hb : 0 < bStar) (hs : 0 < sigma)
    (he : 0 < epsStar) (hg : 0 < gamma) (heta : 0 < etaStar)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hD : gamma-alpha-kappa < 0)
    (hcell : (1-sigma-alpha < 0 ∧ u=0) ∨
      (1-sigma-alpha=0 ∧ u=etaStar/(2*bStar)))
    (hR : 0 ≤ R) (hu1 : u < 1) :
    ∀ e > 0, ∀ᶠ d in atTop, ∀ k : ℕ,
      let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d
      |(P.trajectory ⟨R,0,0⟩ k).R-
        learningProfile u (SparseSGD.Probability.LeastSquares.labelVariance ν*u) R
          ((k : ℝ)*(P.w/P.eps))| < e := by
  let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
  let variance := SparseSGD.Probability.LeastSquares.labelVariance ν
  let Delta := lsDelta pStar etaStar epsStar kappa gamma alpha
  have hvar : 0 ≤ variance := labelVariance_nonneg ν
  have hu0 : 0 ≤ u := by
    rcases hcell with ⟨_,hu⟩ | ⟨_,hu⟩
    · rw [hu]
    · rw [hu]; positivity
  have hnoise : Tendsto (lsNoiseLoad pStar kappa etaStar alpha bStar sigma) atTop (𝓝 u) := by
    rcases hcell with ⟨hneg,hu⟩ | ⟨hzero,hu⟩
    · rw [hu]
      exact lsNoiseLoad_tendsto_zero pStar kappa etaStar alpha bStar sigma hp hk heta hb hs hneg
    · rw [hu]
      exact lsNoiseLoad_tendsto_critical pStar kappa etaStar alpha bStar sigma hp hk heta hb hs hzero
  have hadd : Tendsto (lsAdditiveLoad etaStar alpha bStar sigma variance) atTop (𝓝 (variance*u)) := by
    rcases hcell with ⟨hneg,hu⟩ | ⟨hzero,hu⟩
    · rw [hu,mul_zero]
      exact lsAdditiveLoad_tendsto_zero etaStar alpha bStar sigma variance heta hb hs hneg
    · rw [hu]
      exact lsAdditiveLoad_tendsto_critical etaStar alpha bStar sigma variance heta hb hs hzero
  have hactual : ∀ᶠ d in atTop, P d=lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar alpha variance d := by
    filter_upwards [hpd,eventually_gt_atTop (0 : ℕ)] with d hd hd0
    have hp0 : (p d : ℝ) ≠ 0 := by rw [hd]; exact (scaledSparsity_pos_of_pos pStar kappa d hp hd0).ne'
    exact actualLSParams_eq_lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d hp0 hd
  have hnoiseA : Tendsto (fun d => (P d).noise) atTop (𝓝 u) := by
    apply hnoise.congr'
    filter_upwards [hactual] with d hd
    rw [hd]
    rfl
  have haddA : Tendsto (fun d => (P d).additive) atTop (𝓝 (variance*u)) := by
    apply hadd.congr'
    filter_upwards [hactual] with d hd
    rw [hd]
    rfl
  have hcurv : Tendsto (fun d => (P d).curvature) atTop (𝓝 0) :=
    actualLSParams_curvature_tendsto_zero pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
      hp he heta hg hpd (by linarith)
  have hnu : Tendsto (fun d => (P d).renormNoise) atTop (𝓝 u) := renorm_load_tendsto _ _ u hnoiseA hcurv
  have hphi : Tendsto (fun d => (P d).renormAdditive) atTop (𝓝 (variance*u)) :=
    renorm_load_tendsto _ _ (variance*u) haddA hcurv
  have hDelta : Tendsto Delta atTop (𝓝 0) := lsDelta_tendsto_zero pStar etaStar epsStar kappa gamma alpha hp heta he hD
  have halg := actualLSFamily_algebra pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp hb he hg heta hpd
  have hvalid : ∀ᶠ d in atTop, 1/2 ≤ (P d).beta ∧ (P d).beta < 1 ∧
      0 < Delta d ∧ (P d).w=Delta d*(P d).eps^2 ∧
      0 ≤ (P d).renormNoise ∧ 0 ≤ (P d).renormAdditive := by
    filter_upwards [halg,hcurv.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))] with d hd hc
    obtain ⟨hb0,hb1,_,hdp,hw,hn,ha⟩ := hd
    obtain ⟨hnu0,hph0⟩ := renorm_nonneg_of_curvature_lt_one (P d) hn ha hc
    exact ⟨hb0,hb1,hdp,hw,hnu0,hph0⟩
  exact learning_chain_uniform_convergence P Delta R u (variance*u) jury hR hu0 hu1
    (mul_nonneg hvar hu0) hvalid hDelta hnu hphi

/-- Cell 1 has the pure gradient-flow risk profile. -/
theorem learningProfile_zero_loads (R t : ℝ) : learningProfile 0 0 R t=R*Real.exp (-2*t) := by
  simp [learningProfile]

end
end SparseSGD.Scaling
