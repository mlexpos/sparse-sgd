import SparseSGD.Scaling.LSLearningFamily
import SparseSGD.Scaling.CurvatureWindow
import SparseSGD.Scaling.MatchingLimits

open Filter Topology MeasureTheory
namespace SparseSGD.Scaling
noncomputable section
set_option maxHeartbeats 1200000

/-- Actual noise and forcing limits, including the fixed integer batch edge. -/
theorem actualLSFamily_load_limits
    (pStar kappa bStar sigma epsStar gamma etaStar alpha u : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (hb : 0 < bStar) (hs : 0 ≤ sigma)
    (heta : 0 < etaStar)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hcell : (1-sigma-alpha<0 ∧ u=0) ∨
      (1-sigma-alpha=0 ∧ u=etaStar/(2*realizedBatchScale bStar sigma))) :
    let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
    Tendsto (fun d => (P d).noise) atTop (𝓝 u) ∧
    Tendsto (fun d => (P d).additive) atTop
      (𝓝 (SparseSGD.Probability.LeastSquares.labelVariance ν*u)) := by
  let variance := SparseSGD.Probability.LeastSquares.labelVariance ν
  have heq : ∀ᶠ d in atTop,
      actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d=
        lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar alpha variance d := by
    filter_upwards [hpd,eventually_gt_atTop (0 : ℕ)] with d hd hd0
    have hp0 : (p d : ℝ) ≠ 0 := by rw [hd]; exact (scaledSparsity_pos_of_pos pStar kappa d hp hd0).ne'
    exact actualLSParams_eq_lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d hp0 hd
  obtain ⟨hn,ha⟩ := ls_power_load_limits pStar kappa etaStar alpha bStar sigma variance u hp hk heta hb hs hcell
  constructor
  · apply hn.congr'
    filter_upwards [heq] with d hd
    rw [hd]
    rfl
  · apply ha.congr'
    filter_upwards [heq] with d hd
    rw [hd]
    rfl

/-- The realized curvature parameter has its exact power-law constant. -/
theorem actualLSFamily_w_power
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (hp : 0 < pStar) (he : 0 < epsStar) (heta : 0 < etaStar)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d) :
    ∀ᶠ d in atTop,
      (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).w=
        etaStar*epsStar*pStar*(d : ℝ)^(-(alpha+gamma+kappa)) := by
  filter_upwards [hpd,eventually_gt_atTop (0 : ℕ)] with d hd hd0
  have hp0 : (p d : ℝ) ≠ 0 := by rw [hd]; exact (scaledSparsity_pos_of_pos pStar kappa d hp hd0).ne'
  rw [actualLSParams_eq_lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d hp0 hd]
  change lsCurvature pStar etaStar epsStar kappa gamma alpha d=_
  apply (div_eq_one_iff_eq (by positivity : etaStar*epsStar*pStar*(d : ℝ)^(-(alpha+gamma+kappa)) ≠ 0)).mp
  exact lsCurvature_power_ratio pStar etaStar epsStar kappa gamma alpha d hd0 hp.ne' heta.ne' he.ne'

/-- The actual curvature tends to zero in the small-curvature cells. -/
theorem actualLSFamily_w_tendsto_zero
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (hp : 0 < pStar) (he : 0 < epsStar) (heta : 0 < etaStar)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hw : -(alpha+gamma+kappa)<0) :
    Tendsto (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).w)
      atTop (𝓝 0) :=
  (powerScale_tendsto_zero (etaStar*epsStar*pStar) _ (by positivity) hw).congr'
    ((actualLSFamily_w_power pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp he heta hpd).mono (fun _ H => H.symm))

/-- At the curvature ceiling the actual value is eventually the critical constant. -/
theorem actualLSFamily_w_tendsto_critical
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (hp : 0 < pStar) (he : 0 < epsStar) (heta : 0 < etaStar)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hw : -(alpha+gamma+kappa)=0) :
    Tendsto (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).w)
      atTop (𝓝 (etaStar*epsStar*pStar)) := by
  have H := actualLSFamily_w_power pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp he heta hpd
  simp only [hw,Real.rpow_zero,mul_one] at H
  exact tendsto_const_nhds.congr' (H.mono (fun _ H => H.symm))

/-- Positive raw-curvature exponent gives divergence, without ignoring integer batches. -/
theorem lsDelta_tendsto_atTop
    (pStar etaStar epsStar kappa gamma alpha : ℝ)
    (hp : 0 < pStar) (heta : 0 < etaStar) (he : 0 < epsStar)
    (hD : 0 < gamma-alpha-kappa) :
    Tendsto (lsDelta pStar etaStar epsStar kappa gamma alpha) atTop atTop := by
  apply (powerScale_tendsto_atTop (etaStar*pStar/epsStar) _ (by positivity) hD).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  symm
  apply (div_eq_one_iff_eq (by positivity : (etaStar*pStar/epsStar)*(d : ℝ)^(gamma-alpha-kappa) ≠ 0)).mp
  exact lsDelta_power_ratio pStar etaStar epsStar kappa gamma alpha d hd hp.ne' heta.ne' he.ne'

end
end SparseSGD.Scaling
