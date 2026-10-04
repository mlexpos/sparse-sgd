import SparseSGD.Scaling.LSWindowCells
import SparseSGD.Scaling.LSCurvatureCells
import SparseSGD.Scaling.ActivityFamily

open Filter Topology MeasureTheory
namespace SparseSGD.Scaling
noncomputable section

/-- The actual window slow profile has the table's per-minibatch envelope rate. -/
theorem windowSlow_excess_grid (P : Params) (s : Moments) (k : ℕ) :
    P.windowSlow s ((k : ℝ)*P.matchedStep)-2*P.renormAdditive/(1-P.renormNoise)=
      (slowEnergy P.matchedDelta (P.matchedMoments s)-2*P.renormAdditive/(1-P.renormNoise))*
        Real.exp (-(P.matchedStep*(1-P.renormNoise))*(k : ℝ)) := by
  unfold Params.windowSlow windowSlowProfile
  have H : (P.renormNoise-1)*((k : ℝ)*P.matchedStep)=
      -(P.matchedStep*(1-P.renormNoise))*(k : ℝ) := by ring
  rw [H]
  ring

/-- The per-step window envelope becomes 1-u on the retention clock. -/
theorem actual_window_rate_ratio
    (pStar kappa bStar sigma epsStar gamma etaStar alpha u : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (he : 0 < epsStar) (hg : 0 < gamma)
    (hnu : Tendsto (fun d =>
      (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).renormNoise) atTop (𝓝 u)) :
    Tendsto (fun d =>
      let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d
      (P.matchedStep*(1-P.renormNoise))/scaledRetention epsStar gamma d) atTop (𝓝 (1-u)) := by
  have H := (actualLSParams_matchedStep_over_retention_tendsto_one
    pStar kappa bStar sigma epsStar gamma etaStar alpha p ν he hg).mul (hnu.const_sub 1)
  simpa only [one_mul,div_mul_eq_mul_div] using H

/-- Counting samples multiplies the step count by the actual integer batch;
this conversion changes its exponent by sigma, including sigma=0. -/
theorem sample_retention_clock_ratio
    (b sigma epsStar gamma : ℝ) (hb : 0 < b) (hs : 0 ≤ sigma) (he : 0 < epsStar) :
    Tendsto (fun d : ℕ => ((scaledBatch b sigma d : ℝ)/scaledRetention epsStar gamma d)/
      ((realizedBatchScale b sigma/epsStar)*(d : ℝ)^(gamma+sigma))) atTop (𝓝 1) := by
  apply (scaledBatch_realized_ratio_tendsto b sigma hb hs).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [div_div]
  congr 1
  unfold scaledRetention
  calc
    realizedBatchScale b sigma*(d : ℝ)^sigma =
        realizedBatchScale b sigma*((d : ℝ)^(-gamma)*(d : ℝ)^(gamma+sigma)) := by
      rw [← Real.rpow_add hdR]
      congr 2
      ring
    _ = _ := by field_simp

/-- Cells 5/6 have the stated actual per-step envelope rates. -/
theorem ls_window_cells_envelope_rate
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
    Tendsto (fun d => ((P d).matchedStep*(1-(P d).renormNoise))/scaledRetention epsStar gamma d)
      atTop (𝓝 (1-u)) := by
  obtain ⟨margin,hm,H,hlim,hnu,hphi⟩ := ls_small_curvature_window_parameters pStar kappa bStar sigma epsStar gamma etaStar alpha u p ν hp hk hb hs he hg heta hpd hD hw hcell hu1
  exact actual_window_rate_ratio pStar kappa bStar sigma epsStar gamma etaStar alpha u p ν he hg hnu

/-- Cells 7/8 use the curvature-renormalized limiting noise in their rate. -/
theorem ls_curvature_cells_envelope_rate
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
    Tendsto (fun d => ((P d).matchedStep*(1-(P d).renormNoise))/scaledRetention epsStar gamma d)
      atTop (𝓝 (1-u/(1-etaStar*epsStar*pStar/4))) := by
  have hnu := (ls_curvature_cells_parameters pStar kappa bStar sigma epsStar gamma etaStar alpha u margin p ν hp hk hb hs he hg heta hpd hw hcell hw4 hm hum hnyq).2.1
  exact actual_window_rate_ratio pStar kappa bStar sigma epsStar gamma etaStar alpha
    (u/(1-etaStar*epsStar*pStar/4)) p ν he hg hnu

/-- The regular limiting Perron rate expressed per actual minibatch step. -/
theorem regular_envelope_rate_retention_ratio
    (pStar kappa bStar sigma epsStar gamma etaStar alpha delta u : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (he : 0 < epsStar) (hg : 0 < gamma) :
    Tendsto (fun d =>
      ((actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).matchedStep*
        continuumPerronRate delta u)/scaledRetention epsStar gamma d)
      atTop (𝓝 (continuumPerronRate delta u)) := by
  simpa only [one_mul,div_mul_eq_mul_div] using
    (actualLSParams_matchedStep_over_retention_tendsto_one
      pStar kappa bStar sigma epsStar gamma etaStar alpha p ν he hg).mul_const
        (continuumPerronRate delta u)

end
end SparseSGD.Scaling
