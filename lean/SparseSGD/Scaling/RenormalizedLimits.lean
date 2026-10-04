import SparseSGD.Scaling.LeastSquaresParameters

open Filter Topology

namespace SparseSGD.Scaling
noncomputable section

theorem renorm_load_difference_bound (load curvature target : ℝ)
    (hc0 : 0 ≤ curvature) (hc1 : curvature ≤ 1/2) :
    abs (load/(1-curvature)-target) ≤ 2 * (|load-target|) + 2 * (|target|) * curvature := by
  have hden : 0 < 1-curvature := by linarith
  have hden2 : 1/2 ≤ 1-curvature := by linarith
  have hid : load/(1-curvature)-target =
      (load-target)/(1-curvature)+target*curvature/(1-curvature) := by field_simp; ring
  rw [hid]
  calc
    |(load-target)/(1-curvature)+target*curvature/(1-curvature)| ≤
        |(load-target)/(1-curvature)|+|target*curvature/(1-curvature)| := abs_add_le _ _
    _ ≤ 2 * (|load-target|) + 2 * (|target|) * curvature := by
      rw [abs_div, abs_of_pos hden, abs_div, abs_of_pos hden, abs_mul, abs_of_nonneg hc0]
      have hfirst : |load-target|/(1-curvature) ≤ 2 * |load-target| := by
        exact div_le_iff₀ hden |>.2 (by nlinarith [abs_nonneg (load-target)])
      have hsecond : (|target| * curvature)/(1-curvature) ≤ 2 * |target| * curvature := by
        calc
          _ ≤ (|target| * curvature)/(1/2) := div_le_div_of_nonneg_left
            (mul_nonneg (abs_nonneg _) hc0) (by norm_num) hden2
          _ = 2 * |target| * curvature := by ring
      nlinarith [hfirst,hsecond]

theorem renorm_load_tendsto
    (load curvature : ℕ → ℝ) (u : ℝ)
    (hload : Tendsto load atTop (𝓝 u))
    (hcurv : Tendsto curvature atTop (𝓝 0)) :
    Tendsto (fun d => load d/(1-curvature d)) atTop (𝓝 u) := by
  have hden : Tendsto (fun d => 1-curvature d) atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub hcurv
  have h := hload.div hden (by norm_num : (1:ℝ) ≠ 0)
  have h' : Tendsto (fun d => load d / (1-curvature d)) atTop (𝓝 (u/1)) := by
    apply h.congr'
    filter_upwards with d
    rfl
  simpa only [div_one] using h'

theorem actualLSParams_renormNoise_tendsto
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : MeasureTheory.Measure ℝ) (u : ℝ)
    (hnoise : Tendsto (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).noise) atTop (𝓝 u))
    (hcurv : Tendsto (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).curvature) atTop (𝓝 0)) :
    Tendsto (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).renormNoise) atTop (𝓝 u) := by
  exact renorm_load_tendsto _ _ u hnoise hcurv

theorem actualLSParams_renormAdditive_tendsto
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : MeasureTheory.Measure ℝ) (u : ℝ)
    (hadd : Tendsto (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).additive) atTop (𝓝 u))
    (hcurv : Tendsto (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).curvature) atTop (𝓝 0)) :
    Tendsto (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).renormAdditive) atTop (𝓝 u) := by
  exact renorm_load_tendsto _ _ u hadd hcurv

end
end SparseSGD.Scaling
