import SparseSGD.Scaling.PowerParameters
import SparseSGD.Scaling.LeastSquaresParameters

open Filter Topology
namespace SparseSGD.Scaling
noncomputable section

theorem powerScale_tendsto_zero (c e : ℝ) (hc : 0 < c) (he : e < 0) :
    Tendsto (fun d : ℕ => c*(d:ℝ)^e) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (neg_pos.mpr he)).comp tendsto_natCast_atTop_atTop
  simpa using h.const_mul c

theorem powerScale_tendsto_const (c : ℝ) :
    Tendsto (fun d : ℕ => c*(d:ℝ)^(0:ℝ)) atTop (𝓝 c) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  simp [Real.rpow_zero]

theorem powerScale_tendsto_atTop (c e : ℝ) (hc : 0 < c) (he : 0 < e) :
    Tendsto (fun d : ℕ => c*(d:ℝ)^e) atTop atTop := by
  have h := (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  exact h.const_mul_atTop hc

theorem tendsto_product_zero {f g : ℕ → ℝ} {a : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun d => (f d)*(g d)) atTop (𝓝 0) := by
  simpa using hf.mul hg

theorem product_limit_congr {f g h : ℕ → ℝ} {u v : ℝ}
    (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 v))
    (heq : (fun d => f d*g d) =ᶠ[atTop] h) :
    Tendsto h atTop (𝓝 (u*v)) := by
  exact (hf.mul hg).congr' heq

theorem product_atTop_congr {f g h : ℕ → ℝ} {c : ℝ}
    (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop (𝓝 c)) (hc : 0 < c)
    (heq : (fun d => f d*g d) =ᶠ[atTop] h) :
    Tendsto h atTop atTop := by
  exact (hf.atTop_mul_pos hc hg).congr' heq


theorem product_to_zero {q scale load : ℕ → ℝ} {q0 : ℝ}
    (hq : Tendsto q atTop (𝓝 q0)) (hs : Tendsto scale atTop (𝓝 0))
    (heq : (fun d => q d*scale d) =ᶠ[atTop] load) :
    Tendsto load atTop (𝓝 0) := by
  simpa using (hq.mul hs).congr' heq

theorem product_to_finite {q scale load : ℕ → ℝ} {q0 c : ℝ}
    (hq : Tendsto q atTop (𝓝 q0)) (hs : Tendsto scale atTop (𝓝 c))
    (heq : (fun d => q d*scale d) =ᶠ[atTop] load) :
    Tendsto load atTop (𝓝 (q0*c)) :=
  (hq.mul hs).congr' heq

theorem product_to_atTop {q scale load : ℕ → ℝ} {q0 : ℝ}
    (hq : Tendsto q atTop (𝓝 q0)) (hq0 : 0 < q0)
    (hs : Tendsto scale atTop atTop)
    (heq : (fun d => q d*scale d) =ᶠ[atTop] load) :
    Tendsto load atTop atTop := by
  have hqpos : ∀ᶠ d : ℕ in atTop, 0 < q d := by
    filter_upwards [hq.eventually (Ioi_mem_nhds hq0)] with d hd
    exact hd
  have hprod : Tendsto (fun d => scale d*q d) atTop atTop := hs.atTop_mul_pos hq0 hq
  have heq' : (fun d => scale d*q d) =ᶠ[atTop] load := by
    filter_upwards [heq] with d hd
    simpa [mul_comm] using hd
  exact hprod.congr' heq'

theorem lsNoiseLoad_tendsto_zero
    (pStar kappa etaStar alpha bStar sigma : ℝ)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (heta : 0 < etaStar)
    (hb : 0 < bStar) (hs : 0 < sigma) (hexp : 1-sigma-alpha < 0) :
    Tendsto (fun d => lsNoiseLoad pStar kappa etaStar alpha bStar sigma d) atTop (𝓝 0) := by
  let c := etaStar/(2*bStar)
  let q := fun d : ℕ => lsNoiseLoad pStar kappa etaStar alpha bStar sigma d /
    (c*(d:ℝ)^(1-sigma-alpha))
  let scale := fun d : ℕ => c*(d:ℝ)^(1-sigma-alpha)
  have hc : 0 < c := by dsimp [c]; positivity
  have hq : Tendsto q atTop (𝓝 1) := by
    simpa [q,c] using lsNoise_power_ratio_tendsto pStar kappa etaStar alpha bStar sigma hp hk heta hb hs
  have hscale := powerScale_tendsto_zero c (1-sigma-alpha) hc hexp
  have heq : (fun d => q d*scale d) =ᶠ[atTop] fun d => lsNoiseLoad pStar kappa etaStar alpha bStar sigma d := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    have hdR : (0:ℝ)<d := by exact_mod_cast hd
    have hscalePos : 0 < scale d := by dsimp [scale]; exact mul_pos hc (Real.rpow_pos_of_pos hdR _)
    dsimp [q,scale]
    rw [div_mul_cancel₀ _ hscalePos.ne']
  exact product_to_zero hq hscale heq

theorem lsNoiseLoad_tendsto_critical
    (pStar kappa etaStar alpha bStar sigma : ℝ)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (heta : 0 < etaStar)
    (hb : 0 < bStar) (hs : 0 < sigma) (hexp : 1-sigma-alpha = 0) :
    Tendsto (fun d => lsNoiseLoad pStar kappa etaStar alpha bStar sigma d) atTop (𝓝 (etaStar/(2*bStar))) := by
  let c := etaStar/(2*bStar)
  let q := fun d : ℕ => lsNoiseLoad pStar kappa etaStar alpha bStar sigma d /
    (c*(d:ℝ)^(1-sigma-alpha))
  let scale := fun d : ℕ => c*(d:ℝ)^(1-sigma-alpha)
  have hc : 0 < c := by dsimp [c]; positivity
  have hq : Tendsto q atTop (𝓝 1) := by
    simpa [q,c] using lsNoise_power_ratio_tendsto pStar kappa etaStar alpha bStar sigma hp hk heta hb hs
  have hscale : Tendsto scale atTop (𝓝 c) := by
    simpa [scale,hexp] using powerScale_tendsto_const c
  have heq : (fun d => q d*scale d) =ᶠ[atTop] fun d => lsNoiseLoad pStar kappa etaStar alpha bStar sigma d := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    have hdR : (0:ℝ)<d := by exact_mod_cast hd
    have hscalePos : 0 < scale d := by dsimp [scale]; exact mul_pos hc (Real.rpow_pos_of_pos hdR _)
    dsimp [q,scale]
    rw [div_mul_cancel₀ _ hscalePos.ne']
  simpa [c] using product_to_finite hq hscale heq

theorem lsNoiseLoad_tendsto_atTop
    (pStar kappa etaStar alpha bStar sigma : ℝ)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (heta : 0 < etaStar)
    (hb : 0 < bStar) (hs : 0 < sigma) (hexp : 0 < 1-sigma-alpha) :
    Tendsto (fun d => lsNoiseLoad pStar kappa etaStar alpha bStar sigma d) atTop atTop := by
  let c := etaStar/(2*bStar)
  let q := fun d : ℕ => lsNoiseLoad pStar kappa etaStar alpha bStar sigma d /
    (c*(d:ℝ)^(1-sigma-alpha))
  let scale := fun d : ℕ => c*(d:ℝ)^(1-sigma-alpha)
  have hc : 0 < c := by dsimp [c]; positivity
  have hq : Tendsto q atTop (𝓝 1) := by
    simpa [q,c] using lsNoise_power_ratio_tendsto pStar kappa etaStar alpha bStar sigma hp hk heta hb hs
  have hscale := powerScale_tendsto_atTop c (1-sigma-alpha) hc hexp
  have heq : (fun d => q d*scale d) =ᶠ[atTop] fun d => lsNoiseLoad pStar kappa etaStar alpha bStar sigma d := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    have hdR : (0:ℝ)<d := by exact_mod_cast hd
    have hscalePos : 0 < scale d := by dsimp [scale]; exact mul_pos hc (Real.rpow_pos_of_pos hdR _)
    dsimp [q,scale]
    rw [div_mul_cancel₀ _ hscalePos.ne']
  exact product_to_atTop hq (by norm_num) hscale heq


theorem lsAdditiveLoad_tendsto_zero
    (etaStar alpha bStar sigma variance : ℝ)
    (heta : 0 < etaStar) (hb : 0 < bStar) (hs : 0 < sigma) (hexp : 1-sigma-alpha < 0) :
    Tendsto (fun d => lsAdditiveLoad etaStar alpha bStar sigma variance d) atTop (𝓝 0) := by
  let c := etaStar/(2*bStar)
  let q := fun d : ℕ => lsAdditiveLoad etaStar alpha bStar sigma variance d /
    (c*(d:ℝ)^(1-sigma-alpha))
  let scale := fun d : ℕ => c*(d:ℝ)^(1-sigma-alpha)
  have hc : 0 < c := by dsimp [c]; positivity
  have hq : Tendsto q atTop (𝓝 variance) := by
    simpa [q,c] using lsAdditive_power_ratio_tendsto etaStar alpha bStar sigma variance heta hb hs
  have hscale := powerScale_tendsto_zero c (1-sigma-alpha) hc hexp
  have heq : (fun d => q d*scale d) =ᶠ[atTop] fun d => lsAdditiveLoad etaStar alpha bStar sigma variance d := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    have hdR : (0:ℝ)<d := by exact_mod_cast hd
    have hscalePos : 0 < scale d := by dsimp [scale]; exact mul_pos hc (Real.rpow_pos_of_pos hdR _)
    dsimp [q,scale]
    rw [div_mul_cancel₀ _ hscalePos.ne']
  exact product_to_zero hq hscale heq

theorem lsAdditiveLoad_tendsto_critical
    (etaStar alpha bStar sigma variance : ℝ)
    (heta : 0 < etaStar) (hb : 0 < bStar) (hs : 0 < sigma) (hexp : 1-sigma-alpha = 0) :
    Tendsto (fun d => lsAdditiveLoad etaStar alpha bStar sigma variance d) atTop
      (𝓝 (variance*(etaStar/(2*bStar)))) := by
  let c := etaStar/(2*bStar)
  let q := fun d : ℕ => lsAdditiveLoad etaStar alpha bStar sigma variance d /
    (c*(d:ℝ)^(1-sigma-alpha))
  let scale := fun d : ℕ => c*(d:ℝ)^(1-sigma-alpha)
  have hc : 0 < c := by dsimp [c]; positivity
  have hq : Tendsto q atTop (𝓝 variance) := by
    simpa [q,c] using lsAdditive_power_ratio_tendsto etaStar alpha bStar sigma variance heta hb hs
  have hscale : Tendsto scale atTop (𝓝 c) := by
    simpa [scale,hexp] using powerScale_tendsto_const c
  have heq : (fun d => q d*scale d) =ᶠ[atTop] fun d => lsAdditiveLoad etaStar alpha bStar sigma variance d := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    have hdR : (0:ℝ)<d := by exact_mod_cast hd
    have hscalePos : 0 < scale d := by dsimp [scale]; exact mul_pos hc (Real.rpow_pos_of_pos hdR _)
    dsimp [q,scale]
    rw [div_mul_cancel₀ _ hscalePos.ne']
  simpa [c] using product_to_finite hq hscale heq

theorem lsAdditiveLoad_tendsto_atTop
    (etaStar alpha bStar sigma variance : ℝ)
    (heta : 0 < etaStar) (hb : 0 < bStar) (hs : 0 < sigma) (hvar : 0 < variance)
    (hexp : 0 < 1-sigma-alpha) :
    Tendsto (fun d => lsAdditiveLoad etaStar alpha bStar sigma variance d) atTop atTop := by
  let c := etaStar/(2*bStar)
  let q := fun d : ℕ => lsAdditiveLoad etaStar alpha bStar sigma variance d /
    (c*(d:ℝ)^(1-sigma-alpha))
  let scale := fun d : ℕ => c*(d:ℝ)^(1-sigma-alpha)
  have hc : 0 < c := by dsimp [c]; positivity
  have hq : Tendsto q atTop (𝓝 variance) := by
    simpa [q,c] using lsAdditive_power_ratio_tendsto etaStar alpha bStar sigma variance heta hb hs
  have hscale := powerScale_tendsto_atTop c (1-sigma-alpha) hc hexp
  have heq : (fun d => q d*scale d) =ᶠ[atTop] fun d => lsAdditiveLoad etaStar alpha bStar sigma variance d := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    have hdR : (0:ℝ)<d := by exact_mod_cast hd
    have hscalePos : 0 < scale d := by dsimp [scale]; exact mul_pos hc (Real.rpow_pos_of_pos hdR _)
    dsimp [q,scale]
    rw [div_mul_cancel₀ _ hscalePos.ne']
  exact product_to_atTop hq hvar hscale heq


theorem actualLSParams_curvature_tendsto_zero
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : MeasureTheory.Measure ℝ)
    (hp : 0 < pStar) (heps : 0 < epsStar) (heta : 0 < etaStar) (hg : 0 < gamma)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d : ℝ) = scaledSparsity pStar kappa d)
    (hexp : -(alpha+gamma+kappa) < 0) :
    Tendsto (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).curvature)
      atTop (𝓝 0) := by
  let c := etaStar*epsStar*pStar
  let q := fun d : ℕ => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).curvature /
      (c*(d:ℝ)^(-(alpha+gamma+kappa)))
  let scale := fun d : ℕ => c*(d:ℝ)^(-(alpha+gamma+kappa))
  have hc : 0 < c := by dsimp [c]; positivity
  have hq : Tendsto q atTop (𝓝 (1/4)) := by
    simpa [q,c] using actualLSParams_curvature_ratio_tendsto pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp heta.ne' heps.ne' hg hpd
  have hscale := powerScale_tendsto_zero c (-(alpha+gamma+kappa)) hc hexp
  have heq : (fun d => q d*scale d) =ᶠ[atTop]
      fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).curvature := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    have hdR : (0:ℝ)<d := by exact_mod_cast hd
    have hscalePos : 0 < scale d := by dsimp [scale]; exact mul_pos hc (Real.rpow_pos_of_pos hdR _)
    dsimp [q,scale]
    rw [div_mul_cancel₀ _ hscalePos.ne']
  exact product_to_zero hq hscale heq

theorem actualLSParams_curvature_tendsto_critical
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : MeasureTheory.Measure ℝ)
    (hp : 0 < pStar) (heps : 0 < epsStar) (heta : 0 < etaStar) (hg : 0 < gamma)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d : ℝ) = scaledSparsity pStar kappa d)
    (hexp : -(alpha+gamma+kappa) = 0) :
    Tendsto (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).curvature)
      atTop (𝓝 (etaStar*epsStar*pStar/4)) := by
  let c := etaStar*epsStar*pStar
  let q := fun d : ℕ => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).curvature /
      (c*(d:ℝ)^(-(alpha+gamma+kappa)))
  let scale := fun d : ℕ => c*(d:ℝ)^(-(alpha+gamma+kappa))
  have hc : 0 < c := by dsimp [c]; positivity
  have hq : Tendsto q atTop (𝓝 (1/4)) := by
    simpa [q,c] using actualLSParams_curvature_ratio_tendsto pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp heta.ne' heps.ne' hg hpd
  have hscale : Tendsto scale atTop (𝓝 c) := by
    simpa [scale,hexp] using powerScale_tendsto_const c
  have heq : (fun d => q d*scale d) =ᶠ[atTop]
      fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).curvature := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    have hdR : (0:ℝ)<d := by exact_mod_cast hd
    have hscalePos : 0 < scale d := by dsimp [scale]; exact mul_pos hc (Real.rpow_pos_of_pos hdR _)
    dsimp [q,scale]
    rw [div_mul_cancel₀ _ hscalePos.ne']
  have H := product_to_finite hq hscale heq
  have hlim : (4:ℝ)⁻¹*c = etaStar*epsStar*pStar/4 := by dsimp [c]; ring
  simpa [hlim] using H

theorem actualLSParams_curvature_tendsto_atTop
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : MeasureTheory.Measure ℝ)
    (hp : 0 < pStar) (heps : 0 < epsStar) (heta : 0 < etaStar) (hg : 0 < gamma)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d : ℝ) = scaledSparsity pStar kappa d)
    (hexp : 0 < -(alpha+gamma+kappa)) :
    Tendsto (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).curvature)
      atTop atTop := by
  let c := etaStar*epsStar*pStar
  let q := fun d : ℕ => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).curvature /
      (c*(d:ℝ)^(-(alpha+gamma+kappa)))
  let scale := fun d : ℕ => c*(d:ℝ)^(-(alpha+gamma+kappa))
  have hc : 0 < c := by dsimp [c]; positivity
  have hq : Tendsto q atTop (𝓝 (1/4)) := by
    simpa [q,c] using actualLSParams_curvature_ratio_tendsto pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp heta.ne' heps.ne' hg hpd
  have hscale := powerScale_tendsto_atTop c (-(alpha+gamma+kappa)) hc hexp
  have heq : (fun d => q d*scale d) =ᶠ[atTop]
      fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).curvature := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    have hdR : (0:ℝ)<d := by exact_mod_cast hd
    have hscalePos : 0 < scale d := by dsimp [scale]; exact mul_pos hc (Real.rpow_pos_of_pos hdR _)
    dsimp [q,scale]
    rw [div_mul_cancel₀ _ hscalePos.ne']
  exact product_to_atTop hq (by norm_num) hscale heq

end
end SparseSGD.Scaling
