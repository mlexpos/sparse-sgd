import SparseSGD.Scaling.LSFamily
import SparseSGD.Scaling.LearningLimit

open Filter Topology MeasureTheory
namespace SparseSGD.Scaling
noncomputable section
set_option maxHeartbeats 1200000

/-- Learning-clock convergence with any eventually admissible retention,
including fixed momentum and fixed integer batch size. -/
theorem ls_learning_family_uniform
    (pStar kappa bStar sigma epsStar gamma etaStar alpha R u : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (jury : External.JuryStability)
    (hp : 0 < pStar) (hb : 0 < bStar) (he : 0 < epsStar) (heta : 0 < etaStar)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hret : ∀ᶠ d in atTop, scaledRetention epsStar gamma d ≤ 1/2)
    (hD : gamma-alpha-kappa < 0) (hR : 0 ≤ R) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hnoise : Tendsto (lsNoiseLoad pStar kappa etaStar alpha bStar sigma) atTop (𝓝 u))
    (hadd : Tendsto (lsAdditiveLoad etaStar alpha bStar sigma (SparseSGD.Probability.LeastSquares.labelVariance ν))
      atTop (𝓝 (SparseSGD.Probability.LeastSquares.labelVariance ν*u))) :
    ∀ e > 0, ∀ᶠ d in atTop, ∀ k : ℕ,
      let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d
      |(P.trajectory ⟨R,0,0⟩ k).R-
        learningProfile u (SparseSGD.Probability.LeastSquares.labelVariance ν*u) R
          ((k : ℝ)*(P.w/P.eps))| < e := by
  let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν
  let variance := SparseSGD.Probability.LeastSquares.labelVariance ν
  let Delta := lsDelta pStar etaStar epsStar kappa gamma alpha
  have hvar : 0 ≤ variance := labelVariance_nonneg ν
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
  have hDelta : Tendsto Delta atTop (𝓝 0) := lsDelta_tendsto_zero pStar etaStar epsStar kappa gamma alpha hp heta he hD
  have halg := actualLSFamily_algebra_of_retention_bound pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp hb he heta hpd hret
  have hcurv : Tendsto (fun d => (P d).curvature) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => 0)
      (h := fun d => Delta d/4) tendsto_const_nhds (by simpa using hDelta.div_const 4)
    · filter_upwards [halg] with d hd
      obtain ⟨hb0,hb1,_,hd0,hw,_,_⟩ := hd
      change (P d).w=Delta d*(P d).eps^2 at hw
      unfold Params.curvature
      rw [hw]
      positivity
    · filter_upwards [halg] with d hd
      obtain ⟨hb0,hb1,_,hd0,hw,_,_⟩ := hd
      change (P d).w=Delta d*(P d).eps^2 at hw
      have heps0 := (Params.small_step_bounds (P d) hb0 hb1).1
      have heps1 := (Params.small_step_bounds (P d) hb0 hb1).2.1
      have hw0 : 0 ≤ (P d).w := by rw [hw]; positivity
      have hc : (P d).curvature ≤ (P d).w := by
        unfold Params.curvature
        apply (div_le_iff₀ (by linarith : 0 < 2*(1+(P d).beta))).mpr
        nlinarith
      rw [hw] at hc
      have HH := mul_le_mul_of_nonneg_left (show (P d).eps^2 ≤ 1/4 by nlinarith) hd0.le
      nlinarith only [hc,HH]
  have hnu : Tendsto (fun d => (P d).renormNoise) atTop (𝓝 u) := renorm_load_tendsto _ _ u hnoiseA hcurv
  have hphi : Tendsto (fun d => (P d).renormAdditive) atTop (𝓝 (variance*u)) :=
    renorm_load_tendsto _ _ (variance*u) haddA hcurv
  have hvalid : ∀ᶠ d in atTop, 1/2 ≤ (P d).beta ∧ (P d).beta < 1 ∧
      0 < Delta d ∧ (P d).w=Delta d*(P d).eps^2 ∧
      0 ≤ (P d).renormNoise ∧ 0 ≤ (P d).renormAdditive := by
    filter_upwards [halg,hcurv.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))] with d hd hc
    obtain ⟨hb0,hb1,_,hdp,hw,hn,ha⟩ := hd
    obtain ⟨hnu0,hph0⟩ := renorm_nonneg_of_curvature_lt_one (P d) hn ha hc
    exact ⟨hb0,hb1,hdp,hw,hnu0,hph0⟩
  exact learning_chain_uniform_convergence P Delta R u (variance*u) jury hR hu0 hu1
    (mul_nonneg hvar hu0) hvalid hDelta hnu hphi

/-- Actual fixed-batch feedback and temperature limits, using the realized integer batch. -/
theorem ls_fixed_batch_load_limits
    (pStar kappa etaStar alpha bStar variance u : ℝ) (hk : 0 ≤ kappa) (heta : 0 < etaStar)
    (hcell : (1-alpha<0 ∧ u=0) ∨ (1-alpha=0 ∧ u=etaStar/(2*(fixedRealizedBatch bStar : ℝ)))) :
    Tendsto (lsNoiseLoad pStar kappa etaStar alpha bStar 0) atTop (𝓝 u) ∧
    Tendsto (lsAdditiveLoad etaStar alpha bStar 0 variance) atTop (𝓝 (variance*u)) := by
  have HN := lsNoise_sigma_zero_power_tendsto pStar kappa etaStar alpha bStar hk heta
  have HA := lsAdditive_sigma_zero_power_tendsto etaStar alpha bStar variance
  rcases hcell with ⟨hneg,hu⟩ | ⟨hzero,hu⟩
  · subst u
    have Hpow : Tendsto (fun d : ℕ => (d : ℝ)^(1-alpha)) atTop (𝓝 0) := by
      simpa using powerScale_tendsto_zero 1 (1-alpha) (by norm_num) hneg
    have HN' := HN.mul Hpow
    have HA' := HA.mul Hpow
    have HE (f : ℕ → ℝ) : (fun d => (f d/(d : ℝ)^(1-alpha))*(d : ℝ)^(1-alpha)) =ᶠ[atTop] f := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
      exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos (by exact_mod_cast hd) _).ne'
    constructor
    · simpa using HN'.congr' (HE _)
    · simpa using HA'.congr' (HE _)
  · subst u
    constructor
    · simpa [hzero] using HN
    · convert (show Tendsto (lsAdditiveLoad etaStar alpha bStar 0 variance) atTop
          (𝓝 (etaStar*variance/(2*(fixedRealizedBatch bStar : ℝ)))) by simpa [hzero] using HA) using 1
      congr 1
      ring

/-- At zero batch exponent, the scaling constant is the realized integer. -/
def realizedBatchScale (b sigma : ℝ) : ℝ :=
  if sigma=0 then (fixedRealizedBatch b : ℝ) else b

theorem realizedBatchScale_pos (b sigma : ℝ) (hb : 0 < b) :
    0 < realizedBatchScale b sigma := by
  unfold realizedBatchScale
  split_ifs
  · exact_mod_cast fixedRealizedBatch_pos b
  · exact hb

/-- Both positive batch exponents and the fixed integer batch edge have
actual noise and label-forcing limits. -/
theorem ls_power_load_limits
    (pStar kappa etaStar alpha bStar sigma variance u : ℝ)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (heta : 0 < etaStar)
    (hb : 0 < bStar) (hs : 0 ≤ sigma)
    (hcell : (1-sigma-alpha<0 ∧ u=0) ∨
      (1-sigma-alpha=0 ∧ u=etaStar/(2*realizedBatchScale bStar sigma))) :
    Tendsto (lsNoiseLoad pStar kappa etaStar alpha bStar sigma) atTop (𝓝 u) ∧
    Tendsto (lsAdditiveLoad etaStar alpha bStar sigma variance) atTop (𝓝 (variance*u)) := by
  rcases eq_or_lt_of_le hs with hzero | hspos
  · have hs0 : sigma=0 := hzero.symm
    subst sigma
    apply ls_fixed_batch_load_limits pStar kappa etaStar alpha bStar variance u hk heta
    simpa [realizedBatchScale] using hcell
  · have hbscale : realizedBatchScale bStar sigma=bStar := by simp [realizedBatchScale,hspos.ne']
    rw [hbscale] at hcell
    rcases hcell with ⟨hneg,hu⟩ | ⟨hzero,hu⟩
    · subst u
      exact ⟨lsNoiseLoad_tendsto_zero pStar kappa etaStar alpha bStar sigma hp hk heta hb hspos hneg,
        by simpa using lsAdditiveLoad_tendsto_zero etaStar alpha bStar sigma variance heta hb hspos hneg⟩
    · subst u
      exact ⟨lsNoiseLoad_tendsto_critical pStar kappa etaStar alpha bStar sigma hp hk heta hb hspos hzero,
        lsAdditiveLoad_tendsto_critical etaStar alpha bStar sigma variance heta hb hspos hzero⟩

/-- Cells 1 and 2, including fixed batches, and the learning-clock part of
cell 9. All clock and model parameters come from the actual LS oracle. -/
theorem ls_learning_cells_all_batches
    (pStar kappa bStar sigma epsStar gamma etaStar alpha R u : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (jury : External.JuryStability)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (hb : 0 < bStar) (hs : 0 ≤ sigma)
    (he : 0 < epsStar) (hg : 0 ≤ gamma) (heta : 0 < etaStar)
    (hfixed : gamma=0 → epsStar ≤ 1/2)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hD : gamma-alpha-kappa < 0)
    (hcell : (1-sigma-alpha<0 ∧ u=0) ∨
      (1-sigma-alpha=0 ∧ u=etaStar/(2*realizedBatchScale bStar sigma)))
    (hR : 0 ≤ R) (hu1 : u < 1) :
    ∀ e > 0, ∀ᶠ d in atTop, ∀ k : ℕ,
      let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d
      |(P.trajectory ⟨R,0,0⟩ k).R-
        learningProfile u (SparseSGD.Probability.LeastSquares.labelVariance ν*u) R
          ((k : ℝ)*(P.w/P.eps))| < e := by
  have hu0 : 0 ≤ u := by
    rcases hcell with ⟨_,hu⟩ | ⟨_,hu⟩
    · rw [hu]
    · rw [hu]
      exact (div_pos heta (mul_pos (by norm_num) (realizedBatchScale_pos bStar sigma hb))).le
  have hret : ∀ᶠ d in atTop, scaledRetention epsStar gamma d ≤ 1/2 := by
    rcases eq_or_lt_of_le hg with hzero | hgpos
    · have hg0 : gamma=0 := hzero.symm
      have H := hfixed hg0
      subst gamma
      exact Eventually.of_forall (fun d => by simpa [scaledRetention_gamma_zero] using H)
    · filter_upwards [(scaledRetention_tendsto_zero epsStar gamma hgpos).eventually
        (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/2))] with d hd
      exact hd.le
  obtain ⟨hnoise,hadd⟩ := ls_power_load_limits pStar kappa etaStar alpha bStar sigma
    (SparseSGD.Probability.LeastSquares.labelVariance ν) u hp hk heta hb hs hcell
  exact ls_learning_family_uniform pStar kappa bStar sigma epsStar gamma etaStar alpha R u
    p ν jury hp hb he heta hpd hret hD hR hu0 hu1 hnoise hadd

/-- Exact excess-risk envelope of the scalar limiting profile. -/
theorem learningProfile_excess (u phi R t : ℝ) :
    learningProfile u phi R t-phi/(1-u)=(R-phi/(1-u))*Real.exp (-2*(1-u)*t) := by
  unfold learningProfile
  ring

/-- The learning profile has the source's envelope rate per minibatch step. -/
theorem learningProfile_excess_grid (u phi R z : ℝ) (k : ℕ) :
    learningProfile u phi R ((k : ℝ)*z)-phi/(1-u)=
      (R-phi/(1-u))*Real.exp (-(2*z*(1-u))*(k : ℝ)) := by
  rw [learningProfile_excess]
  congr 2
  ring

end
end SparseSGD.Scaling
