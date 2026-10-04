import SparseSGD.Scaling.FluidPowerParameters

open Filter Topology

namespace SparseSGD.Scaling
noncomputable section

/-- Fixed sparse-probability edge for the actual power-family fluid theorem.
Here kappa=0, so the probability stays at pStar; the learning increment still
vanishes because alpha>0. The actual rounded batch and raw Delta retain the
same realized-prefactor limits as in the vanishing-sparsity family. -/
theorem actual_fluid_fixed_sparsity_parameter_limits
    (pStar b sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : MeasureTheory.Measure ℝ)
    (hp : 0 < pStar) (hp1 : pStar ≤ 1) (hb : 0 < b) (hs : 0 ≤ sigma)
    (heps : 0 < epsStar) (hg : 0 ≤ gamma) (heta : 0 < etaStar)
    (ha : 0 < alpha) (hfixed : gamma=0 → epsStar≤1/2)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d:ℝ)=scaledSparsity pStar 0 d)
    (cap : ℝ) (hcap : pStar ≤ cap)
    (hPhi : 1-sigma-alpha<0 ∨ 1-sigma-alpha=0)
    (hDelta : gamma-alpha<0 ∨ gamma-alpha=0) :
    (∀ᶠ d : ℕ in atTop,
      1/2 ≤ (actualLSParams pStar 0 b sigma epsStar gamma etaStar alpha p ν d).beta ∧
      (actualLSParams pStar 0 b sigma epsStar gamma etaStar alpha p ν d).beta < 1 ∧
      (p d:ℝ) ≤ cap) ∧
    Tendsto (fun d : ℕ => (p d:ℝ)) atTop (𝓝 pStar) ∧
    Tendsto (fun d => scaledLearningRate etaStar alpha d*(p d:ℝ)) atTop (𝓝 0) ∧
    (if 1-sigma-alpha<0 then
      Tendsto (fun d => Logistic.logisticPhi d (scaledBatch b sigma d)
        (scaledLearningRate etaStar alpha d)) atTop (𝓝 0)
     else Tendsto (fun d => Logistic.logisticPhi d (scaledBatch b sigma d)
        (scaledLearningRate etaStar alpha d)) atTop
          (𝓝 (etaStar/(2*realizedBatchScale b sigma)))) ∧
    (if gamma-alpha<0 then
      Tendsto (fun d => rawDelta
        (actualLSParams pStar 0 b sigma epsStar gamma etaStar alpha p ν d)) atTop (𝓝 0)
     else Tendsto (fun d => rawDelta
        (actualLSParams pStar 0 b sigma epsStar gamma etaStar alpha p ν d)) atTop
          (𝓝 (etaStar*pStar/epsStar))) := by
  have hbeta := actual_fluid_beta_eventually_valid pStar 0 b sigma epsStar gamma etaStar alpha
    p ν heps hg hfixed
  have hvalid : ∀ᶠ d : ℕ in atTop,
      1/2 ≤ (actualLSParams pStar 0 b sigma epsStar gamma etaStar alpha p ν d).beta ∧
      (actualLSParams pStar 0 b sigma epsStar gamma etaStar alpha p ν d).beta < 1 := hbeta
  have hpTendsto : Tendsto (fun d : ℕ => (p d:ℝ)) atTop (𝓝 pStar) := by
    have hformal : ∀ᶠ d : ℕ in atTop, scaledSparsity pStar 0 d=pStar := by
      filter_upwards with d
      simp [scaledSparsity,Real.rpow_zero]
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => pStar) atTop (𝓝 pStar)).congr'
    filter_upwards [hpd,hformal] with d hp hd
    rw [hp,hd]
  have hstep : Tendsto (fun d : ℕ => scaledLearningRate etaStar alpha d*(p d:ℝ))
      atTop (𝓝 0) := by
    have hformal : Tendsto (fun d : ℕ => (etaStar*pStar)*(d:ℝ)^(-alpha)) atTop (𝓝 0) :=
      powerScale_tendsto_zero (etaStar*pStar) (-alpha) (mul_pos heta hp) (neg_lt_zero.mpr ha)
    have heq : (fun d : ℕ => scaledLearningRate etaStar alpha d*(p d:ℝ)) =ᶠ[atTop]
        fun d => (etaStar*pStar)*(d:ℝ)^(-alpha) := by
      filter_upwards [hpd,eventually_gt_atTop (0:ℕ)] with d hp hd
      have hdR : (d:ℝ)>0 := by exact_mod_cast hd
      rw [hp]
      simp [scaledSparsity,scaledLearningRate,Real.rpow_zero]
      ring
    exact hformal.congr' heq.symm
  have hPhiLim : (if 1-sigma-alpha<0 then
      Tendsto (fun d => Logistic.logisticPhi d (scaledBatch b sigma d)
        (scaledLearningRate etaStar alpha d)) atTop (𝓝 0)
    else Tendsto (fun d => Logistic.logisticPhi d (scaledBatch b sigma d)
        (scaledLearningRate etaStar alpha d)) atTop
          (𝓝 (etaStar/(2*realizedBatchScale b sigma)))) := by
    by_cases hh : 1-sigma-alpha<0
    · simp [hh]
      exact actual_fluid_phi_tendsto_zero etaStar alpha b sigma heta hb hs hh
    · have hh0 : 1-sigma-alpha=0 := by
        rcases hPhi with hneg | heq
        · exact (hh hneg).elim
        · exact heq
      simp [hh]
      exact actual_fluid_phi_tendsto_critical etaStar alpha b sigma heta hb hs hh0
  have hDeltaLim : (if gamma-alpha<0 then
      Tendsto (fun d => rawDelta
        (actualLSParams pStar 0 b sigma epsStar gamma etaStar alpha p ν d)) atTop (𝓝 0)
    else Tendsto (fun d => rawDelta
        (actualLSParams pStar 0 b sigma epsStar gamma etaStar alpha p ν d)) atTop
          (𝓝 (etaStar*pStar/epsStar))) := by
    by_cases hh : gamma-alpha<0
    · simp [hh]
      exact actual_rawDelta_tendsto_zero pStar 0 b sigma epsStar gamma etaStar alpha
        p ν hp heta heps hpd (by simpa using hh)
    · have hh0 : gamma-alpha=0 := by
        rcases hDelta with hneg | heq
        · exact (hh hneg).elim
        · exact heq
      simp [hh]
      exact actual_rawDelta_tendsto_critical pStar 0 b sigma epsStar gamma etaStar alpha
        p ν hp heta heps hpd (by simpa using hh0)
  have hpCap : ∀ᶠ d : ℕ in atTop, (p d:ℝ)≤cap := by
    filter_upwards [hpd,eventually_gt_atTop (0:ℕ)] with d hp hd
    rw [hp]
    have heq : scaledSparsity pStar 0 d=pStar := by
      simp [scaledSparsity,Real.rpow_zero]
    rw [heq]
    exact hcap
  refine ⟨?_,hpTendsto,hstep,hPhiLim,hDeltaLim⟩
  filter_upwards [hvalid,hpCap] with d hv hpv
  exact ⟨hv.1,hv.2,hpv⟩

end
end SparseSGD.Scaling
