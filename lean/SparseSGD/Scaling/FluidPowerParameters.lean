import SparseSGD.Scaling.ActivityFamily
import SparseSGD.Scaling.LeastSquaresParameters
import SparseSGD.Scaling.PowerLimits
import SparseSGD.Logistic.EquilibriumScaling

open Filter Topology

namespace SparseSGD.Scaling
noncomputable section

private theorem scaledBatch_over_dimension_power_tendsto
    (b sigma : ℝ) (hb : 0 < b) (hs : 0 ≤ sigma) :
    Tendsto (fun d : ℕ => (scaledBatch b sigma d : ℝ)/(d:ℝ)^sigma)
      atTop (𝓝 (realizedBatchScale b sigma)) := by
  have hratio := scaledBatch_realized_ratio_tendsto b sigma hb hs
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · subst sigma
    have hc : (fun d : ℕ => (scaledBatch b 0 d : ℝ)/(d:ℝ)^(0:ℝ)) =
        fun _ => (fixedRealizedBatch b : ℝ) := by
      funext d
      simp [Real.rpow_zero, scaledBatch_zero_eq_fixed, fixedRealizedBatch]
    rw [hc]
    simp [realizedBatchScale, fixedRealizedBatch]
  · have hEq : (fun d : ℕ => (scaledBatch b sigma d : ℝ)/(d:ℝ)^sigma) =ᶠ[atTop]
        fun d => realizedBatchScale b sigma *
          ((scaledBatch b sigma d : ℝ)/(realizedBatchScale b sigma*(d:ℝ)^sigma)) := by
      filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
      have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
      have hc : realizedBatchScale b sigma ≠ 0 := (realizedBatchScale_pos b sigma hb).ne'
      field_simp [hdR, hc]
    have hright : Tendsto (fun d : ℕ => realizedBatchScale b sigma *
        ((scaledBatch b sigma d : ℝ)/(realizedBatchScale b sigma*(d:ℝ)^sigma)))
        atTop (𝓝 (realizedBatchScale b sigma)) := by
      simpa using hratio.const_mul (realizedBatchScale b sigma)
    exact hright.congr' hEq.symm
/-- A vanishing sparse-coordinate family with its actual power-law learning
step. The identity is eventual because the probability family is only required
to agree with the formal power law eventually. -/
theorem actual_fluid_sparse_limits
    (pStar kappa etaStar alpha : ℝ) (p : ℕ → unitInterval)
    (hp : 0 < pStar) (hk : 0 < kappa) (heta : 0 < etaStar)
    (ha : 0 < alpha+kappa)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d : ℝ)=scaledSparsity pStar kappa d) :
    Tendsto (fun d => (p d : ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun d => scaledLearningRate etaStar alpha d*(p d:ℝ)) atTop (𝓝 0) := by
  have hpformal : Tendsto (fun d : ℕ => scaledSparsity pStar kappa d) atTop (𝓝 0) := by
    have hpow := (tendsto_rpow_neg_atTop hk).comp tendsto_natCast_atTop_atTop
    simpa [scaledSparsity] using hpow.const_mul pStar
  have hprob := hpformal.congr' (hpd.mono fun _ h => h.symm)
  have hstepformal : Tendsto (fun d : ℕ => etaStar*pStar*(d:ℝ)^(-(alpha+kappa)))
      atTop (𝓝 0) := powerScale_tendsto_zero (etaStar*pStar) (-(alpha+kappa))
        (mul_pos heta hp) (neg_lt_zero.mpr ha)
  have hstepEq : (fun d : ℕ => scaledLearningRate etaStar alpha d*(p d:ℝ)) =ᶠ[atTop]
      fun d => etaStar*pStar*(d:ℝ)^(-(alpha+kappa)) := by
    filter_upwards [hpd,eventually_gt_atTop (0:ℕ)] with d hpd hd
    have hdR : (d:ℝ)>0 := by exact_mod_cast hd
    have hpw : (d:ℝ)^(-(alpha+kappa))=(d:ℝ)^(-alpha)*(d:ℝ)^(-kappa) := by
      rw [show -(alpha+kappa)=(-alpha)+(-kappa) by ring, Real.rpow_add hdR]
    rw [hpd, scaledSparsity]
    simp only [scaledLearningRate]
    rw [hpw]
    ring
  exact ⟨hprob,hstepformal.congr' hstepEq.symm⟩

/-- Exact equilibrium-load scale for a rounded power batch, including fixed
integer batches at sigma=0. -/
theorem actual_fluid_phi_ratio_tendsto
    (etaStar alpha b sigma : ℝ) (hb : 0 < b) (hs : 0 ≤ sigma) :
    Tendsto
      (fun d : ℕ =>
        SparseSGD.Logistic.logisticPhi d (scaledBatch b sigma d)
          (scaledLearningRate etaStar alpha d) /
          (d:ℝ)^(1-sigma-alpha))
      atTop (𝓝 (etaStar/(2*realizedBatchScale b sigma))) := by
  have hbatch := scaledBatch_over_dimension_power_tendsto b sigma hb hs
  have hphi := SparseSGD.Logistic.familyPhi_ratio_tendsto etaStar alpha sigma
    (realizedBatchScale b sigma) (scaledBatch b sigma)
    (realizedBatchScale_pos b sigma hb) (integerBatch_pos b sigma) hbatch
  have heq : (fun d : ℕ => SparseSGD.Logistic.familyPhi etaStar alpha
      (scaledBatch b sigma) d/(d:ℝ)^(1-sigma-alpha)) =ᶠ[atTop]
      (fun d => SparseSGD.Logistic.logisticPhi d (scaledBatch b sigma d)
        (scaledLearningRate etaStar alpha d)/(d:ℝ)^(1-sigma-alpha)) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    simp [SparseSGD.Logistic.familyPhi, scaledLearningRate]
  exact hphi.congr' heq

/-- If alpha is strictly above the noise threshold, the actual logistic load
vanishes (with the realized rounded-batch prefactor). -/
theorem actual_fluid_phi_tendsto_zero
    (etaStar alpha b sigma : ℝ) (heta : 0 < etaStar) (hb : 0 < b) (hs : 0 ≤ sigma)
    (halpha : 1-sigma-alpha < 0) :
    Tendsto (fun d : ℕ => SparseSGD.Logistic.logisticPhi d
      (scaledBatch b sigma d) (scaledLearningRate etaStar alpha d)) atTop (𝓝 0) := by
  let c := etaStar/(2*realizedBatchScale b sigma)
  let q := fun d : ℕ => SparseSGD.Logistic.logisticPhi d
    (scaledBatch b sigma d) (scaledLearningRate etaStar alpha d)/(d:ℝ)^(1-sigma-alpha)
  let s := fun d : ℕ => (d:ℝ)^(1-sigma-alpha)
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos heta (mul_pos (by norm_num) (realizedBatchScale_pos b sigma hb))
  have hq : Tendsto q atTop (𝓝 c) := by
    simpa [q,c] using actual_fluid_phi_ratio_tendsto etaStar alpha b sigma hb hs
  have hs0 : Tendsto s atTop (𝓝 0) := by
    change Tendsto ((fun x : ℝ => x^(1-sigma-alpha)) ∘
      (fun d : ℕ => (d:ℝ))) atTop (𝓝 0)
    have hpow := (tendsto_rpow_neg_atTop (by linarith : 0 < -(1-sigma-alpha))).comp
      tendsto_natCast_atTop_atTop
    simpa only [neg_neg] using hpow
  have heq : (fun d : ℕ => q d*s d) =ᶠ[atTop] fun d =>
      SparseSGD.Logistic.logisticPhi d (scaledBatch b sigma d)
        (scaledLearningRate etaStar alpha d) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    have hdR : (d:ℝ)>0 := by exact_mod_cast hd
    dsimp [q,s]
    rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hdR _).ne']
  simpa [q,s] using (hq.mul hs0).congr' heq

/-- At the critical load exponent, actual logistic Phi converges to the
realized batch prefactor. -/
theorem actual_fluid_phi_tendsto_critical
    (etaStar alpha b sigma : ℝ) (heta : 0 < etaStar) (hb : 0 < b) (hs : 0 ≤ sigma)
    (halpha : 1-sigma-alpha = 0) :
    Tendsto (fun d : ℕ => SparseSGD.Logistic.logisticPhi d
      (scaledBatch b sigma d) (scaledLearningRate etaStar alpha d)) atTop
      (𝓝 (etaStar/(2*realizedBatchScale b sigma))) := by
  have h := actual_fluid_phi_ratio_tendsto etaStar alpha b sigma hb hs
  have heq : (fun d : ℕ =>
      SparseSGD.Logistic.logisticPhi d (scaledBatch b sigma d)
        (scaledLearningRate etaStar alpha d)/(d:ℝ)^(1-sigma-alpha)) =ᶠ[atTop]
      fun d => SparseSGD.Logistic.logisticPhi d (scaledBatch b sigma d)
        (scaledLearningRate etaStar alpha d) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    have hdR : (d:ℝ)>0 := by exact_mod_cast hd
    rw [halpha, Real.rpow_zero, div_one]
  exact h.congr' heq

/-- Raw Delta is exactly the predicted power, not just asymptotically so. -/
theorem lsDelta_eq_power_eventually
    (pStar etaStar epsStar kappa gamma alpha : ℝ)
    (hp : pStar ≠ 0) (heta : etaStar ≠ 0) (heps : epsStar ≠ 0) :
    (fun d : ℕ => lsDelta pStar etaStar epsStar kappa gamma alpha d) =ᶠ[atTop]
      fun d => (etaStar*pStar/epsStar)*(d:ℝ)^(gamma-alpha-kappa) := by
  filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have h := lsDelta_power_ratio pStar etaStar epsStar kappa gamma alpha d hd hp heta heps
  have hpow : 0 < (d:ℝ)^(gamma-alpha-kappa) := Real.rpow_pos_of_pos hdR _
  have hc : etaStar*pStar/epsStar ≠ 0 := div_ne_zero (mul_ne_zero heta hp) heps
  dsimp only [lsDelta]
  have hh : lsDelta pStar etaStar epsStar kappa gamma alpha d /
      ((etaStar*pStar/epsStar)*(d:ℝ)^(gamma-alpha-kappa))=1 := h
  have hh' := (div_eq_one_iff_eq (mul_ne_zero hc hpow.ne')).mp hh
  simpa [lsDelta] using hh'

/-- The actual LS parameter family's raw Delta equals the power-family Delta
eventually, for any admissible probability family that eventually matches the
sparsity law. -/
theorem actualLSParams_rawDelta_eq_lsDelta_eventually
    (pStar kappa b sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : MeasureTheory.Measure ℝ)
    (hp : 0 < pStar)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d:ℝ)=scaledSparsity pStar kappa d) :
    (fun d : ℕ => rawDelta
      (actualLSParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d)) =ᶠ[atTop]
      fun d => lsDelta pStar etaStar epsStar kappa gamma alpha d := by
  filter_upwards [hpd,eventually_gt_atTop (0:ℕ)] with d hpd hd
  have hpos := scaledSparsity_pos_of_pos pStar kappa d hp hd
  have hp0 : (p d:ℝ) ≠ 0 := by rw [hpd]; exact hpos.ne'
  rw [rawDelta,
    actualLSParams_eq_lsPowerParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d hp0 hpd]
  simp [lsPowerParams, SparseSGD.Params.eps, lsCurvature, scaledMomentum,
    scaledRetention, scaledLearningRate, scaledSparsity, lsDelta, hpd]
  field_simp

/-- Raw Delta tends to zero below its power threshold. -/
theorem actual_rawDelta_tendsto_zero
    (pStar kappa b sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : MeasureTheory.Measure ℝ)
    (hp : 0 < pStar) (heta : 0 < etaStar) (heps : 0 < epsStar)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d:ℝ)=scaledSparsity pStar kappa d)
    (hexp : gamma-alpha-kappa < 0) :
    Tendsto (fun d => rawDelta
      (actualLSParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d)) atTop (𝓝 0) := by
  let c := etaStar*pStar/epsStar
  have hc : 0 < c := by dsimp [c]; positivity
  have hpow := powerScale_tendsto_zero c (gamma-alpha-kappa) hc hexp
  have hEqPower := lsDelta_eq_power_eventually pStar etaStar epsStar kappa gamma alpha
    hp.ne' heta.ne' heps.ne'
  have hls : Tendsto (fun d : ℕ => lsDelta pStar etaStar epsStar kappa gamma alpha d)
      atTop (𝓝 0) := hpow.congr' hEqPower.symm
  exact hls.congr' (actualLSParams_rawDelta_eq_lsDelta_eventually pStar kappa b sigma
    epsStar gamma etaStar alpha p ν hp hpd).symm

/-- At the critical raw-Delta exponent, the actual family has its positive
constant limit. -/
theorem actual_rawDelta_tendsto_critical
    (pStar kappa b sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : MeasureTheory.Measure ℝ)
    (hp : 0 < pStar) (heta : 0 < etaStar) (heps : 0 < epsStar)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d:ℝ)=scaledSparsity pStar kappa d)
    (hexp : gamma-alpha-kappa = 0) :
    Tendsto (fun d => rawDelta
      (actualLSParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d)) atTop
      (𝓝 (etaStar*pStar/epsStar)) := by
  let c := etaStar*pStar/epsStar
  have hpow : Tendsto (fun d : ℕ => c*(d:ℝ)^(gamma-alpha-kappa)) atTop (𝓝 c) := by
    simpa [hexp] using powerScale_tendsto_const c
  have hEqPower := lsDelta_eq_power_eventually pStar etaStar epsStar kappa gamma alpha
    hp.ne' heta.ne' heps.ne'
  have hls : Tendsto (fun d : ℕ => lsDelta pStar etaStar epsStar kappa gamma alpha d)
      atTop (𝓝 c) := hpow.congr' hEqPower.symm
  exact hls.congr' (actualLSParams_rawDelta_eq_lsDelta_eventually pStar kappa b sigma
    epsStar gamma etaStar alpha p ν hp hpd).symm

/-- Eventual momentum admissibility, including the fixed-retention gamma=0
edge. -/
theorem actual_fluid_beta_eventually_valid
    (pStar kappa b sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : MeasureTheory.Measure ℝ)
    (heps : 0 < epsStar) (hg : 0 ≤ gamma)
    (hfixed : gamma = 0 → epsStar ≤ 1/2) :
    ∀ᶠ d : ℕ in atTop,
      1/2 ≤ (actualLSParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d).beta ∧
      (actualLSParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d).beta < 1 := by
  have hsmall : ∀ᶠ d : ℕ in atTop, scaledRetention epsStar gamma d ≤ 1/2 := by
    rcases eq_or_lt_of_le hg with hg0 | hgpos
    · have he := hfixed hg0.symm
      subst gamma
      exact Filter.Eventually.of_forall (fun d => by simpa [scaledRetention_gamma_zero] using he)
    · filter_upwards [(scaledRetention_tendsto_zero epsStar gamma hgpos).eventually
        (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))] with d hd
      exact hd.le
  filter_upwards [hsmall,eventually_gt_atTop (0:ℕ)] with d hsmall hd
  have hret : 0 < scaledRetention epsStar gamma d := by
    unfold scaledRetention
    exact mul_pos heps (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)
  have hbeta : (actualLSParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d).beta =
      1-scaledRetention epsStar gamma d := by rfl
  rw [hbeta]
  exact ⟨by linarith, by linarith⟩

/-- Bundled actual-family endpoint for the fluid theorem: sparse masks and
learning increments vanish, while logistic load and raw Delta take their
strict/critical power-law limits with the realized integer-batch constant. -/
theorem actual_fluid_power_parameter_limits
    (pStar kappa b sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : MeasureTheory.Measure ℝ)
    (hp : 0 < pStar) (hk : 0 < kappa) (hb : 0 < b) (hs : 0 ≤ sigma)
    (heps : 0 < epsStar) (hg : 0 ≤ gamma) (heta : 0 < etaStar)
    (ha : 0 < alpha+kappa) (hfixed : gamma=0 → epsStar≤1/2)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d:ℝ)=scaledSparsity pStar kappa d)
    (hPhi : 1-sigma-alpha<0 ∨ 1-sigma-alpha=0)
    (hDelta : gamma-alpha-kappa<0 ∨ gamma-alpha-kappa=0) :
    (∀ᶠ d : ℕ in atTop,
      1/2 ≤ (actualLSParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d).beta ∧
      (actualLSParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d).beta < 1) ∧
      Tendsto (fun d => (p d:ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun d => scaledLearningRate etaStar alpha d*(p d:ℝ)) atTop (𝓝 0) ∧
      (if 1-sigma-alpha<0 then
        Tendsto (fun d => SparseSGD.Logistic.logisticPhi d (scaledBatch b sigma d)
          (scaledLearningRate etaStar alpha d)) atTop (𝓝 0)
       else Tendsto (fun d => SparseSGD.Logistic.logisticPhi d (scaledBatch b sigma d)
          (scaledLearningRate etaStar alpha d)) atTop
            (𝓝 (etaStar/(2*realizedBatchScale b sigma)))) ∧
      (if gamma-alpha-kappa<0 then
        Tendsto (fun d => rawDelta
          (actualLSParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d)) atTop (𝓝 0)
       else Tendsto (fun d => rawDelta
          (actualLSParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d)) atTop
            (𝓝 (etaStar*pStar/epsStar))) := by
  have hbeta := actual_fluid_beta_eventually_valid pStar kappa b sigma epsStar gamma etaStar alpha
    p ν heps hg hfixed
  have hsparse := actual_fluid_sparse_limits pStar kappa etaStar alpha p hp hk heta ha hpd
  have hphi : (if 1-sigma-alpha<0 then
      Tendsto (fun d => SparseSGD.Logistic.logisticPhi d (scaledBatch b sigma d)
        (scaledLearningRate etaStar alpha d)) atTop (𝓝 0)
    else Tendsto (fun d => SparseSGD.Logistic.logisticPhi d (scaledBatch b sigma d)
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
  have hdelta : (if gamma-alpha-kappa<0 then
      Tendsto (fun d => rawDelta
        (actualLSParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d)) atTop (𝓝 0)
    else Tendsto (fun d => rawDelta
        (actualLSParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d)) atTop
          (𝓝 (etaStar*pStar/epsStar))) := by
    by_cases hh : gamma-alpha-kappa<0
    · simp [hh]
      exact actual_rawDelta_tendsto_zero pStar kappa b sigma epsStar gamma etaStar alpha
        p ν hp heta heps hpd hh
    · have hh0 : gamma-alpha-kappa=0 := by
        rcases hDelta with hneg | heq
        · exact (hh hneg).elim
        · exact heq
      simp [hh]
      exact actual_rawDelta_tendsto_critical pStar kappa b sigma epsStar gamma etaStar alpha
        p ν hp heta heps hpd hh0
  exact ⟨hbeta,hsparse.1,hsparse.2,hphi,hdelta⟩

end
end SparseSGD.Scaling
