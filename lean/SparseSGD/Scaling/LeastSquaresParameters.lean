import SparseSGD.Scaling.FixedParameters
import SparseSGD.Probability.LeastSquares.Process

open Filter Topology MeasureTheory

namespace SparseSGD.Scaling
noncomputable section

lemma scaledSparsity_pos_of_pos (pStar kappa : ℝ) (d : ℕ)
    (hp : 0 < pStar) (hd : 0 < d) : 0 < scaledSparsity pStar kappa d := by
  unfold scaledSparsity
  exact mul_pos hp (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)

/-- Co-scaled LS parameter tuple with integer batch rounding and explicit oracle variance. -/
def lsPowerParams (pStar kappa bStar sigma epsStar gamma etaStar alpha variance : ℝ)
    (d : ℕ) : SparseSGD.Params :=
  ⟨scaledMomentum epsStar gamma d,
    lsCurvature pStar etaStar epsStar kappa gamma alpha d,
    lsNoiseLoad pStar kappa etaStar alpha bStar sigma d,
    lsAdditiveLoad etaStar alpha bStar sigma variance d⟩

/-- The actual model parameters generated from the LS oracle at dimension d. -/
def actualLSParams (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (d : ℕ) : SparseSGD.Params :=
  SparseSGD.Probability.LeastSquares.params d (scaledBatch bStar sigma d) (p d) ν
    (scaledMomentum epsStar gamma d) (scaledLearningRate etaStar alpha d)

theorem actualLSParams_eq_lsPowerParams
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (d : ℕ)
    (hp : (p d : ℝ) ≠ 0)
    (hpd : (p d : ℝ) = scaledSparsity pStar kappa d) :
    actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d =
      lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar alpha
        (SparseSGD.Probability.LeastSquares.labelVariance ν) d := by
  rw [actualLSParams, SparseSGD.Probability.LeastSquares.params_explicit (p d) hp ν
    (scaledMomentum epsStar gamma d) (scaledLearningRate etaStar alpha d)]
  unfold lsPowerParams
  simp [scaledMomentum, lsCurvature, lsNoiseLoad, lsAdditiveLoad,
    scaledLearningRate, scaledRetention, scaledSparsity, hpd]
  <;> ring

theorem actualLSParams_eps
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (d : ℕ)
    (hp : (p d : ℝ) ≠ 0)
    (hpd : (p d : ℝ) = scaledSparsity pStar kappa d) :
    (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).eps =
      scaledRetention epsStar gamma d := by
  rw [actualLSParams_eq_lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d hp hpd]
  simp [lsPowerParams, SparseSGD.Params.eps, scaledMomentum]

theorem actualLSParams_rawDelta
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (d : ℕ)
    (hp : (p d : ℝ) ≠ 0)
    (hpd : (p d : ℝ) = scaledSparsity pStar kappa d) :
    scaledLearningRate etaStar alpha d * (p d : ℝ) /
      (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).eps =
        lsDelta pStar etaStar epsStar kappa gamma alpha d := by
  rw [actualLSParams_eps pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d
    hp hpd]
  simp [lsDelta, hpd]

theorem actualLSParams_curvature
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (d : ℕ)
    (hp : (p d : ℝ) ≠ 0)
    (hpd : (p d : ℝ) = scaledSparsity pStar kappa d) :
    (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).curvature =
      lsCurvatureLoad pStar etaStar epsStar kappa gamma alpha d := by
  rw [actualLSParams_eq_lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d hp hpd]
  simp [lsPowerParams, SparseSGD.Params.curvature, lsCurvatureLoad, scaledMomentum,
    lsCurvature, scaledRetention]
  <;> ring

/-- The realized LS family has the expected momentum limit for positive retention exponent. -/
theorem actualLSParams_beta_tendsto_one
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (hg : 0 < gamma) :
    Tendsto (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).beta)
      atTop (𝓝 1) := by
  have h := scaledMomentum_tendsto_one epsStar gamma hg
  have heq : (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).beta) =ᶠ[atTop]
      fun d => scaledMomentum epsStar gamma d := Filter.Eventually.of_forall (fun _ => rfl)
  exact h.congr' heq.symm


theorem actualLSParams_noise_ratio_tendsto
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (hpstar : 0 < pStar) (hk : 0 ≤ kappa) (heta : 0 < etaStar)
    (hb : 0 < bStar) (hs : 0 < sigma)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d : ℝ) = scaledSparsity pStar kappa d) :
    Tendsto (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).noise /
      ((etaStar / (2*bStar)) * (d : ℝ)^(1-sigma-alpha))) atTop (𝓝 1) := by
  have h := lsNoise_power_ratio_tendsto pStar kappa etaStar alpha bStar sigma
    hpstar hk heta hb hs
  have hEq : (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).noise /
      ((etaStar / (2*bStar)) * (d : ℝ)^(1-sigma-alpha))) =ᶠ[atTop]
      (fun d => lsNoiseLoad pStar kappa etaStar alpha bStar sigma d /
        ((etaStar / (2*bStar)) * (d : ℝ)^(1-sigma-alpha))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hpd] with d hd hpd
    have hpos := scaledSparsity_pos_of_pos pStar kappa d hpstar hd
    have hp : (p d : ℝ) ≠ 0 := by rw [hpd]; exact hpos.ne'
    rw [actualLSParams_eq_lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d hp hpd]
    rfl
  exact h.congr' hEq.symm

theorem actualLSParams_additive_ratio_tendsto
    (pStar kappa bStar sigma epsStar gamma etaStar alpha variance : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (hpstar : 0 < pStar) (hk : 0 ≤ kappa)
    (heta : 0 < etaStar) (hb : 0 < bStar) (hs : 0 < sigma)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d : ℝ) = scaledSparsity pStar kappa d)
    (hvariance : SparseSGD.Probability.LeastSquares.labelVariance ν = variance) :
    Tendsto (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).additive /
      ((etaStar / (2*bStar)) * (d : ℝ)^(1-sigma-alpha))) atTop (𝓝 variance) := by
  have h := lsAdditive_power_ratio_tendsto etaStar alpha bStar sigma variance heta hb hs
  have hEq : (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).additive /
      ((etaStar / (2*bStar)) * (d : ℝ)^(1-sigma-alpha))) =ᶠ[atTop]
      (fun d => lsAdditiveLoad etaStar alpha bStar sigma variance d /
        ((etaStar / (2*bStar)) * (d : ℝ)^(1-sigma-alpha))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hpd] with d hd hpd
    have hpos := scaledSparsity_pos_of_pos pStar kappa d hpstar hd
    have hp : (p d : ℝ) ≠ 0 := by rw [hpd]; exact hpos.ne'
    rw [actualLSParams_eq_lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d hp hpd]
    simp [lsPowerParams, hvariance]
  exact h.congr' hEq.symm

theorem actualLSParams_curvature_ratio_tendsto
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (hpstar : 0 < pStar) (heta : etaStar ≠ 0) (heps : epsStar ≠ 0)
    (hg : 0 < gamma) (hpd : ∀ᶠ d : ℕ in atTop, (p d : ℝ) = scaledSparsity pStar kappa d) :
    Tendsto (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).curvature /
      (etaStar*epsStar*pStar*(d : ℝ)^(-(alpha+gamma+kappa)))) atTop (𝓝 (1/4)) := by
  have h := lsCurvatureLoad_power_ratio_tendsto pStar etaStar epsStar kappa gamma alpha hpstar.ne' heta heps hg
  have hEq : (fun d => (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).curvature /
      (etaStar*epsStar*pStar*(d : ℝ)^(-(alpha+gamma+kappa)))) =ᶠ[atTop]
      (fun d => lsCurvatureLoad pStar etaStar epsStar kappa gamma alpha d /
        (etaStar*epsStar*pStar*(d : ℝ)^(-(alpha+gamma+kappa)))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hpd] with d hd hpd
    have hpos := scaledSparsity_pos_of_pos pStar kappa d hpstar hd
    have hp : (p d : ℝ) ≠ 0 := by rw [hpd]; exact hpos.ne'
    rw [actualLSParams_curvature pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d hp hpd]
  exact h.congr' hEq.symm

end
end SparseSGD.Scaling
