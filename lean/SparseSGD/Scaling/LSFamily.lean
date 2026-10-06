import SparseSGD.Scaling.PowerLimits
import SparseSGD.Scaling.MatchingLimits
import SparseSGD.Scaling.RenormalizedLimits
import SparseSGD.Scaling.ProbabilityFamily

open Filter Topology MeasureTheory
namespace SparseSGD.Scaling
noncomputable section
set_option maxHeartbeats 1000000

theorem labelVariance_nonneg (ν : Measure ℝ) :
    0 ≤ SparseSGD.Probability.LeastSquares.labelVariance ν := integral_nonneg (fun _ => sq_nonneg _)

/-- Eventual physical validity of the actual sparse LS power family. -/
theorem actualLSFamily_algebra_of_retention_bound
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (hp : 0 < pStar) (hb : 0 < bStar) (he : 0 < epsStar) (heta : 0 < etaStar)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hbound : ∀ᶠ d in atTop, scaledRetention epsStar gamma d ≤ 1/2) :
    ∀ᶠ d in atTop,
      let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d
      1/2 ≤ P.beta ∧ P.beta < 1 ∧
      P.eps=scaledRetention epsStar gamma d ∧
      0 < lsDelta pStar etaStar epsStar kappa gamma alpha d ∧
      P.w=lsDelta pStar etaStar epsStar kappa gamma alpha d*P.eps^2 ∧
      0 ≤ P.noise ∧ 0 ≤ P.additive := by
  filter_upwards [hpd,eventually_gt_atTop (0 : ℕ),
    hbound] with d hpd hd hsmall
  have hpd0 := scaledSparsity_pos_of_pos pStar kappa d hp hd
  have hp0 : (p d : ℝ) ≠ 0 := by rw [hpd]; exact hpd0.ne'
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have heps0 : 0 < scaledRetention epsStar gamma d := by
    unfold scaledRetention
    exact mul_pos he (Real.rpow_pos_of_pos hdR _)
  have heta0 : 0 < scaledLearningRate etaStar alpha d := by
    unfold scaledLearningRate
    exact mul_pos heta (Real.rpow_pos_of_pos hdR _)
  have hB : 0 < (scaledBatch bStar sigma d : ℝ) := by exact_mod_cast integerBatch_pos bStar sigma d
  have hdim : 0 ≤ (d : ℝ)+2-scaledSparsity pStar kappa d := by
    rw [← hpd]
    linarith [(p d).property.2]
  dsimp only
  rw [actualLSParams_eq_lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d hp0 hpd]
  have hepsEq : (lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar alpha
      (SparseSGD.Probability.LeastSquares.labelVariance ν) d).eps=scaledRetention epsStar gamma d := by
    simp [lsPowerParams,Params.eps,scaledMomentum]
  refine ⟨?_,?_,hepsEq,?_,?_,?_,?_⟩
  · change 1/2 ≤ scaledMomentum epsStar gamma d
    dsimp [scaledMomentum]
    linarith
  · change scaledMomentum epsStar gamma d < 1
    dsimp [scaledMomentum]
    linarith
  · dsimp [lsDelta]
    positivity
  · rw [hepsEq]
    change lsCurvature pStar etaStar epsStar kappa gamma alpha d = _
    unfold lsCurvature lsDelta
    field_simp
  · change 0 ≤ lsNoiseLoad pStar kappa etaStar alpha bStar sigma d
    unfold lsNoiseLoad
    positivity
  · change 0 ≤ lsAdditiveLoad etaStar alpha bStar sigma (SparseSGD.Probability.LeastSquares.labelVariance ν) d
    unfold lsAdditiveLoad
    have hvar := labelVariance_nonneg ν
    positivity

theorem actualLSFamily_algebra
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (hp : 0 < pStar) (hb : 0 < bStar) (he : 0 < epsStar) (hg : 0 < gamma) (heta : 0 < etaStar)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d) :
    ∀ᶠ d in atTop,
      let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d
      1/2 ≤ P.beta ∧ P.beta < 1 ∧
      P.eps=scaledRetention epsStar gamma d ∧
      0 < lsDelta pStar etaStar epsStar kappa gamma alpha d ∧
      P.w=lsDelta pStar etaStar epsStar kappa gamma alpha d*P.eps^2 ∧
      0 ≤ P.noise ∧ 0 ≤ P.additive := by
  apply actualLSFamily_algebra_of_retention_bound pStar kappa bStar sigma epsStar gamma etaStar alpha p ν hp hb he heta hpd
  filter_upwards [(scaledRetention_tendsto_zero epsStar gamma hg).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/2))] with d hd
  exact hd.le

/-- Exact raw-curvature powers imply decay in the two learning-clock cells. -/
theorem lsDelta_tendsto_zero
    (pStar etaStar epsStar kappa gamma alpha : ℝ)
    (hp : 0 < pStar) (heta : 0 < etaStar) (he : 0 < epsStar)
    (hexp : gamma-alpha-kappa < 0) :
    Tendsto (lsDelta pStar etaStar epsStar kappa gamma alpha) atTop (𝓝 0) := by
  have H := powerScale_tendsto_zero (etaStar*pStar/epsStar) (gamma-alpha-kappa) (by positivity) hexp
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  have Hr := lsDelta_power_ratio pStar etaStar epsStar kappa gamma alpha d hd hp.ne' heta.ne' he.ne'
  have hn : etaStar*pStar/epsStar*(d : ℝ)^(gamma-alpha-kappa) ≠ 0 := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
    exact (mul_pos (by positivity) (Real.rpow_pos_of_pos hdR _)).ne'
  exact ((div_eq_one_iff_eq hn).mp Hr).symm

/-- The renormalized feedback and temperature remain nonnegative once the curvature denominator
is positive. -/
theorem renorm_nonneg_of_curvature_lt_one (p : SparseSGD.Params)
    (hn : 0 ≤ p.noise) (hp : 0 ≤ p.additive) (hc : p.curvature < 1) :
    0 ≤ p.renormNoise ∧ 0 ≤ p.renormAdditive := by
  exact ⟨div_nonneg hn (by linarith),div_nonneg hp (by linarith)⟩

/-- The comparison theorem's learning clock is the physical per-step clock. -/
theorem actualLSParams_learningClock
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (d : ℕ)
    (hp : (p d : ℝ) ≠ 0) (he : scaledRetention epsStar gamma d ≠ 0) :
    (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).w /
      (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).eps =
      scaledLearningRate etaStar alpha d*(p d : ℝ) := by
  rw [actualLSParams,SparseSGD.Probability.LeastSquares.params_explicit (p d) hp]
  simp [Params.eps,scaledMomentum,he,mul_div_assoc]
  <;> field_simp [he]
  <;> ring

end
end SparseSGD.Scaling
