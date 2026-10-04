import SparseSGD.Scaling.LeastSquaresParameters
import SparseSGD.Comparison.MatchedParameters
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter Topology Asymptotics MeasureTheory

namespace SparseSGD.Scaling
noncomputable section

def retentionClock (eps : ℝ) : ℝ := -Real.log (1 - eps)

theorem retentionClock_bounds (eps : ℝ) (heps : 0 < eps) (hhalf : eps ≤ 1/2) :
    eps ≤ retentionClock eps ∧ retentionClock eps ≤ eps + 2 * eps^2 := by
  have hx : 0 < 1 - eps := by linarith
  have hxne : 1 - eps ≠ 0 := hx.ne'
  have hlow := Real.log_lt_sub_one_of_pos hx (by linarith : 1 - eps ≠ 1)
  have hup := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hup
  constructor
  · dsimp [retentionClock]
    linarith
  · have hupper : retentionClock eps ≤ eps / (1-eps) := by
      have hrw : (1 - eps)⁻¹ - 1 = eps / (1-eps) := by
        field_simp [hxne]
        ring
      simpa [retentionClock, hrw] using hup
    have hrem : eps / (1-eps) ≤ eps + 2*eps^2 := by
      have hden : 1/2 ≤ 1-eps := by linarith
      have hdenpos : 0 < 1-eps := by linarith
      rw [div_le_iff₀ hdenpos]
      nlinarith
    exact hupper.trans hrem

def scaledRetentionClock (epsStar gamma : ℝ) (d : ℕ) : ℝ :=
  retentionClock (scaledRetention epsStar gamma d)

theorem scaledRetentionClock_bounds_eventually (epsStar gamma : ℝ)
    (heps : 0 < epsStar) (hg : 0 < gamma) :
    ∀ᶠ d : ℕ in atTop,
      scaledRetention epsStar gamma d ≤ scaledRetentionClock epsStar gamma d ∧
      scaledRetentionClock epsStar gamma d ≤ scaledRetention epsStar gamma d +
        2 * (scaledRetention epsStar gamma d)^2 := by
  have hsmall := (scaledRetention_tendsto_zero epsStar gamma hg).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with d hdsmall hdd
  have hpos : 0 < scaledRetention epsStar gamma d := by
    unfold scaledRetention
    exact mul_pos heps (Real.rpow_pos_of_pos (by exact_mod_cast hdd) _)
  exact retentionClock_bounds _ hpos (by linarith)

theorem scaledRetentionClock_ratio_tendsto_one (epsStar gamma : ℝ)
    (heps : 0 < epsStar) (hg : 0 < gamma) :
    Tendsto (fun d : ℕ => scaledRetentionClock epsStar gamma d /
      scaledRetention epsStar gamma d) atTop (𝓝 1) := by
  have he := scaledRetention_tendsto_zero epsStar gamma hg
  have hup : Tendsto (fun d : ℕ => 1 + 2 * scaledRetention epsStar gamma d) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (he.const_mul 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [scaledRetentionClock_bounds_eventually epsStar gamma heps hg,
      eventually_gt_atTop (0 : ℕ)] with d hbounds hd
    rcases hbounds with ⟨hlo, hhi⟩
    have hepsd : 0 < scaledRetention epsStar gamma d := by
      unfold scaledRetention
      exact mul_pos heps (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)
    apply (le_div_iff₀ hepsd).2
    nlinarith [hlo]
  · filter_upwards [scaledRetentionClock_bounds_eventually epsStar gamma heps hg,
      eventually_gt_atTop (0 : ℕ)] with d hbounds hd
    rcases hbounds with ⟨hlo, hhi⟩
    have hepsd : 0 < scaledRetention epsStar gamma d := by
      unfold scaledRetention
      exact mul_pos heps (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)
    apply (div_le_iff₀ hepsd).2
    calc
      scaledRetentionClock epsStar gamma d ≤ scaledRetention epsStar gamma d +
          2 * (scaledRetention epsStar gamma d)^2 := hhi
      _ = (1 + 2 * scaledRetention epsStar gamma d) * scaledRetention epsStar gamma d := by ring


theorem scaledRetentionClock_error_isBigO (epsStar gamma : ℝ)
    (heps : 0 < epsStar) (hg : 0 < gamma) :
    (fun d : ℕ => |scaledRetentionClock epsStar gamma d - scaledRetention epsStar gamma d|) =O[atTop]
      (fun d : ℕ => (scaledRetention epsStar gamma d)^2) := by
  rw [isBigO_iff]
  refine ⟨2, ?_⟩
  filter_upwards [scaledRetentionClock_bounds_eventually epsStar gamma heps hg,
    eventually_gt_atTop (0 : ℕ)] with d hd hpos
  rcases hd with ⟨hlo, hhi⟩
  have hdiff : 0 ≤ scaledRetentionClock epsStar gamma d - scaledRetention epsStar gamma d := sub_nonneg.mpr hlo
  have hbound : |scaledRetentionClock epsStar gamma d - scaledRetention epsStar gamma d| ≤
      2 * (scaledRetention epsStar gamma d)^2 := by
    rw [abs_of_nonneg hdiff]
    linarith
  calc
    ‖|scaledRetentionClock epsStar gamma d - scaledRetention epsStar gamma d|‖ =
        |scaledRetentionClock epsStar gamma d - scaledRetention epsStar gamma d| := by
          rw [Real.norm_eq_abs, abs_abs]
    _ ≤ 2 * (scaledRetention epsStar gamma d)^2 := hbound
    _ = 2 * ‖(scaledRetention epsStar gamma d)^2‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

theorem actualLSParams_matchedStep_eq_retentionClock
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (d : ℕ) :
    (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).matchedStep =
      scaledRetentionClock epsStar gamma d := by
  simp [SparseSGD.Params.matchedStep, actualLSParams, SparseSGD.Probability.LeastSquares.params,
    SparseSGD.oracleParams, scaledMomentum, scaledRetentionClock, retentionClock]

theorem actualLSParams_matchedStep_over_retention_tendsto_one
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (heps : 0 < epsStar) (hg : 0 < gamma) :
    Tendsto (fun d : ℕ =>
      (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).matchedStep /
        scaledRetention epsStar gamma d) atTop (𝓝 1) := by
  have h := scaledRetentionClock_ratio_tendsto_one epsStar gamma heps hg
  apply h.congr'
  filter_upwards with d
  rw [actualLSParams_matchedStep_eq_retentionClock]

theorem actualLSParams_matchedStep_error_isBigO
    (pStar kappa bStar sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (heps : 0 < epsStar) (hg : 0 < gamma) :
    (fun d : ℕ => |(actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).matchedStep -
      scaledRetention epsStar gamma d|) =O[atTop]
      (fun d : ℕ => (scaledRetention epsStar gamma d)^2) := by
  have h := scaledRetentionClock_error_isBigO epsStar gamma heps hg
  apply h.congr'
  filter_upwards with d
  rw [actualLSParams_matchedStep_eq_retentionClock]
  rfl

end
end SparseSGD.Scaling
