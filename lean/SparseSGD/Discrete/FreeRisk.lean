import SparseSGD.Discrete.RiskBound

open Filter
open scoped Topology

namespace SparseSGD

theorem freeRisk_tendsto_zero (jury : External.JuryStability) (p : Params) (s : Moments)
    (hb : p.beta < 1) (hw : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta)) :
    Tendsto (freeRisk p s) atTop (𝓝 0) := by
  have hcont : Continuous (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
      (M * s.cov * M.transpose) 0 0) := by fun_prop
  change Tendsto (fun k => ((p.meanMatrix ^ k) * s.cov *
    (p.meanMatrix ^ k).transpose) 0 0) atTop (𝓝 0)
  simpa only [Function.comp_def, zero_mul, Matrix.zero_apply] using
    (hcont.tendsto 0).comp (External.mean_powers_tendsto_zero jury p hb hw hw1)

theorem freeRisk_nonneg (p : Params) (s : Moments) (hs : s.psd) (k : ℕ) :
    0 ≤ freeRisk p s k := by
  exact (Matrix.PosSemidef.mul_mul_conjTranspose_same hs (p.meanMatrix ^ k)).diag_nonneg

/-- Source Corollary lift(ii), with the supremum justified by decay of the free
mean dynamics rather than added as an independent boundedness assumption. -/
theorem trajectory_risk_defect_sup_bound (jury : External.JuryStability)
    (p : Params) (s : Moments) (hs : s.psd)
    (hb0 : 1 / 2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta))
    (hnoise : 0 ≤ p.noise) (hadd : 0 ≤ p.additive)
    (hload : p.renormNoise < 1) :
    ∀ k, 0 ≤ (p.trajectory s k).R - freeRisk p s k ∧
      (p.trajectory s k).R - freeRisk p s k ≤
        (p.renormNoise * (⨆ j, freeRisk p s j) + p.renormAdditive) /
          (1 - p.renormNoise) := by
  have hbounded := (freeRisk_tendsto_zero jury p s hb1 hw0 hw1).bddAbove_range
  have hsup : ∀ k, freeRisk p s k ≤ ⨆ j, freeRisk p s j := fun k => le_ciSup hbounded k
  have hA : 0 ≤ ⨆ j, freeRisk p s j := le_trans (freeRisk_nonneg p s hs 0) (hsup 0)
  exact trajectory_risk_defect_bound jury p s _ hs hb0 hb1 hw0 hw1 hnoise hadd hload hA hsup

end SparseSGD
