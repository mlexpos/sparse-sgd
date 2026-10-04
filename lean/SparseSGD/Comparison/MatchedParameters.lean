import SparseSGD.Comparison.Similarity
import SparseSGD.Continuum.CovarianceFlow
import Mathlib.Analysis.SpecialFunctions.Arcosh

namespace SparseSGD
noncomputable section

def Params.matchedStep (p : Params) : ℝ := -Real.log p.beta
def Params.traceCosine (p : Params) : ℝ := (1 + p.beta - p.w) / (2 * Real.sqrt p.beta)
def Params.matchingSign (p : Params) : ℝ := if 0 ≤ p.traceCosine then 1 else -1
def Params.foldedAngle (p : Params) : ℝ := Real.arccos |p.traceCosine|
def Params.matchedDelta (p : Params) : ℝ :=
  if |p.traceCosine| ≤ 1 then 1/4 + (p.foldedAngle / p.matchedStep)^2
  else 1/4 - (Real.arcosh |p.traceCosine| / p.matchedStep)^2
def Params.matchedMeanFlow (p : Params) : Matrix (Fin 2) (Fin 2) ℝ :=
  continuumMeanFlow p.matchedDelta p.matchedStep
def Params.matchingMatrix (p : Params) : Matrix (Fin 2) (Fin 2) ℝ :=
  matchingP p.matchingSign p.matchedMeanFlow p

theorem Params.matchedStep_pos (p : Params) (hb0 : 0 < p.beta) (hb1 : p.beta < 1) :
    0 < p.matchedStep := neg_pos.mpr (Real.log_neg hb0 hb1)

theorem Params.exp_neg_matchedStep (p : Params) (hb : 0 < p.beta) :
    Real.exp (-p.matchedStep) = p.beta := by
  simp [Params.matchedStep, Real.exp_log hb]

theorem Params.matchingSign_sq (p : Params) : p.matchingSign ^ 2 = 1 := by
  unfold Params.matchingSign
  split_ifs <;> norm_num

theorem Params.foldedAngle_bounds (p : Params) :
    0 ≤ p.foldedAngle ∧ p.foldedAngle ≤ Real.pi / 2 :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.mpr (abs_nonneg _)⟩

theorem Params.matchedDelta_critical (p : Params) (hc : |p.traceCosine| = 1) :
    p.matchedDelta = 1/4 := by
  simp [Params.matchedDelta, Params.foldedAngle, hc]

theorem Params.matchedDelta_underdamped (p : Params) (hc : |p.traceCosine| ≤ 1) :
    0 < p.matchedDelta := by
  simp only [Params.matchedDelta, hc, ite_true]
  positivity

/-- The first-row normalization uniquely determines a similarity intertwiner.
No spectral argument or diagonalization is needed for this uniqueness step. -/
theorem matchingP_unique (p : Params) (sign : ℝ) (G P : Matrix (Fin 2) (Fin 2) ℝ)
    (hb : p.beta ≠ 0) (hrow : P 0 = ![1, 0])
    (hinter : p.meanMatrix * P = sign • (P * G)) : P = matchingP sign G p := by
  have h00 : P 0 0 = 1 := congrFun hrow 0
  have h01 : P 0 1 = 0 := congrFun hrow 1
  have h0 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) hinter
  have h1 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hinter
  simp [Params.meanMatrix, Matrix.mul_apply, Fin.sum_univ_two, h00, h01] at h0 h1
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [matchingP] using h00
  · simpa [matchingP] using h01
  · change P 1 0 = (1 - p.w - sign * G 0 0) / p.beta
    apply (eq_div_iff hb).mpr
    linear_combination -h0
  · change P 1 1 = -sign * G 0 1 / p.beta
    apply (eq_div_iff hb).mpr
    linear_combination -h1

end
end SparseSGD
