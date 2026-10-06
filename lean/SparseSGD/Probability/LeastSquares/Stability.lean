import SparseSGD.Probability.LeastSquares.Public
import SparseSGD.Discrete.Stability

open MeasureTheory

namespace SparseSGD.Probability.LeastSquares
noncomputable section

/-- Reciprocal critical learning rate, including both noise and curvature feedback. -/
def inverseCriticalRate (d B : ℕ) (p : unitInterval) (beta : ℝ) : ℝ :=
  ((d : ℝ) + 2 - p) / (2 * B) + (p : ℝ) / 2 * ((1 - beta) / (1 + beta))

def criticalRate (d B : ℕ) (p : unitInterval) (beta : ℝ) : ℝ :=
  (inverseCriticalRate d B p beta)⁻¹

theorem params_totalLoad (d B : ℕ) (p : unitInterval) (hp : (p : ℝ) ≠ 0)
    (ν : Measure ℝ) (beta eta : ℝ) :
    (params d B p ν beta eta).totalLoad = eta * inverseCriticalRate d B p beta := by
  unfold params oracleParams Params.totalLoad Params.curvature vinc inverseCriticalRate
  field_simp

theorem inverseCriticalRate_pos (d B : ℕ) (hB : 0 < B) (p : unitInterval)
    (beta : ℝ) (hb0 : 0 ≤ beta) (hb1 : beta < 1) :
    0 < inverseCriticalRate d B p beta := by
  unfold inverseCriticalRate
  have hp0 := p.2.1
  have hp1 := p.2.2
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hfirst : 0 < ((d : ℝ) + 2 - p) / (2 * B) :=
    div_pos (by linarith) (by positivity)
  have hsecond : 0 ≤ (p : ℝ) / 2 * ((1 - beta) / (1 + beta)) := by positivity
  linarith

/-- For a nondegenerate sparse oracle, the exact feedback threshold is η < η₊. -/
theorem totalLoad_lt_one_iff_eta_lt_critical (d B : ℕ) (hB : 0 < B)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (ν : Measure ℝ)
    (beta eta : ℝ) (hb0 : 0 ≤ beta) (hb1 : beta < 1) :
    (params d B p ν beta eta).totalLoad < 1 ↔ eta < criticalRate d B p beta := by
  rw [params_totalLoad d B p hp.ne' ν beta eta]
  rw [criticalRate, ← one_div]
  exact (lt_div_iff₀ (inverseCriticalRate_pos d B hB p beta hb0 hb1)).symm

/-- The LS floor numerator depends on the learning rate and batch size. -/
theorem params_additive (d B : ℕ) (p : unitInterval) (hp : (p : ℝ) ≠ 0)
    (ν : Measure ℝ) (beta eta : ℝ) :
    (params d B p ν beta eta).additive = labelVariance ν * eta * d / (2 * B) := by
  unfold params oracleParams vadd
  field_simp

theorem leastSquares_floor_formula (d B : ℕ) (p : unitInterval) (hp : (p : ℝ) ≠ 0)
    (ν : Measure ℝ) (beta eta : ℝ) :
    (params d B p ν beta eta).additive / (1 - (params d B p ν beta eta).totalLoad) =
      (labelVariance ν * eta * d / (2 * B)) /
        (1 - eta * inverseCriticalRate d B p beta) := by
  rw [params_additive d B p hp ν beta eta, params_totalLoad d B p hp ν beta eta]

end
end SparseSGD.Probability.LeastSquares
