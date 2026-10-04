import SparseSGD.Logistic.IncrementDriftMap
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1400000

/-- An actual matched-state sup-norm bound controls the full parameter norm
and the scaled bulk momentum, including on the boundary of the PSD cone. -/
theorem matchedSummary_norm_controls {d : ℕ} (eta beta : ℝ) (mu : Vec d) (s : State d)
    (hr : 0 < r mu) (T : ℝ) (hT : 0 ≤ T) (hy : ‖matchedSummary eta beta mu s‖ ≤ T) :
    ‖s.1‖ ≤ Real.sqrt (T^2+T) ∧ ‖(eta/(1-beta)) • bulkPart mu s.2‖ ≤ Real.sqrt T := by
  let y := matchedSummary eta beta mu s
  have h0 : |y 0| ≤ T := by simpa using (norm_le_pi_norm y 0).trans hy
  have h2 : y 2 ≤ T := (le_abs_self _).trans (by simpa using (norm_le_pi_norm y 2).trans hy)
  have h4 : y 4 ≤ T := (le_abs_self _).trans (by simpa using (norm_le_pi_norm y 4).trans hy)
  have hsig : (y 0)^2 ≤ T^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (y 0)) hT).2 h0
  have hvar := matchedSummary_variance eta beta mu s hr
  constructor
  · apply Real.le_sqrt_of_sq_le
    change (y 0)^2+y 2=‖s.1‖^2 at hvar
    nlinarith
  · apply Real.le_sqrt_of_sq_le
    have he : ‖(eta/(1-beta)) • bulkPart mu s.2‖^2 = y 4 := by
      rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
      rfl
    rw [he]
    exact h4

/-- Closed tubes around a uniformly bounded reference sequence yield
explicit bounded stopped-neighborhood parameters. -/
theorem matched_neighborhood_norm_bounds {d : ℕ} (eta beta : ℝ) (mu : Vec d) (s : State d)
    (hr : 0 < r mu) (x : ℕ → (Fin 5 → ℝ)) (N : ℕ) (T radius : ℝ)
    (hT : 0 ≤ T) (hradius : 0 ≤ radius) (hx : ∀ i ≤ N, ‖x i‖ ≤ T)
    (hs : ∃ i ≤ N, ‖matchedSummary eta beta mu s-x i‖ ≤ radius) :
    ‖s.1‖ ≤ Real.sqrt ((T+radius)^2+(T+radius)) ∧
      ‖(eta/(1-beta)) • bulkPart mu s.2‖ ≤ Real.sqrt (T+radius) := by
  rcases hs with ⟨i,hi,hsi⟩
  apply matchedSummary_norm_controls eta beta mu s hr (T+radius) (add_nonneg hT hradius)
  calc
    ‖matchedSummary eta beta mu s‖ = ‖(matchedSummary eta beta mu s-x i)+x i‖ := by congr 1; module
    _ ≤ ‖matchedSummary eta beta mu s-x i‖+‖x i‖ := norm_add_le _ _
    _ ≤ radius+T := add_le_add hsi (hx i hi)
    _ = T+radius := by ring
def stoppedTameConstant {d : ℕ} (mu : Vec d) (Q : ℝ) : ℝ :=
  Real.exp (2*Q^2)+Real.exp (3*Q^2/2)+(1+Real.exp (Q^2/2))*Real.exp (Q*r mu)

theorem stoppedTameConstant_pos {d : ℕ} (mu : Vec d) (Q : ℝ) :
    0 < stoppedTameConstant mu Q := by dsimp [stoppedTameConstant]; positivity

/-- Tameness on a stopped norm ball follows from an explicit small-`p`
condition. The constant may depend on the fixed signal norm. -/
theorem tameError_le_stoppedNorm {d : ℕ} (p : unitInterval) (mu theta : Vec d) (Q : ℝ)
    (hQ : 0 ≤ Q) (htheta : ‖theta‖ ≤ Q) :
    tameError p mu theta ≤ (p : ℝ)*stoppedTameConstant mu Q := by
  have hs : ‖theta‖^2 ≤ Q^2 := by nlinarith [norm_nonneg theta]
  have hinner : |inner ℝ theta mu| ≤ Q*r mu := by
    have h := norm_inner_le_norm (𝕜 := ℝ) theta mu
    rw [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_right htheta (norm_nonneg mu))
  unfold tameError stoppedTameConstant
  apply mul_le_mul_of_nonneg_left _ p.property.1
  apply add_le_add
  · exact add_le_add (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖mu‖]))
      (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖mu‖]))
  · apply mul_le_mul
    · apply add_le_add le_rfl
      unfold gaussianAlpha
      exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖mu‖])
    · exact Real.exp_le_exp.mpr hinner
    · exact (Real.exp_pos _).le
    · positivity

def matchedTubeParameterBound (T radius : ℝ) : ℝ := Real.sqrt ((T+radius)^2+(T+radius))
def matchedTubeMomentumBound (T radius : ℝ) : ℝ := Real.sqrt (T+radius)

theorem matched_neighborhood_tame_bounds {d : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (hr : 0 < r mu) (x : ℕ → (Fin 5 → ℝ)) (N : ℕ) (T radius : ℝ)
    (hT : 0 ≤ T) (hradius : 0 ≤ radius) (hx : ∀ i ≤ N, ‖x i‖ ≤ T)
    (hp : (p : ℝ)*stoppedTameConstant mu (matchedTubeParameterBound T radius) ≤ 1/2)
    (s : State d) (hs : ∃ i ≤ N, ‖matchedSummary eta beta mu s-x i‖ ≤ radius) :
    tameError p mu s.1 ≤ 1/2 ∧ ‖s.1‖ ≤ matchedTubeParameterBound T radius ∧
      ‖(eta/(1-beta)) • bulkPart mu s.2‖ ≤ matchedTubeMomentumBound T radius := by
  have hh := matched_neighborhood_norm_bounds eta beta mu s hr x N T radius hT hradius hx hs
  exact ⟨(tameError_le_stoppedNorm p mu s.1 _ (Real.sqrt_nonneg _) hh.1).trans hp,hh⟩
end
end SparseSGD.Logistic
