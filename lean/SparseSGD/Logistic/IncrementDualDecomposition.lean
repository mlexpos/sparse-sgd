import SparseSGD.Logistic.IncrementQuadraticConditional
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

theorem increment_bulk_inner_mu_zero {d : ℕ} (mu x : Vec d) (hr : 0 < r mu) :
    inner ℝ (bulkPart mu x) mu = 0 := by
  have hm : inner ℝ mu mu = (r mu)^2 := real_inner_self_eq_norm_sq mu
  simp only [bulkPart, signalCoord, inner_sub_left, real_inner_smul_left, hm]
  field_simp
  <;> ring

theorem increment_inner_bulk_projection {d : ℕ} (mu x y : Vec d) (hr : 0 < r mu) :
    inner ℝ (bulkPart mu x) (bulkPart mu y) = inner ℝ (bulkPart mu x) y := by
  change inner ℝ (bulkPart mu x) (y-signalCoord mu y • (r mu)⁻¹ • mu) = _
  simp only [inner_sub_right, real_inner_smul_right,
    increment_bulk_inner_mu_zero mu x hr, mul_zero, sub_zero]

def matchedDualLinearDirection {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (w : Fin 5 → ℝ) (s : State d) : Vec d :=
  (-eta*(1-beta)*w 0+eta*w 1) • ((r mu)⁻¹ • mu)+
    (-2*eta*(1-beta)*w 2+eta*w 3) • bulkPart mu (meanUpdate (B := B) eta beta p mu s).1+
    (-eta^2*w 3+2*eta^2/(1-beta)*w 4) • bulkPart mu (meanUpdate (B := B) eta beta p mu s).2

def matchedDualQuadraticCoefficient (eta beta : ℝ) (w : Fin 5 → ℝ) : ℝ :=
  eta^2*((1-beta)^2*w 2-(1-beta)*w 3+w 4)

/-- Every dual projection of the actual five-coordinate increment is
one actual gradient projection plus a centered bulk square. -/
theorem matchedIncrement_dual_decomposition {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (w : Fin 5 → ℝ) (s : State d) (a : Batch d B)
    (hr : 0 < r mu) (hb : beta ≠ 1) :
    (∑ i, w i*matchedIncrement eta beta p mu s a i) =
      inner ℝ (matchedDualLinearDirection (B := B) eta beta p mu w s)
        (centeredBatchGradient p mu s.1 a)+
      matchedDualQuadraticCoefficient eta beta w*centeredBulkSquare p mu s.1 a := by
  have he : signalCoord mu (centeredBatchGradient p mu s.1 a) =
      inner ℝ ((r mu)⁻¹ • mu) (centeredBatchGradient p mu s.1 a) := by
    dsimp [signalCoord]
    rw [real_inner_smul_left, real_inner_comm mu]
    ring
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change w 0*matchedIncrement eta beta p mu s a 0+
    (w 1*matchedIncrement eta beta p mu s a 1+
    (w 2*matchedIncrement eta beta p mu s a 2+
    (w 3*matchedIncrement eta beta p mu s a 3+
     w 4*matchedIncrement eta beta p mu s a 4))) = _
  rw [matchedIncrement_signal_parameter, matchedIncrement_signal_momentum eta beta p mu s a hb,
    matchedIncrement_bulk_parameter, matchedIncrement_bulk_covariance eta beta p mu s a hb,
    matchedIncrement_bulk_momentum eta beta p mu s a hb, he,
    increment_inner_bulk_projection mu _ _ hr, increment_inner_bulk_projection mu _ _ hr]
  simp only [matchedDualLinearDirection, matchedDualQuadraticCoefficient, inner_add_left,
    real_inner_smul_left]
  ring
theorem matched_dual_coordinates (ell : (Fin 5 → ℝ) →L[ℝ] ℝ) (y : Fin 5 → ℝ) :
    ell y = ∑ i, ell (Pi.single i 1)*y i := by
  calc
    ell y = ell (∑ i, y i • Pi.single i 1) := congrArg ell (pi_eq_sum_univ' y)
    _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul, mul_comm]

theorem matched_dual_coordinate_abs_le (ell : (Fin 5 → ℝ) →L[ℝ] ℝ) (i : Fin 5) :
    |ell (Pi.single i 1)| ≤ ‖ell‖ := by
  simpa only [Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one] using ell.le_opNorm (Pi.single i 1)

theorem matchedIncrement_continuousDual_decomposition {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (ell : (Fin 5 → ℝ) →L[ℝ] ℝ) (s : State d) (a : Batch d B)
    (hr : 0 < r mu) (hb : beta ≠ 1) :
    ell (matchedIncrement eta beta p mu s a) =
      inner ℝ (matchedDualLinearDirection (B := B) eta beta p mu (fun i => ell (Pi.single i 1)) s)
        (centeredBatchGradient p mu s.1 a)+
      matchedDualQuadraticCoefficient eta beta (fun i => ell (Pi.single i 1))*centeredBulkSquare p mu s.1 a := by
  rw [matched_dual_coordinates]
  exact matchedIncrement_dual_decomposition eta beta p mu _ s a hr hb

theorem matchedDualLinearDirection_norm_le {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (w : Fin 5 → ℝ) (s : State d) (hr : 0 < r mu) :
    ‖matchedDualLinearDirection (B := B) eta beta p mu w s‖ ≤
      |-eta*(1-beta)*w 0+eta*w 1|+
      |-2*eta*(1-beta)*w 2+eta*w 3| * ‖bulkPart mu (meanUpdate (B := B) eta beta p mu s).1‖+
      |-eta^2*w 3+2*eta^2/(1-beta)*w 4| * ‖bulkPart mu (meanUpdate (B := B) eta beta p mu s).2‖ := by
  have hunit : ‖(r mu)⁻¹ • mu‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    change (r mu)⁻¹*r mu = 1
    exact inv_mul_cancel₀ hr.ne'
  unfold matchedDualLinearDirection
  have h1 := norm_add_le
    ((-eta*(1-beta)*w 0+eta*w 1) • ((r mu)⁻¹ • mu))
    ((-2*eta*(1-beta)*w 2+eta*w 3) • bulkPart mu (meanUpdate (B := B) eta beta p mu s).1)
  have h2 := norm_add_le
    ((-eta*(1-beta)*w 0+eta*w 1) • ((r mu)⁻¹ • mu)+
      (-2*eta*(1-beta)*w 2+eta*w 3) • bulkPart mu (meanUpdate (B := B) eta beta p mu s).1)
    ((-eta^2*w 3+2*eta^2/(1-beta)*w 4) • bulkPart mu (meanUpdate (B := B) eta beta p mu s).2)
  simp only [norm_smul, Real.norm_eq_abs, hunit, mul_one] at h1 h2
  linarith

end
end SparseSGD.Logistic
