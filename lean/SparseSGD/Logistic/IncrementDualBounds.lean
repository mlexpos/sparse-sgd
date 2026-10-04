import SparseSGD.Logistic.IncrementDualDecomposition
import SparseSGD.Logistic.TameCoefficients
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

theorem increment_abs_two_weights (c e w v : ℝ) (hw : |w| ≤ 1) (hv : |v| ≤ 1) :
    |c*w+e*v| ≤ |c|+|e| := by
  have hc := mul_le_mul_of_nonneg_left hw (abs_nonneg c)
  have he := mul_le_mul_of_nonneg_left hv (abs_nonneg e)
  have hh := abs_add_le (c*w) (e*v)
  simp only [abs_mul, mul_one] at *
  linarith

theorem matchedDualQuadraticCoefficient_abs_le {eta beta : ℝ} (w : Fin 5 → ℝ)
    (hbeta : 0 ≤ beta) (hbeta1 : beta < 1) (hw : ∀ i, |w i| ≤ 1) :
    |matchedDualQuadraticCoefficient eta beta w| ≤ 3*eta^2 := by
  have heps : 0 < 1-beta := by linarith
  have heps1 : 1-beta ≤ 1 := by linarith
  have h12 := increment_abs_two_weights ((1-beta)^2) (-(1-beta)) (w 2) (w 3) (hw 2) (hw 3)
  have hh := abs_add_le ((1-beta)^2*w 2-(1-beta)*w 3) (w 4)
  have hepssq : (1-beta)^2 ≤ 1 := by nlinarith
  simp only [abs_of_nonneg (sq_nonneg (1-beta)), abs_neg, abs_of_pos heps] at h12
  have hcore : |(1-beta)^2*w 2-(1-beta)*w 3+w 4| ≤ 3 := by
    rw [neg_mul, ← sub_eq_add_neg] at h12
    linarith [hw 4]
  have hm := mul_le_mul_of_nonneg_left hcore (sq_nonneg eta)
  simpa only [matchedDualQuadraticCoefficient, abs_mul, abs_of_nonneg (sq_nonneg eta), mul_comm] using hm

theorem matchedDualLinearDirection_norm_le_unit_weights {d B : ℕ}
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (w : Fin 5 → ℝ) (s : State d)
    (hr : 0 < r mu) (heta : 0 ≤ eta) (hbeta : 0 ≤ beta) (hbeta1 : beta < 1)
    (hw : ∀ i, |w i| ≤ 1) :
    ‖matchedDualLinearDirection (B := B) eta beta p mu w s‖ ≤
      eta*(2+3*‖bulkPart mu (meanUpdate (B := B) eta beta p mu s).1‖+
        3*(eta/(1-beta))*‖bulkPart mu (meanUpdate (B := B) eta beta p mu s).2‖) := by
  have heps : 0 < 1-beta := by linarith
  have heps1 : 1-beta ≤ 1 := by linarith
  have hsig := increment_abs_two_weights (-eta*(1-beta)) eta (w 0) (w 1) (hw 0) (hw 1)
  have htheta := increment_abs_two_weights (-2*eta*(1-beta)) eta (w 2) (w 3) (hw 2) (hw 3)
  have hm := increment_abs_two_weights (-eta^2) (2*eta^2/(1-beta)) (w 3) (w 4) (hw 3) (hw 4)
  have hsig' : |-eta*(1-beta)*w 0+eta*w 1| ≤ 2*eta := by
    have hneg : -eta*(1-beta) ≤ 0 := by nlinarith
    rw [abs_of_nonpos hneg, abs_of_nonneg heta] at hsig
    nlinarith
  have htheta' : |-2*eta*(1-beta)*w 2+eta*w 3| ≤ 3*eta := by
    have hneg : -2*eta*(1-beta) ≤ 0 := by nlinarith
    rw [abs_of_nonpos hneg, abs_of_nonneg heta] at htheta
    nlinarith
  have hm' : |-eta^2*w 3+2*eta^2/(1-beta)*w 4| ≤ 3*eta^2/(1-beta) := by
    have hq : 0 ≤ 2*eta^2/(1-beta) := by positivity
    rw [abs_neg, abs_of_nonneg (sq_nonneg eta), abs_of_nonneg hq] at hm
    have hsq := (le_div_iff₀ heps).mpr
      (show eta^2*(1-beta) ≤ eta^2 by nlinarith [sq_nonneg eta])
    rw [show 3*eta^2/(1-beta) = eta^2/(1-beta)+2*eta^2/(1-beta) by ring]
    linarith
  have hmain := matchedDualLinearDirection_norm_le (B := B) eta beta p mu w s hr
  have htheta2 := mul_le_mul_of_nonneg_right htheta' (norm_nonneg (bulkPart mu (meanUpdate (B := B) eta beta p mu s).1))
  have hm2 := mul_le_mul_of_nonneg_right hm' (norm_nonneg (bulkPart mu (meanUpdate (B := B) eta beta p mu s).2))
  calc
    _ ≤ 2*eta+3*eta*‖bulkPart mu (meanUpdate (B := B) eta beta p mu s).1‖+
      (3*eta^2/(1-beta))*‖bulkPart mu (meanUpdate (B := B) eta beta p mu s).2‖ := by linarith
    _ = _ := by ring

end
end SparseSGD.Logistic
