import SparseSGD.Logistic.IncrementDirectionMGF
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

theorem tame_coefA_abs_le_on_norm_ball {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (Q : ℝ) (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2) (hθ : ‖theta‖ ≤ Q) :
    |coefA p mu theta| ≤ 4*Real.exp (Q^2/2)*(p : ℝ) := by
  have hQ : 0 ≤ Q := (norm_nonneg _).trans hθ
  have hα : gaussianAlpha mu theta ≤ Real.exp (Q^2/2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ‖mu‖, norm_nonneg theta]
  have hpa : 0 ≤ (p : ℝ)*gaussianAlpha mu theta := mul_nonneg hp.le (gaussianAlpha_pos mu theta).le
  have hc := (tame_coefficients p mu theta hp htame).1
  have hsmall := mul_le_mul_of_nonneg_left htame (show 0 ≤ 6*(p : ℝ)*gaussianAlpha mu theta by nlinarith)
  have hs := abs_add_le (coefA p mu theta-(p : ℝ)*gaussianAlpha mu theta)
    ((p : ℝ)*gaussianAlpha mu theta)
  rw [sub_add_cancel, abs_of_nonneg hpa] at hs
  have hαp := mul_le_mul_of_nonneg_right hα hp.le
  nlinarith

theorem meanUpdate_bulk_momentum_formula {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) (hB : 0 < B) :
    bulkPart mu (meanUpdate (B := B) eta beta p mu s).2 =
      beta • bulkPart mu s.2+((1-beta)*coefA p mu s.1) • bulkPart mu s.1 := by
  simp only [meanUpdate, bulkPart_add, bulkPart_smul, meanBatchGradient,
    batchGradient_integral H hB, bulkPart_self, smul_zero, add_zero, smul_smul]

theorem meanUpdate_bulk_parameter_formula {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) (hB : 0 < B) :
    bulkPart mu (meanUpdate (B := B) eta beta p mu s).1 =
      (1-eta*(1-beta)*coefA p mu s.1) • bulkPart mu s.1-
        (eta*beta) • bulkPart mu s.2 := by
  simp only [meanUpdate, bulkPart_sub, bulkPart_add, bulkPart_smul, meanBatchGradient,
    batchGradient_integral H hB, bulkPart_self, smul_zero, add_zero, smul_smul, smul_add]
  module

theorem meanUpdate_bulk_parameter_scaled_formula {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) (hB : 0 < B) (hb : beta ≠ 1) :
    bulkPart mu (meanUpdate (B := B) eta beta p mu s).1 =
      (1-eta*(1-beta)*coefA p mu s.1) • bulkPart mu s.1-
        ((1-beta)*beta) • ((eta/(1-beta)) • bulkPart mu s.2) := by
  rw [meanUpdate_bulk_parameter_formula H eta beta p mu s hB, smul_smul]
  congr 2
  field_simp [sub_ne_zero.mpr (Ne.symm hb)]

theorem meanUpdate_bulk_momentum_scaled_formula {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) (hB : 0 < B) (hb : beta ≠ 1) :
    (eta/(1-beta)) • bulkPart mu (meanUpdate (B := B) eta beta p mu s).2 =
      beta • ((eta/(1-beta)) • bulkPart mu s.2)+
        (eta*coefA p mu s.1) • bulkPart mu s.1 := by
  rw [meanUpdate_bulk_momentum_formula H eta beta p mu s hB]
  simp only [smul_add, smul_smul]
  congr 1
  · congr 1
    ring
  · congr 1
    field_simp [sub_ne_zero.mpr (Ne.symm hb)]

/-- Actual mean-update bulk norms on the stopped neighborhood, with the
learning-step hypothesis displayed explicitly. -/
theorem meanUpdate_bulk_norm_bounds {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) (Q K L : ℝ) (hB : 0 < B)
    (heta : 0 ≤ eta) (hbeta : 0 ≤ beta) (hbeta1 : beta < 1)
    (hθ : ‖bulkPart mu s.1‖ ≤ Q)
    (hm : ‖(eta/(1-beta)) • bulkPart mu s.2‖ ≤ K)
    (hstep : eta*|coefA p mu s.1| ≤ L) :
    ‖bulkPart mu (meanUpdate (B := B) eta beta p mu s).1‖ ≤ (1+L)*Q+K ∧
    ‖(eta/(1-beta)) • bulkPart mu (meanUpdate (B := B) eta beta p mu s).2‖ ≤ K+L*Q := by
  have heps : 0 < 1-beta := by linarith
  have heps1 : 1-beta ≤ 1 := by linarith
  have hb : beta ≠ 1 := ne_of_lt hbeta1
  have hQ : 0 ≤ Q := (norm_nonneg _).trans hθ
  have hK : 0 ≤ K := (norm_nonneg _).trans hm
  have hL : 0 ≤ L := (mul_nonneg heta (abs_nonneg _)).trans hstep
  have hcoef : |1-eta*(1-beta)*coefA p mu s.1| ≤ 1+L := by
    have hh := abs_sub 1 (eta*(1-beta)*coefA p mu s.1)
    rw [abs_one, abs_mul, abs_mul, abs_of_nonneg heta, abs_of_pos heps] at hh
    have hscale := mul_le_mul_of_nonneg_right heps1
      (mul_nonneg heta (abs_nonneg (coefA p mu s.1)))
    nlinarith
  have hbetaeps : 0 ≤ (1-beta)*beta := mul_nonneg heps.le hbeta
  have hbetaeps1 : (1-beta)*beta ≤ 1 := by nlinarith
  constructor
  · rw [meanUpdate_bulk_parameter_scaled_formula H eta beta p mu s hB hb]
    have hn := norm_sub_le
      ((1-eta*(1-beta)*coefA p mu s.1) • bulkPart mu s.1)
      (((1-beta)*beta) • ((eta/(1-beta)) • bulkPart mu s.2))
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hbetaeps] at hn
    have hleft := mul_le_mul hcoef hθ (norm_nonneg _) (by positivity : 0 ≤ 1+L)
    have hright := mul_le_mul hbetaeps1 hm (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simp only [norm_smul, Real.norm_eq_abs] at hright
    nlinarith
  · rw [meanUpdate_bulk_momentum_scaled_formula H eta beta p mu s hB hb]
    have hn := norm_add_le
      (beta • ((eta/(1-beta)) • bulkPart mu s.2))
      ((eta*coefA p mu s.1) • bulkPart mu s.1)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hbeta, abs_mul, abs_of_nonneg heta] at hn
    have hleft := mul_le_mul (le_of_lt hbeta1) hm (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hright := mul_le_mul hstep hθ (norm_nonneg _) hL
    simp only [norm_smul, Real.norm_eq_abs] at hleft
    nlinarith

theorem matchedDualLinearDirection_norm_le_stopped {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (w : Fin 5 → ℝ) (s : State d) (Q K L : ℝ) (hB : 0 < B)
    (hr : 0 < r mu) (heta : 0 ≤ eta) (hbeta : 0 ≤ beta) (hbeta1 : beta < 1)
    (hw : ∀ i, |w i| ≤ 1) (hθ : ‖bulkPart mu s.1‖ ≤ Q)
    (hm : ‖(eta/(1-beta)) • bulkPart mu s.2‖ ≤ K)
    (hstep : eta*|coefA p mu s.1| ≤ L) :
    ‖matchedDualLinearDirection (B := B) eta beta p mu w s‖ ≤
      eta*(2+3*(1+2*L)*Q+6*K) := by
  have hn := meanUpdate_bulk_norm_bounds H eta beta p mu s Q K L hB heta hbeta hbeta1 hθ hm hstep
  have hh := matchedDualLinearDirection_norm_le_unit_weights (B := B) eta beta p mu w s hr heta hbeta hbeta1 hw
  have heps : 0 < 1-beta := by linarith
  have hscaled := hn.2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg heta heps.le)] at hscaled
  have hbound : 2+3*‖bulkPart mu (meanUpdate (B := B) eta beta p mu s).1‖+
      3*(eta/(1-beta))*‖bulkPart mu (meanUpdate (B := B) eta beta p mu s).2‖ ≤
      2+3*(1+2*L)*Q+6*K := by nlinarith [hn.1]
  exact hh.trans (mul_le_mul_of_nonneg_left hbound heta)

def stoppedDirectionBound (Q K L : ℝ) : ℝ :=
  2+3*(1+8*Real.exp (Q^2/2)*L)*Q+6*K

/-- On an actual stopped norm neighborhood, bounded `eta*p` controls the
full five-coordinate dual's linear coefficient. This is the explicit
learning-step correction required by LRinc. -/
theorem matchedDualLinearDirection_norm_le_bounded_learning_step {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (ell : (Fin 5 → ℝ) →L[ℝ] ℝ) (s : State d) (Q K L : ℝ) (hB : 0 < B)
    (hr : 0 < r mu) (heta : 0 ≤ eta) (hbeta : 0 ≤ beta) (hbeta1 : beta < 1)
    (hell : ‖ell‖ ≤ 1) (hp : 0 < (p : ℝ)) (htame : tameError p mu s.1 ≤ 1/2)
    (hθ : ‖s.1‖ ≤ Q) (hm : ‖(eta/(1-beta)) • bulkPart mu s.2‖ ≤ K)
    (hstep : eta*(p : ℝ) ≤ L) :
    ‖matchedDualLinearDirection (B := B) eta beta p mu (fun i => ell (Pi.single i 1)) s‖ ≤
      eta*stoppedDirectionBound Q K L := by
  have hbulk : ‖bulkPart mu s.1‖ ≤ Q := by
    have hh := bulkPart_norm_sq mu s.1 hr
    nlinarith [norm_nonneg (bulkPart mu s.1), norm_nonneg s.1, (norm_nonneg s.1).trans hθ,
      sq_nonneg (inner ℝ s.1 mu), div_nonneg (sq_nonneg (inner ℝ s.1 mu)) (sq_nonneg (r mu))]
  have hA := tame_coefA_abs_le_on_norm_ball p mu s.1 Q hp htame hθ
  have hstepA : eta*|coefA p mu s.1| ≤ 4*Real.exp (Q^2/2)*L := by
    have h1 := mul_le_mul_of_nonneg_left hA heta
    have h2 := mul_le_mul_of_nonneg_left hstep (show 0 ≤ 4*Real.exp (Q^2/2) by positivity)
    nlinarith
  have hh := matchedDualLinearDirection_norm_le_stopped H eta beta p mu
    (fun i => ell (Pi.single i 1)) s Q K (4*Real.exp (Q^2/2)*L) hB hr heta hbeta hbeta1
    (fun i => (matched_dual_coordinate_abs_le ell i).trans hell) hbulk hm hstepA
  exact hh.trans_eq (by dsimp [stoppedDirectionBound]; ring)

end
end SparseSGD.Logistic
