import SparseSGD.Logistic.IncrementDualBounds
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

/-- Actual rare linear MGF for a direction with an explicit norm bound. -/
theorem tame_batch_direction_mgf {d B : ℕ}
    (H : SparseSGD.External.BernsteinMomentsCertificate (Sample d)) (p : unitInterval)
    (mu theta u : Vec d) (Q L t : ℝ) (hB : 0 < B) (hp : 0 < (p : ℝ))
    (htame : tameError p mu theta ≤ 1/2) (hθ : ‖theta‖ ≤ Q)
    (hL : 0 ≤ L) (hu : ‖u‖ ≤ L)
    (ht : |t| * (L*projectionScale mu/(B : ℝ)) < 1) :
    Integrable (fun a : Batch d B => Real.exp (t*inner ℝ u (centeredBatchGradient p mu theta a)))
      (batchLaw d B p) ∧
    (∫ a : Batch d B, Real.exp (t*inner ℝ u (centeredBatchGradient p mu theta a)) ∂batchLaw d B p) ≤
      Real.exp (t^2*(L^2*projectionVariance p mu Q/(B : ℝ))/
        (2*(1-|t| * (L*projectionScale mu/(B : ℝ))))) := by
  by_cases hzero : L = 0
  · subst L
    have hu0 : u = 0 := norm_eq_zero.mp (le_antisymm hu (norm_nonneg _))
    subst u
    simp
  · have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm hzero)
    have hunit : ‖L⁻¹ • u‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hLp]
      have hh := mul_le_mul_of_nonneg_left hu (inv_pos.mpr hLp).le
      simpa only [inv_mul_cancel₀ hLp.ne'] using hh
    have ht' : |t*L| * (projectionScale mu/(B : ℝ)) < 1 := by
      rw [abs_mul, abs_of_pos hLp]
      convert ht using 1 <;> ring
    have hh := tame_batch_projection_mgf H p mu theta (L⁻¹ • u) Q (t*L) hB hp htame hθ hunit ht'
    have he (a : Batch d B) : (t*L)*inner ℝ (L⁻¹ • u) (centeredBatchGradient p mu theta a) =
        t*inner ℝ u (centeredBatchGradient p mu theta a) := by
      rw [real_inner_smul_left]
      field_simp
    simp_rw [he] at hh
    refine ⟨hh.1, hh.2.trans_eq ?_⟩
    congr 1
    rw [abs_mul, abs_of_pos hLp]
    ring
end
end SparseSGD.Logistic
