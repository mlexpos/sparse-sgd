import SparseSGD.Probability.LeastSquares.SingleSample
import SparseSGD.Probability.LeastSquares.IndependentBatch
import SparseSGD.Probability.LeastSquares.OracleInterface

open MeasureTheory

namespace SparseSGD.Probability.LeastSquares
noncomputable section

private theorem residual_eq_average_centered {d B : ℕ} (hB : 0 < B)
    (p : unitInterval) (e : Vec d) (a : Batch d B) :
    residual p e a = (B : ℝ)⁻¹ • ∑ i, (gradient e (a i) - (p : ℝ) • e) := by
  classical
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  unfold residual batchGradient
  rw [Finset.sum_sub_distrib, smul_sub]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ B ((p : ℝ) • e), smul_smul, inv_mul_cancel₀ hb, one_smul]

/-- The actual iid least-squares batch law supplies every oracle moment. -/
theorem batchOracle {d B : ℕ} (hB : 0 < B) (p : unitInterval) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0) :
    BatchOracle d B p ν := by
  classical
  have hmem (e : Vec d) : MemLp (batchGradient (B := B) e) 2 (batchLaw d B p ν) := by
    exact iid_batch_average_memLp (gradient e) (gradient_memLp e p ν hz)
  have hcenteredMean (e : Vec d) :
      (∫ a, residual p e a ∂batchLaw d B p ν) = 0 := by
    simp_rw [residual_eq_average_centered hB]
    exact iid_batch_average_mean (fun a => gradient e a - (p : ℝ) • e)
      (gradient_centered_memLp e p ν hz) (gradient_centered_integral e p ν hz hmean)
  have hbatchMean (e : Vec d) :
      (∫ a, batchGradient e a ∂batchLaw d B p ν) = (p : ℝ) • e := by
    have hi := (hmem e).integrable (by norm_num)
    have hc := hcenteredMean e
    unfold residual at hc
    rw [integral_sub hi (integrable_const _)] at hc
    simpa using sub_eq_zero.mp hc
  have hcenteredSecond (e : Vec d) :
      (∫ a, ‖residual p e a‖ ^ 2 ∂batchLaw d B p ν) =
        vinc d B p * ‖e‖ ^ 2 + vadd d B p ν := by
    simp_rw [residual_eq_average_centered hB]
    unfold batchLaw
    rw [iid_batch_average_variance hB (fun a => gradient e a - (p : ℝ) • e)
      (gradient_centered_memLp e p ν hz) (gradient_centered_integral e p ν hz hmean)]
    rw [gradient_centered_norm_sq_integral e p ν hz hmean]
    unfold vinc vadd
    ring
  refine ⟨hmem, hbatchMean, ?_, hcenteredMean, hcenteredSecond⟩
  intro e
  have heq := integral_norm_sq_sub_mean (batchGradient e) (hmem e)
    ((p : ℝ) • e) (hbatchMean e)
  change (∫ a, ‖residual p e a‖ ^ 2 ∂batchLaw d B p ν) = _ at heq
  rw [hcenteredSecond, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at heq
  linarith

end
end SparseSGD.Probability.LeastSquares
