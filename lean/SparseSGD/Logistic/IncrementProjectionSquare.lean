import SparseSGD.Logistic.IncrementSymmetrization
import SparseSGD.Logistic.IncrementConditional
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

/-- Actual centered batch projections have the rare square-exponential
remainder `p²/B²+p/B³`, including exponential integrability. -/
theorem tame_batch_projection_square_remainder {d B : ℕ}
    (G : SparseSGD.External.GaussianQuadraticCertificate) (p : unitInterval)
    (mu theta u : Vec d) (Q A : ℝ) (hB : 0 < B)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (hθ : ‖theta‖ ≤ Q) (hu : ‖u‖ ≤ 1) (hmu : |inner ℝ u mu| ≤ 1)
    (hA : 0 ≤ A) (hsmall : 2*((symmetricProjectionConstant Q 2+9)/(B : ℝ))*A ≤ 1/8) :
    let f := fun a : Batch d B => inner ℝ u (centeredBatchGradient p mu theta a)
    Integrable (fun a => Real.exp (A*f a^2)) (batchLaw d B p) ∧
    (∫ a, Real.exp (A*f a^2) ∂batchLaw d B p)-1-A*(∫ a, f a^2 ∂batchLaw d B p) ≤
      128*(symmetricProjectionConstant Q 4*(p : ℝ)/(B : ℝ)^3+
        (symmetricProjectionConstant Q 2)^2*(p : ℝ)^2/(B : ℝ)^2)*A^2 := by
  let f := fun a : Batch d B => inner ℝ u (centeredBatchGradient p mu theta a)
  let κ := (sampleLaw d p).prod (sampleLaw d p)
  let ν := Measure.pi (fun _ : Fin B => κ)
  let T := fun z : Fin B → Sample d × Sample d => (B : ℝ)⁻¹*∑ i,
    pairedDifference (fun a : Sample d => inner ℝ u (gradient p mu theta a)) (z i)
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Sample d) (Sample d) (Fin B)
  have he : MeasurePreserving e ν ((batchLaw d B p).prod (batchLaw d B p)) :=
    measurePreserving_arrowProdEquivProdArrow (Sample d) (Sample d) (Fin B)
    (fun _ => sampleLaw d p) (fun _ => sampleLaw d p)
  have hfm : Measurable f := measurable_const.inner
    ((measurable_centeredBatchGradient p mu).comp
      (f := fun a : Batch d B => (theta,a)) (measurable_const.prodMk measurable_id))
  have hfLp : MemLp f 2 (batchLaw d B p) := by
    simpa only [f, Function.comp_def, innerSL_apply_apply] using
      ((innerSL ℝ) u).comp_memLp' (centeredBatchGradient_memLp_two p mu theta)
  have hfzero : (∫ a, f a ∂batchLaw d B p) = 0 := by
    dsimp [f]
    rw [integral_inner ((centeredBatchGradient_memLp_two p mu theta).integrable (by norm_num)),
      centeredBatchGradient_integral, inner_zero_right]
  have hT (z : Fin B → Sample d × Sample d) : T z = f (e z).1-f (e z).2 := by
    dsimp [f]
    rw [centeredBatch_projection_eq_average p mu theta u hB,
      centeredBatch_projection_eq_average p mu theta u hB]
    simp [e, MeasurableEquiv.arrowProdEquivProdArrow,
      Equiv.arrowProdEquivProdArrow, T, pairedDifference, Finset.sum_sub_distrib]
    <;> ring
  have hh (s : ℝ) := tame_paired_batch_projection_fourth_remainder p mu theta u Q s hB hp htame hθ hu hmu
  have hTm : Measurable T := by
    change Measurable (fun z => T z)
    simp_rw [hT]
    exact (hfm.comp (measurable_fst.comp e.measurable)).sub
      (hfm.comp (measurable_snd.comp e.measurable))
  have hs := square_fourth_remainder_of_global G ν T hTm (hh 0).1.integrable_sq
    (symmetricProjectionConstant Q 4*(p : ℝ)/(B : ℝ)^3+
      (symmetricProjectionConstant Q 2)^2*(p : ℝ)^2/(B : ℝ)^2)
    ((symmetricProjectionConstant Q 2+9)/(B : ℝ)) A
    (by dsimp [symmetricProjectionConstant]; positivity) hA hsmall
    (fun s => (hh s).2.1) (fun s => by convert (hh s).2.2 using 1 <;> ring)
  have hpE : Integrable (fun z : Batch d B × Batch d B => Real.exp (A*(f z.1-f z.2)^2))
      ((batchLaw d B p).prod (batchLaw d B p)) := by
    apply (he.integrable_comp_emb e.measurableEmbedding).mp
    simpa only [Function.comp_def, ← hT] using hs.1
  have hpi := he.integral_comp' (fun z : Batch d B × Batch d B => Real.exp (A*(f z.1-f z.2)^2))
  have hpq := he.integral_comp' (fun z : Batch d B × Batch d B => (f z.1-f z.2)^2)
  simp only [← hT] at hpi hpq
  rw [hpi, hpq] at hs
  exact square_remainder_symmetrization (batchLaw d B p) f hfm hfLp hfzero A _ hA hpE hs.2

theorem tame_batch_projection_second_moment {d B : ℕ} (p : unitInterval)
    (mu theta u : Vec d) (Q : ℝ) (hB : 0 < B)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (hθ : ‖theta‖ ≤ Q) (hu : ‖u‖ ≤ 1) (hmu : |inner ℝ u mu| ≤ 1) :
    (∫ a : Batch d B, (inner ℝ u (centeredBatchGradient p mu theta a))^2 ∂batchLaw d B p) ≤
      8*Real.exp (2*Q^2+4)*(p : ℝ)/(B : ℝ) := by
  let X := fun a : Sample d => inner ℝ u (gradient p mu theta a)
  let κ := sampleLaw d p
  let Y := fun a : Sample d => X a-(∫ b, X b ∂κ)
  have hXLp : MemLp X 2 κ := by
    simpa only [X, Function.comp_def, innerSL_apply_apply] using
      ((innerSL ℝ) u).comp_memLp' (gradient_memLp_two d p mu theta)
  have hYLp : MemLp Y 2 κ := hXLp.sub (memLp_const _)
  have hYzero : (∫ a, Y a ∂κ) = 0 := by
    rw [integral_sub (hXLp.integrable (by norm_num)) (integrable_const _), integral_const]
    simp
  have hi := SparseSGD.Probability.LeastSquares.iid_batch_average_variance hB Y hYLp hYzero
  simp only [smul_eq_mul, Real.norm_eq_abs, sq_abs] at hi
  have hactual (a : Batch d B) : inner ℝ u (centeredBatchGradient p mu theta a) =
      (B : ℝ)⁻¹*∑ i, Y (a i) := centeredBatch_projection_eq_average p mu theta u hB a
  simp_rw [hactual]
  change (∫ a : Batch d B, ((B : ℝ)⁻¹*∑ i, Y (a i))^2 ∂Measure.pi (fun _ : Fin B => κ)) ≤ _
  rw [hi]
  have hvar : (∫ a, Y a^2 ∂κ) ≤ (∫ a, X a^2 ∂κ) := by
    rw [← variance_eq_integral hXLp.aemeasurable]
    exact variance_le_expectation_sq hXLp.aestronglyMeasurable
  have hb := tame_global_projection_weighted_moment p mu theta u Q 0 2 (by omega)
    hp htame hθ hu hmu
  simp only [abs_zero, zero_mul, Real.exp_zero, mul_one, sq_abs] at hb
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    zero_pow, mul_zero, Real.exp_zero, mul_one] at hb
  have hbr : 0 < (B : ℝ) := by exact_mod_cast hB
  apply div_le_div_of_nonneg_right (hvar.trans ?_) hbr.le
  simpa only [X, κ] using hb.2.trans_eq (by ring)

end
end SparseSGD.Logistic
