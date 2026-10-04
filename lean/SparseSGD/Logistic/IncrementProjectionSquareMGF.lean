import SparseSGD.Logistic.IncrementCenteredSquare
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

def projectionSquareRadius (Q : ℝ) (B : ℕ) : ℝ :=
  (B : ℝ)/(16*(symmetricProjectionConstant Q 2+9))

def projectionSquareVariance (Q : ℝ) (p : unitInterval) (B : ℕ) : ℝ :=
  128*(symmetricProjectionConstant Q 4*(p : ℝ)/(B : ℝ)^3+
    (symmetricProjectionConstant Q 2)^2*(p : ℝ)^2/(B : ℝ)^2)

theorem projectionSquareRadius_pos (Q : ℝ) (B : ℕ) (hB : 0 < B) :
    0 < projectionSquareRadius Q B := by
  dsimp [projectionSquareRadius, symmetricProjectionConstant]
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  positivity

/-- Actual two-sided centered projection-square MGF with rare variance
`p²/B²+p/B³` and radius proportional to the batch size. -/
theorem tame_batch_projection_centered_square_mgf {d B : ℕ}
    (G : SparseSGD.External.GaussianQuadraticCertificate) (p : unitInterval)
    (mu theta u : Vec d) (Q t : ℝ) (hB : 0 < B)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (hθ : ‖theta‖ ≤ Q) (hu : ‖u‖ ≤ 1) (hmu : |inner ℝ u mu| ≤ 1)
    (ht : |t| ≤ projectionSquareRadius Q B) :
    let f := fun a : Batch d B => inner ℝ u (centeredBatchGradient p mu theta a)
    Integrable (fun a => Real.exp (t*(f a^2-(∫ b, f b^2 ∂batchLaw d B p)))) (batchLaw d B p) ∧
    (∫ a, Real.exp (t*(f a^2-(∫ b, f b^2 ∂batchLaw d B p))) ∂batchLaw d B p) ≤
      Real.exp (Real.exp (8*Real.exp (2*Q^2+4))*projectionSquareVariance Q p B*t^2) := by
  let f := fun a : Batch d B => inner ℝ u (centeredBatchGradient p mu theta a)
  let M := 8*Real.exp (2*Q^2+4)*(p : ℝ)/(B : ℝ)
  have hfm : Measurable f := measurable_const.inner
    ((measurable_centeredBatchGradient p mu).comp
      (f := fun a : Batch d B => (theta,a)) (measurable_const.prodMk measurable_id))
  have hfLp : MemLp f 2 (batchLaw d B p) := by
    simpa only [f, Function.comp_def, innerSL_apply_apply] using
      ((innerSL ℝ) u).comp_memLp' (centeredBatchGradient_memLp_two p mu theta)
  have hmean := tame_batch_projection_second_moment p mu theta u Q hB hp htame hθ hu hmu
  have hV : 0 ≤ projectionSquareVariance Q p B := by
    dsimp [projectionSquareVariance, symmetricProjectionConstant]
    positivity
  have hc : 0 < 16*(symmetricProjectionConstant Q 2+9) := by
    dsimp [symmetricProjectionConstant]
    positivity
  have hbr : 0 < (B : ℝ) := by exact_mod_cast hB
  have hrem (A : ℝ) (hA : 0 ≤ A) (hAs : A ≤ projectionSquareRadius Q B) := by
    have hs : 2*((symmetricProjectionConstant Q 2+9)/(B : ℝ))*A ≤ 1/8 := by
      have hh := (le_div_iff₀ hc).mp hAs
      have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ (B : ℝ)⁻¹ by positivity)
      have he : (B : ℝ)*(B : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hbr.ne'
      rw [he] at hh'
      simp only [div_eq_mul_inv]
      nlinarith
    exact tame_batch_projection_square_remainder G p mu theta u Q A hB hp htame hθ hu hmu hA hs
  have hh := centered_square_mgf_of_remainder (batchLaw d B p) f hfm hfLp.integrable_sq
    (projectionSquareVariance Q p B) M (projectionSquareRadius Q B) t hV
    (projectionSquareRadius_pos Q B hB) ht hmean hrem
  refine ⟨hh.1, hh.2.trans ?_⟩
  apply Real.exp_le_exp.mpr
  have hp1 := p.property.2
  have hc1 : 1 ≤ 16*(symmetricProjectionConstant Q 2+9) := by
    have hn : 0 ≤ symmetricProjectionConstant Q 2 := by dsimp [symmetricProjectionConstant]; positivity
    linarith
  have hrad : projectionSquareRadius Q B ≤ B := by
    apply (div_le_iff₀ hc).mpr
    nlinarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hfactor : projectionSquareRadius Q B*M ≤ 8*Real.exp (2*Q^2+4) := by
    have hm := mul_le_mul_of_nonneg_right hrad hM
    have hm2 := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ 8*Real.exp (2*Q^2+4) by positivity)
    have he : (B : ℝ)*M = 8*Real.exp (2*Q^2+4)*(p : ℝ) := by dsimp [M]; field_simp
    rw [he] at hm
    simpa only [mul_one] using hm.trans hm2
  convert mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hfactor)
    (show 0 ≤ projectionSquareVariance Q p B*t^2 by positivity) using 1 <;> ring
end
end SparseSGD.Logistic
