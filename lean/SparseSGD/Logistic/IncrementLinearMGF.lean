import SparseSGD.Logistic.IncrementDecomposition
import SparseSGD.Logistic.IncrementMoments
import SparseSGD.External.BernsteinMoments

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

def projectionVariance (p : unitInterval) (mu : Vec d) (Q : ℝ) : ℝ :=
  8*((p : ℝ)*rareProjectionConstant Q)*(1+r mu)^2

def projectionScale (mu : Vec d) : ℝ := 2*(1+r mu)

/-- Actual single-sample gradient projection MGF, with every moment premise
of the scalar Bernstein theorem discharged from the logistic distribution. -/
theorem tame_single_projection_mgf {d : ℕ}
    (H : SparseSGD.External.BernsteinMomentsCertificate (Sample d))
    (p : unitInterval) (mu theta u : Vec d) (Q t : ℝ)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (hθ : ‖theta‖ ≤ Q) (hu : ‖u‖ ≤ 1) (ht : |t| * projectionScale mu < 1) :
    Integrable (fun a : Sample d => Real.exp (t*(inner ℝ u (gradient p mu theta a) -
      ∫ b, inner ℝ u (gradient p mu theta b) ∂sampleLaw d p))) (sampleLaw d p) ∧
    (∫ a : Sample d, Real.exp (t*(inner ℝ u (gradient p mu theta a) -
      ∫ b, inner ℝ u (gradient p mu theta b) ∂sampleLaw d p)) ∂sampleLaw d p) ≤
      Real.exp (t^2*projectionVariance p mu Q/(2*(1-|t| * projectionScale mu))) := by
  have hmeas : Measurable (fun a : Sample d => inner ℝ u (gradient p mu theta a)) :=
    measurable_const.inner ((measurable_gradient d p mu).comp
      (f := fun a : Sample d => (theta, a)) (measurable_const.prodMk measurable_id))
  exact H.centered_mgf (sampleLaw d p) _ ((p : ℝ)*rareProjectionConstant Q) (1+r mu) t
    hmeas ((gradient_memLp_two d p mu theta).integrable (by norm_num) |>.const_inner (𝕜 := ℝ) u)
    (mul_nonneg hp.le (rareProjectionConstant_pos Q).le) (by dsimp [r]; positivity)
    (residual_projection_moment_integrable p mu theta u)
    (tame_unit_gradient_projection_moments p mu theta u Q hp htame hθ hu) ht

theorem centeredBatch_projection_eq_average {d B : ℕ} (p : unitInterval) (mu theta u : Vec d)
    (hB : 0 < B) (a : Batch d B) :
    inner ℝ u (centeredBatchGradient p mu theta a) =
      (B : ℝ)⁻¹*∑ i, (inner ℝ u (gradient p mu theta (a i)) -
        ∫ b, inner ℝ u (gradient p mu theta b) ∂sampleLaw d p) := by
  have hmean : meanBatchGradient (B := B) p mu theta =
      ∫ b, gradient p mu theta b ∂sampleLaw d p := by
    unfold meanBatchGradient
    have hg := (gradient_memLp_two d p mu theta).integrable (by norm_num)
    have hi (i : Fin B) : Integrable (fun a : Batch d B => gradient p mu theta (a i))
        (batchLaw d B p) :=
      (measurePreserving_eval (fun _ : Fin B => sampleLaw d p) i).integrable_comp_of_integrable hg
    simp only [batchGradient]
    rw [integral_smul, integral_finsetSum _ (fun i _ => hi i)]
    have he (i : Fin B) : (∫ a : Batch d B, gradient p mu theta (a i) ∂batchLaw d B p) =
        ∫ b, gradient p mu theta b ∂sampleLaw d p :=
      integral_comp_eval (μ := fun _ : Fin B => sampleLaw d p) (i := i) hg.aestronglyMeasurable
    simp_rw [he]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rw [inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hB), one_smul]
  simp only [centeredBatchGradient, hmean, batchGradient, inner_sub_right,
    real_inner_smul_right, inner_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [integral_inner ((gradient_memLp_two d p mu theta).integrable (by norm_num))]
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  field_simp
  <;> ring

/-- The actual fresh iid batch has the rare `p/B` linear variance factor.
Exponential integrability is included, so later conditional transport does
not rely on a totalized Bochner expectation. -/
theorem tame_batch_projection_mgf {d B : ℕ}
    (H : SparseSGD.External.BernsteinMomentsCertificate (Sample d))
    (p : unitInterval) (mu theta u : Vec d) (Q t : ℝ) (hB : 0 < B)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (hθ : ‖theta‖ ≤ Q) (hu : ‖u‖ ≤ 1)
    (ht : |t| * (projectionScale mu/(B : ℝ)) < 1) :
    Integrable (fun a : Batch d B => Real.exp (t*inner ℝ u (centeredBatchGradient p mu theta a)))
      (batchLaw d B p) ∧
    (∫ a : Batch d B, Real.exp (t*inner ℝ u (centeredBatchGradient p mu theta a)) ∂batchLaw d B p) ≤
      Real.exp (t^2*(projectionVariance p mu Q/(B : ℝ))/(2*(1-|t| * (projectionScale mu/(B : ℝ))))) := by
  simp_rw [centeredBatch_projection_eq_average p mu theta u hB]
  exact SparseSGD.External.iid_average_mgf (sampleLaw d p)
    (fun a => inner ℝ u (gradient p mu theta a) - ∫ b, inner ℝ u (gradient p mu theta b) ∂sampleLaw d p)
    B hB (projectionVariance p mu Q) (projectionScale mu) t
    (by unfold projectionScale r; positivity) ht
    (fun s hs => tame_single_projection_mgf H p mu theta u Q s hp htame hθ hu hs)

end
end SparseSGD.Logistic
