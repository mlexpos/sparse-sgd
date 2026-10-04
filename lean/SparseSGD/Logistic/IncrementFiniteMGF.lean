import SparseSGD.Logistic.IncrementProjectionSquareMGF
import SparseSGD.Logistic.IncrementMGFAlgebra
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

theorem finite_exp_sum_le_average {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) :
    Real.exp (∑ i, x i) ≤ (m : ℝ)⁻¹*∑ i, Real.exp ((m : ℝ)*x i) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hw : (∑ _ : Fin m, (m : ℝ)⁻¹) = 1 := by simp [mul_inv_cancel₀ hmr.ne']
  have hh := (convexOn_exp).map_sum_le (t := Finset.univ)
    (w := fun _ : Fin m => (m : ℝ)⁻¹) (p := fun i => (m : ℝ)*x i)
    (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul, ← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hmr.ne', one_mul] at hh
  exact hh

/-- Finite dependent MGF assembly by actual Jensen domination. No
independence between the component random variables is required. -/
theorem finite_exp_integrable_bound {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] {m : ℕ} (hm : 0 < m)
    (f : Fin m → X → ℝ) (hfm : ∀ i, Measurable (f i)) (C : ℝ)
    (hi : ∀ i, Integrable (fun x => Real.exp ((m : ℝ)*f i x)) κ)
    (hb : ∀ i, (∫ x, Real.exp ((m : ℝ)*f i x) ∂κ) ≤ Real.exp C) :
    Integrable (fun x => Real.exp (∑ i, f i x)) κ ∧
    (∫ x, Real.exp (∑ i, f i x) ∂κ) ≤ Real.exp C := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hsumI : Integrable (fun x => ∑ i, Real.exp ((m : ℝ)*f i x)) κ :=
    integrable_finsetSum _ (fun i _ => hi i)
  have hmajor := hsumI.const_mul ((m : ℝ)⁻¹)
  have hmeas : Measurable (fun x => Real.exp (∑ i, f i x)) :=
    Real.measurable_exp.comp (Finset.measurable_sum Finset.univ (fun i _ => hfm i))
  have htarget : Integrable (fun x => Real.exp (∑ i, f i x)) κ := by
    apply hmajor.mono' hmeas.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.abs_exp]
    exact finite_exp_sum_le_average hm (fun i => f i x)
  refine ⟨htarget, ?_⟩
  have hh := integral_mono htarget hmajor (fun x => finite_exp_sum_le_average hm (fun i => f i x))
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)] at hh
  have hbound := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  have hscaled := mul_le_mul_of_nonneg_left hbound (show 0 ≤ (m : ℝ)⁻¹ by positivity)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hmr.ne', one_mul] at hscaled
  exact hh.trans hscaled
def batchProjectionEnergy {d B m : ℕ} (p : unitInterval) (mu theta : Vec d)
    (u : Fin m → Vec d) (a : Batch d B) : ℝ :=
  ∑ i, (inner ℝ (u i) (centeredBatchGradient p mu theta a))^2

/-- A finite family of actual dependent projection squares has the same
rare variance orders. The explicit dimension factor is at most four for
the two active bulk directions used by the Gaussian frame split. -/
theorem tame_batch_projection_energy_mgf {d B m : ℕ}
    (G : SparseSGD.External.GaussianQuadraticCertificate) (p : unitInterval)
    (mu theta : Vec d) (u : Fin m → Vec d) (Q t : ℝ) (hB : 0 < B)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (hθ : ‖theta‖ ≤ Q) (hu : ∀ i, ‖u i‖ ≤ 1) (hmu : ∀ i, |inner ℝ (u i) mu| ≤ 1)
    (ht : |(m : ℝ)*t| ≤ projectionSquareRadius Q B) :
    let Z := batchProjectionEnergy p mu theta u
    Integrable (fun a => Real.exp (t*(Z a-(∫ b, Z b ∂batchLaw d B p)))) (batchLaw d B p) ∧
    (∫ a, Real.exp (t*(Z a-(∫ b, Z b ∂batchLaw d B p))) ∂batchLaw d B p) ≤
      Real.exp (Real.exp (8*Real.exp (2*Q^2+4))*projectionSquareVariance Q p B*((m : ℝ)*t)^2) := by
  by_cases hm : 0 < m
  · let X := fun i : Fin m => fun a : Batch d B => inner ℝ (u i) (centeredBatchGradient p mu theta a)
    let f := fun i : Fin m => fun a : Batch d B => t*((X i a)^2-(∫ b, (X i b)^2 ∂batchLaw d B p))
    have hXm (i : Fin m) : Measurable (X i) := measurable_const.inner
      ((measurable_centeredBatchGradient p mu).comp
        (f := fun a : Batch d B => (theta,a)) (measurable_const.prodMk measurable_id))
    have hXLp (i : Fin m) : MemLp (X i) 2 (batchLaw d B p) := by
      simpa only [X, Function.comp_def, innerSL_apply_apply] using
        ((innerSL ℝ) (u i)).comp_memLp' (centeredBatchGradient_memLp_two p mu theta)
    have he (a : Batch d B) : t*(batchProjectionEnergy p mu theta u a-
        (∫ b, batchProjectionEnergy p mu theta u b ∂batchLaw d B p)) = ∑ i, f i a := by
      dsimp [batchProjectionEnergy, f, X]
      rw [integral_finsetSum _ (fun i _ => (hXLp i).integrable_sq)]
      dsimp only [X]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    have hfe (i : Fin m) (a : Batch d B) : (m : ℝ)*f i a =
        ((m : ℝ)*t)*((X i a)^2-(∫ b, (X i b)^2 ∂batchLaw d B p)) := by dsimp [f]; ring
    have hmgf (i : Fin m) := tame_batch_projection_centered_square_mgf G p mu theta (u i) Q
      ((m : ℝ)*t) hB hp htame hθ (hu i) (hmu i) ht
    have hfm (i : Fin m) : Measurable (f i) := ((hXm i).pow_const 2 |>.sub measurable_const).const_mul t
    have hh := finite_exp_integrable_bound (batchLaw d B p) hm f hfm
      (Real.exp (8*Real.exp (2*Q^2+4))*projectionSquareVariance Q p B*((m : ℝ)*t)^2)
      (fun i => by simp_rw [hfe]; exact (hmgf i).1)
      (fun i => by simp_rw [hfe]; exact (hmgf i).2)
    change Integrable (fun a => Real.exp (t*(batchProjectionEnergy p mu theta u a-
        (∫ b, batchProjectionEnergy p mu theta u b ∂batchLaw d B p)))) _ ∧ _
    simp_rw [he]
    exact hh
  · have hm0 : m = 0 := by omega
    subst m
    simp only [batchProjectionEnergy, Finset.univ_eq_empty, Finset.sum_empty, integral_zero,
      sub_self, mul_zero, Real.exp_zero, Nat.cast_zero, zero_mul, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true]
    exact ⟨integrable_const _, by simp⟩

end
end SparseSGD.Logistic
