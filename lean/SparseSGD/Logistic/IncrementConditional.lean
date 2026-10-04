import SparseSGD.Logistic.IncrementLinearMGF
import Mathlib.MeasureTheory.Function.ConditionalLExpectation

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

/-- Fresh nonnegative kernels can be integrated conditionally without any
global exponential integrability hypothesis. This is the localization-safe
counterpart of the Bochner fresh-batch formula. -/
theorem increment_condLExp_of_joint_product {Ω A S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν]
    (P : Ω → A) (Y : Ω → S) (hP : Measurable P) (hY : Measurable Y)
    (hjoint : μ.map (fun ω => (P ω, Y ω)) = (μ.map P).prod ν)
    (f : A × S → ℝ≥0∞) (hf : Measurable f) :
    μ⁻[fun ω => f (P ω, Y ω) | MeasurableSpace.comap P inferInstance] =ᵐ[μ]
      fun ω => ∫⁻ y, f (P ω, y) ∂ν := by
  let I : A → ℝ≥0∞ := fun a => ∫⁻ y, f (a,y) ∂ν
  have hI : Measurable I := hf.lintegral_prod_right'
  have hm : MeasurableSpace.comap P inferInstance ≤ ‹MeasurableSpace Ω› := hP.comap_le
  apply (ae_eq_condLExp hm μ (fun ω => f (P ω,Y ω))
    (hI.comp (measurable_iff_comap_le.mpr le_rfl)) ?_).symm
  intro t ht
  rcases ht with ⟨s, hs, rfl⟩
  let F : A × S → ℝ≥0∞ := (Prod.fst ⁻¹' s).indicator f
  have hF : Measurable F := hf.indicator (measurable_fst hs)
  have he (a : A) : (∫⁻ y, F (a,y) ∂ν) = s.indicator I a := by
    by_cases ha : a ∈ s <;> simp [F, I, Set.indicator, ha]
  calc
    (∫⁻ ω in P ⁻¹' s, I (P ω) ∂μ) = ∫⁻ a, s.indicator I a ∂μ.map P := by
      rw [lintegral_map (hI.indicator hs) hP,
        ← lintegral_indicator (hP hs)]
      rfl
    _ = ∫⁻ z, F z ∂(μ.map P).prod ν := by
      rw [lintegral_prod _ hF.aemeasurable]
      simp_rw [he]
    _ = ∫⁻ ω in P ⁻¹' s, f (P ω,Y ω) ∂μ := by
      rw [← hjoint, lintegral_map hF (hP.prodMk hY),
        ← lintegral_indicator (hP hs)]
      rfl

theorem process_fresh_condLExp {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (ρ : Measure (State d)) [IsProbabilityMeasure ρ] (k : ℕ)
    (F : State d × Batch d B → ℝ≥0∞) (hF : Measurable F) :
    (worldLaw p ρ)⁻[fun ω : World d B => F (process eta beta p mu ω k,ω.2 k) | pastSigma d B k]
      =ᵐ[worldLaw p ρ] (fun ω => ∫⁻ a, F (process eta beta p mu ω k,a) ∂batchLaw d B p) := by
  have hm : Measurable (fun z : History d B k × Batch d B =>
      F (historyState eta beta p mu k z.1,z.2)) :=
    hF.comp (f := fun z : History d B k × Batch d B =>
      (historyState eta beta p mu k z.1,z.2))
      (((measurable_historyState d B eta beta p mu k).comp measurable_fst).prodMk measurable_snd)
  have h := increment_condLExp_of_joint_product (worldLaw p ρ) (batchLaw d B p)
    (past (d := d) (B := B) k) (fun ω : World d B => ω.2 k)
    (measurable_past d B k) (measurable_fresh d B k) (past_fresh_jointLaw p ρ k) _ hm
  simpa only [← process_eq_historyState, pastSigma] using h

theorem measurable_meanBatchGradient {d B : ℕ} (p : unitInterval) (mu : Vec d) :
    Measurable (meanBatchGradient (B := B) p mu) :=
  (measurable_batchGradient d B p mu).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_centeredBatchGradient {d B : ℕ} (p : unitInterval) (mu : Vec d) :
    Measurable (fun z : Vec d × Batch d B => centeredBatchGradient p mu z.1 z.2) :=
  (measurable_batchGradient d B p mu).sub ((measurable_meanBatchGradient p mu).comp measurable_fst)

/-- Actual conditional rare linear MGF on a bounded stopped neighborhood.
The statement uses nonnegative conditional expectation, and requires no
exponential integrability of the process outside the neighborhood. -/
theorem process_tame_projection_condLExp {d B : ℕ}
    (H : SparseSGD.External.BernsteinMomentsCertificate (Sample d))
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (ρ : Measure (State d))
    [IsProbabilityMeasure ρ] (k : ℕ) (u : State d → Vec d) (hu : Measurable u)
    (U : Set (State d)) (Q t : ℝ) (hB : 0 < B) (hp : 0 < (p : ℝ))
    (htame : ∀ s ∈ U, tameError p mu s.1 ≤ 1/2)
    (hθ : ∀ s ∈ U, ‖s.1‖ ≤ Q) (hunit : ∀ s ∈ U, ‖u s‖ ≤ 1)
    (ht : |t| * (projectionScale mu/(B : ℝ)) < 1) :
    ∀ᵐ ω ∂worldLaw p ρ, process eta beta p mu ω k ∈ U →
      (worldLaw p ρ)⁻[fun ω : World d B => ENNReal.ofReal (Real.exp
        (t*inner ℝ (u (process eta beta p mu ω k))
          (centeredBatchGradient p mu (process eta beta p mu ω k).1 (ω.2 k)))) | pastSigma d B k] ω ≤
      ENNReal.ofReal (Real.exp (t^2*(projectionVariance p mu Q/(B : ℝ))/
        (2*(1-|t| * (projectionScale mu/(B : ℝ)))))) := by
  let F : State d × Batch d B → ℝ≥0∞ := fun z => ENNReal.ofReal
    (Real.exp (t*inner ℝ (u z.1) (centeredBatchGradient p mu z.1.1 z.2)))
  have hf : Measurable F := by
    have hg : Measurable (fun z : State d × Batch d B => centeredBatchGradient p mu z.1.1 z.2) :=
      (measurable_centeredBatchGradient (B := B) p mu).comp
      (f := fun z : State d × Batch d B => (z.1.1,z.2))
      ((measurable_fst.fst).prodMk measurable_snd)
    exact ENNReal.measurable_ofReal.comp
      (((hu.comp measurable_fst).inner hg).const_mul t).exp
  have he := process_fresh_condLExp eta beta p mu ρ k F hf
  filter_upwards [he] with ω hω hU
  rw [hω]
  have hh := tame_batch_projection_mgf H p mu (process eta beta p mu ω k).1
    (u (process eta beta p mu ω k)) Q t hB hp (htame _ hU) (hθ _ hU) (hunit _ hU) ht
  change (∫⁻ a : Batch d B, ENNReal.ofReal (Real.exp
    (t*inner ℝ (u (process eta beta p mu ω k))
      (centeredBatchGradient p mu (process eta beta p mu ω k).1 a))) ∂batchLaw d B p) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hh.1
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
  exact ENNReal.ofReal_le_ofReal hh.2

end
end SparseSGD.Logistic
