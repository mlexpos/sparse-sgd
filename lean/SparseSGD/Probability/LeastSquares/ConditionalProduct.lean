import SparseSGD.Probability.LeastSquares.Model

open MeasureTheory
namespace SparseSGD.Probability.LeastSquares

variable {Ω A S E : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure S} [IsProbabilityMeasure ν]

/-- A fresh product coordinate can be integrated out conditionally on the past.
The product-law premise is supplied by Freshness for the canonical SGD model. -/
theorem condExp_of_joint_product (P : Ω → A) (Y : Ω → S)
    (hP : Measurable P) (hY : Measurable Y)
    (hjoint : μ.map (fun ω => (P ω, Y ω)) = (μ.map P).prod ν)
    (f : A × S → E) (hf : StronglyMeasurable f)
    (hi : Integrable f ((μ.map P).prod ν)) :
    μ[fun ω => f (P ω, Y ω) | MeasurableSpace.comap P inferInstance] =ᵐ[μ]
      fun ω => ∫ y, f (P ω, y) ∂ν := by
  let I : A → E := fun a => ∫ y, f (a, y) ∂ν
  have hIs : StronglyMeasurable I := hf.integral_prod_right'
  have hIi : Integrable I (μ.map P) := hi.integral_prod_left
  have hgi : Integrable (fun ω => I (P ω)) μ :=
    (integrable_map_measure hIs.aestronglyMeasurable hP.aemeasurable).mp hIi
  have hfi : Integrable (fun ω => f (P ω, Y ω)) μ := by
    apply (integrable_map_measure hf.aestronglyMeasurable (hP.prodMk hY).aemeasurable).mp
    rwa [hjoint]
  have hm : MeasurableSpace.comap P inferInstance ≤ ‹MeasurableSpace Ω› := hP.comap_le
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hfi
  · intro t ht _
    exact hgi.integrableOn
  · intro t ht _
    rcases ht with ⟨s, hs, rfl⟩
    let F : A × S → E := (Prod.fst ⁻¹' s).indicator f
    have hFs : StronglyMeasurable F := hf.indicator (measurable_fst hs)
    have hFi : Integrable F ((μ.map P).prod ν) := hi.indicator (measurable_fst hs)
    have hF (a : A) : (∫ y, F (a, y) ∂ν) = s.indicator I a := by
      by_cases ha : a ∈ s <;> simp [F, I, Set.indicator, ha]
    calc
      (∫ ω in P ⁻¹' s, I (P ω) ∂μ) = ∫ a, s.indicator I a ∂μ.map P := by
        rw [integral_map hP.aemeasurable (hIs.indicator hs).aestronglyMeasurable,
          ← integral_indicator (hP hs)]
        congr 1
      _ = ∫ z, F z ∂(μ.map P).prod ν := by
        rw [integral_prod _ hFi]
        simp_rw [hF]
      _ = ∫ ω in P ⁻¹' s, f (P ω, Y ω) ∂μ := by
        rw [← hjoint, integral_map (hP.prodMk hY).aemeasurable hFs.aestronglyMeasurable,
          ← integral_indicator (hP hs)]
        congr 1
  · exact hIs.comp_measurable (measurable_iff_comap_le.mpr le_rfl) |>.aestronglyMeasurable

end SparseSGD.Probability.LeastSquares
