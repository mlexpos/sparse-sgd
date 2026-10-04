import SparseSGD.Probability.LeastSquares.ConditionalProduct

open MeasureTheory
namespace SparseSGD.Probability.LeastSquares

/-- Square integrability is obtained from ordinary product integrals, before
asserting any conditional second-moment identity. -/
theorem kernel_memLp_of_second_moment {d : ℕ} {A X : Type*}
    [MeasurableSpace A] [MeasurableSpace X]
    {α : Measure A} {κ : Measure X} [IsProbabilityMeasure α] [IsProbabilityMeasure κ]
    (K : Vec d → X → Vec d) (hK : Measurable (Function.uncurry K))
    (C D : ℝ) (hK2 : ∀ e, MemLp (K e) 2 κ)
    (hsecond : ∀ e, (∫ x, ‖K e x‖ ^ 2 ∂κ) = C * ‖e‖ ^ 2 + D)
    (U : A → Vec d) (hU : Measurable U) (hU2 : MemLp U 2 α) :
    MemLp (fun z : A × X => K (U z.1) z.2) 2 (α.prod κ) := by
  have hm : Measurable (fun z : A × X => K (U z.1) z.2) :=
    hK.comp (f := fun z : A × X => (U z.1, z.2))
      ((hU.comp measurable_fst).prodMk measurable_snd)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hsq : AEStronglyMeasurable (fun z : A × X => ‖K (U z.1) z.2‖ ^ 2) (α.prod κ) :=
    (hm.norm.pow_const 2).aestronglyMeasurable
  apply (integrable_prod_iff hsq).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun a =>
      (memLp_two_iff_integrable_sq_norm (hK2 (U a)).aestronglyMeasurable).mp (hK2 (U a)))
  · simp only [Real.norm_eq_abs, abs_pow, abs_norm, hsecond]
    exact (((memLp_two_iff_integrable_sq_norm hU2.aestronglyMeasurable).mp hU2).const_mul C).add
      (integrable_const D)

end SparseSGD.Probability.LeastSquares
