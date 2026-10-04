import SparseSGD.Foundations

open MeasureTheory

namespace SparseSGD

/-- The scalar pull-out step behind vanishing error/noise cross terms. -/
theorem integral_mul_noise_eq_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)] {f ξ : Ω → ℝ}
    (hf : AEStronglyMeasurable[m] f μ)
    (hprod : Integrable (fun ω => f ω * ξ ω) μ) (hξ : Integrable ξ μ)
    (hzero : μ[ξ | m] =ᵐ[μ] 0) :
    ∫ ω, f ω * ξ ω ∂μ = 0 := by
  rw [← integral_condExp hm]
  calc
    (∫ ω, μ[fun ω => f ω * ξ ω | m] ω ∂μ) =
        ∫ ω, f ω * μ[ξ | m] ω ∂μ :=
      integral_congr_ae (condExp_mul_of_aestronglyMeasurable_left hf hprod hξ)
    _ = 0 := by
      have heq : (fun ω => f ω * μ[ξ | m] ω) =ᵐ[μ] 0 := by
        filter_upwards [hzero] with ω hω
        simp [hω]
      rw [integral_congr_ae heq]
      simp

/-- Vector-valued version used for traced covariance updates. -/
theorem integral_inner_noise_eq_zero {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)] {f ξ : Ω → E}
    (hf : AEStronglyMeasurable[m] f μ)
    (hprod : Integrable (fun ω => inner ℝ (f ω) (ξ ω)) μ) (hξ : Integrable ξ μ)
    (hzero : μ[ξ | m] =ᵐ[μ] 0) :
    ∫ ω, inner ℝ (f ω) (ξ ω) ∂μ = 0 := by
  rw [← integral_condExp hm]
  calc
    (∫ ω, μ[fun ω => inner ℝ (f ω) (ξ ω) | m] ω ∂μ) =
        ∫ ω, inner ℝ (f ω) (μ[ξ | m] ω) ∂μ :=
      integral_congr_ae (condExp_bilin_of_aestronglyMeasurable_left
        (innerSL ℝ) hf hprod hξ)
    _ = 0 := by
      have heq : (fun ω => inner ℝ (f ω) (μ[ξ | m] ω)) =ᵐ[μ] 0 := by
        filter_upwards [hzero] with ω hω
        simp [hω]
      rw [integral_congr_ae heq]
      simp

end SparseSGD
