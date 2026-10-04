import SparseSGD.Foundations
import Mathlib.MeasureTheory.Function.ConditionalLExpectation

/-! The cited scalar conditional Bernstein inequality. This certificate states
only a standard martingale concentration result, not a fluid-limit conclusion.
Nonnegative conditional expectations avoid any prior exponential-integrability
assumption. The strict tail event also covers zero variance and zero scale.

References: Boucheron--Lugosi--Massart (2013), Section 2.4 and Corollary 2.11;
Freedman (1975), martingale Bernstein inequalities.
-/
open MeasureTheory
open scoped ENNReal
namespace SparseSGD.External

structure MartingaleBernsteinCertificate (Ω : Type*) [mΩ : MeasurableSpace Ω] : Prop where
  tail : ∀ (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ)
    (K : ℕ) (v M L : ℝ),
    0 ≤ v → 0 ≤ M → 0 < L →
    (∀ j < K, StronglyMeasurable[ℱ (j+1)] (Y j)) →
    (∀ j < K, ∀ t : ℝ, |t| * M < 1 →
      μ⁻[fun ω => ENNReal.ofReal (Real.exp (t * Y j ω)) | ℱ j] ≤ᵐ[μ]
        fun _ => ENNReal.ofReal (Real.exp (t^2 * v / (2 * (1 - |t| * M))))) →
    μ {ω | Real.sqrt (2 * K * v * L) + 2 * M * L <
      |∑ j ∈ Finset.range K, Y j ω|} ≤ ENNReal.ofReal (2 * Real.exp (-L))

end SparseSGD.External
