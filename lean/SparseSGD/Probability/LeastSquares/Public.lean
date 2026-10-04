import SparseSGD.Probability.LeastSquares.Trajectory

open MeasureTheory
namespace SparseSGD.Probability.LeastSquares
noncomputable section

variable {d B : ℕ} (hB : 0 < B) (p : unitInterval)
  (ν : Measure ℝ) (ρ : Measure (State d))
  [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
  (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0) (beta eta : ℝ)
  (he0 : MemLp (fun s : State d => s.1) 2 ρ)
  (hq0 : MemLp (fun s : State d => s.2) 2 ρ)

include hB hz hmean he0 hq0

/-- Square integrability propagated from the initial state under the actual sample law. -/
theorem leastSquares_process_memLp (k : ℕ) :
    MemLp (fun ω : World d B => (process beta eta ω k).1) 2 (worldLaw p ν ρ) ∧
    MemLp (fun ω : World d B => (process beta eta ω k).2) 2 (worldLaw p ν ρ) :=
  process_memLp p ν ρ (batchOracle hB p ν hz hmean) beta eta he0 hq0 k

/-- The centered oracle in the manuscript's gradient-history filtration.
This includes both endpoints of the sparsification interval. -/
theorem leastSquares_conditional_oracle (k : ℕ) :
    MemLp (fun ω : World d B => residual p (process beta eta ω k).1 (ω.2 k)) 2
      (worldLaw p ν ρ) ∧
    (worldLaw p ν ρ)[fun ω => residual p (process beta eta ω k).1 (ω.2 k) |
      sourceSigma d B beta eta k] =ᵐ[worldLaw p ν ρ] 0 ∧
    (worldLaw p ν ρ)[fun ω => ‖residual p (process beta eta ω k).1 (ω.2 k)‖ ^ 2 |
      sourceSigma d B beta eta k] =ᵐ[worldLaw p ν ρ]
      (fun ω => vinc d B p * ‖(process beta eta ω k).1‖ ^ 2 + vadd d B p ν) :=
  process_source_oracle_facts p ν ρ (batchOracle hB p ν hz hmean) beta eta he0 hq0 k

theorem leastSquares_conditional_gradient (k : ℕ) :
    (worldLaw p ν ρ)[fun ω => batchGradient (process beta eta ω k).1 (ω.2 k) |
      sourceSigma d B beta eta k] =ᵐ[worldLaw p ν ρ]
      (fun ω => (p : ℝ) • (process beta eta ω k).1) :=
  process_source_gradient_condExp p ν ρ (batchOracle hB p ν hz hmean) beta eta he0 hq0 k

end
end SparseSGD.Probability.LeastSquares
