import SparseSGD.Probability.LeastSquares.Dynamic
import SparseSGD.Probability.LeastSquares.SourceFiltration

open MeasureTheory
namespace SparseSGD.Probability.LeastSquares
noncomputable section

variable {d B : ℕ} (p : unitInterval) (ν : Measure ℝ) (ρ : Measure (State d))
  [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

private theorem source_condExp_of_past {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (beta eta : ℝ) (k : ℕ)
    (f g : World d B → E)
    (hf : (worldLaw p ν ρ)[f | pastSigma d B k] =ᵐ[worldLaw p ν ρ] g)
    (hg : StronglyMeasurable[sourceSigma d B beta eta k] g)
    (hgi : Integrable g (worldLaw p ν ρ)) :
    (worldLaw p ν ρ)[f | sourceSigma d B beta eta k] =ᵐ[worldLaw p ν ρ] g := by
  have hle := sourceSigma_le_pastSigma d B beta eta k
  have hamb := pastSigma_le_ambient (d := d) (B := B) k
  have ht := condExp_condExp_of_le (μ := worldLaw p ν ρ) (f := f) hle hamb
  have hc := condExp_congr_ae (m := sourceSigma d B beta eta k) hf
  rw [condExp_of_stronglyMeasurable (hle.trans hamb) hg hgi] at hc
  exact ht.symm.trans hc

theorem process_source_oracle_facts (O : BatchOracle d B p ν) (beta eta : ℝ)
    (he0 : MemLp (fun s : State d => s.1) 2 ρ)
    (hq0 : MemLp (fun s : State d => s.2) 2 ρ) (k : ℕ) :
    MemLp (fun ω : World d B => residual p (process beta eta ω k).1 (ω.2 k)) 2
      (worldLaw p ν ρ) ∧
    (worldLaw p ν ρ)[fun ω => residual p (process beta eta ω k).1 (ω.2 k) |
      sourceSigma d B beta eta k] =ᵐ[worldLaw p ν ρ] 0 ∧
    (worldLaw p ν ρ)[fun ω => ‖residual p (process beta eta ω k).1 (ω.2 k)‖ ^ 2 |
      sourceSigma d B beta eta k] =ᵐ[worldLaw p ν ρ]
      (fun ω => vinc d B p * ‖(process beta eta ω k).1‖ ^ 2 + vadd d B p ν) := by
  have h := process_oracle_facts p ν ρ O beta eta he0 hq0 k
  refine ⟨h.1, ?_, ?_⟩
  · exact source_condExp_of_past p ν ρ beta eta k _ _ h.2.1
      stronglyMeasurable_zero (integrable_zero _ _ _)
  · have hs := process_sourceSigma_measurable d B beta eta k
    have hg : StronglyMeasurable[sourceSigma d B beta eta k]
        (fun ω : World d B => vinc d B p * ‖(process beta eta ω k).1‖ ^ 2 +
          vadd d B p ν) := by
      letI : MeasurableSpace (World d B) := sourceSigma d B beta eta k
      exact (((hs.fst.norm.pow_const 2).const_mul (vinc d B p)).add measurable_const).stronglyMeasurable
    have he := (process_memLp p ν ρ O beta eta he0 hq0 k).1
    have hi : Integrable (fun ω : World d B => ‖(process beta eta ω k).1‖ ^ 2)
        (worldLaw p ν ρ) :=
      (memLp_two_iff_integrable_sq_norm he.aestronglyMeasurable).mp he
    exact source_condExp_of_past p ν ρ beta eta k _ _ h.2.2 hg
      ((hi.const_mul (vinc d B p)).add (integrable_const (vadd d B p ν)))

theorem process_source_gradient_condExp (O : BatchOracle d B p ν) (beta eta : ℝ)
    (he0 : MemLp (fun s : State d => s.1) 2 ρ)
    (hq0 : MemLp (fun s : State d => s.2) 2 ρ) (k : ℕ) :
    (worldLaw p ν ρ)[fun ω => batchGradient (process beta eta ω k).1 (ω.2 k) |
      sourceSigma d B beta eta k] =ᵐ[worldLaw p ν ρ]
      (fun ω => (p : ℝ) • (process beta eta ω k).1) := by
  have hs := process_sourceSigma_measurable d B beta eta k
  exact source_condExp_of_past p ν ρ beta eta k _ _
    (process_gradient_condExp p ν ρ O beta eta he0 hq0 k)
    (by
      letI : MeasurableSpace (World d B) := sourceSigma d B beta eta k
      exact (hs.fst.const_smul (p : ℝ)).stronglyMeasurable)
    (((process_memLp p ν ρ O beta eta he0 hq0 k).1.const_smul (p : ℝ)).integrable
      (by norm_num))

end
end SparseSGD.Probability.LeastSquares
