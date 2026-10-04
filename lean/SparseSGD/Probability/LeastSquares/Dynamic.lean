import SparseSGD.Probability.LeastSquares.KernelL2
import SparseSGD.Probability.LeastSquares.Freshness
import SparseSGD.Probability.LeastSquares.Process
import SparseSGD.Probability.LeastSquares.OracleInterface

open MeasureTheory
namespace SparseSGD.Probability.LeastSquares
noncomputable section

variable {d B : ℕ} (p : unitInterval) (ν : Measure ℝ) (ρ : Measure (State d))
  [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

theorem fresh_kernel_facts (k : ℕ) (K : Vec d → Batch d B → Vec d)
    (hK : Measurable (Function.uncurry K)) (C D : ℝ)
    (hK2 : ∀ e, MemLp (K e) 2 (batchLaw d B p ν))
    (hsecond : ∀ e, (∫ a, ‖K e a‖ ^ 2 ∂batchLaw d B p ν) = C * ‖e‖ ^ 2 + D)
    (U : History d B k → Vec d) (hU : Measurable U)
    (hU2 : MemLp (fun ω : World d B => U (past k ω)) 2 (worldLaw p ν ρ)) :
    MemLp (fun ω : World d B => K (U (past k ω)) (ω.2 k)) 2 (worldLaw p ν ρ) ∧
    (worldLaw p ν ρ)[fun ω => K (U (past k ω)) (ω.2 k) | pastSigma d B k] =ᵐ[worldLaw p ν ρ]
      (fun ω => ∫ a, K (U (past k ω)) a ∂batchLaw d B p ν) ∧
    (worldLaw p ν ρ)[fun ω => ‖K (U (past k ω)) (ω.2 k)‖ ^ 2 | pastSigma d B k] =ᵐ[worldLaw p ν ρ]
      (fun ω => C * ‖U (past k ω)‖ ^ 2 + D) := by
  letI : IsProbabilityMeasure (pastLaw (B := B) p ν ρ k) := by unfold pastLaw; infer_instance
  have hu : MemLp U 2 (pastLaw (B := B) p ν ρ k) :=
    (memLp_map_measure_iff hU.aestronglyMeasurable (measurable_past k).aemeasurable).mpr hU2
  have hp := kernel_memLp_of_second_moment K hK C D hK2 hsecond U hU hu
  have hm : Measurable (fun z : History d B k × Batch d B => K (U z.1) z.2) :=
    hK.comp (f := fun z : History d B k × Batch d B => (U z.1, z.2))
      ((hU.comp measurable_fst).prodMk measurable_snd)
  have hraw : MemLp (fun ω : World d B => K (U (past k ω)) (ω.2 k)) 2 (worldLaw p ν ρ) := by
    apply (memLp_map_measure_iff hm.aestronglyMeasurable
      ((measurable_past k).prodMk (measurable_fresh k)).aemeasurable).mp
    rwa [past_fresh_jointLaw p ν ρ k]
  refine ⟨hraw, ?_, ?_⟩
  · exact condExp_of_joint_product (past k) (fun ω : World d B => ω.2 k)
      (measurable_past k) (measurable_fresh k) (past_fresh_jointLaw p ν ρ k)
      _ hm.stronglyMeasurable (hp.integrable (by norm_num))
  · have h := condExp_of_joint_product (past k) (fun ω : World d B => ω.2 k)
      (measurable_past k) (measurable_fresh k) (past_fresh_jointLaw p ν ρ k)
      (fun z : History d B k × Batch d B => ‖K (U z.1) z.2‖ ^ 2)
      (hm.norm.pow_const 2).stronglyMeasurable
      ((memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp)
    simpa only [hsecond, pastSigma] using h

theorem process_memLp (O : BatchOracle d B p ν) (beta eta : ℝ)
    (he0 : MemLp (fun s : State d => s.1) 2 ρ)
    (hq0 : MemLp (fun s : State d => s.2) 2 ρ) (k : ℕ) :
    MemLp (fun ω : World d B => (process beta eta ω k).1) 2 (worldLaw p ν ρ) ∧
    MemLp (fun ω : World d B => (process beta eta ω k).2) 2 (worldLaw p ν ρ) := by
  induction k with
  | zero =>
    constructor
    · exact he0.comp_fst _
    · exact hq0.comp_fst _
  | succ k ih =>
    have h := fresh_kernel_facts p ν ρ k (batchGradient (B := B))
      (measurable_batchGradient d B) ((p : ℝ)^2 + vinc d B p) (vadd d B p ν)
      O.memLp O.second (fun h => (historyState beta eta k h).1)
      (measurable_historyState d B beta eta k).fst
      (by simpa only [← process_eq_historyState] using ih.1)
    have hg : MemLp (fun ω : World d B => batchGradient (process beta eta ω k).1 (ω.2 k))
        2 (worldLaw p ν ρ) := by simpa only [← process_eq_historyState] using h.1
    have hq := (ih.2.const_smul beta).add (hg.const_smul (eta * (1-beta)))
    exact ⟨ih.1.sub hq, hq⟩

theorem process_oracle_facts (O : BatchOracle d B p ν) (beta eta : ℝ)
    (he0 : MemLp (fun s : State d => s.1) 2 ρ)
    (hq0 : MemLp (fun s : State d => s.2) 2 ρ) (k : ℕ) :
    MemLp (fun ω : World d B => residual p (process beta eta ω k).1 (ω.2 k)) 2
      (worldLaw p ν ρ) ∧
    (worldLaw p ν ρ)[fun ω => residual p (process beta eta ω k).1 (ω.2 k) |
      pastSigma d B k] =ᵐ[worldLaw p ν ρ] 0 ∧
    (worldLaw p ν ρ)[fun ω => ‖residual p (process beta eta ω k).1 (ω.2 k)‖ ^ 2 |
      pastSigma d B k] =ᵐ[worldLaw p ν ρ]
      (fun ω => vinc d B p * ‖(process beta eta ω k).1‖ ^ 2 + vadd d B p ν) := by
  have hm : Measurable (Function.uncurry (residual (d := d) (B := B) p)) :=
    (measurable_batchGradient d B).sub (measurable_fst.const_smul (p : ℝ))
  have hi (e : Vec d) : MemLp (residual p e) 2 (batchLaw d B p ν) :=
    (O.memLp e).sub (memLp_const ((p : ℝ) • e))
  have h := fresh_kernel_facts p ν ρ k (residual p) hm (vinc d B p) (vadd d B p ν)
    hi O.centered_second (fun h => (historyState beta eta k h).1)
    (measurable_historyState d B beta eta k).fst
    (by simpa only [← process_eq_historyState] using
      (process_memLp p ν ρ O beta eta he0 hq0 k).1)
  simpa only [← process_eq_historyState, O.centered_mean, Pi.zero_def] using h

theorem process_gradient_condExp (O : BatchOracle d B p ν) (beta eta : ℝ)
    (he0 : MemLp (fun s : State d => s.1) 2 ρ)
    (hq0 : MemLp (fun s : State d => s.2) 2 ρ) (k : ℕ) :
    (worldLaw p ν ρ)[fun ω => batchGradient (process beta eta ω k).1 (ω.2 k) |
      pastSigma d B k] =ᵐ[worldLaw p ν ρ]
      (fun ω => (p : ℝ) • (process beta eta ω k).1) := by
  have h := fresh_kernel_facts p ν ρ k (batchGradient (B := B))
    (measurable_batchGradient d B) ((p : ℝ)^2 + vinc d B p) (vadd d B p ν)
    O.memLp O.second (fun h => (historyState beta eta k h).1)
    (measurable_historyState d B beta eta k).fst
    (by simpa only [← process_eq_historyState] using
      (process_memLp p ν ρ O beta eta he0 hq0 k).1)
  simpa only [← process_eq_historyState, O.mean] using h.2.1

end
end SparseSGD.Probability.LeastSquares
