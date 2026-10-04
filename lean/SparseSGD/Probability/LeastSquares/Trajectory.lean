import SparseSGD.Probability.LeastSquares.BatchOracle
import SparseSGD.Probability.LeastSquares.SourceOracle

open MeasureTheory
namespace SparseSGD.Probability.LeastSquares
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

def integratedMoments {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure Ω) (e q : Ω → E) : Moments :=
  ⟨∫ ω, ‖e ω‖ ^ 2 ∂μ, ∫ ω, ‖q ω‖ ^ 2 ∂μ, ∫ ω, inner ℝ (e ω) (q ω) ∂μ⟩

theorem gramMoments_toLp {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure Ω}
    (e q : Ω → E) (he : MemLp e 2 μ) (hq : MemLp q 2 μ) :
    gramMoments (he.toLp e) (hq.toLp q) = integratedMoments μ e q := by
  apply Moments.ext
  · change ‖he.toLp e‖ ^ 2 = _
    rw [l2_norm_sq]
    exact integral_congr_ae (he.coeFn_toLp.fun_comp (fun v => ‖v‖ ^ 2))
  · change ‖hq.toLp q‖ ^ 2 = _
    rw [l2_norm_sq]
    exact integral_congr_ae (hq.coeFn_toLp.fun_comp (fun v => ‖v‖ ^ 2))
  · change inner ℝ (he.toLp e) (hq.toLp q) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [he.coeFn_toLp, hq.coeFn_toLp] with ω heω hqω
    simp only [heω, hqω]

/-- Internal integration theorem. Its oracle premise is discharged by
`batchOracle` in the public least-squares theorem below. -/
theorem integrated_trajectory_of_oracle {d B : ℕ} (p : unitInterval) (hp : (p : ℝ) ≠ 0)
    (ν : Measure ℝ) (ρ : Measure (State d)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (O : BatchOracle d B p ν) (beta eta : ℝ)
    (he0 : MemLp (fun s : State d => s.1) 2 ρ)
    (hq0 : MemLp (fun s : State d => s.2) 2 ρ) (k : ℕ) :
    integratedMoments (worldLaw p ν ρ)
      (fun ω : World d B => (process beta eta ω k).1)
      (fun ω : World d B => (process beta eta ω k).2) =
    (params d B p ν beta eta).trajectory
      (integratedMoments ρ Prod.fst Prod.snd) k := by
  let μ := worldLaw (B := B) p ν ρ
  let e : ℕ → World d B → Vec d := fun k ω => (process beta eta ω k).1
  let q : ℕ → World d B → Vec d := fun k ω => (process beta eta ω k).2
  let x : ℕ → World d B → Vec d := fun k ω => residual p (e k ω) (ω.2 k)
  have he (k) : MemLp (e k) 2 μ := (process_memLp p ν ρ O beta eta he0 hq0 k).1
  have hq (k) : MemLp (q k) 2 μ := (process_memLp p ν ρ O beta eta he0 hq0 k).2
  have hx (k) : MemLp (x k) 2 μ := (process_source_oracle_facts p ν ρ O beta eta he0 hq0 k).1
  let eL : ℕ → Lp (Vec d) 2 μ := fun k => (he k).toLp (e k)
  let qL : ℕ → Lp (Vec d) 2 μ := fun k => (hq k).toLp (q k)
  let xL : ℕ → Lp (Vec d) 2 μ := fun k => (hx k).toLp (x k)
  have heL (k) : eL k =ᵐ[μ] e k := (he k).coeFn_toLp
  have hqL (k) : qL k =ᵐ[μ] q k := (hq k).coeFn_toLp
  have hxL (k) : xL k =ᵐ[μ] x k := (hx k).coeFn_toLp
  have heAdapt (k) : AEStronglyMeasurable[sourceSigma d B beta eta k] (eL k) μ := by
    have hm := (process_sourceSigma_measurable d B beta eta k).fst
    exact hm.stronglyMeasurable.aestronglyMeasurable.congr (heL k).symm
  have hqAdapt (k) : AEStronglyMeasurable[sourceSigma d B beta eta k] (qL k) μ := by
    have hm := (process_sourceSigma_measurable d B beta eta k).snd
    exact hm.stronglyMeasurable.aestronglyMeasurable.congr (hqL k).symm
  have hz (k) : μ[xL k | sourceSigma d B beta eta k] =ᵐ[μ] 0 :=
    (condExp_congr_ae (hxL k)).trans
      (process_source_oracle_facts p ν ρ O beta eta he0 hq0 k).2.1
  have hv (k) : μ[fun ω => ‖xL k ω‖ ^ 2 | sourceSigma d B beta eta k] =ᵐ[μ]
      (fun ω => vinc d B p * ‖eL k ω‖ ^ 2 + vadd d B p ν) := by
    apply (condExp_congr_ae ((hxL k).fun_comp (fun v => ‖v‖ ^ 2))).trans
    apply (process_source_oracle_facts p ν ρ O beta eta he0 hq0 k).2.2.trans
    exact ((heL k).fun_comp (fun v => vinc d B p * ‖v‖ ^ 2 + vadd d B p ν)).symm
  have heStep (k) : eL (k+1) = (1-eta*(1-beta)*(p : ℝ)) • eL k -
      beta • qL k - (eta*(1-beta)) • xL k := by
    have hraw : e (k+1) = (1-eta*(1-beta)*(p : ℝ)) • e k -
        beta • q k - (eta*(1-beta)) • x k := by
      funext ω
      dsimp [e, q, x, process, update, residual]
      module
    have hmem := (((he k).const_smul (1-eta*(1-beta)*(p : ℝ))).sub
      ((hq k).const_smul beta)).sub ((hx k).const_smul (eta*(1-beta)))
    have hh := MemLp.toLp_congr (he (k+1)) hmem (Filter.EventuallyEq.of_eq hraw)
    exact hh
  have hqStep (k) : qL (k+1) = (eta*(1-beta)*(p : ℝ)) • eL k +
      beta • qL k + (eta*(1-beta)) • xL k := by
    have hraw : q (k+1) = (eta*(1-beta)*(p : ℝ)) • e k +
        beta • q k + (eta*(1-beta)) • x k := by
      funext ω
      dsimp [e, q, x, process, update, residual]
      module
    have hmem := (((he k).const_smul (eta*(1-beta)*(p : ℝ))).add
      ((hq k).const_smul beta)).add ((hx k).const_smul (eta*(1-beta)))
    have hh := MemLp.toLp_congr (hq (k+1)) hmem (Filter.EventuallyEq.of_eq hraw)
    exact hh
  have htraj := oracle_moment_trajectory (sourceSigma d B beta eta)
    (fun k => (sourceSigma_le_pastSigma d B beta eta k).trans (pastSigma_le_ambient k))
    beta eta p (vinc d B p) (vadd d B p ν) hp eL qL xL
    heAdapt hqAdapt hz hv heStep hqStep k
  have hinit : integratedMoments μ (e 0) (q 0) = integratedMoments ρ Prod.fst Prod.snd := by
    apply Moments.ext
    · change (∫ ω : World d B, ‖ω.1.1‖ ^ 2 ∂ρ.prod _) = _
      rw [integral_fun_fst (fun s : State d => ‖s.1‖ ^ 2)]
      simp [integratedMoments]
    · change (∫ ω : World d B, ‖ω.1.2‖ ^ 2 ∂ρ.prod _) = _
      rw [integral_fun_fst (fun s : State d => ‖s.2‖ ^ 2)]
      simp [integratedMoments]
    · change (∫ ω : World d B, inner ℝ ω.1.1 ω.1.2 ∂ρ.prod _) = _
      rw [integral_fun_fst (fun s : State d => inner ℝ s.1 s.2)]
      simp [integratedMoments]
  simpa only [eL, qL, gramMoments_toLp, hinit, params, e, q, μ] using htraj

/-- The actual sparse Gaussian minibatch process has exactly the manuscript's
deterministic moment trajectory. All oracle facts and all-time L2 bounds are proved. -/
theorem leastSquares_moment_trajectory {d B : ℕ} (hB : 0 < B)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (ν : Measure ℝ) (ρ : Measure (State d))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0) (beta eta : ℝ)
    (he0 : MemLp (fun s : State d => s.1) 2 ρ)
    (hq0 : MemLp (fun s : State d => s.2) 2 ρ) (k : ℕ) :
    integratedMoments (worldLaw p ν ρ)
      (fun ω : World d B => (process beta eta ω k).1)
      (fun ω : World d B => (process beta eta ω k).2) =
    (params d B p ν beta eta).trajectory
      (integratedMoments ρ Prod.fst Prod.snd) k :=
  integrated_trajectory_of_oracle p hp.ne' ν ρ (batchOracle hB p ν hz hmean)
    beta eta he0 hq0 k

end
end SparseSGD.Probability.LeastSquares
