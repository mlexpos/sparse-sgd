import SparseSGD.Logistic.Drift
import SparseSGD.Probability.LeastSquares.ConditionalProduct
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1200000

abbrev History (d B k : ℕ) := State d × (Fin k → Batch d B)

def past {d B : ℕ} (k : ℕ) (ω : World d B) : History d B k :=
  (ω.1, fun i => ω.2 i)

def pastSigma (d B k : ℕ) : MeasurableSpace (World d B) :=
  MeasurableSpace.comap (past (d := d) (B := B) k) inferInstance

def pastLaw {d B : ℕ} (p : unitInterval) (ρ : Measure (State d)) (k : ℕ) : Measure (History d B k) :=
  (worldLaw (B := B) p ρ).map (past k)

theorem measurable_past (d B k : ℕ) : Measurable (past (d := d) (B := B) k) := by
  unfold past; fun_prop

theorem measurable_fresh (d B k : ℕ) : Measurable (fun ω : World d B => ω.2 k) := by fun_prop

instance pastLaw_probability {d B : ℕ} (p : unitInterval) (ρ : Measure (State d))
    [IsProbabilityMeasure ρ] (k : ℕ) : IsProbabilityMeasure (pastLaw (B := B) p ρ k) := by
  unfold pastLaw
  infer_instance

theorem process_succ {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (ω : World d B) (k : ℕ) : process eta beta p mu ω (k+1) =
      update eta beta p mu (process eta beta p mu ω k) (ω.2 k) := rfl

theorem pastSigma_le_ambient (d B k : ℕ) :
    pastSigma d B k ≤ (inferInstance : MeasurableSpace (World d B)) :=
  (measurable_past d B k).comap_le

theorem pastSigma_mono {d B j k : ℕ} (hjk : j ≤ k) : pastSigma d B j ≤ pastSigma d B k := by
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (fun h : History d B k => (h.1, fun i : Fin j => h.2 (Fin.castLE hjk i)))
  · fun_prop
  · rfl

def historyState {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) :
    (k : ℕ) → History d B k → State d
  | 0, h => h.1
  | k + 1, h => update eta beta p mu
      (historyState eta beta p mu k (h.1, fun i => h.2 i.castSucc)) (h.2 (Fin.last k))

theorem measurable_historyState (d B : ℕ) (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (k : ℕ) :
    Measurable (historyState (B := B) eta beta p mu k) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
    apply (measurable_update d B eta beta p mu).comp
      (f := fun h : History d B (k+1) =>
        (historyState eta beta p mu k (h.1, fun i => h.2 i.castSucc), h.2 (Fin.last k)))
    apply Measurable.prodMk
    · apply ih.comp
      apply measurable_fst.prodMk
      exact Measurable.of_eval (fun i => (measurable_pi_apply i.castSucc).comp measurable_snd)
    · exact (measurable_pi_apply (Fin.last k)).comp measurable_snd

theorem process_eq_historyState {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (ω : World d B) (k : ℕ) :
    process eta beta p mu ω k = historyState eta beta p mu k (past k ω) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [process, historyState, past, Fin.val_castSucc, Fin.val_last] using
      congrArg (fun s => update eta beta p mu s (ω.2 k)) ih

theorem process_past_measurable (d B : ℕ) (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (k : ℕ) :
    @Measurable (World d B) (State d) (pastSigma d B k) inferInstance
      (fun ω => process eta beta p mu ω k) := by
  have h := (measurable_historyState d B eta beta p mu k).comp
    (show @Measurable (World d B) (History d B k) (pastSigma d B k) inferInstance
      (past k) from measurable_iff_comap_le.mpr le_rfl)
  simpa only [Function.comp_def, ← process_eq_historyState] using h

theorem past_fresh_jointLaw {d B : ℕ} (p : unitInterval) (ρ : Measure (State d))
    [IsProbabilityMeasure ρ] (k : ℕ) :
    (worldLaw (B := B) p ρ).map (fun ω => (past k ω, ω.2 k)) =
      (pastLaw (B := B) p ρ k).prod (batchLaw d B p) := by
  let ν := Measure.infinitePi (fun _ : ℕ => batchLaw d B p)
  have hi := iIndepFun_infinitePi
    (P := fun _ : ℕ => batchLaw d B p)
    (X := fun _ (a : Batch d B) => a) (fun _ => measurable_id)
  have h := iIndepFun.indepFun_finset (Finset.range k) {k} (by simp) hi
    (fun i => measurable_pi_apply i)
  have hleft : Measurable (fun h : (i : Finset.range k) → Batch d B =>
      fun i : Fin k => h ⟨i, Finset.mem_range.mpr i.isLt⟩) := by fun_prop
  have hright : Measurable (fun h : (i : ({k} : Finset ℕ)) → Batch d B => h ⟨k, by simp⟩) := by fun_prop
  have hindep : IndepFun (fun ω : ℕ → Batch d B => fun i : Fin k => ω i)
      (fun ω : ℕ → Batch d B => ω k) ν := h.comp hleft hright
  have hstream : ν.map (fun ω : ℕ → Batch d B => ((fun i : Fin k => ω i), ω k)) =
      (ν.map (fun ω : ℕ → Batch d B => fun i : Fin k => ω i)).prod (batchLaw d B p) := by
    rw [hindep.map_prod_eq_prod_map_map
      ((show Measurable (fun ω : ℕ → Batch d B => fun i : Fin k => ω i) by fun_prop).aemeasurable)
      (measurable_pi_apply k).aemeasurable]
    simp only [ν, Measure.infinitePi_map_eval]
  have hpast : pastLaw (B := B) p ρ k =
      ρ.prod (ν.map (fun ω : ℕ → Batch d B => fun i : Fin k => ω i)) := by
    unfold pastLaw worldLaw past
    simpa [Measure.map_id, Prod.map_def] using
      (Measure.map_prod_map ρ ν measurable_id
        (show Measurable (fun ω : ℕ → Batch d B => fun i : Fin k => ω i) by fun_prop)).symm
  rw [hpast]
  apply MeasurableEquiv.prodAssoc.map_measurableEquiv_injective
  rw [Measure.prodAssoc_prod, Measure.map_map (by fun_prop)
    ((measurable_past d B k).prodMk (measurable_fresh d B k))]
  change (ρ.prod ν).map (Prod.map id
    (fun ω : ℕ → Batch d B => ((fun i : Fin k => ω i), ω k))) = _
  rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id, hstream]

def featureNormAverage {d B : ℕ} (mu : Vec d) (a : Batch d B) : ℝ :=
  |(B : ℝ)⁻¹| * ∑ i, ‖feature mu (a i)‖

theorem featureNormAverage_memLp_two {d B : ℕ} (p : unitInterval) (mu : Vec d) :
    MemLp (featureNormAverage (B := B) mu) 2 (batchLaw d B p) := by
  classical
  have hi (i : Fin B) : MemLp (fun a : Batch d B => ‖feature mu (a i)‖) 2 (batchLaw d B p) :=
    ((sample_feature_memLp_two d p mu).norm).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin B => sampleLaw d p) i)
  exact (memLp_finsetSum Finset.univ (fun i _ => hi i)).const_mul _

theorem batchGradient_norm_le_featureNormAverage {d B : ℕ} (p : unitInterval)
    (mu theta : Vec d) (a : Batch d B) : ‖batchGradient p mu theta a‖ ≤ featureNormAverage mu a := by
  classical
  rw [batchGradient, norm_smul, Real.norm_eq_abs, featureNormAverage]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    ‖∑ i, gradient p mu theta (a i)‖ ≤ ∑ i, ‖gradient p mu theta (a i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖feature mu (a i)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [gradient, norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (logistic_residual_abs_le_one _ _)

theorem batchGradient_kernel_memLp_two {A : Type*} [MeasurableSpace A] {α : Measure A}
    [IsProbabilityMeasure α] {d B : ℕ} (p : unitInterval) (mu : Vec d)
    (U : A → Vec d) (hU : Measurable U) :
    MemLp (fun z : A × Batch d B => batchGradient p mu (U z.1) z.2) 2 (α.prod (batchLaw d B p)) := by
  have hm : Measurable (fun z : A × Batch d B => batchGradient p mu (U z.1) z.2) :=
    (measurable_batchGradient d B p mu).comp
      (f := fun z : A × Batch d B => (U z.1, z.2))
      ((hU.comp measurable_fst).prodMk measurable_snd)
  have hmajor := (featureNormAverage_memLp_two (B := B) p mu).comp_snd α
  apply hmajor.of_le hm.aestronglyMeasurable
  filter_upwards with z
  have h := batchGradient_norm_le_featureNormAverage p mu (U z.1) z.2
  simpa only [Real.norm_eq_abs] using h.trans (le_abs_self _)

theorem fresh_batchGradient_memLp_two {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (ρ : Measure (State d)) [IsProbabilityMeasure ρ] (k : ℕ) :
    MemLp (fun ω : World d B => batchGradient p mu (process eta beta p mu ω k).1 (ω.2 k))
      2 (worldLaw p ρ) := by
  letI : IsProbabilityMeasure (pastLaw (B := B) p ρ k) := by unfold pastLaw; infer_instance
  have hp := batchGradient_kernel_memLp_two (α := pastLaw (B := B) p ρ k) (B := B) p mu
    (fun h : History d B k => (historyState eta beta p mu k h).1)
    (measurable_historyState d B eta beta p mu k).fst
  have hm : Measurable (fun z : History d B k × Batch d B =>
      batchGradient p mu (historyState eta beta p mu k z.1).1 z.2) :=
    (measurable_batchGradient d B p mu).comp
      (f := fun z : History d B k × Batch d B => ((historyState eta beta p mu k z.1).1, z.2))
      (((measurable_historyState d B eta beta p mu k).fst.comp measurable_fst).prodMk measurable_snd)
  have hraw : MemLp (fun ω : World d B =>
      batchGradient p mu (historyState eta beta p mu k (past k ω)).1 (ω.2 k)) 2 (worldLaw p ρ) := by
    apply (memLp_map_measure_iff hm.aestronglyMeasurable
      ((measurable_past d B k).prodMk (measurable_fresh d B k)).aemeasurable).mp
    rwa [past_fresh_jointLaw p ρ k]
  simpa only [← process_eq_historyState] using hraw

theorem process_memLp_two {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (ρ : Measure (State d)) [IsProbabilityMeasure ρ]
    (hθ0 : MemLp (fun s : State d => s.1) 2 ρ)
    (hm0 : MemLp (fun s : State d => s.2) 2 ρ) (k : ℕ) :
    MemLp (fun ω : World d B => (process eta beta p mu ω k).1) 2 (worldLaw p ρ) ∧
    MemLp (fun ω : World d B => (process eta beta p mu ω k).2) 2 (worldLaw p ρ) := by
  induction k with
  | zero => exact ⟨hθ0.comp_fst _, hm0.comp_fst _⟩
  | succ k ih =>
    have hg := fresh_batchGradient_memLp_two (B := B) eta beta p mu ρ k
    have hm := (ih.2.const_smul beta).add (hg.const_smul (1 - beta))
    exact ⟨ih.1.sub (hm.const_smul eta), hm⟩

theorem process_fresh_condExp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (ρ : Measure (State d)) [IsProbabilityMeasure ρ] (k : ℕ)
    (F : State d × Batch d B → E) (hF : Measurable F)
    (hFi : Integrable (fun z : History d B k × Batch d B =>
      F (historyState eta beta p mu k z.1, z.2)) ((pastLaw (B := B) p ρ k).prod (batchLaw d B p))) :
    (worldLaw p ρ)[fun ω : World d B => F (process eta beta p mu ω k, ω.2 k) | pastSigma d B k]
      =ᵐ[worldLaw p ρ] (fun ω => ∫ a, F (process eta beta p mu ω k, a) ∂batchLaw d B p) := by
  have hm : Measurable (fun z : History d B k × Batch d B =>
      F (historyState eta beta p mu k z.1, z.2)) :=
    hF.comp (f := fun z : History d B k × Batch d B =>
      (historyState eta beta p mu k z.1, z.2))
      (((measurable_historyState d B eta beta p mu k).comp measurable_fst).prodMk measurable_snd)
  have h := SparseSGD.Probability.LeastSquares.condExp_of_joint_product
    (past (d := d) (B := B) k) (fun ω : World d B => ω.2 k)
    (measurable_past d B k) (measurable_fresh d B k) (past_fresh_jointLaw p ρ k)
    _ hm.stronglyMeasurable hFi
  simpa only [← process_eq_historyState, pastSigma] using h

theorem history_update_kernel_memLp_two {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (ρ : Measure (State d)) [IsProbabilityMeasure ρ]
    (hθ0 : MemLp (fun s : State d => s.1) 2 ρ)
    (hm0 : MemLp (fun s : State d => s.2) 2 ρ) (k : ℕ) :
    MemLp (fun z : History d B k × Batch d B =>
      (update eta beta p mu (historyState eta beta p mu k z.1) z.2).1) 2
      ((pastLaw (B := B) p ρ k).prod (batchLaw d B p)) ∧
    MemLp (fun z : History d B k × Batch d B =>
      (update eta beta p mu (historyState eta beta p mu k z.1) z.2).2) 2
      ((pastLaw (B := B) p ρ k).prod (batchLaw d B p)) := by
  letI : IsProbabilityMeasure (pastLaw (B := B) p ρ k) := by unfold pastLaw; infer_instance
  have hs := process_memLp_two (B := B) eta beta p mu ρ hθ0 hm0 k
  have hθ : MemLp (fun h : History d B k => (historyState eta beta p mu k h).1) 2 (pastLaw p ρ k) := by
    apply (memLp_map_measure_iff
      (measurable_historyState d B eta beta p mu k).fst.aestronglyMeasurable
      (measurable_past d B k).aemeasurable).mpr
    simpa only [Function.comp_def, ← process_eq_historyState] using hs.1
  have hm : MemLp (fun h : History d B k => (historyState eta beta p mu k h).2) 2 (pastLaw p ρ k) := by
    apply (memLp_map_measure_iff
      (measurable_historyState d B eta beta p mu k).snd.aestronglyMeasurable
      (measurable_past d B k).aemeasurable).mpr
    simpa only [Function.comp_def, ← process_eq_historyState] using hs.2
  have hg := batchGradient_kernel_memLp_two (α := pastLaw (B := B) p ρ k) (B := B) p mu
    (fun h : History d B k => (historyState eta beta p mu k h).1)
    (measurable_historyState d B eta beta p mu k).fst
  have hnextm := ((hm.comp_fst _).const_smul beta).add (hg.const_smul (1 - beta))
  exact ⟨(hθ.comp_fst _).sub (hnextm.const_smul eta), hnextm⟩

theorem measurable_signalCoord {d : ℕ} (mu : Vec d) : Measurable (signalCoord mu) := by
  unfold signalCoord; fun_prop

theorem measurable_bulkPart {d : ℕ} (mu : Vec d) : Measurable (bulkPart mu) := by
  have h : (bulkLinear mu : Vec d → Vec d) = bulkPart mu := funext (bulkLinear_apply mu)
  rw [← h]
  exact (bulkLinear mu).measurable

private theorem conditional_signal_memLp {A : Type*} [MeasurableSpace A] {α : Measure A}
    {d : ℕ} (mu : Vec d) (f : A → Vec d) (hf : MemLp f 2 α) :
    MemLp (fun a => signalCoord mu (f a)) 2 α := by
  simpa only [signalCoord, div_eq_mul_inv] using (hf.inner_const (𝕜 := ℝ) mu).mul_const (r mu)⁻¹

private theorem conditional_inner_integrable {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {α : Measure A}
    (f g : A → E) (hf : MemLp f 2 α) (hg : MemLp g 2 α) :
    Integrable (fun a => inner ℝ (f a) (g a)) α := by
  have h := L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  apply h.congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with a ha hb
  rw [ha, hb]

abbrev SourceHistory (d k : ℕ) := State d × (Fin k → Vec d)

def sourcePast {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (k : ℕ)
    (ω : World d B) : SourceHistory d k :=
  (ω.1, fun i => batchGradient p mu (process eta beta p mu ω i).1 (ω.2 i))

def sourceSigma (d B : ℕ) (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (k : ℕ) :
    MeasurableSpace (World d B) := MeasurableSpace.comap (sourcePast eta beta p mu k) inferInstance

private def conditional_gradientUpdate {d : ℕ} (eta beta : ℝ) (s : State d) (g : Vec d) : State d :=
  let m := beta • s.2 + (1 - beta) • g
  (s.1 - eta • m, m)

private def conditional_sourceState {d : ℕ} (eta beta : ℝ) : (k : ℕ) → SourceHistory d k → State d
  | 0, h => h.1
  | k+1, h => conditional_gradientUpdate eta beta
      (conditional_sourceState eta beta k (h.1, fun i => h.2 i.castSucc)) (h.2 (Fin.last k))

theorem sourcePast_past_measurable (d B : ℕ) (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (k : ℕ) :
    @Measurable (World d B) (SourceHistory d k) (pastSigma d B k) inferInstance
      (sourcePast eta beta p mu k) := by
  letI : MeasurableSpace (World d B) := pastSigma d B k
  have hp : Measurable (past (d := d) (B := B) k) := measurable_iff_comap_le.mpr le_rfl
  apply (measurable_fst.comp (f := past k) hp).prodMk
  apply Measurable.of_eval
  intro i
  have hs : Measurable (fun ω : World d B => process eta beta p mu ω i.val) :=
    (process_past_measurable d B eta beta p mu i.val).mono
      (pastSigma_mono (Nat.le_of_lt i.isLt)) le_rfl
  have hb : Measurable (fun ω : World d B => ω.2 i.val) :=
    ((measurable_pi_apply i).comp measurable_snd).comp (f := past k) hp
  exact (measurable_batchGradient d B p mu).comp
    (f := fun ω : World d B => ((process eta beta p mu ω i.val).1, ω.2 i.val))
    (hs.fst.prodMk hb)

theorem sourceSigma_le_past (d B : ℕ) (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (k : ℕ) :
    sourceSigma d B eta beta p mu k ≤ pastSigma d B k :=
  measurable_iff_comap_le.mp (sourcePast_past_measurable d B eta beta p mu k)

private theorem conditional_measurable_sourceState (d : ℕ) (eta beta : ℝ) (k : ℕ) :
    Measurable (conditional_sourceState (d := d) eta beta k) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
    change Measurable (fun h : SourceHistory d (k+1) => conditional_gradientUpdate eta beta
      (conditional_sourceState eta beta k (h.1, fun i => h.2 i.castSucc)) (h.2 (Fin.last k)))
    have hp : Measurable (fun h : SourceHistory d (k+1) =>
        conditional_sourceState eta beta k (h.1, fun i => h.2 i.castSucc)) := by
      apply ih.comp
      apply measurable_fst.prodMk
      exact Measurable.of_eval (fun i => (measurable_pi_apply i.castSucc).comp measurable_snd)
    have hg : Measurable (fun h : SourceHistory d (k+1) => h.2 (Fin.last k)) :=
      (measurable_pi_apply (Fin.last k)).comp measurable_snd
    dsimp [conditional_gradientUpdate]
    exact (hp.fst.sub ((hp.snd.const_smul beta |>.add (hg.const_smul (1-beta))).const_smul eta)).prodMk
      (hp.snd.const_smul beta |>.add (hg.const_smul (1-beta)))

private theorem conditional_process_eq_sourceState {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (ω : World d B) (k : ℕ) :
    process eta beta p mu ω k = conditional_sourceState eta beta k (sourcePast eta beta p mu k ω) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change update eta beta p mu (process eta beta p mu ω k) (ω.2 k) =
      conditional_gradientUpdate eta beta
        (conditional_sourceState eta beta k (sourcePast eta beta p mu k ω))
        (batchGradient p mu (process eta beta p mu ω k).1 (ω.2 k))
    rw [← ih]
    rfl

theorem process_source_measurable (d B : ℕ) (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (k : ℕ) :
    @Measurable (World d B) (State d) (sourceSigma d B eta beta p mu k) inferInstance
      (fun ω => process eta beta p mu ω k) := by
  have h := (conditional_measurable_sourceState d eta beta k).comp
    (show @Measurable (World d B) (SourceHistory d k) (sourceSigma d B eta beta p mu k)
      inferInstance (sourcePast eta beta p mu k) from measurable_iff_comap_le.mpr le_rfl)
  simpa only [Function.comp_def, ← conditional_process_eq_sourceState] using h

theorem process_source_fresh_condExp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (ρ : Measure (State d)) [IsProbabilityMeasure ρ] (k : ℕ)
    (F : State d × Batch d B → E) (hF : Measurable F)
    (hFi : Integrable (fun z : History d B k × Batch d B =>
      F (historyState eta beta p mu k z.1, z.2)) ((pastLaw (B := B) p ρ k).prod (batchLaw d B p))) :
    (worldLaw p ρ)[fun ω : World d B => F (process eta beta p mu ω k, ω.2 k) |
      sourceSigma d B eta beta p mu k] =ᵐ[worldLaw p ρ]
      (fun ω => ∫ a, F (process eta beta p mu ω k, a) ∂batchLaw d B p) := by
  have hfull := process_fresh_condExp eta beta p mu ρ k F hF hFi
  have hle := sourceSigma_le_past d B eta beta p mu k
  have hamb := pastSigma_le_ambient d B k
  have hI : StronglyMeasurable (fun s : State d => ∫ a, F (s, a) ∂batchLaw d B p) :=
    hF.stronglyMeasurable.integral_prod_right'
  have hg : StronglyMeasurable[sourceSigma d B eta beta p mu k]
      (fun ω : World d B => ∫ a, F (process eta beta p mu ω k, a) ∂batchLaw d B p) :=
    hI.comp_measurable (process_source_measurable d B eta beta p mu k)
  have hgi : Integrable (fun ω : World d B => ∫ a, F (process eta beta p mu ω k, a) ∂batchLaw d B p)
      (worldLaw p ρ) := integrable_condExp.congr hfull
  have ht := condExp_condExp_of_le (μ := worldLaw p ρ)
    (f := fun ω : World d B => F (process eta beta p mu ω k, ω.2 k)) hle hamb
  have hc := condExp_congr_ae (m := sourceSigma d B eta beta p mu k) hfull
  rw [condExp_of_stronglyMeasurable (hle.trans hamb) hg hgi] at hc
  exact ht.symm.trans hc

/-- Conditional vector gradient mean for the actual iid stream, without a
moment assumption on the initial state: the logistic residual is bounded. -/
theorem process_gradient_condExp {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (ρ : Measure (State d)) [IsProbabilityMeasure ρ] (k : ℕ) :
    (worldLaw p ρ)[fun ω : World d B => batchGradient p mu (process eta beta p mu ω k).1 (ω.2 k) |
      pastSigma d B k] =ᵐ[worldLaw p ρ]
      (fun ω => coefA p mu (process eta beta p mu ω k).1 • (process eta beta p mu ω k).1 +
        coefB p mu (process eta beta p mu ω k).1 • mu) ∧
    (worldLaw p ρ)[fun ω : World d B => batchGradient p mu (process eta beta p mu ω k).1 (ω.2 k) |
      sourceSigma d B eta beta p mu k] =ᵐ[worldLaw p ρ]
      (fun ω => coefA p mu (process eta beta p mu ω k).1 • (process eta beta p mu ω k).1 +
        coefB p mu (process eta beta p mu ω k).1 • mu) := by
  have hF : Measurable (fun z : State d × Batch d B => batchGradient p mu z.1.1 z.2) :=
    (measurable_batchGradient d B p mu).comp
      (f := fun z : State d × Batch d B => (z.1.1, z.2))
      (measurable_fst.fst.prodMk measurable_snd)
  have hp := batchGradient_kernel_memLp_two (α := pastLaw (B := B) p ρ k) (B := B) p mu
    (fun h : History d B k => (historyState eta beta p mu k h).1)
    (measurable_historyState d B eta beta p mu k).fst
  constructor
  · have h := process_fresh_condExp eta beta p mu ρ k _ hF (hp.integrable (by norm_num))
    simpa only [batchGradient_integral H hB] using h
  · have h := process_source_fresh_condExp eta beta p mu ρ k _ hF (hp.integrable (by norm_num))
    simpa only [batchGradient_integral H hB] using h

/-- Signal drift conditioned on the actual complete sample history. -/
theorem process_conditional_signal_drift {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (hr : 0 < r mu)
    (ρ : Measure (State d)) [IsProbabilityMeasure ρ]
    (hθ0 : MemLp (fun s : State d => s.1) 2 ρ)
    (hm0 : MemLp (fun s : State d => s.2) 2 ρ) (k : ℕ) :
    (worldLaw p ρ)[fun ω : World d B => signalCoord mu (process eta beta p mu ω (k+1)).2 |
      pastSigma d B k] =ᵐ[worldLaw p ρ]
      (fun ω => beta * signalCoord mu (process eta beta p mu ω k).2 + (1 - beta) *
        (coefA p mu (process eta beta p mu ω k).1 * signalCoord mu (process eta beta p mu ω k).1 +
          coefB p mu (process eta beta p mu ω k).1 * r mu)) ∧
    (worldLaw p ρ)[fun ω : World d B => signalCoord mu (process eta beta p mu ω (k+1)).1 |
      pastSigma d B k] =ᵐ[worldLaw p ρ]
      (fun ω => signalCoord mu (process eta beta p mu ω k).1 - eta *
        (beta * signalCoord mu (process eta beta p mu ω k).2 + (1 - beta) *
          (coefA p mu (process eta beta p mu ω k).1 * signalCoord mu (process eta beta p mu ω k).1 +
            coefB p mu (process eta beta p mu ω k).1 * r mu))) := by
  have hnext := history_update_kernel_memLp_two (B := B) eta beta p mu ρ hθ0 hm0 k
  constructor
  · have hF : Measurable (fun z : State d × Batch d B => signalCoord mu (update eta beta p mu z.1 z.2).2) :=
      (measurable_signalCoord mu).comp (measurable_update d B eta beta p mu).snd
    have h := process_fresh_condExp eta beta p mu ρ k _ hF
      ((conditional_signal_memLp mu _ hnext.2).integrable (by norm_num))
    have hfix (s : State d) := update_signal_momentum_integral H hB eta beta p mu s hr
    simpa only [← process_succ, hfix] using h
  · have hF : Measurable (fun z : State d × Batch d B => signalCoord mu (update eta beta p mu z.1 z.2).1) :=
      (measurable_signalCoord mu).comp (measurable_update d B eta beta p mu).fst
    have h := process_fresh_condExp eta beta p mu ρ k _ hF
      ((conditional_signal_memLp mu _ hnext.1).integrable (by norm_num))
    have hfix (s : State d) := update_signal_parameter_integral H hB eta beta p mu s hr
    simpa only [← process_succ, hfix] using h

def stateBulkMoments {d : ℕ} (eta : ℝ) (mu : Vec d) (s : State d) : SparseSGD.Moments :=
  SparseSGD.gramMoments (bulkPart mu s.1) (eta • bulkPart mu s.2)

def stepBulkMoments {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d) : SparseSGD.Moments :=
  (driftParams (B := B) eta beta p mu s.1).step (stateBulkMoments eta mu s)

/-- All three normalized bulk moments conditioned on the actual sample history.
The signed multiplicative variance coefficient needs no positivity premise. -/
theorem process_conditional_bulk_drift {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (hr : 0 < r mu)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (ρ : Measure (State d)) [IsProbabilityMeasure ρ]
    (hθ0 : MemLp (fun s : State d => s.1) 2 ρ)
    (hm0 : MemLp (fun s : State d => s.2) 2 ρ) (k : ℕ) :
    (worldLaw p ρ)[fun ω : World d B => ‖bulkPart mu (process eta beta p mu ω (k+1)).1‖ ^ 2 |
      pastSigma d B k] =ᵐ[worldLaw p ρ]
      (fun ω => (stepBulkMoments (B := B) eta beta p mu (process eta beta p mu ω k)).R) ∧
    (worldLaw p ρ)[fun ω : World d B => ‖eta • bulkPart mu (process eta beta p mu ω (k+1)).2‖ ^ 2 |
      pastSigma d B k] =ᵐ[worldLaw p ρ]
      (fun ω => (stepBulkMoments (B := B) eta beta p mu (process eta beta p mu ω k)).V) ∧
    (worldLaw p ρ)[fun ω : World d B => inner ℝ (bulkPart mu (process eta beta p mu ω (k+1)).1)
      (eta • bulkPart mu (process eta beta p mu ω (k+1)).2) | pastSigma d B k] =ᵐ[worldLaw p ρ]
      (fun ω => (stepBulkMoments (B := B) eta beta p mu (process eta beta p mu ω k)).C) := by
  have hnext := history_update_kernel_memLp_two (B := B) eta beta p mu ρ hθ0 hm0 k
  have hθ := (bulkLinear mu).comp_memLp' hnext.1
  have hθ' : MemLp (fun z : History d B k × Batch d B =>
      bulkPart mu (update eta beta p mu (historyState eta beta p mu k z.1) z.2).1) 2
      ((pastLaw (B := B) p ρ k).prod (batchLaw d B p)) := by
    simpa only [Function.comp_def, bulkLinear_apply] using hθ
  have hq' : MemLp (fun z : History d B k × Batch d B =>
      eta • bulkPart mu (update eta beta p mu (historyState eta beta p mu k z.1) z.2).2) 2
      ((pastLaw (B := B) p ρ k).prod (batchLaw d B p)) := by
    have hbulk : MemLp (fun z : History d B k × Batch d B =>
        bulkPart mu (update eta beta p mu (historyState eta beta p mu k z.1) z.2).2) 2
        ((pastLaw (B := B) p ρ k).prod (batchLaw d B p)) := by
      simpa only [Function.comp_def, bulkLinear_apply] using (bulkLinear mu).comp_memLp' hnext.2
    exact hbulk.const_smul eta
  have hθm : Measurable (fun z : State d × Batch d B => bulkPart mu (update eta beta p mu z.1 z.2).1) :=
    (measurable_bulkPart mu).comp (measurable_update d B eta beta p mu).fst
  have hqm : Measurable (fun z : State d × Batch d B => eta • bulkPart mu (update eta beta p mu z.1 z.2).2) :=
    ((measurable_bulkPart mu).comp (measurable_update d B eta beta p mu).snd).const_smul eta
  have hfix (s : State d) := update_bulk_integratedGram H hB eta beta p mu s hr
    (ne_of_gt (coefA_pos p mu s.1 hp0 hp1))
  have hR (s : State d) : (∫ a : Batch d B, ‖bulkPart mu (update eta beta p mu s a).1‖ ^ 2
      ∂batchLaw d B p) = (stepBulkMoments (B := B) eta beta p mu s).R :=
    congrArg SparseSGD.Moments.R (hfix s)
  have hV (s : State d) : (∫ a : Batch d B, ‖eta • bulkPart mu (update eta beta p mu s a).2‖ ^ 2
      ∂batchLaw d B p) = (stepBulkMoments (B := B) eta beta p mu s).V :=
    congrArg SparseSGD.Moments.V (hfix s)
  have hC (s : State d) : (∫ a : Batch d B, inner ℝ (bulkPart mu (update eta beta p mu s a).1)
      (eta • bulkPart mu (update eta beta p mu s a).2) ∂batchLaw d B p) =
      (stepBulkMoments (B := B) eta beta p mu s).C := congrArg SparseSGD.Moments.C (hfix s)
  refine ⟨?_, ?_, ?_⟩
  · have h := process_fresh_condExp eta beta p mu ρ k _ (hθm.norm.pow_const 2)
      ((memLp_two_iff_integrable_sq_norm hθ'.aestronglyMeasurable).mp hθ')
    simpa only [← process_succ, hR] using h
  · have h := process_fresh_condExp eta beta p mu ρ k _ (hqm.norm.pow_const 2)
      ((memLp_two_iff_integrable_sq_norm hq'.aestronglyMeasurable).mp hq')
    simpa only [← process_succ, hV] using h
  · have h := process_fresh_condExp eta beta p mu ρ k _ (hθm.inner hqm)
      (conditional_inner_integrable _ _ hθ' hq')
    simpa only [← process_succ, hC] using h

/-- Signal drift conditioned on the actual gradient history. -/
theorem process_source_conditional_signal_drift {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (hr : 0 < r mu)
    (ρ : Measure (State d)) [IsProbabilityMeasure ρ]
    (hθ0 : MemLp (fun s : State d => s.1) 2 ρ)
    (hm0 : MemLp (fun s : State d => s.2) 2 ρ) (k : ℕ) :
    (worldLaw p ρ)[fun ω : World d B => signalCoord mu (process eta beta p mu ω (k+1)).2 |
      sourceSigma d B eta beta p mu k] =ᵐ[worldLaw p ρ]
      (fun ω => beta * signalCoord mu (process eta beta p mu ω k).2 + (1 - beta) *
        (coefA p mu (process eta beta p mu ω k).1 * signalCoord mu (process eta beta p mu ω k).1 +
          coefB p mu (process eta beta p mu ω k).1 * r mu)) ∧
    (worldLaw p ρ)[fun ω : World d B => signalCoord mu (process eta beta p mu ω (k+1)).1 |
      sourceSigma d B eta beta p mu k] =ᵐ[worldLaw p ρ]
      (fun ω => signalCoord mu (process eta beta p mu ω k).1 - eta *
        (beta * signalCoord mu (process eta beta p mu ω k).2 + (1 - beta) *
          (coefA p mu (process eta beta p mu ω k).1 * signalCoord mu (process eta beta p mu ω k).1 +
            coefB p mu (process eta beta p mu ω k).1 * r mu))) := by
  have hnext := history_update_kernel_memLp_two (B := B) eta beta p mu ρ hθ0 hm0 k
  constructor
  · have hF : Measurable (fun z : State d × Batch d B => signalCoord mu (update eta beta p mu z.1 z.2).2) :=
      (measurable_signalCoord mu).comp (measurable_update d B eta beta p mu).snd
    have h := process_source_fresh_condExp eta beta p mu ρ k _ hF
      ((conditional_signal_memLp mu _ hnext.2).integrable (by norm_num))
    have hfix (s : State d) := update_signal_momentum_integral H hB eta beta p mu s hr
    simpa only [← process_succ, hfix] using h
  · have hF : Measurable (fun z : State d × Batch d B => signalCoord mu (update eta beta p mu z.1 z.2).1) :=
      (measurable_signalCoord mu).comp (measurable_update d B eta beta p mu).fst
    have h := process_source_fresh_condExp eta beta p mu ρ k _ hF
      ((conditional_signal_memLp mu _ hnext.1).integrable (by norm_num))
    have hfix (s : State d) := update_signal_parameter_integral H hB eta beta p mu s hr
    simpa only [← process_succ, hfix] using h

/-- All three normalized bulk moments conditioned on the actual gradient history.
The signed multiplicative variance coefficient needs no positivity premise. -/
theorem process_source_conditional_bulk_drift {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (hr : 0 < r mu)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (ρ : Measure (State d)) [IsProbabilityMeasure ρ]
    (hθ0 : MemLp (fun s : State d => s.1) 2 ρ)
    (hm0 : MemLp (fun s : State d => s.2) 2 ρ) (k : ℕ) :
    (worldLaw p ρ)[fun ω : World d B => ‖bulkPart mu (process eta beta p mu ω (k+1)).1‖ ^ 2 |
      sourceSigma d B eta beta p mu k] =ᵐ[worldLaw p ρ]
      (fun ω => (stepBulkMoments (B := B) eta beta p mu (process eta beta p mu ω k)).R) ∧
    (worldLaw p ρ)[fun ω : World d B => ‖eta • bulkPart mu (process eta beta p mu ω (k+1)).2‖ ^ 2 |
      sourceSigma d B eta beta p mu k] =ᵐ[worldLaw p ρ]
      (fun ω => (stepBulkMoments (B := B) eta beta p mu (process eta beta p mu ω k)).V) ∧
    (worldLaw p ρ)[fun ω : World d B => inner ℝ (bulkPart mu (process eta beta p mu ω (k+1)).1)
      (eta • bulkPart mu (process eta beta p mu ω (k+1)).2) | sourceSigma d B eta beta p mu k] =ᵐ[worldLaw p ρ]
      (fun ω => (stepBulkMoments (B := B) eta beta p mu (process eta beta p mu ω k)).C) := by
  have hnext := history_update_kernel_memLp_two (B := B) eta beta p mu ρ hθ0 hm0 k
  have hθ := (bulkLinear mu).comp_memLp' hnext.1
  have hθ' : MemLp (fun z : History d B k × Batch d B =>
      bulkPart mu (update eta beta p mu (historyState eta beta p mu k z.1) z.2).1) 2
      ((pastLaw (B := B) p ρ k).prod (batchLaw d B p)) := by
    simpa only [Function.comp_def, bulkLinear_apply] using hθ
  have hq' : MemLp (fun z : History d B k × Batch d B =>
      eta • bulkPart mu (update eta beta p mu (historyState eta beta p mu k z.1) z.2).2) 2
      ((pastLaw (B := B) p ρ k).prod (batchLaw d B p)) := by
    have hbulk : MemLp (fun z : History d B k × Batch d B =>
        bulkPart mu (update eta beta p mu (historyState eta beta p mu k z.1) z.2).2) 2
        ((pastLaw (B := B) p ρ k).prod (batchLaw d B p)) := by
      simpa only [Function.comp_def, bulkLinear_apply] using (bulkLinear mu).comp_memLp' hnext.2
    exact hbulk.const_smul eta
  have hθm : Measurable (fun z : State d × Batch d B => bulkPart mu (update eta beta p mu z.1 z.2).1) :=
    (measurable_bulkPart mu).comp (measurable_update d B eta beta p mu).fst
  have hqm : Measurable (fun z : State d × Batch d B => eta • bulkPart mu (update eta beta p mu z.1 z.2).2) :=
    ((measurable_bulkPart mu).comp (measurable_update d B eta beta p mu).snd).const_smul eta
  have hfix (s : State d) := update_bulk_integratedGram H hB eta beta p mu s hr
    (ne_of_gt (coefA_pos p mu s.1 hp0 hp1))
  have hR (s : State d) : (∫ a : Batch d B, ‖bulkPart mu (update eta beta p mu s a).1‖ ^ 2
      ∂batchLaw d B p) = (stepBulkMoments (B := B) eta beta p mu s).R :=
    congrArg SparseSGD.Moments.R (hfix s)
  have hV (s : State d) : (∫ a : Batch d B, ‖eta • bulkPart mu (update eta beta p mu s a).2‖ ^ 2
      ∂batchLaw d B p) = (stepBulkMoments (B := B) eta beta p mu s).V :=
    congrArg SparseSGD.Moments.V (hfix s)
  have hC (s : State d) : (∫ a : Batch d B, inner ℝ (bulkPart mu (update eta beta p mu s a).1)
      (eta • bulkPart mu (update eta beta p mu s a).2) ∂batchLaw d B p) =
      (stepBulkMoments (B := B) eta beta p mu s).C := congrArg SparseSGD.Moments.C (hfix s)
  refine ⟨?_, ?_, ?_⟩
  · have h := process_source_fresh_condExp eta beta p mu ρ k _ (hθm.norm.pow_const 2)
      ((memLp_two_iff_integrable_sq_norm hθ'.aestronglyMeasurable).mp hθ')
    simpa only [← process_succ, hR] using h
  · have h := process_source_fresh_condExp eta beta p mu ρ k _ (hqm.norm.pow_const 2)
      ((memLp_two_iff_integrable_sq_norm hq'.aestronglyMeasurable).mp hq')
    simpa only [← process_succ, hV] using h
  · have h := process_source_fresh_condExp eta beta p mu ρ k _ (hθm.inner hqm)
      (conditional_inner_integrable _ _ hθ' hq')
    simpa only [← process_succ, hC] using h

end
end SparseSGD.Logistic
