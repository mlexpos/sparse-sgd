import SparseSGD.Probability.LeastSquares.Model
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Probability.LeastSquares
noncomputable section

variable {d B : ℕ} (p : unitInterval) (ν : Measure ℝ) (ρ : Measure (State d))

def pastLaw (k : ℕ) : Measure (History d B k) :=
  (worldLaw (B := B) p ν ρ).map (past (d := d) (B := B) k)

lemma measurable_past (k : ℕ) : Measurable (past (d := d) (B := B) k) := by
  change Measurable (fun ω : World d B => (ω.1, fun i : Fin k => ω.2 i))
  fun_prop

lemma measurable_fresh (k : ℕ) : Measurable (fun ω : World d B => ω.2 k) := by
  exact (measurable_pi_apply k).comp measurable_snd

lemma pastSigma_le_ambient (k : ℕ) :
    pastSigma d B k ≤ (inferInstance : MeasurableSpace (World d B)) := by
  exact (measurable_iff_comap_le).1 (measurable_past (d := d) (B := B) k)

lemma pastSigma_mono {j k : ℕ} (hjk : j ≤ k) :
    pastSigma d B j ≤ pastSigma d B k := by
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (fun h : History d B k => (h.1, fun i : Fin j => h.2 (Fin.castLE hjk i)))
  · fun_prop
  · rfl

variable [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

lemma stream_past_indep_fresh (k : ℕ) :
    IndepFun (fun ω : ℕ → Batch d B => fun i : Fin k => ω i)
      (fun ω : ℕ → Batch d B => ω k)
      (Measure.infinitePi (fun _ : ℕ => batchLaw d B p ν)) := by
  have hi := iIndepFun_infinitePi
    (P := fun _ : ℕ => batchLaw d B p ν)
    (X := fun _ (a : Batch d B) => a) (fun _ => measurable_id)
  have h := iIndepFun.indepFun_finset (Finset.range k) {k}
    (by simp) hi (fun i => measurable_pi_apply i)
  have hleft : Measurable
      (fun h : (i : Finset.range k) → Batch d B =>
        fun i : Fin k => h ⟨i, Finset.mem_range.mpr i.isLt⟩) := by fun_prop
  have hright : Measurable
      (fun h : (i : ({k} : Finset ℕ)) → Batch d B => h ⟨k, by simp⟩) := by fun_prop
  exact h.comp hleft hright

lemma stream_past_fresh_jointLaw (k : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => batchLaw d B p ν)).map
      (fun ω : ℕ → Batch d B => ((fun i : Fin k => ω i), ω k)) =
    ((Measure.infinitePi (fun _ : ℕ => batchLaw d B p ν)).map
      (fun ω : ℕ → Batch d B => fun i : Fin k => ω i)).prod (batchLaw d B p ν) := by
  rw [(stream_past_indep_fresh p ν k).map_prod_eq_prod_map_map
    ((by fun_prop : Measurable (fun ω : ℕ → Batch d B => fun i : Fin k => ω i)).aemeasurable)
    (measurable_pi_apply k).aemeasurable, Measure.infinitePi_map_eval]

lemma pastLaw_eq_prod (k : ℕ) :
    pastLaw (B := B) p ν ρ k = ρ.prod
      ((Measure.infinitePi (fun _ : ℕ => batchLaw d B p ν)).map
        (fun ω : ℕ → Batch d B => fun i : Fin k => ω i)) := by
  unfold pastLaw worldLaw past
  simpa [Measure.map_id, Prod.map_def] using
    (Measure.map_prod_map ρ (Measure.infinitePi (fun _ : ℕ => batchLaw d B p ν))
      measurable_id (show Measurable (fun ω : ℕ → Batch d B => fun i : Fin k => ω i)
        by fun_prop)).symm

lemma past_fresh_jointLaw (k : ℕ) :
    (worldLaw (B := B) p ν ρ).map (fun ω => (past (B := B) k ω, ω.2 k)) =
      (pastLaw (B := B) p ν ρ k).prod (batchLaw d B p ν) := by
  rw [pastLaw_eq_prod p ν ρ k]
  apply MeasurableEquiv.prodAssoc.map_measurableEquiv_injective
  rw [Measure.prodAssoc_prod, Measure.map_map (by fun_prop)
    ((measurable_past k).prodMk (measurable_fresh k))]
  change (ρ.prod (Measure.infinitePi (fun _ : ℕ => batchLaw d B p ν))).map
    (Prod.map id (fun ω : ℕ → Batch d B => ((fun i : Fin k => ω i), ω k))) = _
  rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id,
    stream_past_fresh_jointLaw p ν k]

lemma past_indep_fresh (k : ℕ) :
    IndepFun (past (d := d) (B := B) k) (fun ω : World d B => ω.2 k)
      (worldLaw (B := B) p ν ρ) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_past k).aemeasurable (measurable_fresh k).aemeasurable).mpr
  rw [past_fresh_jointLaw p ν ρ k]
  congr 1
  change batchLaw d B p ν =
    (ρ.prod (Measure.infinitePi (fun _ : ℕ => batchLaw d B p ν))).map
      ((fun ω : ℕ → Batch d B => ω k) ∘ Prod.snd)
  rw [← Measure.map_map (measurable_pi_apply k) measurable_snd,
    Measure.map_snd_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]

end
end SparseSGD.Probability.LeastSquares
