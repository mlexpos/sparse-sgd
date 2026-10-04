import SparseSGD.Logistic.Model

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 800000

theorem measurable_sigma : Measurable sigma := by
  unfold sigma
  fun_prop

theorem measurable_labelReal : Measurable labelReal := by
  unfold labelReal
  fun_prop

theorem measurable_feature (d : ℕ) (mu : Vec d) : Measurable (feature mu) := by
  unfold feature
  exact (Measurable.ite (measurable_fst (measurableSet_singleton true))
    measurable_const measurable_const).add
      ((WithLp.measurable_toLp 2 (Fin d → ℝ)).comp measurable_snd)

theorem measurable_gradient (d : ℕ) (p : unitInterval) (mu : Vec d) :
    Measurable (fun z : Vec d × Sample d => gradient p mu z.1 z.2) := by
  unfold gradient
  have hf : Measurable (fun z : Vec d × Sample d => feature mu z.2) :=
    (measurable_feature d mu).comp measurable_snd
  have hl : Measurable (fun z : Vec d × Sample d => labelReal z.2.1) :=
    measurable_labelReal.comp (measurable_fst.comp measurable_snd)
  have hi : Measurable (fun z : Vec d × Sample d =>
      inner ℝ z.1 (feature mu z.2) + bias p mu) :=
    (measurable_fst.inner hf).add measurable_const
  exact ((measurable_sigma.comp hi).sub hl).smul hf

theorem measurable_batchGradient (d B : ℕ) (p : unitInterval) (mu : Vec d) :
    Measurable (fun z : Vec d × Batch d B => batchGradient p mu z.1 z.2) := by
  unfold batchGradient
  have hsum : Measurable (fun z : Vec d × Batch d B =>
      ∑ i, gradient p mu z.1 (z.2 i)) := by
    apply Finset.measurable_sum
    intro i hi
    have hmap : Measurable (fun z : Vec d × Batch d B => (z.1, z.2 i)) :=
      measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
    exact (measurable_gradient d p mu).comp
      (f := fun z : Vec d × Batch d B => (z.1, z.2 i)) hmap
  exact hsum.const_smul ((B : ℝ)⁻¹)

theorem measurable_update (d B : ℕ) (eta beta : ℝ) (p : unitInterval) (mu : Vec d) :
    Measurable (fun z : State d × Batch d B => update eta beta p mu z.1 z.2) := by
  have hg : Measurable (fun z : State d × Batch d B => batchGradient p mu z.1.1 z.2) :=
    (measurable_batchGradient d B p mu).comp
      (f := fun z : State d × Batch d B => (z.1.1, z.2))
      (measurable_fst.fst.prodMk measurable_snd)
  have hm : Measurable (fun z : State d × Batch d B =>
      beta • z.1.2 + (1-beta) • batchGradient p mu z.1.1 z.2) :=
    (measurable_fst.snd.const_smul beta).add (hg.const_smul (1-beta))
  exact (measurable_fst.fst.sub (hm.const_smul eta)).prodMk hm

theorem measurable_process (d B : ℕ) (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (k : ℕ) :
    Measurable (fun ω : World d B => process eta beta p mu ω k) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
    exact (measurable_update d B eta beta p mu).comp
      (f := fun ω : World d B =>
        (process eta beta p mu ω k, ω.2 k))
      (ih.prodMk ((measurable_pi_apply k).comp measurable_snd))

end
end SparseSGD.Logistic
