import SparseSGD.Probability.LeastSquares.Model

open MeasureTheory ProbabilityTheory
namespace SparseSGD.Probability.LeastSquares
set_option maxHeartbeats 800000

theorem measurable_feature (d : ℕ) : Measurable (feature (d := d)) := by
  unfold feature
  apply Measurable.ite (measurable_fst (measurableSet_singleton true))
  · exact (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp measurable_snd.fst
  · exact measurable_const

theorem measurable_gradient (d : ℕ) :
    Measurable (fun x : Vec d × Sample d => gradient x.1 x.2) := by
  unfold gradient
  exact ((measurable_feature d |>.comp measurable_snd).inner measurable_fst |>.sub
    (measurable_snd.snd.snd)).smul ((measurable_feature d).comp measurable_snd)

theorem measurable_batchGradient (d B : ℕ) :
    Measurable (fun x : Vec d × Batch d B => batchGradient x.1 x.2) := by
  unfold batchGradient
  have h : Measurable (fun x : Vec d × Batch d B => ∑ i, gradient x.1 (x.2 i)) := by
    apply Finset.measurable_sum
    intro i _
    have hmap : Measurable (fun x : Vec d × Batch d B => (x.1, x.2 i)) :=
      measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
    exact (measurable_gradient d).comp (f := fun x : Vec d × Batch d B => (x.1, x.2 i)) hmap
  exact h.const_smul ((B : ℝ)⁻¹)

theorem measurable_update (d B : ℕ) (beta eta : ℝ) :
    Measurable (fun x : State d × Batch d B => update beta eta x.1 x.2) := by
  have hg : Measurable (fun x : State d × Batch d B => batchGradient x.1.1 x.2) :=
    (measurable_batchGradient d B).comp
      (f := fun x : State d × Batch d B => (x.1.1, x.2))
      (measurable_fst.fst.prodMk measurable_snd)
  have hq : Measurable (fun x : State d × Batch d B =>
      beta • x.1.2 + (eta * (1-beta)) • batchGradient x.1.1 x.2) :=
    (measurable_fst.snd.const_smul beta).add (hg.const_smul (eta * (1-beta)))
  exact (measurable_fst.fst.sub hq).prodMk hq

theorem measurable_process (d B : ℕ) (beta eta : ℝ) (k : ℕ) :
    Measurable (fun ω : World d B => process beta eta ω k) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
    exact (measurable_update d B beta eta).comp
      (ih.prodMk ((measurable_pi_apply k).comp measurable_snd))

end SparseSGD.Probability.LeastSquares
