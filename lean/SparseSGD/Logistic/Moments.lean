import SparseSGD.Logistic.Measurability
import SparseSGD.Probability.LeastSquares.GaussianVector
import SparseSGD.Probability.LeastSquares.IndependentBatch

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 800000

theorem sigma_pos (t : ℝ) : 0 < sigma t := by
  unfold sigma
  exact div_pos (Real.exp_pos _) (by positivity)

theorem sigma_lt_one (t : ℝ) : sigma t < 1 := by
  unfold sigma
  apply (div_lt_one (by positivity)).2
  nlinarith [Real.exp_pos t]

theorem logistic_residual_abs_le_one (t : ℝ) (y : Bool) :
    |sigma t - labelReal y| ≤ 1 := by
  cases y <;> simp only [labelReal, Bool.false_eq_true, ↓reduceIte] <;>
    rw [abs_le] <;> constructor <;> nlinarith [sigma_pos t, sigma_lt_one t]

private theorem gaussianVec_memLp_two (d : ℕ) :
    MemLp (fun z : Fin d → ℝ => (WithLp.toLp 2 z : Vec d)) 2
      (SparseSGD.Probability.standardGaussianProduct d) := by
  let Z : (Fin d → ℝ) → ℝ := fun z => ‖(WithLp.toLp 2 z : Vec d)‖ ^ 2
  have hZ : MemLp Z 2 (SparseSGD.Probability.standardGaussianProduct d) := by
    simpa [Z] using SparseSGD.Probability.LeastSquares.gaussian_norm_sq_memLp_two d
  have hmajor : MemLp (fun z : Fin d → ℝ => 1 + Z z) 2
      (SparseSGD.Probability.standardGaussianProduct d) :=
    (memLp_const (1 : ℝ)).add hZ
  have hmeas : AEStronglyMeasurable
      (fun z : Fin d → ℝ => (WithLp.toLp 2 z : Vec d))
      (SparseSGD.Probability.standardGaussianProduct d) :=
    ((WithLp.measurable_toLp 2 (Fin d → ℝ)).aestronglyMeasurable)
  have hbound : ∀ᵐ z ∂SparseSGD.Probability.standardGaussianProduct d,
      ‖(WithLp.toLp 2 z : Vec d)‖ ≤ ‖1 + Z z‖ := by
    filter_upwards with z
    have hn : 0 ≤ ‖(WithLp.toLp 2 z : Vec d)‖ := norm_nonneg _
    have hfirst : ‖(WithLp.toLp 2 z : Vec d)‖ ≤ 1 + Z z := by
      dsimp [Z]
      nlinarith [sq_nonneg (‖(WithLp.toLp 2 z : Vec d)‖ - 1/2)]
    calc
      ‖(WithLp.toLp 2 z : Vec d)‖ ≤ 1 + Z z := hfirst
      _ = ‖1 + Z z‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hmajor.of_le hmeas hbound

theorem sample_feature_memLp_two (d : ℕ) (p : unitInterval) (mu : Vec d) :
    MemLp (feature mu) 2 (sampleLaw d p) := by
  have hlabel : MemLp (fun a : Sample d => if a.1 then mu else 0) 2 (sampleLaw d p) := by
    apply MemLp.of_bound
      ((Measurable.ite (measurable_fst (measurableSet_singleton true))
        measurable_const measurable_const).aestronglyMeasurable) ‖mu‖
    filter_upwards with a
    by_cases ha : a.1 <;> simp [ha]
  have hnoise : MemLp (fun a : Sample d => (WithLp.toLp 2 a.2 : Vec d)) 2
      (sampleLaw d p) := by
    have hbase := gaussianVec_memLp_two d
    change MemLp (fun a : Sample d => (WithLp.toLp 2 a.2 : Vec d)) 2 (sampleLaw d p)
    simpa [sampleLaw, Function.comp_def] using hbase.comp_measurePreserving
      (measurePreserving_snd (μ := bernoulliMeasure true false p)
        (ν := SparseSGD.Probability.standardGaussianProduct d))
  have hsum := hlabel.add hnoise
  have hm : AEStronglyMeasurable (feature mu) (sampleLaw d p) :=
    (measurable_feature d mu).aestronglyMeasurable
  apply hsum.congr_norm hm
  filter_upwards with a
  simp [feature]

theorem gradient_memLp_two (d : ℕ) (p : unitInterval) (mu theta : Vec d) :
    MemLp (fun a : Sample d => gradient p mu theta a) 2 (sampleLaw d p) := by
  have hf := sample_feature_memLp_two d p mu
  apply hf.of_le
  · exact ((measurable_gradient d p mu).comp
      (f := fun a : Sample d => (theta, a))
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · filter_upwards with a
    rw [gradient, norm_smul, Real.norm_eq_abs]
    have hr := logistic_residual_abs_le_one
      (inner ℝ theta (feature mu a) + bias p mu) a.1
    exact mul_le_of_le_one_left (norm_nonneg _) hr

theorem batchGradient_memLp_two (d B : ℕ) (p : unitInterval) (mu theta : Vec d) :
    MemLp (fun a : Batch d B => batchGradient p mu theta a) 2
      (Measure.pi fun _ : Fin B => sampleLaw d p) := by
  simpa [batchGradient] using
    SparseSGD.Probability.LeastSquares.iid_batch_average_memLp
      (κ := sampleLaw d p) (f := gradient p mu theta) (gradient_memLp_two d p mu theta)

end
end SparseSGD.Logistic
