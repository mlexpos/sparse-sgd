import SparseSGD.Probability.LeastSquares.Public
import SparseSGD.Probability.LeastSquares.BoundaryCases

open MeasureTheory
open SparseSGD.Probability.LeastSquares

namespace SparseSGD.Examples
noncomputable section

/-- Unit error in one dimension. -/
def seedVec1 : Vec 1 := WithLp.toLp 2 (fun _ => (1 : ℝ))

def leastSquaresInitialLaw : Measure (State 1) := Measure.dirac (seedVec1, 0)

instance : IsProbabilityMeasure leastSquaresInitialLaw := by
  unfold leastSquaresInitialLaw
  infer_instance

def leastSquaresWorldLaw : Measure (World 1 1) :=
  worldLaw (1 : unitInterval) (Measure.dirac (0 : ℝ)) leastSquaresInitialLaw

private theorem seedVec1_norm_sq : ‖seedVec1‖ ^ 2 = 1 := by
  simp [seedVec1, euclidean_norm_sq_eq_sum]

private theorem seed_fst_memLp :
    MemLp (fun s : State 1 => s.1) 2 leastSquaresInitialLaw := by
  exact (memLp_congr_ae (ae_eq_dirac (fun s : State 1 => s.1))).2
    (memLp_const seedVec1)

private theorem seed_snd_memLp :
    MemLp (fun s : State 1 => s.2) 2 leastSquaresInitialLaw := by
  exact (memLp_congr_ae (ae_eq_dirac (fun s : State 1 => s.2))).2
    (memLp_const (0 : Vec 1))

private theorem seed_integratedMoments :
    integratedMoments leastSquaresInitialLaw Prod.fst Prod.snd = ⟨1, 0, 0⟩ := by
  apply Moments.ext <;>
    simp [integratedMoments, leastSquaresInitialLaw, seedVec1_norm_sq]

/-- End-to-end regression for the actual Gaussian process: one sample, one
dimension, no sparsification or label noise, and a deterministic cold start. -/
theorem leastSquares_one_step :
    integratedMoments leastSquaresWorldLaw
      (fun ω => (process (3/4) (1/4) ω 1).1)
      (fun ω => (process (3/4) (1/4) ω 1).2) = ⟨227/256, 3/256, 13/256⟩ := by
  have h := leastSquares_moment_trajectory (d := 1) (B := 1) (by norm_num)
    (1 : unitInterval) (by norm_num) (Measure.dirac (0 : ℝ)) leastSquaresInitialLaw
    label_memLp_dirac_zero label_mean_dirac_zero (3/4) (1/4)
    seed_fst_memLp seed_snd_memLp 1
  change integratedMoments leastSquaresWorldLaw _ _ = _ at h
  rw [h, seed_integratedMoments]
  apply Moments.ext <;>
    norm_num [Params.trajectory, params, oracleParams, vinc, vadd,
      labelVariance_dirac_zero, Params.step, Params.eps]

/-- The risk value is obtained from the process integral, not just its recurrence. -/
theorem leastSquares_one_step_risk :
    (∫ ω : World 1 1, ‖(process (3/4) (1/4) ω 1).1‖ ^ 2 ∂leastSquaresWorldLaw) =
      227/256 := by
  exact congrArg Moments.R leastSquares_one_step

end
end SparseSGD.Examples
