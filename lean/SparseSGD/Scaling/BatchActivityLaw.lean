import SparseSGD.Scaling.BatchActivity
import SparseSGD.Probability.LeastSquares.Model

open MeasureTheory ProbabilityTheory
namespace SparseSGD.Scaling
noncomputable section

open SparseSGD.Probability.LeastSquares

def someMaskActive {d B : ℕ} (a : Batch d B) : Prop := ∃ i : Fin B, (a i).1 = true

theorem sampleLaw_inactive_real (d : ℕ) (p : unitInterval) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] :
    (sampleLaw d p ν).real {a | a.1 = false} = 1 - (p : ℝ) := by
  rw [sampleLaw, show ({a : Sample d | a.1 = false} : Set (Sample d)) = ({false} : Set Bool) ×ˢ Set.univ by
    ext a; simp]
  rw [measureReal_prod_prod]
  simp [bernoulliMeasure_real_apply]


theorem batchLaw_someMaskActive_real (d B : ℕ) (p : unitInterval) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] :
    (batchLaw d B p ν).real {a | someMaskActive a} = batchActivity (p:ℝ) B := by
  classical
  let inactive : Set (Sample d) := {a | a.1 = false}
  let S : Set (Batch d B) := {a | someMaskActive a}
  have hcomp : Sᶜ = Set.pi Set.univ (fun _ : Fin B => inactive) := by
    ext a
    simp [S, someMaskActive, inactive]
  have hI : MeasurableSet inactive := by
    exact measurable_fst (MeasurableSet.singleton false)
  have hSc : MeasurableSet Sᶜ := by rw [hcomp]; exact MeasurableSet.univ_pi (fun _ => hI)
  have hS : MeasurableSet S := by simpa using hSc.compl
  have hcompl := probReal_compl_eq_one_sub (μ := batchLaw d B p ν) hS
  have hprod : (batchLaw d B p ν).real (Set.pi Set.univ (fun _ : Fin B => inactive)) =
      (1-(p:ℝ))^B := by
    rw [batchLaw, measureReal_def, Measure.pi_pi]
    have hsample := sampleLaw_inactive_real d p ν
    change ((sampleLaw d p ν).real inactive) = 1-(p:ℝ) at hsample
    rw [measureReal_def] at hsample
    simp [hsample, Finset.prod_const]
  have hprodS : (batchLaw d B p ν).real Sᶜ = (1-(p:ℝ))^B := by rw [hcomp]; exact hprod
  rw [hprodS] at hcompl
  dsimp [batchActivity]
  linarith

end
end SparseSGD.Scaling
