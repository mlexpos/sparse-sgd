import SparseSGD.Examples.LogisticTeacher
import SparseSGD.Logistic.FluidPowerTameCells

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open SparseSGD.Logistic SparseSGD.Scaling
namespace SparseSGD.Examples
noncomputable section

/-- The fixed-probability branch has an actual admissible probability:
with unit teacher, B=d, eta=1/d and beta=1/2, some fixed p>0 satisfies
the fluid conclusion. Every family hypothesis is discharged. -/
theorem logistic_fixed_probability_fluid_example
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : ∀ n, SparseSGD.External.GaussianSteinCertificate n)
    (F : ∀ d, SparseSGD.External.MartingaleBernsteinCertificate
      (World d (scaledBatch 1 1 d))) :
    ∃ p : unitInterval, 0<(p : ℝ) ∧ ∃ C : ℝ, 0<C ∧ ∀ᶠ d : ℕ in atTop,
      ENNReal.ofReal (1-((d:ℝ)^10)⁻¹) ≤
        (worldLaw (B:=scaledBatch 1 1 d) p (Measure.dirac (coldState d)))
          {ω | ∀ k≤fluidGridHorizon 1 1 (p : ℝ) 1 0 (1/2) 0 d,
            ‖matchedProcess (scaledLearningRate 1 1 d) (scaledMomentum (1/2) 0 d)
                p (logisticTeacher 1 d) k ω-
              matchedOrbit (B:=scaledBatch 1 1 d) (scaledLearningRate 1 1 d)
                (scaledMomentum (1/2) 0 d) p (logisticTeacher 1 d) (coldState d) k‖ ≤
              C*Real.sqrt (Real.log d/(d:ℝ))} := by
  obtain ⟨cap,hcap,hfamily⟩ := actual_fluid_power_tame_cell_two H Ho G S
    1 1 1 1 (1/2) 0 1 1 (logisticTeacher 1) (Measure.dirac (0 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (logisticTeacher_norm_eventually 1 (by norm_num)) F
  let x := min (1 : ℝ) cap / 2
  have hm : 0 < min (1 : ℝ) cap := lt_min (by norm_num) hcap
  have hx : 0 < x := by dsimp [x]; positivity
  have hxm : x ≤ min (1 : ℝ) cap := by dsimp [x]; linarith
  let p : unitInterval := ⟨x,hx.le,hxm.trans (min_le_left _ _)⟩
  refine ⟨p,hx,?_⟩
  exact hfamily x (fun _ => p) ⟨hx,hxm⟩
    (Filter.Eventually.of_forall (fun d => by simp [p,scaledSparsity]))

end
end SparseSGD.Examples
