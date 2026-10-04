import SparseSGD.Examples.LogisticTeacher
import SparseSGD.Logistic.FluidPowerCells

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open SparseSGD.Logistic SparseSGD.Scaling
namespace SparseSGD.Examples
noncomputable section

/-- Probability 1/d for positive dimensions, with a valid value at dimension 0. -/
def reciprocalProbability (d : ℕ) : unitInterval :=
  ⟨(max 1 (d : ℝ))⁻¹, by
    constructor
    · positivity
    · exact (inv_le_one₀ (by positivity)).mpr (le_max_left _ _)⟩

theorem reciprocalProbability_power :
    ∀ᶠ d : ℕ in atTop, (reciprocalProbability d : ℝ)=scaledSparsity 1 1 d := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with d hd
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  simp [reciprocalProbability,scaledSparsity,max_eq_right hdR,Real.rpow_neg_one]

/-- End-to-end actual logistic fluid example: unit teacher, B=d, eta=p=1/d,
beta=1/2, zero initial state, and one unit of the minimum clock. All family,
containment and rate hypotheses are discharged. Only the documented generic
Gaussian and concentration certificates are parameters. -/
theorem logistic_fluid_example
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : ∀ n, SparseSGD.External.GaussianSteinCertificate n)
    (F : ∀ d, SparseSGD.External.MartingaleBernsteinCertificate
      (World d (scaledBatch 1 1 d))) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ d : ℕ in atTop,
      ENNReal.ofReal (1-((d:ℝ)^10)⁻¹) ≤
        (worldLaw (B:=scaledBatch 1 1 d) (reciprocalProbability d)
          (Measure.dirac (coldState d)))
          {ω | ∀ k≤fluidGridHorizon 1 1 1 1 1 (1/2) 0 d,
            ‖matchedProcess (scaledLearningRate 1 1 d) (scaledMomentum (1/2) 0 d)
                (reciprocalProbability d) (logisticTeacher 1 d) k ω-
              matchedOrbit (B:=scaledBatch 1 1 d) (scaledLearningRate 1 1 d)
                (scaledMomentum (1/2) 0 d) (reciprocalProbability d)
                (logisticTeacher 1 d) (coldState d) k‖ ≤
              C*Real.sqrt (Real.log d/(d:ℝ))} := by
  apply actual_fluid_power_cell_two H Ho G S 1 1 1 1 (1/2) 0 1 1 1 1
    reciprocalProbability (logisticTeacher 1) (Measure.dirac (0 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) reciprocalProbability_power (by norm_num) (by norm_num)
    (by norm_num) (logisticTeacher_norm_eventually 1 (by norm_num)) F

end
end SparseSGD.Examples
