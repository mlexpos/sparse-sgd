import SparseSGD.Logistic.IncrementDriftMap
import SparseSGD.Logistic.IncrementSourceRates
import SparseSGD.Logistic.FluidDomain
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

def pastFiltration (d B : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (World d B)) :=
  ⟨pastSigma d B,fun _ _ h => pastSigma_mono h,pastSigma_le_ambient d B⟩

def matchedProcess {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) :
    ℕ → World d B → (Fin 5 → ℝ) := fun j ω => matchedSummary eta beta mu (process eta beta p mu ω j)

theorem matchedProcess_stronglyAdapted {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) :
    StronglyAdapted (pastFiltration d B) (matchedProcess (B := B) eta beta p mu) := by
  intro j
  exact ((measurable_matchedSummary eta beta mu).comp (process_past_measurable d B eta beta p mu j)).stronglyMeasurable

theorem matchedProcess_fluidNoise {d B : ℕ}
    (S : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (hr : 0 < r mu) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (heps : 1-beta ≠ 0)
    (j : ℕ) (ω : World d B) :
    fluidNoise (matchedDriftMap (B := B) eta beta p mu) (matchedProcess eta beta p mu) j ω =
      matchedIncrement eta beta p mu (process eta beta p mu ω j) (ω.2 j) := by
  dsimp [fluidNoise,matchedProcess,matchedIncrement]
  rw [matchedDriftMap_summary S hB eta beta p mu _ hr hp0 hp1 heps]
  rfl

/-- Literal source A3 for the actual matched process, with every fresh-batch
law and exponential-integrability premise discharged. The stopped-domain
bounds and bounded effective learning step are explicit. -/
theorem matchedProcess_fluidUnitBernstein {d B : ℕ}
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (J : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : SparseSGD.External.GaussianSteinCertificate d)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (ν : Measure (State d)) [IsProbabilityMeasure ν]
    (x : ℕ → (Fin 5 → ℝ)) (radius Q Km L : ℝ) (N : ℕ)
    (hB : 0 < B) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hr : 0 < r mu)
    (heta : 0 ≤ eta) (hbeta : 0 ≤ beta) (hbeta1 : beta < 1) (hstep : eta*(p : ℝ) ≤ L)
    (hdom : ∀ s : State d, (∃ i ≤ N, ‖matchedSummary eta beta mu s-x i‖ ≤ radius) →
      tameError p mu s.1 ≤ 1/2 ∧ ‖s.1‖ ≤ Q ∧ ‖(eta/(1-beta)) • bulkPart mu s.2‖ ≤ Km) :
    FluidUnitBernstein (worldLaw p ν) (pastFiltration d B) (matchedDriftMap (B := B) eta beta p mu)
      (matchedProcess eta beta p mu) x radius (lrIncrementVariance eta p mu Q Km L B)
      (lrIncrementScale eta mu Q Km L B) N := by
  intro j hj ell hell t ht0 ht
  let U : Set (State d) := {s | ∃ i ≤ N, ‖matchedSummary eta beta mu s-x i‖ ≤ radius}
  have hraw := process_tame_matchedIncrement_dual_condLExp H J G S eta beta p mu ν j U ell
    Q Km L t hB hp0 hr heta hbeta hbeta1 hell.le
    (fun s hs => (hdom s hs).1) (fun s hs => (hdom s hs).2.1)
    (fun s hs => (hdom s hs).2.2) hstep (by simpa only [abs_of_nonneg ht0] using ht)
  simpa only [matchedProcess_fluidNoise S hB eta beta p mu hr hp0 hp1 (by linarith) j,
    abs_of_nonneg ht0,U,Set.mem_setOf_eq,matchedProcess,pastFiltration] using hraw
end
end SparseSGD.Logistic
