import SparseSGD.Logistic.IncrementFluidBridge
import SparseSGD.Logistic.IncrementStoppedDomain
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false

def matchedOrbit {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s0 : State d) :
    ℕ → (Fin 5 → ℝ) := fun j => (matchedDriftMap (B := B) eta beta p mu)^[j] (matchedSummary eta beta mu s0)

theorem matchedOrbit_succ {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s0 : State d) (j : ℕ) :
    matchedOrbit (B := B) eta beta p mu s0 (j+1) =
      matchedDriftMap (B := B) eta beta p mu (matchedOrbit (B := B) eta beta p mu s0 j) :=
  Function.iterate_succ_apply' _ _ _

theorem matchedProcess_initial_dirac {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s0 : State d) :
    ∀ᵐ ω ∂worldLaw (B := B) p (Measure.dirac s0),
      matchedProcess eta beta p mu 0 ω = matchedOrbit (B := B) eta beta p mu s0 0 := by
  have hfirst : ∀ᵐ ω ∂worldLaw (B := B) p (Measure.dirac s0), ω.1 = s0 := by
    apply ae_of_ae_map (μ := worldLaw (B := B) p (Measure.dirac s0)) (f := Prod.fst)
      (p := fun s : State d => s = s0) measurable_fst.aemeasurable
    simp [worldLaw]
  filter_upwards [hfirst] with ω hω
  simp [matchedProcess,matchedOrbit,process,hω]

theorem lrIncrementVariance_nonneg {d B : ℕ} (eta : ℝ) (p : unitInterval) (mu : Vec d) (Q K L : ℝ) :
    0 ≤ lrIncrementVariance eta p mu Q K L B := by
  have hp : 0 ≤ (p : ℝ) := p.property.1
  dsimp [lrIncrementVariance,projectionVariance,rareProjectionConstant,bulkQuadraticVariance,
    bulkQuadraticConstant,complementQuadraticVariance,symmetricProjectionConstant]
  positivity

theorem lrIncrementScale_nonneg {d B : ℕ} (eta : ℝ) (mu : Vec d) (Q K L : ℝ)
    (heta : 0 ≤ eta) (hQ : 0 ≤ Q) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    0 ≤ lrIncrementScale eta mu Q K L B := by
  dsimp [lrIncrementScale,stoppedDirectionBound,projectionScale,bulkQuadraticScale,symmetricProjectionConstant,r]
  positivity

private theorem matched_proj_unit (i : Fin 5) :
    ‖(ContinuousLinearMap.proj i : (Fin 5 → ℝ) →L[ℝ] ℝ)‖ = 1 := by
  apply le_antisymm
  · apply (ContinuousLinearMap.proj i : (Fin 5 → ℝ) →L[ℝ] ℝ).opNorm_le_bound (by norm_num)
    intro y
    simpa using norm_le_pi_norm y i
  · have h := (ContinuousLinearMap.proj i : (Fin 5 → ℝ) →L[ℝ] ℝ).le_opNorm (Pi.single i 1)
    simpa only [ContinuousLinearMap.proj_apply,Pi.single_eq_same,Real.norm_eq_abs,abs_one,Pi.norm_single,norm_one,mul_one] using h

/-- Finite-horizon fluid estimate for the actual matched SGD process started
at a deterministic state. Actual conditional Bernstein A3 is proved here;
Jacobian-response and physical-process Taylor hypotheses remain explicit.
The Bernstein `M log` term is retained without a growth-rate absorption. -/
theorem actual_matched_fluid_limit {d B : ℕ}
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : SparseSGD.External.GaussianSteinCertificate d)
    (F : SparseSGD.External.MartingaleBernsteinCertificate (World d B))
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s0 : State d)
    (J : ℕ → (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ))
    (N : ℕ) (radius Gamma L2 Q Km L delta : ℝ)
    (hB : 0 < B) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hr : 0 < r mu)
    (heta : 0 ≤ eta) (hbeta : 0 ≤ beta) (hbeta1 : beta < 1) (hstep : eta*(p : ℝ) ≤ L)
    (hQ : 0 ≤ Q) (hKm : 0 ≤ Km) (hL : 0 ≤ L)
    (hN : 0 < N) (hGamma : 0 < Gamma) (hL2 : 0 ≤ L2) (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hdom : ∀ s : State d,
      (∃ i ≤ N, ‖matchedSummary eta beta mu s-matchedOrbit (B := B) eta beta p mu s0 i‖ ≤ radius) →
      tameError p mu s.1 ≤ 1/2 ∧ ‖s.1‖ ≤ Q ∧ ‖(eta/(1-beta)) • bulkPart mu s.2‖ ≤ Km)
    (hJ : ∀ k ≤ N, ∀ j < k, ‖jacobianResponse J k j‖ ≤ Gamma)
    (hTaylor : ∀ j < N, ∀ ω : World d B,
      ‖matchedProcess eta beta p mu j ω-matchedOrbit (B := B) eta beta p mu s0 j‖ ≤ radius →
      ‖matchedDriftMap (B := B) eta beta p mu (matchedProcess eta beta p mu j ω)-
        matchedDriftMap (B := B) eta beta p mu (matchedOrbit (B := B) eta beta p mu s0 j)-
        J j (matchedProcess eta beta p mu j ω-matchedOrbit (B := B) eta beta p mu s0 j)‖ ≤
        L2/2*‖matchedProcess eta beta p mu j ω-matchedOrbit (B := B) eta beta p mu s0 j‖^2)
    (hradius : 2*fluidThreshold Gamma (lrIncrementVariance eta p mu Q Km L B)
      (lrIncrementScale eta mu Q Km L B) N (Real.log (10*N/delta)) ≤ radius)
    (hsmall : 2*N*Gamma*L2*fluidThreshold Gamma (lrIncrementVariance eta p mu Q Km L B)
      (lrIncrementScale eta mu Q Km L B) N (Real.log (10*N/delta)) ≤ 1) :
    ENNReal.ofReal (1-delta) ≤ (worldLaw (B := B) p (Measure.dirac s0)) {ω | ∀ k ≤ N,
      ‖matchedProcess eta beta p mu k ω-matchedOrbit (B := B) eta beta p mu s0 k‖ ≤
        2*Gamma*(Real.sqrt (2*N*lrIncrementVariance eta p mu Q Km L B*Real.log (10*N/delta))+
          2*lrIncrementScale eta mu Q Km L B*Real.log (10*N/delta))} := by
  have hh := fluid_limit_normingFamily_on_process F (worldLaw p (Measure.dirac s0)) (pastFiltration d B)
    (matchedDriftMap (B := B) eta beta p mu) (measurable_matchedDriftMap eta beta p mu)
    (matchedProcess eta beta p mu) (matchedOrbit (B := B) eta beta p mu s0)
    (matchedProcess_stronglyAdapted eta beta p mu)
    (fun i : Fin 5 => ContinuousLinearMap.proj i) matched_proj_unit (fun y => le_rfl)
    J N radius Gamma L2 (lrIncrementVariance eta p mu Q Km L B) (lrIncrementScale eta mu Q Km L B) delta
    (by norm_num) hN hGamma hL2 (lrIncrementVariance_nonneg eta p mu Q Km L)
    (lrIncrementScale_nonneg eta mu Q Km L heta hQ hKm hL) hdelta0 hdelta1
    (matchedOrbit_succ eta beta p mu s0) (matchedProcess_initial_dirac eta beta p mu s0)
    hJ hTaylor (matchedProcess_fluidUnitBernstein H Ho G S eta beta p mu (Measure.dirac s0)
      _ radius Q Km L N hB hp0 hp1 hr heta hbeta hbeta1 hstep hdom) (by simpa only [Nat.cast_ofNat, show (2 : ℝ)*5 = 10 by norm_num] using hradius)
      (by simpa only [Nat.cast_ofNat, show (2 : ℝ)*5 = 10 by norm_num] using hsmall)
  simpa only [Nat.cast_ofNat, show (2 : ℝ)*5 = 10 by norm_num] using hh

def matchedTubeVariance {d : ℕ} (eta : ℝ) (p : unitInterval) (mu : Vec d) (T radius L : ℝ) (B : ℕ) : ℝ :=
  lrIncrementVariance eta p mu (matchedTubeParameterBound T radius) (matchedTubeMomentumBound T radius) L B

def matchedTubeScale {d : ℕ} (eta : ℝ) (mu : Vec d) (T radius L : ℝ) (B : ℕ) : ℝ :=
  lrIncrementScale eta mu (matchedTubeParameterBound T radius) (matchedTubeMomentumBound T radius) L B

/-- The actual finite-horizon estimate on a concrete closed matched tube.
Small `p` proves tameness throughout the tube; actual moment bounds supply
its parameter and momentum bounds. No stopped-domain assertion is assumed. -/
theorem actual_matched_fluid_limit_on_tube {d B : ℕ}
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : SparseSGD.External.GaussianSteinCertificate d)
    (F : SparseSGD.External.MartingaleBernsteinCertificate (World d B))
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s0 : State d)
    (J : ℕ → (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ))
    (N : ℕ) (radius Gamma L2 T L delta : ℝ)
    (hB : 0 < B) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hr : 0 < r mu)
    (heta : 0 ≤ eta) (hbeta : 0 ≤ beta) (hbeta1 : beta < 1) (hstep : eta*(p : ℝ) ≤ L)
    (hT : 0 ≤ T) (hradius0 : 0 ≤ radius) (hL : 0 ≤ L)
    (hN : 0 < N) (hGamma : 0 < Gamma) (hL2 : 0 ≤ L2) (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (href : ∀ i ≤ N, ‖matchedOrbit (B := B) eta beta p mu s0 i‖ ≤ T)
    (hptame : (p : ℝ)*stoppedTameConstant mu (matchedTubeParameterBound T radius) ≤ 1/2)
    (hJ : ∀ k ≤ N, ∀ j < k, ‖jacobianResponse J k j‖ ≤ Gamma)
    (hTaylor : ∀ j < N, ∀ ω : World d B,
      ‖matchedProcess eta beta p mu j ω-matchedOrbit (B := B) eta beta p mu s0 j‖ ≤ radius →
      ‖matchedDriftMap (B := B) eta beta p mu (matchedProcess eta beta p mu j ω)-
        matchedDriftMap (B := B) eta beta p mu (matchedOrbit (B := B) eta beta p mu s0 j)-
        J j (matchedProcess eta beta p mu j ω-matchedOrbit (B := B) eta beta p mu s0 j)‖ ≤
        L2/2*‖matchedProcess eta beta p mu j ω-matchedOrbit (B := B) eta beta p mu s0 j‖^2)
    (hradius : 2*fluidThreshold Gamma (matchedTubeVariance eta p mu T radius L B)
      (matchedTubeScale eta mu T radius L B) N (Real.log (10*N/delta)) ≤ radius)
    (hsmall : 2*N*Gamma*L2*fluidThreshold Gamma (matchedTubeVariance eta p mu T radius L B)
      (matchedTubeScale eta mu T radius L B) N (Real.log (10*N/delta)) ≤ 1) :
    ENNReal.ofReal (1-delta) ≤ (worldLaw (B := B) p (Measure.dirac s0)) {ω | ∀ k ≤ N,
      ‖matchedProcess eta beta p mu k ω-matchedOrbit (B := B) eta beta p mu s0 k‖ ≤
        2*Gamma*(Real.sqrt (2*N*matchedTubeVariance eta p mu T radius L B*Real.log (10*N/delta))+
          2*matchedTubeScale eta mu T radius L B*Real.log (10*N/delta))} := by
  exact actual_matched_fluid_limit H Ho G S F eta beta p mu s0 J N radius Gamma L2
    (matchedTubeParameterBound T radius) (matchedTubeMomentumBound T radius) L delta
    hB hp0 hp1 hr heta hbeta hbeta1 hstep (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hL
    hN hGamma hL2 hdelta0 hdelta1
    (matched_neighborhood_tame_bounds eta beta p mu hr _ N T radius hT hradius0 href hptame)
    hJ hTaylor hradius hsmall
end
end SparseSGD.Logistic
