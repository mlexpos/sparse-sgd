import SparseSGD.Logistic.FluidConfidence
import SparseSGD.Logistic.IncrementFluidRates

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 2200000

def boundedFluidVarianceConstant (rr Q Km L T P : ℝ) : ℝ :=
  10*lrSourceVarianceConstant Q Km L*T*(1+P)^3*(1+rr^2)

def boundedFluidScaleConstant (rr Q Km L P : ℝ) : ℝ :=
  4*lrSourceScaleConstant Q Km L*P*(1+rr)*(1+P)

def boundedFluidRateConstant (rr Q Km L T P Gamma q a : ℝ) : ℝ :=
  2*Gamma*(Real.sqrt (2*boundedFluidVarianceConstant rr Q Km L T P*(q+14))+
    2*boundedFluidScaleConstant rr Q Km L P*(q+14)*(1+a))

/-- All factors in this square-root dimension bound are uniform once signal,
temperature, horizon, stopped neighborhood and the step-size absorption are bounded. -/
theorem actual_fluid_radius_sqrt_dimension {d B : ℕ}
    (eta : ℝ) (p : unitInterval) (mu : Vec d) (Q Km L T P Gamma q a : ℝ) (N : ℕ)
    (hd : 2 ≤ d) (hB : 0 < B) (hp : 0 < (p : ℝ)) (heta : 0 ≤ eta)
    (hQ : 0 ≤ Q) (hKm : 0 ≤ Km) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hP : 0 ≤ P) (hPhi : logisticPhi d B eta ≤ P) (hGamma : 0 ≤ Gamma)
    (hq : 0 ≤ q+14) (hN : 0 < N) (hpoly : (N : ℝ) ≤ (d : ℝ)^q)
    (hz : eta*(p : ℝ) ≤ 1) (hclock : (N : ℝ)*(eta*(p : ℝ)) ≤ T)
    (hetaSize : eta*Real.sqrt (Real.log d/(d : ℝ)) ≤ a) :
    2*Gamma*(Real.sqrt (2*N*lrIncrementVariance eta p mu Q Km L B*
      Real.log (10*(N : ℝ)/((d : ℝ)^10)⁻¹))+
      2*lrIncrementScale eta mu Q Km L B*Real.log (10*(N : ℝ)/((d : ℝ)^10)⁻¹)) ≤
      boundedFluidRateConstant (r mu) Q Km L T P Gamma q a * Real.sqrt (Real.log d/(d : ℝ)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hdm : 0 ≤ (d : ℝ)-1 := by linarith
  have hphi0 : 0 ≤ logisticPhi d B eta := by dsimp [logisticPhi]; positivity
  have hr : 0 ≤ r mu := norm_nonneg mu
  have hCv := lrSourceVarianceConstant_nonneg Q Km L
  have hCm := lrSourceScaleConstant_nonneg Q Km L hQ hKm hL
  have hv : (N : ℝ)*lrIncrementVariance eta p mu Q Km L B ≤
      boundedFluidVarianceConstant (r mu) Q Km L T P/(d : ℝ) := by
    apply (lrIncrement_horizon_variance_le_source eta p mu Q Km L N T hd hB hp heta hz hclock).trans
    dsimp [sourceFluidVarianceRate,boundedFluidVarianceConstant]
    gcongr
  have hm : lrIncrementScale eta mu Q Km L B ≤
      boundedFluidScaleConstant (r mu) Q Km L P*(1+eta)/(d : ℝ) := by
    apply (lrIncrement_scale_le_source_rate eta mu Q Km L hd hB heta hQ hKm hL).trans
    dsimp [sourceFluidScaleRate,boundedFluidScaleConstant]
    have hh : 1+logisticPhi d B eta+eta ≤ (1+P)*(1+eta) := by nlinarith
    calc
      _ ≤ 4*lrSourceScaleConstant Q Km L*P/(d : ℝ)*(1+r mu)*((1+P)*(1+eta)) := by gcongr
      _ = _ := by ring
  apply fluid_radius_sqrt_dimension_bound d N q
    (boundedFluidVarianceConstant (r mu) Q Km L T P)
    (boundedFluidScaleConstant (r mu) Q Km L P) eta a Gamma _ _ hd hN hpoly hq
    (by dsimp [boundedFluidVarianceConstant]; positivity)
    (by dsimp [boundedFluidScaleConstant]; positivity) heta hGamma hv hm hetaSize

theorem actual_matched_fluid_sqrt_dimension {d B : ℕ}
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : SparseSGD.External.GaussianSteinCertificate d)
    (F : SparseSGD.External.MartingaleBernsteinCertificate (World d B))
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s0 : State d)
    (J : ℕ → (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ))
    (N : ℕ) (radius Gamma L2 T L LearningT P q a : ℝ)
    (hd : 2 ≤ d) (hB : 0 < B) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hr : 0 < r mu)
    (heta : 0 ≤ eta) (hbeta : 0 ≤ beta) (hbeta1 : beta < 1) (hstep : eta*(p : ℝ) ≤ L)
    (hT : 0 ≤ T) (hradius0 : 0 ≤ radius) (hL : 0 ≤ L)
    (hN : 0 < N) (hGamma : 0 < Gamma) (hL2 : 0 ≤ L2)
    (hLearningT : 0 ≤ LearningT) (hP : 0 ≤ P) (hPhi : logisticPhi d B eta ≤ P)
    (hq : 0 ≤ q+14) (hpoly : (N : ℝ) ≤ (d : ℝ)^q)
    (hz : eta*(p : ℝ) ≤ 1) (hclock : (N : ℝ)*(eta*(p : ℝ)) ≤ LearningT)
    (hetaSize : eta*Real.sqrt (Real.log d/(d : ℝ)) ≤ a)
    (href : ∀ i ≤ N, ‖matchedOrbit (B := B) eta beta p mu s0 i‖ ≤ T)
    (hptame : (p : ℝ)*stoppedTameConstant mu (matchedTubeParameterBound T radius) ≤ 1/2)
    (hJ : ∀ k ≤ N, ∀ j < k, ‖jacobianResponse J k j‖ ≤ Gamma)
    (hTaylor : ∀ j < N, ∀ ω : World d B,
      ‖matchedProcess eta beta p mu j ω-matchedOrbit (B := B) eta beta p mu s0 j‖ ≤ radius →
      ‖matchedDriftMap (B := B) eta beta p mu (matchedProcess eta beta p mu j ω)-
        matchedDriftMap (B := B) eta beta p mu (matchedOrbit (B := B) eta beta p mu s0 j)-
        J j (matchedProcess eta beta p mu j ω-matchedOrbit (B := B) eta beta p mu s0 j)‖ ≤
        L2/2*‖matchedProcess eta beta p mu j ω-matchedOrbit (B := B) eta beta p mu s0 j‖^2)
    (hradius : boundedFluidRateConstant (r mu) (matchedTubeParameterBound T radius)
      (matchedTubeMomentumBound T radius) L LearningT P Gamma q a * Real.sqrt (Real.log d/(d : ℝ)) ≤ radius)
    (hsmall : N*Gamma*L2*(boundedFluidRateConstant (r mu) (matchedTubeParameterBound T radius)
      (matchedTubeMomentumBound T radius) L LearningT P Gamma q a * Real.sqrt (Real.log d/(d : ℝ))) ≤ 1) :
    ENNReal.ofReal (1-((d : ℝ)^10)⁻¹) ≤ (worldLaw (B := B) p (Measure.dirac s0)) {ω | ∀ k ≤ N,
      ‖matchedProcess eta beta p mu k ω-matchedOrbit (B := B) eta beta p mu s0 k‖ ≤
        boundedFluidRateConstant (r mu) (matchedTubeParameterBound T radius)
          (matchedTubeMomentumBound T radius) L LearningT P Gamma q a * Real.sqrt (Real.log d/(d : ℝ))} := by
  have hdelta := fluid_dimension_confidence d hd
  have hrate := actual_fluid_radius_sqrt_dimension eta p mu (matchedTubeParameterBound T radius)
    (matchedTubeMomentumBound T radius) L LearningT P Gamma q a N hd hB hp0 heta
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hL hLearningT hP hPhi hGamma.le hq hN hpoly hz hclock hetaSize
  have hrad : 2*fluidThreshold Gamma (matchedTubeVariance eta p mu T radius L B)
      (matchedTubeScale eta mu T radius L B) N (Real.log (10*N/((d : ℝ)^10)⁻¹)) ≤ radius := by
    convert hrate.trans hradius using 1 <;> dsimp [fluidThreshold,matchedTubeVariance,matchedTubeScale]; ring
  have hsm : 2*N*Gamma*L2*fluidThreshold Gamma (matchedTubeVariance eta p mu T radius L B)
      (matchedTubeScale eta mu T radius L B) N (Real.log (10*N/((d : ℝ)^10)⁻¹)) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hrate (show 0 ≤ (N : ℝ)*Gamma*L2 by positivity)
    apply le_trans _ hsmall
    convert hh using 1 <;> dsimp [fluidThreshold,matchedTubeVariance,matchedTubeScale]; ring
  have hh := actual_matched_fluid_limit_on_tube H Ho G S F eta beta p mu s0 J N radius Gamma L2 T L
    (((d : ℝ)^10)⁻¹) hB hp0 hp1 hr heta hbeta hbeta1 hstep hT hradius0 hL hN hGamma hL2
    hdelta.1 hdelta.2 href hptame hJ hTaylor hrad hsm
  exact hh.trans (measure_mono (fun ω hω k hk => (hω k hk).trans hrate))
end
end SparseSGD.Logistic
