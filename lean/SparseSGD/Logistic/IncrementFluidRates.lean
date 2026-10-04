import SparseSGD.Logistic.IncrementFluidLimit
import SparseSGD.Logistic.FluidScaling
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 2200000

def sourceFluidVarianceRate {d : ℕ} (eta : ℝ) (mu : Vec d) (Q Km L T : ℝ) (B : ℕ) : ℝ :=
  10*lrSourceVarianceConstant Q Km L*T*(1+logisticPhi d B eta)^3*(1+(r mu)^2)/(d : ℝ)

def sourceFluidScaleRate {d : ℕ} (eta : ℝ) (mu : Vec d) (Q Km L : ℝ) (B : ℕ) : ℝ :=
  4*lrSourceScaleConstant Q Km L*logisticPhi d B eta/(d : ℝ)*(1+r mu)*(1+logisticPhi d B eta+eta)

def sourceFluidRadius {d : ℕ} (eta : ℝ) (mu : Vec d) (Q Km L T Gamma logConfidence : ℝ) (B : ℕ) : ℝ :=
  2*Gamma*(Real.sqrt (2*sourceFluidVarianceRate eta mu Q Km L T B*logConfidence)+
    2*sourceFluidScaleRate eta mu Q Km L B*logConfidence)

theorem lrSourceVarianceConstant_nonneg (Q Km L : ℝ) : 0 ≤ lrSourceVarianceConstant Q Km L := by
  dsimp [lrSourceVarianceConstant,rareProjectionConstant,bulkQuadraticConstant,symmetricProjectionConstant]
  positivity

theorem lrSourceScaleConstant_nonneg (Q Km L : ℝ) (hQ : 0 ≤ Q) (hKm : 0 ≤ Km) (hL : 0 ≤ L) :
    0 ≤ lrSourceScaleConstant Q Km L := by
  dsimp [lrSourceScaleConstant,stoppedDirectionBound,symmetricProjectionConstant]
  positivity

theorem lrIncrement_horizon_variance_le_source {d B : ℕ} (eta : ℝ) (p : unitInterval)
    (mu : Vec d) (Q Km L : ℝ) (N : ℕ) (T : ℝ)
    (hd : 2 ≤ d) (hB : 0 < B) (hp : 0 < (p : ℝ)) (heta : 0 ≤ eta)
    (hz : eta*(p : ℝ) ≤ 1) (hT : (N : ℝ)*(eta*(p : ℝ)) ≤ T) :
    (N : ℝ)*lrIncrementVariance eta p mu Q Km L B ≤ sourceFluidVarianceRate eta mu Q Km L T B := by
  have h1 := mul_le_mul_of_nonneg_left (lrIncrementVariance_le_source eta p mu Q Km L hd hB hp)
    (show 0 ≤ (N : ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left (lrSourceVariance_horizon_bound eta p mu N T hd hB hp heta hz hT)
    (lrSourceVarianceConstant_nonneg Q Km L)
  calc
    _ ≤ lrSourceVarianceConstant Q Km L*((N : ℝ)*lrSourceVariance d B eta p mu) := by convert h1 using 1 <;> ring
    _ ≤ _ := by convert h2 using 1 <;> dsimp [sourceFluidVarianceRate]; ring

theorem lrIncrement_scale_le_source_rate {d B : ℕ} (eta : ℝ) (mu : Vec d) (Q Km L : ℝ)
    (hd : 2 ≤ d) (hB : 0 < B) (heta : 0 ≤ eta) (hQ : 0 ≤ Q) (hKm : 0 ≤ Km) (hL : 0 ≤ L) :
    lrIncrementScale eta mu Q Km L B ≤ sourceFluidScaleRate eta mu Q Km L B := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdminus : 0 ≤ (d : ℝ)-1 := by linarith
  have hphi : 0 ≤ logisticPhi d B eta := by dsimp [logisticPhi]; positivity
  have hr : 0 ≤ r mu := norm_nonneg mu
  have hh := mul_le_mul_of_nonneg_right (eta_div_batch_le_phi eta hd hB heta)
    (show 0 ≤ (1+r mu)*(1+logisticPhi d B eta+eta) by positivity)
  have hh' := mul_le_mul_of_nonneg_left hh (lrSourceScaleConstant_nonneg Q Km L hQ hKm hL)
  exact (lrIncrementScale_le_source eta mu Q Km L hd hB heta hQ hKm hL).trans (by
    dsimp [lrSourceScale,sourceFluidScaleRate]
    convert hh' using 1 <;> ring)

theorem actual_fluid_radius_le_source {d B : ℕ} (eta : ℝ) (p : unitInterval)
    (mu : Vec d) (Q Km L : ℝ) (N : ℕ) (T Gamma ell : ℝ)
    (hd : 2 ≤ d) (hB : 0 < B) (hp : 0 < (p : ℝ)) (heta : 0 ≤ eta)
    (hQ : 0 ≤ Q) (hKm : 0 ≤ Km) (hL : 0 ≤ L) (hGamma : 0 ≤ Gamma) (hell : 0 ≤ ell)
    (hz : eta*(p : ℝ) ≤ 1) (hT : (N : ℝ)*(eta*(p : ℝ)) ≤ T) :
    2*Gamma*(Real.sqrt (2*N*lrIncrementVariance eta p mu Q Km L B*ell)+
      2*lrIncrementScale eta mu Q Km L B*ell) ≤ sourceFluidRadius eta mu Q Km L T Gamma ell B := by
  have hv := lrIncrement_horizon_variance_le_source eta p mu Q Km L N T hd hB hp heta hz hT
  have hm := lrIncrement_scale_le_source_rate eta mu Q Km L hd hB heta hQ hKm hL
  dsimp [sourceFluidRadius]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply Real.sqrt_le_sqrt
    convert mul_le_mul_of_nonneg_right hv (show 0 ≤ 2*ell by positivity) using 1 <;> ring
  · convert mul_le_mul_of_nonneg_right hm (show 0 ≤ 2*ell by positivity) using 1 <;> ring
def matchedTubeSourceRadius {d : ℕ} (eta : ℝ) (mu : Vec d)
    (RefBound radius L LearningT Gamma ell : ℝ) (B : ℕ) : ℝ :=
  sourceFluidRadius eta mu (matchedTubeParameterBound RefBound radius) (matchedTubeMomentumBound RefBound radius)
    L LearningT Gamma ell B

/-- Actual stopped matched-process concentration in the source's cubic-Phi
variance scale. The dimension correction and the Bernstein linear term
are explicit; no asymptotic variance or conditional-noise conclusion is assumed. -/
theorem actual_matched_fluid_source_radius {d B : ℕ}
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : SparseSGD.External.GaussianSteinCertificate d)
    (F : SparseSGD.External.MartingaleBernsteinCertificate (World d B))
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s0 : State d)
    (J : ℕ → (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ))
    (N : ℕ) (radius Gamma L2 RefBound LearningT L delta : ℝ)
    (hd : 2 ≤ d) (hB : 0 < B) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hr : 0 < r mu)
    (heta : 0 ≤ eta) (hbeta : 0 ≤ beta) (hbeta1 : beta < 1) (hstep : eta*(p : ℝ) ≤ L)
    (hz : eta*(p : ℝ) ≤ 1) (hclock : (N : ℝ)*(eta*(p : ℝ)) ≤ LearningT)
    (hRef : 0 ≤ RefBound) (hradius0 : 0 ≤ radius) (hL : 0 ≤ L)
    (hN : 0 < N) (hGamma : 0 < Gamma) (hL2 : 0 ≤ L2) (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (href : ∀ i ≤ N, ‖matchedOrbit (B := B) eta beta p mu s0 i‖ ≤ RefBound)
    (hptame : (p : ℝ)*stoppedTameConstant mu (matchedTubeParameterBound RefBound radius) ≤ 1/2)
    (hJ : ∀ k ≤ N, ∀ j < k, ‖jacobianResponse J k j‖ ≤ Gamma)
    (hTaylor : ∀ j < N, ∀ ω : World d B,
      ‖matchedProcess eta beta p mu j ω-matchedOrbit (B := B) eta beta p mu s0 j‖ ≤ radius →
      ‖matchedDriftMap (B := B) eta beta p mu (matchedProcess eta beta p mu j ω)-
        matchedDriftMap (B := B) eta beta p mu (matchedOrbit (B := B) eta beta p mu s0 j)-
        J j (matchedProcess eta beta p mu j ω-matchedOrbit (B := B) eta beta p mu s0 j)‖ ≤
        L2/2*‖matchedProcess eta beta p mu j ω-matchedOrbit (B := B) eta beta p mu s0 j‖^2)
    (hradius : matchedTubeSourceRadius eta mu RefBound radius L LearningT Gamma (Real.log (10*N/delta)) B ≤ radius)
    (hsmall : N*Gamma*L2*matchedTubeSourceRadius eta mu RefBound radius L LearningT Gamma (Real.log (10*N/delta)) B ≤ 1) :
    ENNReal.ofReal (1-delta) ≤ (worldLaw (B := B) p (Measure.dirac s0)) {ω | ∀ k ≤ N,
      ‖matchedProcess eta beta p mu k ω-matchedOrbit (B := B) eta beta p mu s0 k‖ ≤
        matchedTubeSourceRadius eta mu RefBound radius L LearningT Gamma (Real.log (10*N/delta)) B} := by
  have hlog : 0 ≤ Real.log (10*N/delta) := by
    have hh := (fluid_log_confidence (by norm_num : 0 < 5) hN hdelta0 hdelta1).1
    simpa only [Nat.cast_ofNat,show (2 : ℝ)*5 = 10 by norm_num] using hh.le
  have hrate := actual_fluid_radius_le_source eta p mu
    (matchedTubeParameterBound RefBound radius) (matchedTubeMomentumBound RefBound radius) L N LearningT Gamma
    (Real.log (10*N/delta)) hd hB hp0 heta (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hL hGamma.le hlog hz hclock
  have hrad : 2*fluidThreshold Gamma (matchedTubeVariance eta p mu RefBound radius L B)
      (matchedTubeScale eta mu RefBound radius L B) N (Real.log (10*N/delta)) ≤ radius := by
    convert hrate.trans hradius using 1 <;> dsimp [fluidThreshold,matchedTubeVariance,matchedTubeScale]; ring
  have hsm : 2*N*Gamma*L2*fluidThreshold Gamma (matchedTubeVariance eta p mu RefBound radius L B)
      (matchedTubeScale eta mu RefBound radius L B) N (Real.log (10*N/delta)) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hrate (show 0 ≤ (N : ℝ)*Gamma*L2 by positivity)
    apply le_trans _ hsmall
    convert hh using 1 <;> dsimp [fluidThreshold,matchedTubeVariance,matchedTubeScale,matchedTubeSourceRadius]; ring
  have hh := actual_matched_fluid_limit_on_tube H Ho G S F eta beta p mu s0 J N radius Gamma L2 RefBound L delta
    hB hp0 hp1 hr heta hbeta hbeta1 hstep hRef hradius0 hL hN hGamma hL2 hdelta0 hdelta1 href hptame hJ hTaylor hrad hsm
  exact hh.trans (measure_mono (fun ω hω k hk => (hω k hk).trans hrate))
end
end SparseSGD.Logistic
