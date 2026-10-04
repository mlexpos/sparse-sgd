import SparseSGD.Logistic.IncrementFluidMapBounds
import SparseSGD.Logistic.FluidDeterministicVariance
import SparseSGD.Logistic.FluidDeterministicResponses
import SparseSGD.Logistic.FluidDimensionRate
import SparseSGD.Logistic.FluidDeterministicDerivative
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false

def matchedOrbitGamma (C LearningT : ℝ) : ℝ := 4*Real.exp (4*C*LearningT)

def boundedOrbitFluidRate (teacherNorm RefBound radius Load LearningT C q a : ℝ) (d : ℕ) : ℝ :=
  boundedFluidRateConstant teacherNorm (matchedTubeParameterBound RefBound radius)
    (matchedTubeMomentumBound RefBound radius) 1 LearningT Load (matchedOrbitGamma C LearningT) q a *
      Real.sqrt (Real.log d/(d : ℝ))

/-- Actual finite-horizon fluid concentration on a bounded deterministic
orbit. Jacobian products and physical-state Taylor estimates are proved,
not supplied as source assumptions. The only remaining dynamical input is
actual reference-orbit containment. Constants are dimension uniform. -/
theorem actual_matched_fluid_on_bounded_orbit
    (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (teacherNorm RefBound radius Load : ℝ)
    (hteacher : 0 ≤ teacherNorm) (hRef : 0 ≤ RefBound) (hradius0 : 0 ≤ radius) (hLoad : 0 ≤ Load) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d B : ℕ}
      (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
      (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
      (G : SparseSGD.External.GaussianQuadraticCertificate)
      (S : SparseSGD.External.GaussianSteinCertificate d)
      (S2 : SparseSGD.External.GaussianSteinCertificate 2)
      (F : SparseSGD.External.MartingaleBernsteinCertificate (World d B))
      (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s0 : State d)
      (N : ℕ) (LearningT q a : ℝ),
      2 ≤ d → 0 < B → 0 < (p : ℝ) → (p : ℝ) ≤ 1/2 →
      r mu=teacherNorm → 0 < r mu → 0 ≤ eta → 0 ≤ beta → beta < 1 →
      eta*(p : ℝ) ≤ 1 → logisticPhi d B eta ≤ Load → 0 < N →
      0 ≤ LearningT → (N : ℝ)*(eta*(p : ℝ)) ≤ LearningT →
      0 ≤ q+14 → (N : ℝ) ≤ (d : ℝ)^q → eta*Real.sqrt (Real.log d/(d : ℝ)) ≤ a →
      (∀ i ≤ N, ‖matchedOrbit (B := B) eta beta p mu s0 i‖ ≤ RefBound) →
      (p : ℝ)*stoppedTameConstant mu (matchedTubeParameterBound RefBound radius) ≤ 1/2 →
      boundedOrbitFluidRate teacherNorm RefBound radius Load LearningT C q a d ≤ radius →
      2*C*LearningT*matchedOrbitGamma C LearningT*
        boundedOrbitFluidRate teacherNorm RefBound radius Load LearningT C q a d ≤ 1 →
      ENNReal.ofReal (1-((d : ℝ)^10)⁻¹) ≤ (worldLaw (B := B) p (Measure.dirac s0)) {ω | ∀ k ≤ N,
        ‖matchedProcess eta beta p mu k ω-matchedOrbit (B := B) eta beta p mu s0 k‖ ≤
          boundedOrbitFluidRate teacherNorm RefBound radius Load LearningT C q a d} := by
  obtain ⟨C,hC,hcontrols⟩ := matchedPopulationJacobian_uniform_controls S1 teacherNorm
    (RefBound+radius) (teacherNorm+2*Load+2) (add_nonneg hRef hradius0) (by positivity)
  refine ⟨C,hC,?_⟩
  intro d B H Ho G S S2 F eta beta p mu s0 N LearningT q a hd hB hp hpHalf hmu hr heta hb0 hb1 hz hPhi
    hN hLearningT hclock hq hpoly hetaSize href hptame hrad hsmall
  let x := matchedOrbit (B := B) eta beta p mu s0
  let X := matchedProcess (B := B) eta beta p mu
  let J := fun j => matchedPopulationJacobian (B := B) eta beta p mu (x j)
  let Gamma := matchedOrbitGamma C LearningT
  let L2 := 2*C*(eta*(p : ℝ))
  have hparam : ‖matchedDimensionlessParameters (B := B) eta beta p mu‖ ≤ teacherNorm+2*Load+2 := by
    simpa only [hmu] using matchedDimensionlessParameters_norm_le eta beta p mu Load hd hB heta hb0 hb1.le hz hPhi
  have hctrl := hcontrols eta beta p mu hmu heta hp hpHalf hparam
  have hphysical : ∀ j, matchedPhysical (x j) := matchedDriftOrbit_physical S2 hd hB eta beta p mu hr x
    (matchedSummary_physical eta beta mu s0) (matchedOrbit_succ eta beta p mu s0)
  have hxnorm : ∀ j ≤ N, ‖x j‖ ≤ RefBound+radius := fun j hj => (href j hj).trans (by linarith)
  have hz0 : 0 ≤ eta*(p : ℝ) := mul_nonneg heta hp.le
  have hGamma : 0 < Gamma := by dsimp [Gamma,matchedOrbitGamma]; positivity
  have hL2 : 0 ≤ L2 := by dsimp [L2]; positivity
  have hJ : ∀ k ≤ N, ∀ j < k, ‖jacobianResponse J k j‖ ≤ Gamma := by
    have hce : (N : ℝ)*(C*(eta*(p : ℝ))) ≤ C*LearningT := by
      convert mul_le_mul_of_nonneg_left hclock hC using 1 <;> ring
    have hjperb : ∀ j < N, ‖J j-matchedFreeOperator beta‖ ≤ C*(eta*(p : ℝ)) := by
      intro j hj
      exact hctrl.1 (x j) (hphysical j) (hxnorm j hj.le)
    intro k hk j hj
    have hh := matchedJacobianResponse_bound beta (C*(eta*(p : ℝ))) (C*LearningT) hb0 hb1.le
      (mul_nonneg hC hz0) N hce J hjperb k hk j hj
    convert hh using 1 <;> dsimp [Gamma,matchedOrbitGamma] <;> ring
  have hTaylor : ∀ j < N, ∀ ω : World d B, ‖X j ω-x j‖ ≤ radius →
      ‖matchedDriftMap (B := B) eta beta p mu (X j ω)-matchedDriftMap (B := B) eta beta p mu (x j)-
        J j (X j ω-x j)‖ ≤ L2/2*‖X j ω-x j‖^2 := by
    intro j hj ω he
    have hXphys : matchedPhysical (X j ω) := matchedSummary_physical eta beta mu _
    have hXnorm : ‖X j ω‖ ≤ RefBound+radius := by
      calc
        _ = ‖(X j ω-x j)+x j‖ := by congr 1; module
        _ ≤ ‖X j ω-x j‖+‖x j‖ := norm_add_le _ _
        _ ≤ radius+RefBound := add_le_add he (href j hj.le)
        _ = _ := by ring
    have hrem := hctrl.2 (X j ω) (x j) hXphys (hphysical j) hXnorm (hxnorm j hj.le)
    change ‖matchedDriftMap (B := B) eta beta p mu (X j ω)-matchedDriftMap (B := B) eta beta p mu (x j)-
      J j (X j ω-x j)‖ ≤ C*(eta*(p : ℝ))*‖X j ω-x j‖^2 at hrem
    calc
      _ ≤ C*(eta*(p : ℝ))*‖X j ω-x j‖^2 := hrem
      _ = _ := by dsimp [L2]; ring
  have ha : 0 ≤ a := (mul_nonneg heta (Real.sqrt_nonneg _)).trans hetaSize
  have hCv := lrSourceVarianceConstant_nonneg (matchedTubeParameterBound RefBound radius)
    (matchedTubeMomentumBound RefBound radius) 1
  have hCm := lrSourceScaleConstant_nonneg (matchedTubeParameterBound RefBound radius)
    (matchedTubeMomentumBound RefBound radius) 1 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (by norm_num)
  have hrate0 : 0 ≤ boundedOrbitFluidRate teacherNorm RefBound radius Load LearningT C q a d := by
    dsimp [boundedOrbitFluidRate,boundedFluidRateConstant,boundedFluidVarianceConstant,boundedFluidScaleConstant]
    positivity
  have hsm : (N : ℝ)*Gamma*L2*boundedOrbitFluidRate teacherNorm RefBound radius Load LearningT C q a d ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hclock
      (show 0 ≤ 2*C*Gamma*boundedOrbitFluidRate teacherNorm RefBound radius Load LearningT C q a d by positivity)
    apply le_trans _ hsmall
    convert hh using 1 <;> dsimp [L2,Gamma] <;> ring
  have hh := actual_matched_fluid_sqrt_dimension H Ho G S F eta beta p mu s0 J N radius Gamma L2 RefBound 1
    LearningT Load q a hd hB hp (by linarith) hr heta hb0 hb1 hz hRef hradius0 (by norm_num) hN hGamma hL2
    hLearningT hLoad hPhi hq hpoly hz hclock hetaSize href hptame hJ hTaylor
    (by simpa only [hmu,boundedOrbitFluidRate,Gamma] using hrad)
    (by simpa only [hmu,boundedOrbitFluidRate,Gamma] using hsm)
  simpa only [hmu,boundedOrbitFluidRate,Gamma] using hh
/-- The formal heat-jet Jacobian is the genuine derivative within the
physical Gram domain, including at zero variance. -/
theorem matchedPopulationJacobian_hasFDerivWithinAt_physical {d B : ℕ}
    (S1 : SparseSGD.External.GaussianSteinCertificate 1) (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (T P : ℝ) (heta : 0 ≤ eta) (hp : 0 < (p : ℝ)) (hpHalf : (p : ℝ) ≤ 1/2)
    (hpar : ‖matchedDimensionlessParameters (B := B) eta beta p mu‖ ≤ P)
    (x : MatchedCoordinate) (hx : matchedPhysical x) (hxn : ‖x‖ < T) :
    HasFDerivWithinAt (matchedDriftMap (B := B) eta beta p mu)
      (matchedPopulationJacobian (B := B) eta beta p mu x) {y | matchedPhysical y} x := by
  have hT : 0 ≤ T := (norm_nonneg _).trans hxn.le
  have hP : 0 ≤ P := (norm_nonneg _).trans hpar
  obtain ⟨C,hC,h⟩ := matchedPopulationJacobian_uniform_controls S1 (r mu) T P hT hP
  have hc := h eta beta p mu rfl heta hp hpHalf hpar
  apply hasFDerivWithinAt_of_local_quadratic_bound _ _ _ _ (C*(eta*(p : ℝ))) (T-‖x‖)
    (mul_nonneg hC (mul_nonneg heta hp.le)) (by linarith)
  intro y hy hdist
  have hyn : ‖y‖ ≤ T := by
    calc
      _ = ‖(y-x)+x‖ := by congr 1; module
      _ ≤ ‖y-x‖+‖x‖ := norm_add_le _ _
      _ ≤ T := by linarith
  exact hc.2 y x hy hx hyn hxn.le

/-- All derivative, response, and final rate constants are chosen before
any dimension, batch size or SGD parameter. The actual bounded-orbit
concentration needs no Jacobian, Taylor, conditional-noise, or variance
conclusion as a hypothesis. -/
theorem actual_matched_fluid_uniform_constants
    (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (teacherNorm RefBound radius Load LearningT q a : ℝ)
    (hteacher : 0 ≤ teacherNorm) (hRef : 0 ≤ RefBound) (hradius0 : 0 ≤ radius) (hLoad : 0 ≤ Load)
    (hLearningT : 0 ≤ LearningT) (hq : 0 ≤ q+14) (ha : 0 ≤ a) :
    ∃ Cjet Gamma Csqrt : ℝ, 0 ≤ Cjet ∧ 0 < Gamma ∧ 0 ≤ Csqrt ∧ ∀ {d B : ℕ}
      (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
      (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
      (G : SparseSGD.External.GaussianQuadraticCertificate)
      (S : SparseSGD.External.GaussianSteinCertificate d)
      (S2 : SparseSGD.External.GaussianSteinCertificate 2)
      (F : SparseSGD.External.MartingaleBernsteinCertificate (World d B))
      (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s0 : State d) (N : ℕ),
      2 ≤ d → 0 < B → 0 < (p : ℝ) → (p : ℝ) ≤ 1/2 →
      r mu=teacherNorm → 0 < r mu → 0 ≤ eta → 0 ≤ beta → beta < 1 →
      eta*(p : ℝ) ≤ 1 → logisticPhi d B eta ≤ Load → 0 < N →
      (N : ℝ)*(eta*(p : ℝ)) ≤ LearningT →
      (N : ℝ) ≤ (d : ℝ)^q → eta*Real.sqrt (Real.log d/(d : ℝ)) ≤ a →
      (∀ i ≤ N, ‖matchedOrbit (B := B) eta beta p mu s0 i‖ ≤ RefBound) →
      (p : ℝ)*stoppedTameConstant mu (matchedTubeParameterBound RefBound radius) ≤ 1/2 →
      Csqrt*Real.sqrt (Real.log d/(d : ℝ)) ≤ radius →
      2*Cjet*LearningT*Gamma*Csqrt*Real.sqrt (Real.log d/(d : ℝ)) ≤ 1 →
      ENNReal.ofReal (1-((d : ℝ)^10)⁻¹) ≤ (worldLaw (B := B) p (Measure.dirac s0)) {ω | ∀ k ≤ N,
        ‖matchedProcess eta beta p mu k ω-matchedOrbit (B := B) eta beta p mu s0 k‖ ≤
          Csqrt*Real.sqrt (Real.log d/(d : ℝ))} := by
  obtain ⟨C,hC,h⟩ := actual_matched_fluid_on_bounded_orbit S1 teacherNorm RefBound radius Load
    hteacher hRef hradius0 hLoad
  let Gamma := matchedOrbitGamma C LearningT
  let Csqrt := boundedFluidRateConstant teacherNorm (matchedTubeParameterBound RefBound radius)
    (matchedTubeMomentumBound RefBound radius) 1 LearningT Load Gamma q a
  have hGamma : 0 < Gamma := by dsimp [Gamma,matchedOrbitGamma]; positivity
  have hCv := lrSourceVarianceConstant_nonneg (matchedTubeParameterBound RefBound radius)
    (matchedTubeMomentumBound RefBound radius) 1
  have hCm := lrSourceScaleConstant_nonneg (matchedTubeParameterBound RefBound radius)
    (matchedTubeMomentumBound RefBound radius) 1 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (by norm_num)
  have hCsqrt : 0 ≤ Csqrt := by
    dsimp [Csqrt,boundedFluidRateConstant,boundedFluidVarianceConstant,boundedFluidScaleConstant]
    positivity
  refine ⟨C,Gamma,Csqrt,hC,hGamma,hCsqrt,?_⟩
  intro d B H Ho G S S2 F eta beta p mu s0 N hd hB hp hpHalf hmu hr heta hb0 hb1 hz hPhi hN hclock hpoly
    hetaSize href hptame hrad hsmall
  have hh := h H Ho G S S2 F eta beta p mu s0 N LearningT q a hd hB hp hpHalf hmu hr heta hb0 hb1 hz hPhi hN
    hLearningT hclock hq hpoly hetaSize href hptame
    (by simpa only [boundedOrbitFluidRate,Csqrt,Gamma] using hrad)
    (by simpa only [boundedOrbitFluidRate,Csqrt,Gamma,mul_assoc] using hsmall)
  simpa only [boundedOrbitFluidRate,Csqrt,Gamma] using hh
end
end SparseSGD.Logistic

