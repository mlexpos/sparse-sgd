import SparseSGD.Comparison.BoundedComparison
import SparseSGD.Comparison.SingleModeQuadrature

open MeasureTheory Set

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1000000

def Params.comparisonForcing (p : Params) (s : Moments) (t : ℝ) : ℝ :=
  p.renormNoise*(p.comparisonFlow s t).R+p.renormAdditive

def Params.comparisonForcingDeriv (p : Params) (s : Moments) (t : ℝ) : ℝ :=
  p.renormNoise*(continuumField p.matchedDelta p.renormNoise p.renormAdditive
    (p.comparisonFlow s t)).R

theorem Params.comparisonForcing_hasDerivAt (p : Params) (s : Moments) (t : ℝ) :
    HasDerivAt (p.comparisonForcing s) (p.comparisonForcingDeriv s t) t :=
  ((continuumFlow_hasDerivAt p.matchedDelta p.renormNoise p.renormAdditive
    (p.matchedMoments s) t).1.const_mul p.renormNoise).add_const p.renormAdditive

theorem Params.comparisonForcingDeriv_continuous (p : Params) (s : Moments) :
    Continuous (p.comparisonForcingDeriv s) := by
  have hC : Continuous (fun x => (p.comparisonFlow s x).C) :=
    continuous_iff_continuousAt.mpr fun x =>
      (continuumFlow_hasDerivAt p.matchedDelta p.renormNoise p.renormAdditive
        (p.matchedMoments s) x).2.2.continuousAt
  exact (hC.const_mul (-2*p.matchedDelta)).const_mul p.renormNoise

theorem Params.comparisonForcing_bounds (p : Params) (s : Moments)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) (hs : s.psd)
    (hu0 : 0 ≤ p.renormNoise) (hp : 0 ≤ p.renormAdditive)
    (margin : ℝ) (hm : 0 < margin) (hu : p.renormNoise ≤ 1-margin)
    (t : ℝ) (ht : 0 ≤ t) :
    |p.comparisonForcing s t| ≤ (p.comparisonInitialSize s+p.renormAdditive)/margin ∧
    |p.comparisonForcingDeriv s t| ≤ Real.sqrt p.matchedDelta*(1+2/margin)*
      (p.comparisonInitialSize s+p.renormAdditive) := by
  have hd := p.matchedDelta_pos (by linarith) hb1 hw0 hw1
  have hu1 : p.renormNoise < 1 := by linarith
  have hgap : 0 < 1-p.renormNoise := by linarith
  have hs0 := p.matchedMoments_psd s hs
  let e := (p.matchedMoments s).R+p.matchedDelta*(p.matchedMoments s).V
  let B := continuumRiskBound p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s)
  let N := p.comparisonInitialSize s+p.renormAdditive
  have he : 0 ≤ e := add_nonneg (Moments.psd_R_nonneg hs0)
    (mul_nonneg hd.le (Moments.psd_V_nonneg hs0))
  have hB : 0 ≤ B := div_nonneg (add_nonneg he hp) hgap.le
  have hBeq : (1-p.renormNoise)*B = e+p.renormAdditive := by
    dsimp [B,continuumRiskBound,e]
    field_simp
  have hF : p.renormNoise*B+p.renormAdditive ≤ B := by nlinarith
  have hE : continuumEnergyBound p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s) ≤
      e+p.renormAdditive+2*B := by
    change e+(1+p.renormNoise)*B+p.renormAdditive ≤ _
    nlinarith
  have hEn : 0 ≤ continuumEnergyBound p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s) :=
    add_nonneg (add_nonneg he (mul_nonneg (by linarith) hB)) hp
  have hE' : p.renormNoise*continuumEnergyBound p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s) ≤
      e+p.renormAdditive+2*B := by nlinarith
  have hBN : B ≤ N/margin := by
    apply (le_div_iff₀ hm).2
    have hmul := mul_le_mul_of_nonneg_right (show margin ≤ 1-p.renormNoise by linarith) hB
    dsimp [N,Params.comparisonInitialSize]
    dsimp [e] at hBeq
    nlinarith [abs_nonneg (p.matchedMoments s).C]
  have heN : e+p.renormAdditive ≤ N := by
    dsimp [N,Params.comparisonInitialSize,e]
    linarith [abs_nonneg (p.matchedMoments s).C]
  constructor
  · have hR0 := continuumFlow_R_nonneg hd hu0 hp _ hs0 ht
    have hR := continuumFlow_risk_uniform_bound hd hu0 hu1 hp _ hs0 ht
    change 0 ≤ (p.comparisonFlow s t).R at hR0
    change (p.comparisonFlow s t).R ≤ B at hR
    unfold Params.comparisonForcing
    rw [abs_of_nonneg (by positivity)]
    exact (add_le_add (mul_le_mul_of_nonneg_left hR hu0) le_rfl).trans (hF.trans hBN)
  · have hder := continuumFlow_risk_derivative_bound hd hu0 hu1 hp _ hs0 ht
    rw [((continuumFlow_hasDerivAt p.matchedDelta p.renormNoise p.renormAdditive
      (p.matchedMoments s) t).1).deriv] at hder
    have h1 : |p.comparisonForcingDeriv s t| ≤
        Real.sqrt p.matchedDelta*(p.renormNoise*
          continuumEnergyBound p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s)) := by
      unfold Params.comparisonForcingDeriv
      rw [abs_mul, abs_of_nonneg hu0]
      simpa only [mul_assoc, mul_comm, mul_left_comm, Params.comparisonFlow] using
        mul_le_mul_of_nonneg_left hder hu0
    have h2 : p.renormNoise*continuumEnergyBound p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s) ≤
        (1+2/margin)*N := by
      rw [show (1+2/margin)*N = N+2*(N/margin) by ring]
      linarith
    exact h1.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg p.matchedDelta))

theorem Params.single_mode_comparison_quadrature_bounded (p : Params) (s : Moments)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) (hs : s.psd)
    (hu0 : 0 ≤ p.renormNoise) (hp : 0 ≤ p.renormAdditive)
    (D0 margin : ℝ) (hm : 0 < margin) (hu : p.renormNoise ≤ 1-margin)
    (hD : p.matchedDelta ≤ D0) (lambda : ℂ) (hl : lambda.re = -1)
    (hnorm : ‖lambda‖ ≤ 2*Real.sqrt D0) (k : ℕ) :
    ‖(∫ x in (0 : ℝ)..(k : ℝ)*p.matchedStep,
        Complex.exp (lambda*(x : ℂ))*(p.comparisonForcing s ((k : ℝ)*p.matchedStep-x) : ℂ)) -
      rightEndpointSum (fun x => Complex.exp (lambda*(x : ℂ))*
        (p.comparisonForcing s ((k : ℝ)*p.matchedStep-x) : ℂ)) p.matchedStep k‖ ≤
      p.matchedStep*Real.sqrt D0*(1+4/margin)*(p.comparisonInitialSize s+p.renormAdditive) := by
  have hd := p.matchedDelta_pos (by linarith) hb1 hw0 hw1
  have hh := p.matchedStep_pos (by linarith) hb1
  have hs0 := p.matchedMoments_psd s hs
  let N := p.comparisonInitialSize s+p.renormAdditive
  have hN : 0 ≤ N := by
    have hr := Moments.psd_R_nonneg hs0
    have hv := Moments.psd_V_nonneg hs0
    dsimp [N,Params.comparisonInitialSize]
    positivity
  have H := single_mode_convolution_quadrature_bound lambda hl hh k
    (p.comparisonForcing s) (p.comparisonForcingDeriv s)
    (p.comparisonForcing_hasDerivAt s) (p.comparisonForcingDeriv_continuous s)
    (N/margin) (Real.sqrt p.matchedDelta*(1+2/margin)*N) (by positivity) (by positivity)
    (fun t ht => (p.comparisonForcing_bounds s hb0 hb1 hw0 hw1 hs hu0 hp margin hm hu t ht.1).1)
    (fun t ht => (p.comparisonForcing_bounds s hb0 hb1 hw0 hw1 hs hu0 hp margin hm hu t ht.1).2)
  apply H.trans
  have H1 := mul_le_mul_of_nonneg_right hnorm (show 0 ≤ N/margin by positivity)
  have H2 := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hD)
    (show 0 ≤ (1+2/margin)*N by positivity)
  have H3 : ‖lambda‖*(N/margin)+Real.sqrt p.matchedDelta*(1+2/margin)*N ≤
      Real.sqrt D0*(1+4/margin)*N := by
    have heq : Real.sqrt D0*(1+4/margin)*N =
      (2*Real.sqrt D0)*(N/margin)+Real.sqrt D0*((1+2/margin)*N) := by ring
    rw [heq]
    nlinarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left H3 hh.le

end
end SparseSGD
