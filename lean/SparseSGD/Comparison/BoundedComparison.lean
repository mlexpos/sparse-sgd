import SparseSGD.Comparison.MatchedFlow

open MeasureTheory Set

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1200000

def Params.sampledConvolution (p : Params) (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, normalizedKernelLag p (k-j)*f ((j : ℝ)*p.matchedStep)

variable (p : Params) (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
  (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) (jury : External.JuryStability)

include hb0 hb1 hw0 hw1 jury

theorem Params.sampledKernelMass_pos : 0 < p.sampledKernelMass := by
  have hs := p.sampledKernelMass_hasSum hb0 hb1 hw0 hw1 jury
  have hh := p.matchedStep_pos (by linarith) hb1
  have hd := p.matchedDelta_pos (by linarith) hb1 hw0 hw1
  rw [← hs.tsum_eq]
  apply hs.summable.tsum_pos (fun n => mul_nonneg hh.le (continuumRenewalKernel_nonneg hd _)) 0
  simp only [zero_add, Nat.cast_one, one_mul, continuumRenewalKernel,continuumImpulseResponse]
  exact mul_pos hh (mul_pos (by positivity)
    (sq_pos_of_ne_zero (p.matchedMeanFlow_impulse_ne_zero hb0 hb1 hw0 hw1)))

theorem Params.sampledConvolution_abs_le (f : ℝ → ℝ) (F : ℝ) (hF : 0 ≤ F) (k : ℕ)
    (hf : ∀ t ∈ Icc 0 ((k : ℝ)*p.matchedStep), |f t| ≤ F) :
    |p.sampledConvolution f k| ≤ F := by
  have hh := p.matchedStep_pos (by linarith) hb1
  calc
    _ ≤ ∑ j ∈ Finset.range k, |normalizedKernelLag p (k-j)*f ((j : ℝ)*p.matchedStep)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range k, normalizedKernelLag p (k-j)*F := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : (j : ℝ) ≤ k := by exact_mod_cast (Finset.mem_range.mp hj).le
      have hnn := normalized_kernel_lag_nonneg jury p hb0 hb1 hw0 hw1 (k-j)
      rw [abs_mul,abs_of_nonneg hnn]
      apply mul_le_mul_of_nonneg_left (hf _ ⟨by positivity,mul_le_mul_of_nonneg_right hjk hh.le⟩) hnn
    _ = (∑ j ∈ Finset.range k, normalizedKernelLag p (k-j))*F := (Finset.sum_mul _ _ _).symm
    _ ≤ F := by
      simpa using mul_le_mul_of_nonneg_right
        (normalized_kernel_partial_mass_le_one jury p hb0 hb1 hw0 hw1 k) hF

theorem Params.raw_sampledConvolution (f : ℝ → ℝ) (k : ℕ) :
    rightEndpointSum (fun x => continuumRenewalKernel p.matchedDelta x *
      f ((k : ℝ)*p.matchedStep-x)) p.matchedStep k =
      p.sampledKernelMass*p.sampledConvolution f k := by
  have hden : (∑' m : ℕ, continuumRenewalKernel p.matchedDelta
      (((m+1 : ℕ) : ℝ)*p.matchedStep)) ≠ 0 := by
    intro hz
    have hm := p.sampledKernelMass_pos hb0 hb1 hw0 hw1 jury
    simp only [Params.sampledKernelMass,tsum_mul_left,hz,mul_zero] at hm
    exact (lt_irrefl 0 hm)
  rw [rightEndpointSum,← Finset.sum_range_reflect]
  unfold Params.sampledConvolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk := Finset.mem_range.mp hj
  have hage : k-1-j+1 = k-j := by omega
  have ht : (k : ℝ)*p.matchedStep-((k-j : ℕ) : ℝ)*p.matchedStep = (j : ℝ)*p.matchedStep := by
    rw [Nat.cast_sub hjk.le]; ring
  rw [hage,ht,p.normalizedKernelLag_eq_continuum_sampling hb0 hb1 hw0 hw1 jury]
  simp only [smul_eq_mul,Params.sampledKernelMass,tsum_mul_left]
  field_simp [hden]
  have hden' : (∑' x : ℕ, continuumRenewalKernel p.matchedDelta
      (p.matchedStep * ((x+1 : ℕ) : ℝ))) ≠ 0 := by simpa only [mul_comm] using hden
  rw [mul_div_cancel_right₀ _ hden']

theorem Params.normalized_convolution_quadrature_bound (f f' : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hfc : Continuous f')
    (F D : ℝ) (hF : 0 ≤ F) (hD : 0 ≤ D) (k : ℕ)
    (hbound : ∀ t ∈ Icc 0 ((k : ℝ)*p.matchedStep), |f t| ≤ F)
    (hderiv : ∀ t ∈ Icc 0 ((k : ℝ)*p.matchedStep), |f' t| ≤ D) :
    |(∫ x in (0 : ℝ)..(k : ℝ)*p.matchedStep,
      continuumRenewalKernel p.matchedDelta x*f ((k : ℝ)*p.matchedStep-x)) -
        p.sampledConvolution f k| ≤ p.matchedStep*(4*Real.sqrt p.matchedDelta*F+D) := by
  have hd := p.matchedDelta_pos (by linarith) hb1 hw0 hw1
  have hh := p.matchedStep_pos (by linarith) hb1
  have hquad := continuum_convolution_quadrature_bound hd hh k f f' hf hfc F D hF hD hbound hderiv
  rw [p.raw_sampledConvolution hb0 hb1 hw0 hw1 jury] at hquad
  have hmass := p.sampledKernelMass_error hb0 hb1 hw0 hw1 jury
  have hfbound := p.sampledConvolution_abs_le hb0 hb1 hw0 hw1 jury f F hF k hbound
  have hnorm : |p.sampledKernelMass*p.sampledConvolution f k-p.sampledConvolution f k| ≤
      p.matchedStep*(2*Real.sqrt p.matchedDelta)*F := by
    rw [← sub_one_mul,abs_mul]
    exact mul_le_mul hmass hfbound (abs_nonneg _) (by positivity)
  have htri := abs_sub_le
    (∫ x in (0 : ℝ)..(k : ℝ)*p.matchedStep,
      continuumRenewalKernel p.matchedDelta x*f ((k : ℝ)*p.matchedStep-x))
    (p.sampledKernelMass*p.sampledConvolution f k) (p.sampledConvolution f k)
  nlinarith

omit hb0 hb1 hw0 hw1 jury in
theorem Params.comparisonFlow_renewal_reversed (s : Moments) (T : ℝ) :
    (p.comparisonFlow s T).R = p.matchedFreeRisk s T +
      ∫ x in (0 : ℝ)..T, continuumRenewalKernel p.matchedDelta x *
        (p.renormNoise*(p.comparisonFlow s (T-x)).R+p.renormAdditive) := by
  have h := continuumFlow_renewal p.matchedDelta p.renormNoise p.renormAdditive
    (p.matchedMoments s) T
  rw [← p.matchedFreeRisk_eq_continuumFreeRisk] at h
  have hint := intervalIntegral.integral_comp_sub_left
    (fun x => continuumRenewalKernel p.matchedDelta (T-x)*
      (p.renormNoise*(p.comparisonFlow s x).R+p.renormAdditive))
    (a := (0 : ℝ)) (b := T) T
  simp only [sub_sub_cancel,sub_self,sub_zero] at hint
  exact h.trans (congrArg (fun z => p.matchedFreeRisk s T+z) hint.symm)

/-- The exact chain/flow comparison reduces to its actual quadrature defect. -/
theorem Params.risk_comparison_of_quadrature_bound (s : Moments)
    (hu0 : 0 ≤ p.renormNoise) (hu1 : p.renormNoise < 1)
    (E : ℝ) (hE : 0 ≤ E)
    (hq : ∀ k : ℕ,
      |(∫ x in (0 : ℝ)..(k : ℝ)*p.matchedStep, continuumRenewalKernel p.matchedDelta x *
        (p.renormNoise*(p.comparisonFlow s ((k : ℝ)*p.matchedStep-x)).R+p.renormAdditive)) -
        p.sampledConvolution (fun x => p.renormNoise*(p.comparisonFlow s x).R+p.renormAdditive) k| ≤ E) :
    ∀ k : ℕ, |(p.trajectory s k).R-(p.comparisonFlow s ((k : ℝ)*p.matchedStep)).R| ≤
      E/(1-p.renormNoise) := by
  let D := fun k : ℕ => (p.trajectory s k).R-(p.comparisonFlow s ((k : ℝ)*p.matchedStep)).R
  apply absolute_renewal_bound (normalizedKernelLag p) D p.renormNoise E
    (normalized_kernel_lag_nonneg jury p hb0 hb1 hw0 hw1)
    (normalized_kernel_partial_mass_le_one jury p hb0 hb1 hw0 hw1) hu0 hu1 hE
  intro k
  let Q := ∫ x in (0 : ℝ)..(k : ℝ)*p.matchedStep, continuumRenewalKernel p.matchedDelta x *
        (p.renormNoise*(p.comparisonFlow s ((k : ℝ)*p.matchedStep-x)).R+p.renormAdditive)
  let S := p.sampledConvolution
    (fun x => p.renormNoise*(p.comparisonFlow s x).R+p.renormAdditive) k
  have hd := normalized_trajectory_recurrence jury p s hb0 hb1 hw0 hw1 k
  rw [p.freeRisk_eq_matched_grid hb0 hb1 hw0 hw1] at hd
  have hc := p.comparisonFlow_renewal_reversed s ((k : ℝ)*p.matchedStep)
  have heq : D k = p.renormNoise*(∑ j ∈ Finset.range k, normalizedKernelLag p (k-j)*D j)-(Q-S) := by
    have hsum : p.renormNoise*(∑ j ∈ Finset.range k, normalizedKernelLag p (k-j)*D j)+S =
        ∑ j ∈ Finset.range k, normalizedKernelLag p (k-j)*
          (p.renormNoise*(p.trajectory s j).R+p.renormAdditive) := by
      dsimp [S,Params.sampledConvolution]
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [D]
      ring
    dsimp [D,Q] at *
    linarith
  rw [heq]
  have hab : |∑ j ∈ Finset.range k, normalizedKernelLag p (k-j)*D j| ≤
      ∑ j ∈ Finset.range k, normalizedKernelLag p (k-j)*|D j| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    rw [abs_mul,abs_of_nonneg (normalized_kernel_lag_nonneg jury p hb0 hb1 hw0 hw1 _)]
  have h := abs_sub (p.renormNoise*(∑ j ∈ Finset.range k, normalizedKernelLag p (k-j)*D j)) (Q-S)
  rw [abs_mul,abs_of_nonneg hu0] at h
  have hmul := mul_le_mul_of_nonneg_left hab hu0
  have he : |Q-S| ≤ E := hq k
  linarith

omit hb0 hb1 hw0 hw1 jury in
def Params.boundedComparisonError (s : Moments) : ℝ :=
  let d := p.matchedDelta
  let u := p.renormNoise
  let phi := p.renormAdditive
  let s0 := p.matchedMoments s
  p.matchedStep*(4*Real.sqrt d*(u*continuumRiskBound d u phi s0+phi)+
    u*Real.sqrt d*continuumEnergyBound d u phi s0)

theorem Params.comparison_quadrature_bound (s : Moments) (hs : s.psd)
    (hu0 : 0 ≤ p.renormNoise) (hu1 : p.renormNoise < 1) (hp : 0 ≤ p.renormAdditive)
    (k : ℕ) :
    |(∫ x in (0 : ℝ)..(k : ℝ)*p.matchedStep, continuumRenewalKernel p.matchedDelta x *
        (p.renormNoise*(p.comparisonFlow s ((k : ℝ)*p.matchedStep-x)).R+p.renormAdditive)) -
        p.sampledConvolution (fun x => p.renormNoise*(p.comparisonFlow s x).R+p.renormAdditive) k| ≤
      p.boundedComparisonError s := by
  have hd := p.matchedDelta_pos (by linarith) hb1 hw0 hw1
  have hs0 := p.matchedMoments_psd s hs
  let f := fun x => p.renormNoise*(p.comparisonFlow s x).R+p.renormAdditive
  let f' := fun x => p.renormNoise*
    (continuumField p.matchedDelta p.renormNoise p.renormAdditive (p.comparisonFlow s x)).R
  have hf (x : ℝ) : HasDerivAt f (f' x) x :=
    ((continuumFlow_hasDerivAt p.matchedDelta p.renormNoise p.renormAdditive
      (p.matchedMoments s) x).1.const_mul p.renormNoise).add_const p.renormAdditive
  have hC : Continuous (fun x => (p.comparisonFlow s x).C) :=
    continuous_iff_continuousAt.mpr fun x =>
      (continuumFlow_hasDerivAt p.matchedDelta p.renormNoise p.renormAdditive
        (p.matchedMoments s) x).2.2.continuousAt
  have hfc : Continuous f' := (hC.const_mul (-2*p.matchedDelta)).const_mul p.renormNoise
  have hE0 : 0 ≤ (p.matchedMoments s).R+p.matchedDelta*(p.matchedMoments s).V := by
    exact add_nonneg (Moments.psd_R_nonneg hs0) (mul_nonneg hd.le (Moments.psd_V_nonneg hs0))
  have hB : 0 ≤ continuumRiskBound p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s) := by
    exact div_nonneg (add_nonneg hE0 hp) (sub_nonneg.mpr hu1.le)
  have hE : 0 ≤ continuumEnergyBound p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s) := by
    exact add_nonneg (add_nonneg hE0 (mul_nonneg (by linarith) hB)) hp
  apply p.normalized_convolution_quadrature_bound hb0 hb1 hw0 hw1 jury f f' hf hfc
    (p.renormNoise*continuumRiskBound p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s)+p.renormAdditive)
    (p.renormNoise*Real.sqrt p.matchedDelta*
      continuumEnergyBound p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s))
    (by positivity) (by positivity) k
  · intro x hx
    have hR0 := continuumFlow_R_nonneg hd hu0 hp _ hs0 hx.1
    have hR := continuumFlow_risk_uniform_bound hd hu0 hu1 hp _ hs0 hx.1
    change 0 ≤ (p.comparisonFlow s x).R at hR0
    change (p.comparisonFlow s x).R ≤ continuumRiskBound _ _ _ _ at hR
    dsimp [f]
    rw [abs_of_nonneg (by positivity)]
    exact add_le_add (mul_le_mul_of_nonneg_left hR hu0) le_rfl
  · intro x hx
    have hdR := continuumFlow_risk_derivative_bound hd hu0 hu1 hp _ hs0 hx.1
    rw [((continuumFlow_hasDerivAt p.matchedDelta p.renormNoise p.renormAdditive
      (p.matchedMoments s) x).1).deriv] at hdR
    dsimp [f']
    rw [abs_mul,abs_of_nonneg hu0]
    simpa only [mul_assoc, Params.comparisonFlow] using mul_le_mul_of_nonneg_left hdR hu0

/-- Actual risk comparison for every delta, with the explicit sqrt(delta) loss
used on the bounded-parameter branch of the main comparison theorem. -/
theorem Params.risk_comparison_bounded (s : Moments) (hs : s.psd)
    (hu0 : 0 ≤ p.renormNoise) (hu1 : p.renormNoise < 1) (hp : 0 ≤ p.renormAdditive)
    (k : ℕ) :
    |(p.trajectory s k).R-(p.comparisonFlow s ((k : ℝ)*p.matchedStep)).R| ≤
      p.boundedComparisonError s/(1-p.renormNoise) := by
  apply p.risk_comparison_of_quadrature_bound hb0 hb1 hw0 hw1 jury s hu0 hu1
    (p.boundedComparisonError s)
  · have h := p.comparison_quadrature_bound hb0 hb1 hw0 hw1 jury s hs hu0 hu1 hp 0
    exact (abs_nonneg _).trans h
  · exact p.comparison_quadrature_bound hb0 hb1 hw0 hw1 jury s hs hu0 hu1 hp

/-- A constant uniform over every bounded delta interval and fixed load margin. -/
theorem Params.risk_comparison_bounded_margin (s : Moments) (hs : s.psd)
    (hu0 : 0 ≤ p.renormNoise) (hp : 0 ≤ p.renormAdditive)
    (D0 margin : ℝ) (hm : 0 < margin) (hu : p.renormNoise ≤ 1-margin)
    (hD : p.matchedDelta ≤ D0) (k : ℕ) :
    |(p.trajectory s k).R-(p.comparisonFlow s ((k : ℝ)*p.matchedStep)).R| ≤
      (Real.sqrt D0*(1+6/margin)/margin)*p.matchedStep*
        (p.comparisonInitialSize s+p.renormAdditive) := by
  have hd := p.matchedDelta_pos (by linarith) hb1 hw0 hw1
  have hh := p.matchedStep_pos (by linarith) hb1
  have hu1 : p.renormNoise < 1 := by linarith
  have hgap : 0 < 1-p.renormNoise := by linarith
  have hs0 := p.matchedMoments_psd s hs
  let e := (p.matchedMoments s).R+p.matchedDelta*(p.matchedMoments s).V
  let B := continuumRiskBound p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s)
  let N := p.comparisonInitialSize s+p.renormAdditive
  have he : 0 ≤ e := add_nonneg (Moments.psd_R_nonneg hs0)
    (mul_nonneg hd.le (Moments.psd_V_nonneg hs0))
  have hN : 0 ≤ N := by dsimp [N,Params.comparisonInitialSize]; linarith [abs_nonneg (p.matchedMoments s).C]
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
      e+p.renormAdditive+2*B := by
    nlinarith
  have hBN : B ≤ N/margin := by
    apply (le_div_iff₀ hm).2
    have hmargin : margin ≤ 1-p.renormNoise := by linarith
    have hmul := mul_le_mul_of_nonneg_right hmargin hB
    dsimp [N,Params.comparisonInitialSize]
    dsimp [e] at hBeq
    nlinarith [abs_nonneg (p.matchedMoments s).C]
  have heN : e+p.renormAdditive ≤ N := by
    dsimp [N,Params.comparisonInitialSize,e]
    linarith [abs_nonneg (p.matchedMoments s).C]
  have hbr : e+p.renormAdditive+6*B ≤ (1+6/margin)*N := by
    have hn := hBN
    have hfactor : (1+6/margin)*N = N+6*(N/margin) := by ring
    rw [hfactor]
    linarith
  have hsq : Real.sqrt p.matchedDelta ≤ Real.sqrt D0 := Real.sqrt_le_sqrt hD
  have herror : p.boundedComparisonError s ≤ p.matchedStep*Real.sqrt D0*((1+6/margin)*N) := by
    have h1 := mul_le_mul_of_nonneg_left hF (show 0 ≤ 4*Real.sqrt p.matchedDelta by positivity)
    have h2 := mul_le_mul_of_nonneg_left hE' (Real.sqrt_nonneg p.matchedDelta)
    have h3 := mul_le_mul_of_nonneg_left hbr (Real.sqrt_nonneg p.matchedDelta)
    have h4 := mul_le_mul_of_nonneg_right hsq (show 0 ≤ (1+6/margin)*N by positivity)
    dsimp only [Params.boundedComparisonError]
    rw [mul_assoc p.matchedStep (Real.sqrt D0)]
    apply mul_le_mul_of_nonneg_left _ hh.le
    change 4*Real.sqrt p.matchedDelta*(p.renormNoise*B+p.renormAdditive)+
      p.renormNoise*Real.sqrt p.matchedDelta*
        continuumEnergyBound p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s) ≤ _
    nlinarith
  have hdiv := div_le_div_of_nonneg_left
    (show 0 ≤ p.matchedStep*Real.sqrt D0*((1+6/margin)*N) by positivity)
    hm (show margin ≤ 1-p.renormNoise by linarith)
  have h := (p.risk_comparison_bounded hb0 hb1 hw0 hw1 jury s hs hu0 hu1 hp k).trans
    ((div_le_div_of_nonneg_right herror hgap.le).trans hdiv)
  convert h using 1 <;> dsimp [N] <;> ring


end
end SparseSGD
