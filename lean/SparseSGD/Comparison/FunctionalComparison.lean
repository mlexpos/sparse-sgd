import SparseSGD.Comparison.FunctionalModes
import SparseSGD.Comparison.FunctionalQuadrature

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

/-- Reduction from actual risk and forcing quadrature to either actual energy. -/
theorem Params.energy_comparison_of_forcing_quadrature_bound (p : Params)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) (jury : External.JuryStability)
    (s : Moments) (omega : ℝ) (hosq : omega^2 = p.matchedDelta-1/4)
    (hd1 : 1 ≤ p.matchedDelta) (hu0 : 0 ≤ p.renormNoise) (hu1 : p.renormNoise ≤ 1)
    (D E L F : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (hrisk : ∀ j, |(p.trajectory s j).R-(p.comparisonFlow s ((j : ℝ)*p.matchedStep)).R| ≤ D)
    (hforce : ∀ t, 0 ≤ t → |p.renormNoise*(p.comparisonFlow s t).R+p.renormAdditive| ≤ F)
    (hmass : |p.sampledKernelMass-1| ≤ L)
    (k : ℕ) (i : Fin 2)
    (hquad : ‖(∫ x in (0 : ℝ)..(k : ℝ)*p.matchedStep,
        Complex.exp (energyModeRates omega i*(x : ℂ))*
          ((p.renormNoise*(p.comparisonFlow s ((k : ℝ)*p.matchedStep-x)).R+p.renormAdditive : ℝ) : ℂ))-
      rightEndpointSum (fun x => Complex.exp (energyModeRates omega i*(x : ℂ))*
        ((p.renormNoise*(p.comparisonFlow s ((k : ℝ)*p.matchedStep-x)).R+p.renormAdditive : ℝ) : ℂ))
        p.matchedStep k‖ ≤ E) :
    ‖energyFunctional p.matchedDelta omega i (p.matchedMoments (p.trajectory s k))-
      energyFunctional p.matchedDelta omega i (p.comparisonFlow s ((k : ℝ)*p.matchedStep))‖ ≤
      10*(D+E+L*F) := by
  let lambda := energyModeRates omega i
  let f : ℝ → ℂ := fun t => ((p.renormNoise*(p.comparisonFlow s t).R+p.renormAdditive : ℝ) : ℂ)
  let fgrid : ℕ → ℂ := fun j => ((p.renormNoise*(p.trajectory s j).R+p.renormAdditive : ℝ) : ℂ)
  let A := sampledFunctionalConvolution lambda p.matchedStep fgrid k
  let B := sampledFunctionalConvolution lambda p.matchedStep (fun j => f ((j : ℝ)*p.matchedStep)) k
  let I := ∫ x in (0 : ℝ)..(k : ℝ)*p.matchedStep, Complex.exp (lambda*(x : ℂ))*f ((k : ℝ)*p.matchedStep-x)
  have hh := p.matchedStep_pos (by linarith) hb1
  have hl : lambda.re = -1 := energyModeRates_real omega i
  have hAB : ‖A-B‖ ≤ D := by
    dsimp only [A,B]
    rw [sampledFunctionalConvolution_sub]
    apply sampledFunctionalConvolution_norm_le lambda hl p.matchedStep hh _ D hD
    intro j
    simp only [fgrid,f,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    have heq : p.renormNoise*(p.trajectory s j).R+p.renormAdditive-
        (p.renormNoise*(p.comparisonFlow s ((j : ℝ)*p.matchedStep)).R+p.renormAdditive) =
        p.renormNoise*((p.trajectory s j).R-(p.comparisonFlow s ((j : ℝ)*p.matchedStep)).R) := by ring
    rw [heq,abs_mul,abs_of_nonneg hu0]
    exact (mul_le_mul_of_nonneg_left (hrisk j) hu0).trans (by nlinarith)
  have hBI : ‖B-I‖ ≤ E := by
    dsimp only [B]
    rw [sampledFunctionalConvolution_eq_rightEndpoint,norm_sub_rev]
    exact hquad
  have hIF : ‖I‖ ≤ F := single_mode_convolution_norm_le lambda hl f F _ hF
    (by positivity) (fun t ht => by simpa only [f,Complex.norm_real,Real.norm_eq_abs] using hforce t ht)
  have H := normalized_functional_error (energyModeGain omega i) A B I p.sampledKernelMass D E F
    (p.sampledKernelMass_ge_one_fifth hb0 hb1 hw0 hw1 jury hd1)
    (energyModeGain_norm omega i).le hAB hBI hIF
  have hflow := continuumFlow_energyFunctional_duhamel p.matchedDelta p.renormNoise p.renormAdditive omega
    (p.matchedDelta_pos (by linarith) hb1 hw0 hw1).ne' hosq (p.matchedMoments s)
    ((k : ℝ)*p.matchedStep) (by positivity) i
  rw [p.matched_energyFunctional_grid hb0 hb1 hw0 hw1 jury omega hosq s k i]
  change ‖_ - energyFunctional _ _ _ (continuumFlow _ _ _ _ _)‖ ≤ _
  rw [hflow]
  convert H.trans (show 10*(D+E+|p.sampledKernelMass-1| * F) ≤ 10*(D+E+L*F) by gcongr) using 1
  congr 1
  dsimp only [lambda,A,I,f,fgrid,Params.comparisonFlow]
  ring

/-- Uniform comparison for both actual energy functionals, with constants
depending only on the stability and Nyquist margin. -/
theorem moment_comparison_energyFunctional (margin : ℝ) (hm : 0 < margin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Params) (s : Moments) (omega : ℝ),
      1/2 ≤ p.beta → p.beta < 1 → 0 < p.w → p.w < 2*(1+p.beta) →
      External.JuryStability → s.psd → 0 ≤ p.renormNoise →
      p.renormNoise ≤ 1-margin → 0 ≤ p.renormAdditive → 1 ≤ p.matchedDelta →
      0 < omega → omega^2 = p.matchedDelta-1/4 →
      (comparisonDeltaThreshold margin ≤ p.matchedDelta → p.foldedAngle ≤ Real.pi/2-margin) →
      ∀ (k : ℕ) (i : Fin 2),
      ‖energyFunctional p.matchedDelta omega i (p.matchedMoments (p.trajectory s k))-
        energyFunctional p.matchedDelta omega i (p.comparisonFlow s ((k : ℝ)*p.matchedStep))‖ ≤
        C*p.matchedStep*(p.comparisonInitialSize s+p.renormAdditive) := by
  obtain ⟨CR,hCR0,hCR⟩ := moment_comparison_risk margin hm
  obtain ⟨CE,hCE0,hCE⟩ := large_energy_convolution_quadrature_bound margin hm
  obtain ⟨CK,hCK0,hCK⟩ := large_kernel_quadrature_bound margin hm
  let CB := Real.sqrt (comparisonDeltaThreshold margin)*(1+6/margin)
  let CL := (46*CE+6*CK)/margin
  let C := 10*(CR+max CB CL)
  have hCB : 0 ≤ CB := by dsimp only [CB]; positivity
  have hCL : 0 ≤ CL := by dsimp only [CL]; positivity
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro p s omega hb0 hb1 hw0 hw1 jury hs hu0 hu hp hd1 ho hosq hnyq k i
  have hh := p.matchedStep_pos (by linarith) hb1
  have hd := p.matchedDelta_pos (by linarith) hb1 hw0 hw1
  have hu1 : p.renormNoise < 1 := by linarith
  have hs' := p.matchedMoments_psd s hs
  let N := p.comparisonInitialSize s+p.renormAdditive
  have hN : 0 ≤ N := by
    have hr := Moments.psd_R_nonneg hs'
    have hv := Moments.psd_V_nonneg hs'
    dsimp only [N,Params.comparisonInitialSize]
    positivity
  have hforce : ∀ t, 0 ≤ t → |p.renormNoise*(p.comparisonFlow s t).R+p.renormAdditive| ≤ N/margin := by
    intro t ht
    exact (p.comparisonForcing_bounds s hb0 hb1 hw0 hw1 hs hu0 hp margin hm hu t ht).1
  have hrisk := hCR p s hb0 hb1 hw0 hw1 jury hs hu0 hu hp hnyq
  by_cases hD : comparisonDeltaThreshold margin ≤ p.matchedDelta
  · obtain ⟨omega',ho',hosq',hangle,hfreq⟩ := p.large_matched_frequency margin hm hb0 hb1 hD
    have he : omega' = omega := by nlinarith
    subst omega'
    have hd4 : 4 ≤ p.matchedDelta := (le_max_left _ _).trans hD
    have hphase : omega*p.matchedStep ≤ Real.pi/2-margin := by rw [hangle]; exact hnyq hD
    have hquad := hCE p.matchedDelta p.renormNoise p.renormAdditive omega p.matchedStep
      (p.matchedMoments s) hd4 hu0 hu1 hp hs' ho hosq hh (p.matchedStep_le_one hb0) hphase hfreq k i
    let E0 := (p.matchedMoments s).R+p.matchedDelta*(p.matchedMoments s).V
    have hE0 : 0 ≤ E0 := add_nonneg (Moments.psd_R_nonneg hs')
      (mul_nonneg hd.le (Moments.psd_V_nonneg hs'))
    have hEN : E0+p.renormAdditive/(1-p.renormNoise) ≤ N/margin := by
      calc
        _ ≤ (E0+p.renormAdditive)/(1-p.renormNoise) := by
          apply (le_div_iff₀ (by linarith : 0 < 1-p.renormNoise)).2
          have hc := div_mul_cancel₀ p.renormAdditive (show 1-p.renormNoise ≠ 0 by linarith)
          nlinarith [mul_nonneg hu0 hE0]
        _ ≤ (E0+p.renormAdditive)/margin := div_le_div_of_nonneg_left (by positivity) hm (by linarith)
        _ ≤ N/margin := div_le_div_of_nonneg_right (by
          dsimp only [E0,N,Params.comparisonInitialSize]
          linarith [abs_nonneg (p.matchedMoments s).C]) hm.le
    have hquad' : ‖(∫ x in (0 : ℝ)..(k : ℝ)*p.matchedStep,
        Complex.exp (energyModeRates omega i*(x : ℂ))*
          ((p.renormNoise*(p.comparisonFlow s ((k : ℝ)*p.matchedStep-x)).R+p.renormAdditive : ℝ) : ℂ))-
      rightEndpointSum (fun x => Complex.exp (energyModeRates omega i*(x : ℂ))*
        ((p.renormNoise*(p.comparisonFlow s ((k : ℝ)*p.matchedStep-x)).R+p.renormAdditive : ℝ) : ℂ))
        p.matchedStep k‖ ≤ 46*CE*p.matchedStep*(N/margin) :=
      hquad.trans (mul_le_mul_of_nonneg_left hEN (by positivity))
    have hmass := p.sampledKernelMass_error_of_partial_bound hb0 hb1 hw0 hw1 jury (6*CK*p.matchedStep)
      (hCK p.matchedDelta omega p.matchedStep hd4 ho hosq hh (p.matchedStep_le_one hb0)
        (by linarith [Real.pi_pos]))
    have H := p.energy_comparison_of_forcing_quadrature_bound hb0 hb1 hw0 hw1 jury s omega hosq hd1
      hu0 hu1.le (CR*p.matchedStep*N) (46*CE*p.matchedStep*(N/margin)) (6*CK*p.matchedStep)
      (N/margin) (by positivity) (by positivity) hrisk hforce hmass k i hquad'
    apply H.trans
    calc
      _ = 10*(CR+CL)*p.matchedStep*N := by dsimp only [CL]; ring
      _ ≤ C*p.matchedStep*N := by
        dsimp only [C]
        gcongr
        exact le_max_right _ _
  · have hD' : p.matchedDelta ≤ comparisonDeltaThreshold margin := le_of_not_ge hD
    have hn := (energyModeRates_norm_le p.matchedDelta omega hd1 hosq i).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hD') (by norm_num : (0 : ℝ) ≤ 2))
    have hquad := p.single_mode_comparison_quadrature_bounded s hb0 hb1 hw0 hw1 hs hu0 hp
      (comparisonDeltaThreshold margin) margin hm hu hD' (energyModeRates omega i)
      (energyModeRates_real omega i) hn k
    have hmass := (p.sampledKernelMass_error hb0 hb1 hw0 hw1 jury).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hD') (by norm_num : (0 : ℝ) ≤ 2)) hh.le)
    have H := p.energy_comparison_of_forcing_quadrature_bound hb0 hb1 hw0 hw1 jury s omega hosq hd1
      hu0 hu1.le (CR*p.matchedStep*N)
      (p.matchedStep*Real.sqrt (comparisonDeltaThreshold margin)*(1+4/margin)*N)
      (p.matchedStep*(2*Real.sqrt (comparisonDeltaThreshold margin))) (N/margin)
      (by positivity) (by positivity) hrisk hforce hmass k i hquad
    apply H.trans
    calc
      _ = 10*(CR+CB)*p.matchedStep*N := by dsimp only [CB]; ring
      _ ≤ C*p.matchedStep*N := by
        dsimp only [C]
        gcongr
        exact le_max_left _ _

/-- The complete moment comparison theorem for the actual chain and actual
matched continuum flow: risk everywhere, and both energies when delta ≥ 1. -/
theorem moment_comparison (margin : ℝ) (hm : 0 < margin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Params) (s : Moments),
      1/2 ≤ p.beta → p.beta < 1 → 0 < p.w → p.w < 2*(1+p.beta) →
      External.JuryStability → s.psd → 0 ≤ p.renormNoise →
      p.renormNoise ≤ 1-margin → 0 ≤ p.renormAdditive →
      (comparisonDeltaThreshold margin ≤ p.matchedDelta → p.foldedAngle ≤ Real.pi/2-margin) →
      ∀ k : ℕ,
      |(p.trajectory s k).R-(p.comparisonFlow s ((k : ℝ)*p.matchedStep)).R| ≤
        C*p.matchedStep*(p.comparisonInitialSize s+p.renormAdditive) ∧
      (1 ≤ p.matchedDelta →
        |slowEnergy p.matchedDelta (p.matchedMoments (p.trajectory s k))-
          slowEnergy p.matchedDelta (p.comparisonFlow s ((k : ℝ)*p.matchedStep))| ≤
            C*p.matchedStep*(p.comparisonInitialSize s+p.renormAdditive) ∧
        ‖oscillatoryEnergy p.matchedDelta (oscillatoryRoot (Real.sqrt (p.matchedDelta-1/4)))
            (p.matchedMoments (p.trajectory s k))-
          oscillatoryEnergy p.matchedDelta (oscillatoryRoot (Real.sqrt (p.matchedDelta-1/4)))
            (p.comparisonFlow s ((k : ℝ)*p.matchedStep))‖ ≤
            C*p.matchedStep*(p.comparisonInitialSize s+p.renormAdditive)) := by
  obtain ⟨CR,hCR0,hCR⟩ := moment_comparison_risk margin hm
  obtain ⟨CE,hCE0,hCE⟩ := moment_comparison_energyFunctional margin hm
  refine ⟨max CR CE,le_trans hCR0 (le_max_left _ _),?_⟩
  intro p s hb0 hb1 hw0 hw1 jury hs hu0 hu hp hnyq k
  have hh := p.matchedStep_pos (by linarith) hb1
  have hd := p.matchedDelta_pos (by linarith) hb1 hw0 hw1
  have hs' := p.matchedMoments_psd s hs
  have hN : 0 ≤ p.comparisonInitialSize s+p.renormAdditive := by
    have hr := Moments.psd_R_nonneg hs'
    have hv := Moments.psd_V_nonneg hs'
    unfold Params.comparisonInitialSize
    positivity
  constructor
  · exact (hCR p s hb0 hb1 hw0 hw1 jury hs hu0 hu hp hnyq k).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hh.le) hN)
  · intro hd1
    have ho : 0 < Real.sqrt (p.matchedDelta-1/4) := Real.sqrt_pos.mpr (by linarith)
    have hosq : (Real.sqrt (p.matchedDelta-1/4))^2 = p.matchedDelta-1/4 :=
      Real.sq_sqrt (by linarith)
    have H := hCE p s (Real.sqrt (p.matchedDelta-1/4)) hb0 hb1 hw0 hw1 jury hs hu0 hu hp hd1
      ho hosq hnyq k
    have hconstant : CE*p.matchedStep*(p.comparisonInitialSize s+p.renormAdditive) ≤
        max CR CE*p.matchedStep*(p.comparisonInitialSize s+p.renormAdditive) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hh.le) hN
    constructor
    · have H0 := (H 0).trans hconstant
      simpa only [energyFunctional,Matrix.cons_val_zero,← Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs] using H0
    · exact (H 1).trans hconstant

end
end SparseSGD
