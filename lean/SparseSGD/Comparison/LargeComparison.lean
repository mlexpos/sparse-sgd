import SparseSGD.Comparison.ForcingModes
import SparseSGD.Comparison.BoundedComparison

open MeasureTheory Set Filter Topology

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

/-- Actual continuum forcing quadrature, uniformly in large delta. The phase
conditions are stated in physical frequency and step size. -/
theorem large_continuum_convolution_quadrature_bound (margin : ℝ) (hm : 0 < margin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (delta u phi omega h : ℝ) (s : Moments),
      4 ≤ delta → 0 ≤ u → u < 1 → 0 ≤ phi → s.psd →
      0 < omega → omega^2 = delta-1/4 → 0 < h → h ≤ 1 →
      omega*h ≤ Real.pi/2-margin → 22*h ≤ margin*omega → ∀ k : ℕ,
      |(∫ x in (0 : ℝ)..(k : ℝ)*h, continuumRenewalKernel delta x*
          (u*(continuumFlow delta u phi s ((k : ℝ)*h-x)).R+phi))-
        rightEndpointSum (fun x => continuumRenewalKernel delta x*
          (u*(continuumFlow delta u phi s ((k : ℝ)*h-x)).R+phi)) h k| ≤
        138*C*h*(s.R+delta*s.V+phi/(1-u)) := by
  obtain ⟨C,hC0,hC⟩ := modal_convolution_quadrature_bound (ι := Fin 3) (κ := Fin 4)
    (3*margin) (by positivity)
  refine ⟨C,hC0,?_⟩
  intro delta u phi omega h s hd hu0 hu1 hp hs ho hosq hh0 hh1 hnyq hlarge k
  obtain ⟨a,ha0,ha1,ha⟩ := exists_largeMode_parameter delta u (by linarith) hu0 hu1
  have hmu : ∀ i, (freeModeRates omega i).re ≤ 0 := by
    intro i
    rw [freeModeRates_real]
    norm_num
  have hlam : ∀ j, (forcingModeRates delta a j).re ≤ 0 :=
    fun j => (forcingModeRates_real_parts delta a ha0 ha1 j).2
  have hstrip := forcing_kernel_relative_phase_bound delta a omega h margin hd ha0 ha1 ho hosq
    hh0 hh1 hnyq hlarge
  have H := hC (freeModeRates omega) (kernelModeCoefficients delta omega)
    (forcingModeRates delta a) (forcingModeCoefficients delta u phi a s) h k hh0 hmu hlam
    (fun i j => (hstrip i j).1) (fun i j => (hstrip i j).2)
  rw [← real_modal_convolution_error_eq (continuumRenewalKernel delta)
    (fun t => u*(continuumFlow delta u phi s t).R+phi)
    (freeModeRates omega) (kernelModeCoefficients delta omega)
    (forcingModeRates delta a) (forcingModeCoefficients delta u phi a s)
    (fun t ht => continuumRenewalKernel_eq_modes delta omega t ho.ne' hosq ht)
    (fun t ht => continuum_forcing_eq_modes delta u phi a s (by linarith) hu1.ne ha t ht) h hh0 k,
    abs_sub_comm] at H
  apply H.trans
  have hb := kernelModeCoefficients_mass_le delta omega hd ho hosq
  have hc := forcingModeCoefficients_mass_le delta u phi a s hd hu0 hu1 hp ha0 ha1.le hs
  have hN : 0 ≤ s.R+delta*s.V+phi/(1-u) := by
    have := Moments.psd_R_nonneg hs
    have := Moments.psd_V_nonneg hs
    positivity
  calc
    _ ≤ 2*C*h*3*(23*(s.R+delta*s.V+phi/(1-u))) := by
      gcongr
    _ = _ := by ring

/-- Kernel normalization has the same uniform modal quadrature constant. -/
theorem large_kernel_quadrature_bound (margin : ℝ) (hm : 0 < margin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (delta omega h : ℝ),
      4 ≤ delta → 0 < omega → omega^2 = delta-1/4 → 0 < h → h ≤ 1 →
      2*omega*h ≤ 2*Real.pi-margin → ∀ k : ℕ,
      |(∫ x in (0 : ℝ)..(k : ℝ)*h, continuumRenewalKernel delta x)-
        rightEndpointSum (continuumRenewalKernel delta) h k| ≤ 6*C*h := by
  obtain ⟨C,hC0,hC⟩ := modal_convolution_quadrature_bound (ι := Fin 3) (κ := Fin 1) margin hm
  refine ⟨C,hC0,?_⟩
  intro delta omega h hd ho hosq hh0 hh1 hphase k
  let zeroRate : Fin 1 → ℂ := fun _ => 0
  let oneCoeff : Fin 1 → ℂ := fun _ => 1
  have hz (t : ℝ) : exponentialModeSum zeroRate oneCoeff t = 1 := by
    simp [exponentialModeSum,zeroRate,oneCoeff]
  have hstripre (i : Fin 3) (j : Fin 1) :
      |((zeroRate j-freeModeRates omega i)*(h : ℂ)).re| ≤ 3 := by
    simp [zeroRate,Complex.mul_re,freeModeRates_real,abs_of_pos hh0]
    linarith
  have hstripim (i : Fin 3) (j : Fin 1) :
      |((zeroRate j-freeModeRates omega i)*(h : ℂ)).im| ≤ 2*Real.pi-margin := by
    simp only [zeroRate,zero_sub,Complex.neg_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,zero_add,abs_mul,abs_neg,abs_of_pos hh0]
    exact (mul_le_mul_of_nonneg_right (freeModeRates_imag_bound omega ho.le i) hh0.le).trans hphase
  have H := hC (freeModeRates omega) (kernelModeCoefficients delta omega) zeroRate oneCoeff h k
    hh0 (fun i => by rw [freeModeRates_real]; norm_num) (fun _ => by simp [zeroRate]) hstripre hstripim
  rw [← real_modal_convolution_error_eq (continuumRenewalKernel delta) (fun _ => 1)
    (freeModeRates omega) (kernelModeCoefficients delta omega) zeroRate oneCoeff
    (fun t ht => continuumRenewalKernel_eq_modes delta omega t ho.ne' hosq ht)
    (fun t _ => by simp [hz]) h hh0 k] at H
  simp only [mul_one,abs_sub_comm] at H
  have hb := kernelModeCoefficients_mass_le delta omega hd ho hosq
  have hresult := H.trans
    (show 2*C*h*(∑ i, ‖kernelModeCoefficients delta omega i‖)*(∑ j, ‖oneCoeff j‖) ≤
      6*C*h by simp [oneCoeff]; nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*C*h by positivity)])
  rw [abs_sub_comm] at hresult
  exact hresult


/-- Passing the actual finite quadrature estimate to the normalization mass. -/
theorem Params.sampledKernelMass_error_of_partial_bound (p : Params)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) (jury : External.JuryStability)
    (E : ℝ) (hq : ∀ k : ℕ,
      |(∫ x in (0 : ℝ)..(k : ℝ)*p.matchedStep, continuumRenewalKernel p.matchedDelta x)-
        rightEndpointSum (continuumRenewalKernel p.matchedDelta) p.matchedStep k| ≤ E) :
    |p.sampledKernelMass-1| ≤ E := by
  have hd := p.matchedDelta_pos (by linarith) hb1 hw0 hw1
  have hh := p.matchedStep_pos (by linarith) hb1
  have hgrid : Tendsto (fun n : ℕ => (n : ℝ)*p.matchedStep) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hh
  have hi := intervalIntegral_tendsto_integral_Ioi 0 (continuumRenewalKernel_integrableOn hd) hgrid
  rw [continuumRenewalKernel_mass hd] at hi
  have hs := (p.sampledKernelMass_hasSum hb0 hb1 hw0 hw1 jury).tendsto_sum_nat
  have hs' : Tendsto (rightEndpointSum (continuumRenewalKernel p.matchedDelta) p.matchedStep)
      atTop (nhds p.sampledKernelMass) := by
    change Tendsto (fun k => rightEndpointSum (continuumRenewalKernel p.matchedDelta) p.matchedStep k)
      atTop (nhds p.sampledKernelMass)
    simpa only [rightEndpointSum,smul_eq_mul] using hs
  have H := le_of_tendsto_of_tendsto' (hi.sub hs').abs tendsto_const_nhds hq
  rwa [abs_sub_comm] at H

/-- Large-parameter comparison for the actual chain and its actual matched flow.
Only the explicit physical Nyquist and frequency-separation conditions occur. -/
theorem risk_comparison_large (margin : ℝ) (hm : 0 < margin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Params) (s : Moments) (omega : ℝ),
      1/2 ≤ p.beta → p.beta < 1 → 0 < p.w → p.w < 2*(1+p.beta) →
      External.JuryStability → s.psd → 0 ≤ p.renormNoise → p.renormNoise < 1 →
      0 ≤ p.renormAdditive → 4 ≤ p.matchedDelta → 0 < omega →
      omega^2 = p.matchedDelta-1/4 → p.matchedStep ≤ 1 →
      omega*p.matchedStep ≤ Real.pi/2-margin → 22*p.matchedStep ≤ margin*omega →
      ∀ k : ℕ,
      |(p.trajectory s k).R-(p.comparisonFlow s ((k : ℝ)*p.matchedStep)).R| ≤
        C*p.matchedStep*((p.matchedMoments s).R+p.matchedDelta*(p.matchedMoments s).V+
          p.renormAdditive)/(1-p.renormNoise)^2 := by
  obtain ⟨C1,hC10,hC1⟩ := large_continuum_convolution_quadrature_bound margin hm
  obtain ⟨C2,hC20,hC2⟩ := large_kernel_quadrature_bound margin hm
  refine ⟨144*(C1+C2),by positivity,?_⟩
  intro p s omega hb0 hb1 hw0 hw1 jury hs hu0 hu1 hp hd ho hosq hh1 hnyq hlarge
  have hh := p.matchedStep_pos (by linarith) hb1
  have hdp := p.matchedDelta_pos (by linarith) hb1 hw0 hw1
  have hs' := p.matchedMoments_psd s hs
  let E0 := (p.matchedMoments s).R+p.matchedDelta*(p.matchedMoments s).V
  let B := (E0+p.renormAdditive)/(1-p.renormNoise)
  have hE0 : 0 ≤ E0 := add_nonneg (Moments.psd_R_nonneg hs')
    (mul_nonneg hdp.le (Moments.psd_V_nonneg hs'))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hB_eq : (1-p.renormNoise)*B = E0+p.renormAdditive := by
    dsimp only [B]
    field_simp [show 1-p.renormNoise ≠ 0 by linarith]
  have hN_le : E0+p.renormAdditive/(1-p.renormNoise) ≤ B := by
    apply (le_div_iff₀ (by linarith : 0 < 1-p.renormNoise)).2
    change _ ≤ E0+p.renormAdditive
    have heq : (p.renormAdditive/(1-p.renormNoise))*(1-p.renormNoise) = p.renormAdditive :=
      div_mul_cancel₀ _ (by linarith)
    nlinarith [mul_nonneg hu0 hE0]
  let f := fun t => p.renormNoise*(p.comparisonFlow s t).R+p.renormAdditive
  have hF (t : ℝ) (ht : 0 ≤ t) : |f t| ≤ B := by
    have hR0 := continuumFlow_R_nonneg hdp hu0 hp (p.matchedMoments s) hs' ht
    have hR1 := continuumFlow_risk_uniform_bound hdp hu0 hu1 hp (p.matchedMoments s) hs' ht
    change _ ≤ B at hR1
    have hf0 : 0 ≤ f t := by dsimp only [f,Params.comparisonFlow]; positivity
    rw [abs_of_nonneg hf0]
    dsimp only [f,Params.comparisonFlow]
    nlinarith [mul_le_mul_of_nonneg_left hR1 hu0]
  have hphase : 2*omega*p.matchedStep ≤ 2*Real.pi-margin := by
    nlinarith [Real.pi_pos]
  have hmerror := p.sampledKernelMass_error_of_partial_bound hb0 hb1 hw0 hw1 jury (6*C2*p.matchedStep)
    (hC2 p.matchedDelta omega p.matchedStep hd ho hosq hh hh1 hphase)
  have hq (k : ℕ) :
      |(∫ x in (0 : ℝ)..(k : ℝ)*p.matchedStep, continuumRenewalKernel p.matchedDelta x*
        f ((k : ℝ)*p.matchedStep-x))-p.sampledConvolution f k| ≤
        144*(C1+C2)*p.matchedStep*B := by
    have hraw := hC1 p.matchedDelta p.renormNoise p.renormAdditive omega p.matchedStep
      (p.matchedMoments s) hd hu0 hu1 hp hs' ho hosq hh hh1 hnyq hlarge k
    change |(∫ x in (0 : ℝ)..(k : ℝ)*p.matchedStep, continuumRenewalKernel p.matchedDelta x*
        f ((k : ℝ)*p.matchedStep-x))-
      rightEndpointSum (fun x => continuumRenewalKernel p.matchedDelta x*
        f ((k : ℝ)*p.matchedStep-x)) p.matchedStep k| ≤ _ at hraw
    rw [p.raw_sampledConvolution hb0 hb1 hw0 hw1 jury] at hraw
    have hb := p.sampledConvolution_abs_le hb0 hb1 hw0 hw1 jury f B hB k
      (fun t ht => hF t ht.1)
    have hnorm : |p.sampledKernelMass*p.sampledConvolution f k-p.sampledConvolution f k| ≤
        6*C2*p.matchedStep*B := by
      rw [← sub_one_mul,abs_mul]
      exact mul_le_mul hmerror hb (abs_nonneg _) (by positivity)
    have hraw' : |(∫ x in (0 : ℝ)..(k : ℝ)*p.matchedStep, continuumRenewalKernel p.matchedDelta x*
        f ((k : ℝ)*p.matchedStep-x))-p.sampledKernelMass*p.sampledConvolution f k| ≤
        138*C1*p.matchedStep*B := hraw.trans (mul_le_mul_of_nonneg_left hN_le (by positivity))
    have htri := abs_sub_le
      (∫ x in (0 : ℝ)..(k : ℝ)*p.matchedStep, continuumRenewalKernel p.matchedDelta x*
        f ((k : ℝ)*p.matchedStep-x))
      (p.sampledKernelMass*p.sampledConvolution f k) (p.sampledConvolution f k)
    nlinarith [mul_nonneg hC10 (mul_nonneg hh.le hB),mul_nonneg hC20 (mul_nonneg hh.le hB)]
  have H := p.risk_comparison_of_quadrature_bound hb0 hb1 hw0 hw1 jury s hu0 hu1
    (144*(C1+C2)*p.matchedStep*B) (by positivity) hq
  intro k
  apply (H k).trans
  dsimp only [B,E0]
  apply le_of_eq
  field_simp

end
end SparseSGD
