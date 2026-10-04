import SparseSGD.Comparison.FunctionalBounds

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

def energyModeRates (omega : ℝ) : Fin 2 → ℂ := ![-1,oscillatoryRoot omega]
def energyModeGain (omega : ℝ) : Fin 2 → ℂ :=
  ![2,-(2*oscillatoryRoot omega/(oscillatoryRoot omega+2))]
def energyFunctional (delta omega : ℝ) (i : Fin 2) (s : Moments) : ℂ :=
  ![(slowEnergy delta s : ℂ),oscillatoryEnergy delta (oscillatoryRoot omega) s] i

theorem energyModeRates_real (omega : ℝ) (i : Fin 2) :
    (energyModeRates omega i).re = -1 := by
  fin_cases i <;> simp [energyModeRates,oscillatoryRoot]

theorem energyModeRates_free (omega : ℝ) (i : Fin 2) :
    energyModeRates omega i = freeModeRates omega ⟨i.val,by omega⟩ := by
  fin_cases i <;> rfl

theorem energyModeGain_norm (omega : ℝ) (i : Fin 2) :
    ‖energyModeGain omega i‖ = 2 := by
  fin_cases i
  · norm_num [energyModeGain]
  · have hstar : oscillatoryRoot omega+2 = -star (oscillatoryRoot omega) := by
      apply Complex.ext <;> simp [oscillatoryRoot] <;> ring
    have hn : ‖oscillatoryRoot omega‖ ≠ 0 := norm_ne_zero_iff.mpr (by
      intro H
      have := congrArg Complex.re H
      norm_num [oscillatoryRoot] at this)
    change ‖-(2*oscillatoryRoot omega/(oscillatoryRoot omega+2))‖ = 2
    simp only [norm_neg,norm_div,norm_mul]
    rw [hstar,norm_neg,norm_star]
    norm_num
    field_simp

theorem energyModeRates_norm_le (delta omega : ℝ) (hd : 1 ≤ delta)
    (hosq : omega^2 = delta-1/4) (i : Fin 2) :
    ‖energyModeRates omega i‖ ≤ 2*Real.sqrt delta := by
  have hdp : 0 ≤ delta := by linarith
  have hs := Real.sq_sqrt hdp
  fin_cases i
  · norm_num [energyModeRates]
    nlinarith [Real.sqrt_nonneg delta]
  · have hn : ‖oscillatoryRoot omega‖^2 = 4*delta := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply,oscillatoryRoot]
      nlinarith
    change ‖oscillatoryRoot omega‖ ≤ _
    nlinarith [norm_nonneg (oscillatoryRoot omega),Real.sqrt_nonneg delta]

theorem continuumFlow_energyFunctional_duhamel (delta u phi omega : ℝ) (hd : delta ≠ 0)
    (hosq : omega^2 = delta-1/4) (s : Moments) (T : ℝ) (hT : 0 ≤ T) (i : Fin 2) :
    energyFunctional delta omega i (continuumFlow delta u phi s T) =
      Complex.exp (energyModeRates omega i*(T : ℂ))*energyFunctional delta omega i s+
        energyModeGain omega i*(∫ x in (0 : ℝ)..T, Complex.exp (energyModeRates omega i*(x : ℂ))*
          ((u*(continuumFlow delta u phi s (T-x)).R+phi : ℝ) : ℂ)) := by
  fin_cases i
  · simpa [energyFunctional,energyModeRates,energyModeGain] using
      continuumFlow_slowEnergy_duhamel delta u phi hd s T hT
  · simpa [energyFunctional,energyModeRates,energyModeGain,sub_eq_add_neg,neg_mul] using
      continuumFlow_oscillatoryEnergy_duhamel delta u phi hd (oscillatoryRoot omega)
        (oscillatoryRoot_add_two_ne_zero omega) (oscillatoryRoot_quadratic delta omega hosq) s T hT

theorem Params.matched_energyFunctional_grid (p : Params)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) (jury : External.JuryStability)
    (omega : ℝ) (hosq : omega^2 = p.matchedDelta-1/4) (s : Moments) (k : ℕ) (i : Fin 2) :
    energyFunctional p.matchedDelta omega i (p.matchedMoments (p.trajectory s k)) =
      Complex.exp (energyModeRates omega i*((k : ℝ)*p.matchedStep : ℝ))*
        energyFunctional p.matchedDelta omega i (p.matchedMoments s)+
      (energyModeGain omega i/(p.sampledKernelMass : ℂ))*
        sampledFunctionalConvolution (energyModeRates omega i) p.matchedStep
          (fun j => ((p.renormNoise*(p.trajectory s j).R+p.renormAdditive : ℝ) : ℂ)) k := by
  fin_cases i
  · simpa [energyFunctional,energyModeRates,energyModeGain] using
      p.matched_slowEnergy_grid hb0 hb1 hw0 hw1 jury s k
  · simpa [energyFunctional,energyModeRates,energyModeGain,sub_eq_add_neg,neg_mul,neg_div] using
      p.matched_oscillatoryEnergy_grid hb0 hb1 hw0 hw1 jury (oscillatoryRoot omega)
        (oscillatoryRoot_add_two_ne_zero omega) (oscillatoryRoot_quadratic _ _ hosq) s k

/-- Actual forcing quadrature for either energy mode in the large regime. -/
theorem large_energy_convolution_quadrature_bound (margin : ℝ) (hm : 0 < margin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (delta u phi omega h : ℝ) (s : Moments),
      4 ≤ delta → 0 ≤ u → u < 1 → 0 ≤ phi → s.psd →
      0 < omega → omega^2 = delta-1/4 → 0 < h → h ≤ 1 →
      omega*h ≤ Real.pi/2-margin → 22*h ≤ margin*omega → ∀ (k : ℕ) (i : Fin 2),
      ‖(∫ x in (0 : ℝ)..(k : ℝ)*h, Complex.exp (energyModeRates omega i*(x : ℂ))*
          ((u*(continuumFlow delta u phi s ((k : ℝ)*h-x)).R+phi : ℝ) : ℂ))-
        rightEndpointSum (fun x => Complex.exp (energyModeRates omega i*(x : ℂ))*
          ((u*(continuumFlow delta u phi s ((k : ℝ)*h-x)).R+phi : ℝ) : ℂ)) h k‖ ≤
        46*C*h*(s.R+delta*s.V+phi/(1-u)) := by
  obtain ⟨C,hC0,hC⟩ := modal_convolution_quadrature_bound (ι := Fin 1) (κ := Fin 4)
    (3*margin) (by positivity)
  refine ⟨C,hC0,?_⟩
  intro delta u phi omega h s hd hu0 hu1 hp hs ho hosq hh0 hh1 hnyq hlarge k i
  obtain ⟨a,ha0,ha1,ha⟩ := exists_largeMode_parameter delta u (by linarith) hu0 hu1
  let mu : Fin 1 → ℂ := fun _ => energyModeRates omega i
  let b : Fin 1 → ℂ := fun _ => 1
  have hq (t : ℝ) : Complex.exp (energyModeRates omega i*(t : ℂ)) = exponentialModeSum mu b t := by
    simp [exponentialModeSum,mu,b]
  have hstrip := forcing_kernel_relative_phase_bound delta a omega h margin hd ha0 ha1 ho hosq
    hh0 hh1 hnyq hlarge ⟨i.val,by omega⟩
  have H := hC mu b (forcingModeRates delta a) (forcingModeCoefficients delta u phi a s) h k hh0
    (fun _ => by dsimp only [mu]; rw [energyModeRates_real]; norm_num)
    (fun j => (forcingModeRates_real_parts delta a ha0 ha1 j).2)
    (fun _ j => by dsimp only [mu]; rw [energyModeRates_free]; exact (hstrip j).1)
    (fun _ j => by dsimp only [mu]; rw [energyModeRates_free]; exact (hstrip j).2)
  rw [← complex_modal_convolution_error_eq
    (fun t => Complex.exp (energyModeRates omega i*(t : ℂ)))
    (fun t => ((u*(continuumFlow delta u phi s t).R+phi : ℝ) : ℂ))
    mu b (forcingModeRates delta a) (forcingModeCoefficients delta u phi a s)
    (fun t _ => hq t) (fun t ht => continuum_forcing_eq_modes delta u phi a s
      (by linarith) hu1.ne ha t ht) h hh0 k,norm_sub_rev] at H
  have hc := forcingModeCoefficients_mass_le delta u phi a s hd hu0 hu1 hp ha0 ha1.le hs
  simp only [b,Fin.sum_univ_one,norm_one,mul_one] at H
  exact H.trans (by nlinarith [mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*C*h by positivity)])

end
end SparseSGD
