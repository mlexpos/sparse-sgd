import SparseSGD.Scaling.WindowEstimates
import SparseSGD.Scaling.WindowInitialBounds

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

def windowWeights (delta omega : ℝ) : Fin 2 → (Fin 3 → ℂ) :=
  ![windowSlowWeights delta,windowOscWeights delta (oscillatoryRoot omega)]
def windowCleanRates (u omega : ℝ) : Fin 2 → ℂ :=
  ![((u-1 : ℝ) : ℂ),windowOscillatoryRate u omega]

theorem windowWeights_functional (delta omega : ℝ) (s : Moments) (i : Fin 2) :
    windowLinearFunctional (windowWeights delta omega i) s = energyFunctional delta omega i s := by
  fin_cases i
  · exact windowLinearFunctional_slow delta s
  · exact windowLinearFunctional_osc delta (oscillatoryRoot omega) s

theorem window_initial_centered_bound (delta u phi omega : ℝ)
    (hd : 4 ≤ delta) (hu : u < 1) (hp : 0 ≤ phi) (ho : 0 < omega)
    (hosq : omega^2 = delta-1/4) (s : Moments) (hs : s.psd) (i : Fin 2) :
    ‖energyFunctional delta omega i s-energyFunctional delta omega i (windowEquilibrium delta u phi)‖ ≤
      2*windowSize delta u phi s := by
  have hL : 0 ≤ phi/(1-u) := by positivity
  have ho1 : 1 ≤ omega := by nlinarith
  fin_cases i
  · change ‖(slowEnergy delta s : ℂ)-(slowEnergy delta (windowEquilibrium delta u phi) : ℂ)‖ ≤ _
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,windowEquilibrium_slow _ _ _ (by linarith)]
    have H := (abs_sub (slowEnergy delta s) (2*phi/(1-u))).trans
      (add_le_add (window_initial_slow_bound delta (by linarith) s hs) le_rfl)
    rw [show 2*phi/(1-u) = 2*(phi/(1-u)) by ring,
      abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL)] at H
    simpa only [windowSize,mul_add,show 2*phi/(1-u) = 2*(phi/(1-u)) by ring] using H
  · change ‖oscillatoryEnergy delta (oscillatoryRoot omega) s-
      oscillatoryEnergy delta (oscillatoryRoot omega) (windowEquilibrium delta u phi)‖ ≤ _
    have H := (norm_sub_le _ _).trans (add_le_add
      (window_initial_osc_bound delta omega (by linarith) hosq s hs)
      (windowEquilibrium_osc_bound delta u phi omega (by linarith) hu hp ho))
    apply H.trans
    have hdiv : (phi/(1-u))/omega ≤ phi/(1-u) := (div_le_self hL ho1)
    dsimp only [windowSize]
    linarith

theorem window_clean_exponential_bound (delta u a omega margin t : ℝ)
    (hd : 4 ≤ delta) (hm : 0 < margin) (hu0 : 0 ≤ u) (hu : u ≤ 1-margin)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ha : a^3+(4*delta-1)*a-4*delta*u = 0)
    (ho : 0 < omega) (hosq : omega^2 = delta-1/4) (hlarge : 1 ≤ 2*margin*delta)
    (ht : 0 ≤ t) (i : Fin 2) :
    ‖Complex.exp (largeModeRates delta a i.castSucc*(t : ℂ))-
      Complex.exp (windowCleanRates u omega i*(t : ℂ))‖ ≤ 2/(margin*omega) := by
  have hms : margin ≤ 1 := by linarith
  fin_cases i
  · change ‖Complex.exp (((a-1 : ℝ) : ℂ)*(t : ℂ))-
      Complex.exp (((u-1 : ℝ) : ℂ)*(t : ℂ))‖ ≤ _
    have hshift := largeMode_parameter_shift delta u a (by linarith) ha0 ha1 ha
    have how : omega ≤ delta := by nlinarith
    have herr : ‖((a-1 : ℝ) : ℂ)-((u-1 : ℝ) : ℂ)‖ ≤ 1/omega := by
      rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        show a-1-(u-1) = a-u by ring,abs_of_nonneg hshift.1]
      exact hshift.2.trans (div_le_div_of_nonneg_left (by norm_num) ho (by linarith))
    have hdecay : (((a-1 : ℝ) : ℂ)).re ≤ -(margin/2) := by
      simp only [Complex.ofReal_re]
      have H := largeMode_parameter_margin delta u a margin (by linarith) hm hu ha0 ha1 ha hlarge
      linarith
    have hreference : (((u-1 : ℝ) : ℂ)).re ≤ -(margin/2) := by simp only [Complex.ofReal_re]; linarith
    have H := damped_exponential_difference ((a-1 : ℝ) : ℂ) ((u-1 : ℝ) : ℂ) (margin/2)
      (by positivity) hdecay hreference t ht
    exact H.trans (by
      calc
        _ ≤ (1/omega)/(margin/2) := div_le_div_of_nonneg_right herr (by positivity)
        _ = _ := by ring)
  · change ‖Complex.exp (largeModeRootPlus delta a*(t : ℂ))-
      Complex.exp (windowOscillatoryRate u omega*(t : ℂ))‖ ≤ _
    have herr := largeMode_oscillatory_rate_error delta u a omega hd ha0 ha1 ha ho hosq
    have H := damped_exponential_difference (largeModeRootPlus delta a) (windowOscillatoryRate u omega)
      1 (by norm_num) (by simp [largeModeRootPlus]; linarith)
      (by simp [windowOscillatoryRate]; linarith) t ht
    have H' : ‖Complex.exp (largeModeRootPlus delta a*(t : ℂ))-
        Complex.exp (windowOscillatoryRate u omega*(t : ℂ))‖ ≤ 1/omega := by simpa using H.trans (by simpa using herr)
    exact H'.trans (by
      apply (le_div_iff₀ (by positivity : 0 < margin*omega)).2
      have he : (1/omega)*(margin*omega) = margin := by field_simp
      rw [he]
      linarith)

/-- Uniform continuum window estimate, derived from the actual three-mode
solution, for either centered eigenfunctional. -/
theorem continuum_window_centered_bound (delta u phi omega margin : ℝ) (s : Moments)
    (hd : 4 ≤ delta) (hm : 0 < margin) (hu0 : 0 ≤ u) (hu : u ≤ 1-margin)
    (hp : 0 ≤ phi) (hs : s.psd) (ho : 0 < omega) (hosq : omega^2 = delta-1/4)
    (hlarge : 1 ≤ 2*margin*delta) (t : ℝ) (ht : 0 ≤ t) (i : Fin 2) :
    ‖energyFunctional delta omega i (continuumFlow delta u phi s t)-
      (energyFunctional delta omega i (windowEquilibrium delta u phi)+
        (energyFunctional delta omega i s-energyFunctional delta omega i (windowEquilibrium delta u phi))*
          Complex.exp (windowCleanRates u omega i*(t : ℂ)))‖ ≤
      (44+4/margin)*windowSize delta u phi s/omega := by
  have hu1 : u < 1 := by linarith
  obtain ⟨a,ha0,ha1,ha⟩ := exists_largeMode_parameter delta u (by linarith) hu0 hu1
  let coeff := largeModeCoefficients delta u phi a s
  let factors := fun j => windowModeFactor (windowWeights delta omega i) delta (largeModeRates delta a j)
  have hB : ∑ j, ‖coeff j‖ ≤ 22*windowSize delta u phi s :=
    continuumFlow_largeMode_sum_coefficients_bound delta u phi a s hd hu1 hp ha0 ha1.le hs
  have hf : ∀ j, j ≠ i.castSucc → ‖factors j‖ ≤ 1/omega := by
    fin_cases i
    · exact windowSlowFactor_fast_bound delta u a omega (by linarith) hu0 hu1.le ha0 ha1.le ha ho hosq
    · exact windowOscFactor_wrong_bound delta u a omega (by linarith) hu0 hu1.le ha ho hosq
  have hflow := continuumFlow_window_functional delta u phi a s (by linarith) hu1.ne ha t ht
    (windowWeights delta omega i)
  simp only [windowWeights_functional] at hflow
  have hinit := continuumFlow_window_functional delta u phi a s (by linarith) hu1.ne ha 0 (by norm_num)
    (windowWeights delta omega i)
  simp only [windowWeights_functional,continuumFlow_initial,Complex.ofReal_zero,mul_zero,
    Complex.exp_zero,mul_one] at hinit
  have hsum : (∑ j, coeff j*factors j) = energyFunctional delta omega i s-
      energyFunctional delta omega i (windowEquilibrium delta u phi) := by
    dsimp only [coeff,factors]
    dsimp only [windowEquilibrium]
    linear_combination -hinit
  have hI : ‖∑ j, coeff j*factors j‖ ≤ 2*windowSize delta u phi s := by
    rw [hsum]
    exact window_initial_centered_bound delta u phi omega hd hu1 hp ho hosq s hs i
  have H := modal_dominant_approximation (largeModeRates delta a) coeff factors i.castSucc
    (windowCleanRates u omega i) (1/omega) (22*windowSize delta u phi s)
    (2*windowSize delta u phi s) (2/(margin*omega)) t (by positivity) hB hI
    (fun j => (largeModeRates_real_parts delta a ha0 ha1 j).2.le) ht hf
    (window_clean_exponential_bound delta u a omega margin t hd hm hu0 hu ha0 ha1.le ha ho hosq hlarge ht i)
  have H' : ‖(∑ j, coeff j*factors j*Complex.exp (largeModeRates delta a j*(t : ℂ)))-
      (energyFunctional delta omega i s-energyFunctional delta omega i (windowEquilibrium delta u phi))*
        Complex.exp (windowCleanRates u omega i*(t : ℂ))‖ ≤ (44+4/margin)*windowSize delta u phi s/omega := by
    rw [hsum] at H
    convert H using 1 <;> ring
  rw [hflow]
  convert H' using 1
  congr 1
  dsimp only [windowEquilibrium,coeff,factors]
  ring

end
end SparseSGD
