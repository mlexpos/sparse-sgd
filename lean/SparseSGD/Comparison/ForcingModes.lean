import SparseSGD.Continuum.KernelModes

namespace SparseSGD
noncomputable section

def forcingModeRates (delta a : ℝ) : Fin 4 → ℂ :=
  Matrix.vecCons 0 (largeModeRates delta a)

def forcingModeCoefficients (delta u phi a : ℝ) (s : Moments) : Fin 4 → ℂ :=
  Matrix.vecCons ((phi/(1-u) : ℝ) : ℂ) (fun i => (u : ℂ)*largeModeCoefficients delta u phi a s i)

theorem continuum_forcing_eq_modes (delta u phi a : ℝ) (s : Moments)
    (hd : 1 ≤ delta) (hu : u ≠ 1) (ha : a^3+(4*delta-1)*a-4*delta*u = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    ((u*(continuumFlow delta u phi s t).R+phi : ℝ) : ℂ) =
      exponentialModeSum (forcingModeRates delta a) (forcingModeCoefficients delta u phi a s) t := by
  have hune : (1-(u : ℂ)) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr (Ne.symm hu))
  push_cast
  rw [continuumFlow_largeMode_sum delta u phi a s hd hu ha t ht]
  have hconstant : (u : ℂ)*(phi/(1-u) : ℝ)+phi = (phi/(1-u) : ℝ) := by
    push_cast
    field_simp
    ring
  simp only [exponentialModeSum,forcingModeRates,forcingModeCoefficients,Fin.sum_univ_succ,
    Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,zero_mul,Complex.exp_zero,mul_one,add_zero]
  push_cast at hconstant ⊢
  linear_combination hconstant

theorem forcingModeCoefficients_mass_le (delta u phi a : ℝ) (s : Moments)
    (hd : 4 ≤ delta) (hu0 : 0 ≤ u) (hu1 : u < 1) (hp : 0 ≤ phi)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hs : s.psd) :
    (∑ i : Fin 4, ‖forcingModeCoefficients delta u phi a s i‖) ≤
      23*(s.R+delta*s.V+phi/(1-u)) := by
  have H := continuumFlow_largeMode_sum_coefficients_bound delta u phi a s hd hu1 hp ha0 ha1 hs
  have hR := Moments.psd_R_nonneg hs
  have hV := Moments.psd_V_nonneg hs
  have hL : 0 ≤ phi/(1-u) := by positivity
  have hE : 0 ≤ s.R+delta*s.V+phi/(1-u) := by positivity
  simp only [forcingModeCoefficients,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu0,abs_of_nonneg hL]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at H
  simp only [Fin.sum_univ_zero,add_zero]
  have H' := mul_le_mul_of_nonneg_left H hu0
  nlinarith [mul_nonneg (show 0 ≤ 1-u by linarith) hE]

theorem forcingModeRates_real_parts (delta a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ∀ i : Fin 4, -3/2 ≤ (forcingModeRates delta a i).re ∧ (forcingModeRates delta a i).re ≤ 0 := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · norm_num [forcingModeRates]
  · simpa [forcingModeRates] using
      ⟨(largeModeRates_real_parts delta a ha0 ha1 j).1,
        (largeModeRates_real_parts delta a ha0 ha1 j).2.le⟩

theorem forcingModeRates_imag_bound (delta a omega : ℝ)
    (hd : 4 ≤ delta) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ho : 0 < omega) (hosq : omega^2 = delta-1/4) (i : Fin 4) :
    |(forcingModeRates delta a i).im| ≤ 2*omega+22/omega := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [forcingModeRates]
    positivity
  · simpa [forcingModeRates] using largeModeRates_imag_bound delta a omega hd ha0 ha1 ho hosq j

/-- The Nyquist condition and the explicit frequency perturbation imply the
actual modal strip needed by exponential-pair quadrature. -/
theorem forcing_kernel_relative_phase_bound (delta a omega h margin : ℝ)
    (hd : 4 ≤ delta) (ha0 : 0 ≤ a) (ha1 : a < 1) (ho : 0 < omega)
    (hosq : omega^2 = delta-1/4) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hmargin : omega*h ≤ Real.pi/2-margin) (hlarge : 22*h ≤ margin*omega)
    (i : Fin 3) (j : Fin 4) :
    |((forcingModeRates delta a j-freeModeRates omega i)*(h : ℂ)).re| ≤ 3 ∧
    |((forcingModeRates delta a j-freeModeRates omega i)*(h : ℂ)).im| ≤ 2*Real.pi-3*margin := by
  have hreal := forcingModeRates_real_parts delta a ha0 ha1 j
  have hmu := freeModeRates_real omega i
  have himu := freeModeRates_imag_bound omega ho.le i
  have hilam := forcingModeRates_imag_bound delta a omega hd ha0 ha1.le ho hosq j
  have hf : 22/omega*h ≤ margin := by
    have H : 22/omega*h = (22*h)/omega := by ring
    rw [H]
    exact (div_le_iff₀ ho).2 hlarge
  constructor
  · simp only [Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,hmu]
    rw [abs_mul,abs_of_pos hh0]
    have hr : |(forcingModeRates delta a j).re-(-1)| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
    nlinarith [mul_le_mul_of_nonneg_right hr hh0.le]
  · simp only [Complex.mul_im,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add]
    rw [abs_mul,abs_of_pos hh0]
    have hs : |(forcingModeRates delta a j).im-(freeModeRates omega i).im| ≤
        4*omega+22/omega := (abs_sub _ _).trans (by linarith)
    have H := mul_le_mul_of_nonneg_right hs hh0.le
    nlinarith

end
end SparseSGD
