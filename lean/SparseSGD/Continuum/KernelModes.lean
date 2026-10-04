import SparseSGD.Continuum.LargeDeltaModes
import SparseSGD.Continuum.OscillatorFormula
import SparseSGD.Comparison.ModalQuadrature

namespace SparseSGD
noncomputable section

def freeModeRates (omega : ℝ) : Fin 3 → ℂ :=
  ![-1,oscillatoryRoot omega,star (oscillatoryRoot omega)]

def kernelModeCoefficients (delta omega : ℝ) : Fin 3 → ℂ :=
  ![((delta/omega^2 : ℝ) : ℂ),((-delta/(2*omega^2) : ℝ) : ℂ),
    ((-delta/(2*omega^2) : ℝ) : ℂ)]

theorem freeModeRates_real (omega : ℝ) (i : Fin 3) :
    (freeModeRates omega i).re = -1 := by
  fin_cases i <;> simp [freeModeRates,oscillatoryRoot]

theorem freeModeRates_imag_bound (omega : ℝ) (ho : 0 ≤ omega) (i : Fin 3) :
    |(freeModeRates omega i).im| ≤ 2*omega := by
  fin_cases i <;> simp [freeModeRates,oscillatoryRoot,abs_of_nonneg ho] <;> positivity

/-- The actual renewal kernel has exactly three free exponential modes. -/
theorem continuumRenewalKernel_eq_modes (delta omega t : ℝ) (ho : omega ≠ 0)
    (hosq : omega^2 = delta-1/4) (ht : 0 ≤ t) :
    (continuumRenewalKernel delta t : ℂ) =
      exponentialModeSum (freeModeRates omega) (kernelModeCoefficients delta omega) t := by
  have hk : continuumRenewalKernel delta t =
      2/delta*(Real.exp (-t/2)*(-delta*(Real.sin (t*omega)/omega)))^2 := by
    unfold continuumRenewalKernel continuumImpulseResponse
    rw [continuumMeanFlow_oscillatory delta omega t ho hosq ht]
    simp [oscillatorFormula]
  rw [hk]
  have hdelta : delta ≠ 0 := by
    nlinarith [sq_nonneg omega]
  have hE : Real.exp (-t/2)^2 = Real.exp (-t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  apply Complex.ext
  · simp only [Complex.ofReal_re,Complex.ofReal_im]
    simp [exponentialModeSum,freeModeRates,kernelModeCoefficients,Fin.sum_univ_succ,
      oscillatoryRoot,Complex.exp_re,Complex.mul_re,Complex.mul_im,
      ← Complex.ofReal_div,← Complex.ofReal_pow,← Complex.ofReal_mul,← Complex.ofReal_neg]
    rw [mul_pow,hE]
    simp only [div_pow,mul_pow,neg_sq]
    have hc : Real.cos (2*omega*t) = Real.cos (2*(t*omega)) := by congr 1; ring
    rw [hc,Real.cos_two_mul]
    field_simp [ho,hdelta]
    nlinarith [Real.sin_sq_add_cos_sq (t*omega)]
  · simp only [Complex.ofReal_re,Complex.ofReal_im]
    simp [exponentialModeSum,freeModeRates,kernelModeCoefficients,Fin.sum_univ_succ,
      oscillatoryRoot,Complex.exp_im,Complex.mul_re,Complex.mul_im,
      ← Complex.ofReal_div,← Complex.ofReal_pow,← Complex.ofReal_mul,← Complex.ofReal_neg]

/-- The total absolute kernel coefficient mass is uniformly bounded. -/
theorem kernelModeCoefficients_mass_le (delta omega : ℝ) (hd : 4 ≤ delta)
    (ho : 0 < omega) (hosq : omega^2 = delta-1/4) :
    (∑ i : Fin 3, ‖kernelModeCoefficients delta omega i‖) ≤ 3 := by
  have hdp : 0 < delta := by linarith
  simp [kernelModeCoefficients,Fin.sum_univ_succ,abs_div,
    abs_of_pos hdp,abs_of_nonneg (sq_nonneg omega)]
  have heq : delta/omega^2+(delta/(2*omega^2)+delta/(2*omega^2)) = 2*delta/omega^2 := by ring
  rw [heq]
  apply (div_le_iff₀ (sq_pos_of_pos ho)).2
  nlinarith

end
end SparseSGD
