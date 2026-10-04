import SparseSGD.Continuum.Eigenfunctionals

namespace SparseSGD
noncomputable section

def oscillatoryRoot (omega : ℝ) : ℂ := -1 + 2 * Complex.I * omega

def riskSlowCoefficient (delta omega : ℝ) : ℝ := delta / (2 * omega ^ 2)

def riskOscillatoryCoefficient (omega : ℝ) : ℂ :=
  -(1 + 2 * Complex.I * (omega : ℂ)) ^ 2 / (16 * (omega : ℂ) ^ 2)

theorem oscillatoryRoot_quadratic (delta omega : ℝ)
    (h : omega ^ 2 = delta - 1 / 4) :
    oscillatoryRoot omega ^ 2 + 2 * oscillatoryRoot omega + 4 * (delta : ℂ) = 0 := by
  apply Complex.ext <;> simp [oscillatoryRoot, Complex.mul_re, Complex.mul_im, pow_two] <;>
    nlinarith

theorem oscillatoryRoot_add_two_ne_zero (omega : ℝ) :
    oscillatoryRoot omega + 2 ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num [oscillatoryRoot] at hr

theorem oscillatoryEnergy_polynomial (delta : ℝ) (lambda : ℂ) (s : Moments)
    (hl : lambda + 2 ≠ 0)
    (hq : lambda ^ 2 + 2 * lambda + 4 * (delta : ℂ) = 0) :
    oscillatoryEnergy delta lambda s = s.R + lambda ^ 2 / 4 * s.V + lambda * s.C := by
  unfold oscillatoryEnergy
  field_simp
  linear_combination -(s.V : ℂ) * lambda * hq

theorem oscillatoryEnergy_re (delta omega : ℝ) (s : Moments)
    (h : omega ^ 2 = delta - 1 / 4) :
    (oscillatoryEnergy delta (oscillatoryRoot omega) s).re =
      s.R + (1 / 4 - omega ^ 2) * s.V - s.C := by
  rw [oscillatoryEnergy_polynomial delta _ s (oscillatoryRoot_add_two_ne_zero omega)
    (oscillatoryRoot_quadratic delta omega h)]
  simp [oscillatoryRoot, pow_two, Complex.mul_re, Complex.mul_im, Complex.div_re]
  ring

theorem oscillatoryEnergy_im (delta omega : ℝ) (s : Moments)
    (h : omega ^ 2 = delta - 1 / 4) :
    (oscillatoryEnergy delta (oscillatoryRoot omega) s).im =
      omega * (2 * s.C - s.V) := by
  rw [oscillatoryEnergy_polynomial delta _ s (oscillatoryRoot_add_two_ne_zero omega)
    (oscillatoryRoot_quadratic delta omega h)]
  simp [oscillatoryRoot, pow_two, Complex.mul_re, Complex.mul_im, Complex.div_im]
  ring

/-- Exact reconstruction of risk from the slow and oscillatory eigenfunctionals. -/
theorem risk_modal_inversion (delta omega : ℝ) (s : Moments) (ho : omega ≠ 0)
    (h : omega ^ 2 = delta - 1 / 4) :
    s.R = riskSlowCoefficient delta omega * slowEnergy delta s +
      2 * (riskOscillatoryCoefficient omega *
        oscillatoryEnergy delta (oscillatoryRoot omega) s).re := by
  rw [Complex.mul_re, oscillatoryEnergy_re delta omega s h,
    oscillatoryEnergy_im delta omega s h]
  simp [riskOscillatoryCoefficient, riskSlowCoefficient, slowEnergy,
    Complex.div_re, Complex.div_im, Complex.normSq_apply, pow_two]
  field_simp
  have hd : delta = omega ^ 2 + 1 / 4 := by linarith
  rw [hd]
  ring

end
end SparseSGD
