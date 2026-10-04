import SparseSGD.Comparison.MatchingScalars

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1000000

/-- A scalar complex-exponential Taylor remainder with a generous constant. -/
theorem complex_exp_cubic_remainder (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z-(1+z+z^2/2+z^3/6)‖ ≤ ‖z‖^4 := by
  have H := Complex.exp_bound hz (by norm_num : 0 < (4 : ℕ))
  norm_num [Finset.sum_range_succ] at H
  exact H.trans (by nlinarith [sq_nonneg (‖z‖^2)])

theorem cos_quadratic_remainder (x : ℝ) (hx : |x| ≤ 1) :
    |Real.cos x-(1-x^2/2)| ≤ x^4 := by
  have hz : ‖(x : ℂ)*Complex.I‖ ≤ 1 := by simpa using hx
  have H := complex_exp_cubic_remainder ((x : ℂ)*Complex.I) hz
  have Hr := (Complex.abs_re_le_norm (Complex.exp ((x : ℂ)*Complex.I)-
    (1+(x : ℂ)*Complex.I+((x : ℂ)*Complex.I)^2/2+((x : ℂ)*Complex.I)^3/6))).trans H
  have hpoly : (1+(x : ℂ)*Complex.I+((x : ℂ)*Complex.I)^2/2+((x : ℂ)*Complex.I)^3/6).re=1-x^2/2 := by
    simp [Complex.mul_re,Complex.mul_im,pow_succ]
    <;> ring
  rw [Complex.sub_re,Complex.exp_ofReal_mul_I_re,hpoly] at Hr
  have hn : ‖(x : ℂ)*Complex.I‖^4=x^4 := by
    simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,←abs_pow]
    exact abs_of_nonneg (by positivity)
  simpa only [hn] using Hr

theorem real_exp_cubic_remainder (x : ℝ) (hx : |x| ≤ 1) :
    |Real.exp x-(1+x+x^2/2+x^3/6)| ≤ x^4 := by
  have H := complex_exp_cubic_remainder (x : ℂ) (by simpa using hx)
  have Hr := (Complex.abs_re_le_norm (Complex.exp (x : ℂ)-
    (1+(x : ℂ)+(x : ℂ)^2/2+(x : ℂ)^3/6))).trans H
  have Hp : (1+(x : ℂ)+(x : ℂ)^2/2+(x : ℂ)^3/6).re=1+x+x^2/2+x^3/6 := by simp only [←Complex.ofReal_pow,Complex.add_re,Complex.one_re,Complex.ofReal_re,Complex.div_ofNat_re]
  rw [Complex.sub_re,Complex.exp_ofReal_re,Hp] at Hr
  have hn : ‖(x : ℂ)‖^4=x^4 := by
    simp only [Complex.norm_real,Real.norm_eq_abs,←abs_pow]
    exact abs_of_nonneg (by positivity)
  simpa only [hn] using Hr

theorem cosh_quadratic_remainder (x : ℝ) (hx : |x| ≤ 1) :
    |Real.cosh x-(1+x^2/2)| ≤ x^4 := by
  have H1 := abs_le.mp (real_exp_cubic_remainder x hx)
  have H2 := abs_le.mp (real_exp_cubic_remainder (-x) (by simpa using hx))
  rw [Real.cosh_eq,abs_le]
  constructor <;> nlinarith [H1.1,H1.2,H2.1,H2.2]


end
end SparseSGD
