import SparseSGD.Logistic.Coefficients

namespace SparseSGD.Logistic
noncomputable section

theorem sigma_le_exp (t : ℝ) : sigma t ≤ Real.exp t := by
  unfold sigma
  apply (div_le_iff₀ (by positivity : 0 < 1+Real.exp t)).mpr
  nlinarith [Real.exp_pos t]

theorem sigmaPrime_le_exp (t : ℝ) : sigmaPrime t ≤ Real.exp t := by
  have h0 := sigma_pos t
  have h1 := sigma_lt_one t
  have he := sigma_le_exp t
  unfold sigmaPrime
  nlinarith

theorem sigmaPrime_exp_error (t : ℝ) :
    |sigmaPrime t-Real.exp t| ≤ 2*Real.exp (2*t) := by
  rw [abs_of_nonpos (sub_nonpos.mpr (sigmaPrime_le_exp t))]
  have hden : 0 < 1+Real.exp t := by positivity
  have he : Real.exp (2*t) = Real.exp t^2 := by rw [two_mul, Real.exp_add, pow_two]
  rw [he]
  unfold sigmaPrime sigma
  field_simp
  nlinarith [Real.exp_pos t, pow_nonneg (Real.exp_pos t).le 3,
    pow_nonneg (Real.exp_pos t).le 4]

theorem sigma_sq_le_exp (t : ℝ) : sigma t^2 ≤ Real.exp (2*t) := by
  rw [two_mul, Real.exp_add]
  have h := sigma_le_exp t
  nlinarith [sigma_pos t, Real.exp_pos t]

theorem oneMinusSigma_sq_error (t : ℝ) : |(1-sigma t)^2-1| ≤ 2*Real.exp t := by
  have h0 := sigma_pos t
  have h1 := sigma_lt_one t
  have he := sigma_le_exp t
  rw [abs_of_nonpos (by nlinarith : (1-sigma t)^2-1 ≤ 0)]
  nlinarith

theorem sigmaSqSecond_abs_le_exp (t : ℝ) :
    |sigmaSqSecond t| ≤ 4*Real.exp (2*t) := by
  have h0 := sigma_pos t
  have h1 := sigma_lt_one t
  have hfactor : |(1-sigma t)*(2-3*sigma t)| ≤ 2 := by
    apply abs_le.mpr
    constructor
    · nlinarith [sq_nonneg (sigma t-1)]
    · nlinarith [mul_nonneg h0.le (sub_nonneg.mpr h1.le)]
  have heq : sigmaSqSecond t = 2*sigma t^2*((1-sigma t)*(2-3*sigma t)) := by
    unfold sigmaSqSecond sigmaSecond sigmaPrime
    ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*sigma t^2)]
  calc
    _ ≤ (2*sigma t^2)*2 := mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ ≤ _ := by nlinarith [sigma_sq_le_exp t]

theorem oneMinusSigmaSqSecond_abs_le_exp (t : ℝ) :
    |oneMinusSigmaSqSecond t| ≤ 2*Real.exp t := by
  have h0 := sigma_pos t
  have h1 := sigma_lt_one t
  have hfactor : |(1-sigma t)*(3*sigma t-1)| ≤ 1 := by
    apply abs_le.mpr
    constructor
    · nlinarith [mul_nonneg h0.le (sub_nonneg.mpr h1.le)]
    · nlinarith [sq_nonneg (3*sigma t-2)]
  have heq : oneMinusSigmaSqSecond t =
      2*sigmaPrime t*((1-sigma t)*(3*sigma t-1)) := by
    unfold oneMinusSigmaSqSecond sigmaSecond sigmaPrime
    ring
  have hp := (sigmaPrime_pos t).le
  rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*sigmaPrime t)]
  calc
    _ ≤ (2*sigmaPrime t)*1 := mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ ≤ _ := by nlinarith [sigmaPrime_le_exp t]

end
end SparseSGD.Logistic
