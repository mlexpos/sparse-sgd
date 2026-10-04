import SparseSGD.Logistic.DynamicEuler
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1200000

/-- The field's parameter dependence is affine in delta and the noise rate;
the exponential curvature is evaluated at the same state on both sides. -/
theorem dynamicField_parameter_error (r delta Phi delta0 Phi0 M : ℝ)
    (y : DynamicState) (hM : 0 ≤ M) (hy : ‖y‖ ≤ M) :
    ‖dynamicField r delta Phi y-dynamicField r delta0 Phi0 y‖ ≤
      (2*M+1)*(|delta-delta0|+|2*Phi/delta-2*Phi0/delta0|) := by
  have hcoord : ∀ j, |y j| ≤ M := fun j => by simpa using (norm_le_pi_norm y j).trans hy
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i <;> simp [dynamicField,Real.norm_eq_abs]
  · have hi : -(delta*y 1)+delta0*y 1 = -(delta-delta0)*y 1 := by ring
    rw [hi,abs_mul,abs_neg]
    have hb := mul_le_mul_of_nonneg_left (hcoord 1) (abs_nonneg (delta-delta0))
    nlinarith [abs_nonneg (delta-delta0),abs_nonneg (2*Phi/delta-2*Phi0/delta0)]
  · positivity
  · have hi : -(2*delta*y 4)+2*delta0*y 4 = -2*(delta-delta0)*y 4 := by ring
    rw [hi,abs_mul,abs_mul]
    norm_num
    have hb := mul_le_mul_of_nonneg_left (hcoord 4) (by positivity : 0 ≤ 2*|delta-delta0|)
    nlinarith [abs_nonneg (delta-delta0),abs_nonneg (2*Phi/delta-2*Phi0/delta0)]
  · nlinarith [abs_nonneg (delta-delta0),abs_nonneg (2*Phi/delta-2*Phi0/delta0)]
  · have hi : delta0*y 3-delta*y 3 = -(delta-delta0)*y 3 := by ring
    rw [hi,abs_mul,abs_neg]
    have hb := mul_le_mul_of_nonneg_left (hcoord 3) (abs_nonneg (delta-delta0))
    nlinarith [abs_nonneg (delta-delta0),abs_nonneg (2*Phi/delta-2*Phi0/delta0)]

/-- The physical floor parameters control the noise-rate discrepancy,
uniformly when the nominal retention ratio stays away from zero. -/
theorem dynamicNoiseRate_parameter_error (delta Phi delta0 Phi0 a : ℝ)
    (ha : 0 < a) (hd : a ≤ delta) (hd0 : a ≤ delta0) :
    |2*Phi/delta-2*Phi0/delta0| ≤
      (2/a)*|Phi-Phi0|+(2*|Phi0|/a^2)*|delta-delta0| := by
  have hdpos : 0 < delta := ha.trans_le hd
  have hd0pos : 0 < delta0 := ha.trans_le hd0
  have hi : 2*Phi/delta-2*Phi0/delta0 =
      2*(Phi-Phi0)/delta+2*Phi0*(delta0-delta)/(delta*delta0) := by field_simp; ring
  rw [hi]
  calc
    _ ≤ |2*(Phi-Phi0)/delta|+|2*Phi0*(delta0-delta)/(delta*delta0)| := abs_add_le _ _
    _ = (2*|Phi-Phi0|)/delta+(2*|Phi0| *|delta-delta0|)/(delta*delta0) := by
      simp [abs_div,abs_mul,abs_of_pos hdpos,abs_of_pos hd0pos,abs_sub_comm]
    _ ≤ (2*|Phi-Phi0|)/a+(2*|Phi0| *|delta-delta0|)/a^2 := by
      gcongr
      nlinarith
    _ = _ := by ring

end
end SparseSGD.Logistic
