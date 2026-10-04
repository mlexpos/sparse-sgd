import SparseSGD.Comparison.FunctionalGrid
import SparseSGD.Comparison.SingleModeQuadrature

open MeasureTheory Set

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

theorem decaying_exp_sampled_mass (h : ℝ) (hh : 0 < h) (k : ℕ) :
    (∑ j ∈ Finset.range k, h*Real.exp (-((j+1 : ℕ) : ℝ)*h)) ≤ 1 := by
  have hb : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hstep : Real.exp (-h)*(h+1) ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left (Real.add_one_le_exp h) (Real.exp_pos (-h)).le
    have he : Real.exp (-h)*Real.exp h = 1 := by rw [← Real.exp_add]; simp
    rwa [he] at H
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ']
    have he (j : ℕ) : h*Real.exp (-((j+1+1 : ℕ) : ℝ)*h) =
        Real.exp (-h)*(h*Real.exp (-((j+1 : ℕ) : ℝ)*h)) := by
      have hex : Real.exp (-((j+1+1 : ℕ) : ℝ)*h) =
          Real.exp (-h)*Real.exp (-((j+1 : ℕ) : ℝ)*h) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [hex]
      ring
    simp_rw [he]
    rw [← Finset.mul_sum]
    rw [show -((0+1 : ℕ) : ℝ)*h = -h by norm_num]
    nlinarith [mul_le_mul_of_nonneg_left ih (Real.exp_pos (-h)).le]

theorem sampledFunctionalConvolution_norm_le (lambda : ℂ) (hl : lambda.re = -1)
    (h : ℝ) (hh : 0 < h) (f : ℕ → ℂ) (F : ℝ) (hF : 0 ≤ F)
    (hf : ∀ j, ‖f j‖ ≤ F) (k : ℕ) :
    ‖sampledFunctionalConvolution lambda h f k‖ ≤ F := by
  unfold sampledFunctionalConvolution
  calc
    _ ≤ ∑ j ∈ Finset.range k, ‖(h : ℂ)*Complex.exp (lambda*((k-j : ℕ) : ℂ)*(h : ℂ))*f j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range k, h*Real.exp (-((k-j : ℕ) : ℝ)*h)*F := by
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh,Complex.norm_exp]
      simp only [Complex.mul_re,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,
        Complex.ofReal_re,Complex.ofReal_im,hl,mul_zero,sub_zero,zero_add,neg_one_mul]
      exact mul_le_mul_of_nonneg_left (hf j) (by positivity)
    _ = (∑ j ∈ Finset.range k, h*Real.exp (-((j+1 : ℕ) : ℝ)*h))*F := by
      rw [← Finset.sum_mul]
      congr 1
      conv_lhs => rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk := Finset.mem_range.mp hj
      rw [show k-(k-1-j) = j+1 by omega]
    _ ≤ 1*F := mul_le_mul_of_nonneg_right (decaying_exp_sampled_mass h hh k) hF
    _ = F := one_mul F

theorem single_mode_convolution_norm_le (lambda : ℂ) (hl : lambda.re = -1)
    (f : ℝ → ℂ) (F T : ℝ) (hF : 0 ≤ F) (hT : 0 ≤ T)
    (hf : ∀ t, 0 ≤ t → ‖f t‖ ≤ F) :
    ‖∫ x in (0 : ℝ)..T, Complex.exp (lambda*(x : ℂ))*f (T-x)‖ ≤ F := by
  have H : ‖∫ x in (0 : ℝ)..T, Complex.exp (lambda*(x : ℂ))*f (T-x)‖ ≤
      ∫ x in (0 : ℝ)..T, Real.exp (-x)*F := by
    apply intervalIntegral.norm_integral_le_of_norm_le hT
    · filter_upwards [] with x hx
      simp only [norm_mul,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,hl,mul_zero,sub_zero,neg_one_mul]
      exact mul_le_mul_of_nonneg_left (hf _ (by linarith [hx.2])) (Real.exp_pos _).le
    · exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (-x)*F)).intervalIntegrable 0 T
  rw [intervalIntegral.integral_mul_const] at H
  exact H.trans (by nlinarith [mul_le_mul_of_nonneg_right (decaying_exp_partial_mass T hT) hF])

theorem sampledFunctionalConvolution_sub (lambda : ℂ) (h : ℝ) (f g : ℕ → ℂ) (k : ℕ) :
    sampledFunctionalConvolution lambda h f k-sampledFunctionalConvolution lambda h g k =
      sampledFunctionalConvolution lambda h (fun j => f j-g j) k := by
  unfold sampledFunctionalConvolution
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The normalization cost for either actual energy functional. -/
theorem normalized_functional_error (gain A B I : ℂ) (M D E F : ℝ)
    (hM : 1/5 ≤ M) (hg : ‖gain‖ ≤ 2) (hD : ‖A-B‖ ≤ D)
    (hE : ‖B-I‖ ≤ E) (hF : ‖I‖ ≤ F) :
    ‖gain/(M : ℂ)*A-gain*I‖ ≤ 10*(D+E+|M-1| * F) := by
  have hm : 0 < M := by linarith
  have hmc : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  have hid : gain/(M : ℂ)*A-gain*I =
      (gain/(M : ℂ))*((A-B)+(B-I)+(1-(M : ℂ))*I) := by field_simp; ring
  rw [hid,norm_mul]
  have hn : ‖gain/(M : ℂ)‖ ≤ 10 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hm]
    apply (div_le_iff₀ hm).2
    linarith
  have hrest : ‖(A-B)+(B-I)+(1-(M : ℂ))*I‖ ≤ D+E+|M-1| * F := by
    calc
      _ ≤ ‖A-B‖+‖B-I‖+‖(1-(M : ℂ))*I‖ := (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ D+E+|M-1| * F := by
        rw [norm_mul,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
          Real.norm_eq_abs,abs_sub_comm]
        gcongr
  exact (mul_le_mul_of_nonneg_left hrest (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hn (by linarith [norm_nonneg ((A-B)+(B-I)+(1-(M : ℂ))*I)]))

end
end SparseSGD
