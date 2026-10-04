import SparseSGD.Comparison.RiemannBound

open MeasureTheory Set

namespace SparseSGD
noncomputable section

theorem decaying_exp_partial_mass (T : ℝ) (hT : 0 ≤ T) :
    (∫ x in (0 : ℝ)..T, Real.exp (-x)) ≤ 1 := by
  have H : (∫ x in (0 : ℝ)..T, Real.exp (-x)) = -Real.exp (-T)+1 := by
    have hd (x : ℝ) : HasDerivAt (fun t : ℝ => -Real.exp (-t)) (Real.exp (-x)) x := by
      convert (((hasDerivAt_id x).neg).exp).neg using 1 <;> simp [Pi.neg_def]
    have hc : Continuous (fun x : ℝ => Real.exp (-x)) := by fun_prop
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hd x) (hc.intervalIntegrable 0 T)
  rw [H]
  linarith [Real.exp_pos (-T)]

/-- Uniform finite quadrature for a single damped complex mode and a real
forcing, with no dependence on the length of the time interval. -/
theorem single_mode_convolution_quadrature_bound (lambda : ℂ) (hl : lambda.re = -1)
    {h : ℝ} (hh : 0 < h) (k : ℕ) (f f' : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f')
    (F D : ℝ) (hF : 0 ≤ F) (hD : 0 ≤ D)
    (hbound : ∀ t ∈ Icc 0 ((k : ℝ)*h), |f t| ≤ F)
    (hderiv : ∀ t ∈ Icc 0 ((k : ℝ)*h), |f' t| ≤ D) :
    ‖(∫ x in (0 : ℝ)..(k : ℝ)*h,
        Complex.exp (lambda*(x : ℂ))*(f ((k : ℝ)*h-x) : ℂ)) -
      rightEndpointSum (fun x => Complex.exp (lambda*(x : ℂ))*
        (f ((k : ℝ)*h-x) : ℂ)) h k‖ ≤ h*(‖lambda‖*F+D) := by
  let T := (k : ℝ)*h
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let q := fun x : ℝ => Complex.exp (lambda*(x : ℂ))
  let g := fun x : ℝ => q x*(f (T-x) : ℂ)
  let g' := fun x : ℝ => lambda*q x*(f (T-x) : ℂ)-q x*(f' (T-x) : ℂ)
  have hq (x : ℝ) : HasDerivAt q (lambda*q x) x := by
    convert ((hasDerivAt_id x).ofReal_comp.const_mul lambda).cexp using 1 <;> simp [q] <;> ring
  have hqn (x : ℝ) : ‖q x‖ = Real.exp (-x) := by
    simp [q, Complex.norm_exp, Complex.mul_re, hl]
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hg (x : ℝ) : HasDerivAt g (g' x) x := by
    have hc := ((hf (T-x)).comp x ((hasDerivAt_const x T).sub (hasDerivAt_id x))).ofReal_comp
    convert (hq x).mul hc using 1
    · rfl
    · dsimp [g']
      push_cast
      ring
  have hgc : Continuous g' := by dsimp [g',q]; fun_prop
  have hnorm (x : ℝ) (hx : x ∈ Icc 0 T) :
      ‖g' x‖ ≤ Real.exp (-x)*(‖lambda‖*F+D) := by
    have htx : T-x ∈ Icc 0 T := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    calc
      _ ≤ ‖lambda*q x*(f (T-x) : ℂ)‖+‖q x*(f' (T-x) : ℂ)‖ := norm_sub_le _ _
      _ = ‖lambda‖*Real.exp (-x)*|f (T-x)|+Real.exp (-x)*|f' (T-x)| := by
        simp only [norm_mul,hqn,Complex.norm_real,Real.norm_eq_abs]
      _ ≤ ‖lambda‖*Real.exp (-x)*F+Real.exp (-x)*D := add_le_add
        (mul_le_mul_of_nonneg_left (hbound _ htx) (by positivity))
        (mul_le_mul_of_nonneg_left (hderiv _ htx) (Real.exp_pos _).le)
      _ = _ := by ring
  have hmono : (∫ x in (0 : ℝ)..T, ‖g' x‖) ≤ ‖lambda‖*F+D := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..T, Real.exp (-x)*(‖lambda‖*F+D) :=
        intervalIntegral.integral_mono_on hT (hgc.norm.intervalIntegrable 0 T)
          ((by fun_prop : Continuous (fun x : ℝ => Real.exp (-x)*(‖lambda‖*F+D))).intervalIntegrable 0 T)
          hnorm
      _ = (∫ x in (0 : ℝ)..T, Real.exp (-x))*(‖lambda‖*F+D) :=
        intervalIntegral.integral_mul_const _ _
      _ ≤ 1*(‖lambda‖*F+D) := mul_le_mul_of_nonneg_right (decaying_exp_partial_mass T hT) (by positivity)
      _ = _ := one_mul _
  exact (rightEndpoint_error g g' hg hgc h hh.le k).trans
    (mul_le_mul_of_nonneg_left hmono hh.le)

end
end SparseSGD
