import SparseSGD.Logistic.IncrementProjectionSquare
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

theorem increment_exp_neg_le_quadratic (y : ℝ) (hy : 0 ≤ y) :
    Real.exp (-y) ≤ 1-y+y^2/2 := by
  have hp : 0 ≤ 1-y+y^2/2 := by nlinarith [sq_nonneg (y-1)]
  have hh := mul_le_mul_of_nonneg_right (Real.quadratic_le_exp_of_nonneg hy) hp
  have hprod : 1 ≤ Real.exp y*(1-y+y^2/2) := by nlinarith [sq_nonneg (y^2)]
  have hm := mul_le_mul_of_nonneg_left hprod (Real.exp_pos (-y)).le
  have he : Real.exp (-y)*Real.exp y = 1 := by rw [← Real.exp_add]; simp
  simpa only [mul_one, ← mul_assoc, he, one_mul] using hm

/-- A positive square-exponential remainder bounds the fourth moment. -/
theorem fourth_moment_of_square_remainder {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ) (hfm : Measurable f)
    (hf2 : Integrable (fun x => f x^2) κ) (A V : ℝ) (hA : 0 < A)
    (hi : Integrable (fun x => Real.exp (A*f x^2)) κ)
    (hb : (∫ x, Real.exp (A*f x^2) ∂κ)-1-A*(∫ x, f x^2 ∂κ) ≤ V*A^2) :
    Integrable (fun x => f x^4) κ ∧ (∫ x, f x^4 ∂κ) ≤ 2*V := by
  have hR : Integrable (fun x => Real.exp (A*f x^2)-1-A*f x^2) κ :=
    (hi.sub (integrable_const _)).sub (hf2.const_mul A)
  have hd (x : X) : (A^2/2)*f x^4 ≤ Real.exp (A*f x^2)-1-A*f x^2 := by
    have hh := Real.quadratic_le_exp_of_nonneg (show 0 ≤ A*f x^2 by positivity)
    nlinarith [sq_nonneg (f x)]
  have hI : Integrable (fun x => (A^2/2)*f x^4) κ := by
    apply hR.mono' ((hfm.pow_const 4).const_mul _).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hd x
  have hf4 : Integrable (fun x => f x^4) κ := by
    have hh := hI.const_mul ((A^2/2)⁻¹)
    simpa only [← mul_assoc, inv_mul_cancel₀ (by positivity : A^2/2 ≠ 0), one_mul] using hh
  refine ⟨hf4, ?_⟩
  have hm := integral_mono hI hR hd
  rw [integral_const_mul,
    integral_sub (f := fun x => Real.exp (A*f x^2)-1) (hi.sub (integrable_const _)) (hf2.const_mul A),
    integral_sub hi (integrable_const _), integral_const_mul] at hm
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hm
  have hp := sq_pos_of_pos hA
  nlinarith

/-- Positive centered-square MGFs preserve the square-remainder coefficient. -/
theorem positive_centered_square_mgf {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ)
    (V t : ℝ) (hV : 0 ≤ V) (ht : 0 ≤ t)
    (hi : Integrable (fun x => Real.exp (t*f x^2)) κ)
    (hb : (∫ x, Real.exp (t*f x^2) ∂κ)-1-t*(∫ x, f x^2 ∂κ) ≤ V*t^2) :
    Integrable (fun x => Real.exp (t*(f x^2-(∫ y, f y^2 ∂κ)))) κ ∧
    (∫ x, Real.exp (t*(f x^2-(∫ y, f y^2 ∂κ))) ∂κ) ≤ Real.exp (V*t^2) := by
  let m := ∫ y, f y^2 ∂κ
  have hm : 0 ≤ m := integral_nonneg (fun _ => sq_nonneg _)
  have he (x : X) : Real.exp (t*(f x^2-m)) = Real.exp (-t*m)*Real.exp (t*f x^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change Integrable (fun x => Real.exp (t*(f x^2-m))) κ ∧
    (∫ x, Real.exp (t*(f x^2-m)) ∂κ) ≤ Real.exp (V*t^2)
  simp_rw [he]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  have he1 : Real.exp (-t*m) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hpoly : Real.exp (-t*m)*(1+t*m) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (t*m)) (Real.exp_pos (-t*m)).le
    rw [← Real.exp_add, show -t*m+t*m = 0 by ring, Real.exp_zero] at hh
    simpa only [add_comm (t*m) 1] using hh
  have hscaled := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-t*m)).le
  have hterm := mul_le_mul_of_nonneg_right he1 (show 0 ≤ V*t^2 by positivity)
  have hbound : Real.exp (-t*m)*(∫ x, Real.exp (t*f x^2) ∂κ) ≤ 1+V*t^2 := by
    dsimp [m] at *
    nlinarith
  exact hbound.trans (by linarith [Real.add_one_le_exp (V*t^2)])

/-- The negative centered-square MGF is controlled by its actual fourth
moment and the explicitly bounded centering factor. -/
theorem negative_centered_square_mgf {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ) (hfm : Measurable f)
    (hf2 : Integrable (fun x => f x^2) κ) (hf4 : Integrable (fun x => f x^4) κ)
    (V M Amax s : ℝ) (hV : 0 ≤ V) (hs : 0 ≤ s) (hsmax : s ≤ Amax)
    (hmean : (∫ x, f x^2 ∂κ) ≤ M) (hfour : (∫ x, f x^4 ∂κ) ≤ 2*V) :
    Integrable (fun x => Real.exp (-s*(f x^2-(∫ y, f y^2 ∂κ)))) κ ∧
    (∫ x, Real.exp (-s*(f x^2-(∫ y, f y^2 ∂κ))) ∂κ) ≤
      Real.exp (Real.exp (Amax*M)*V*s^2) := by
  let m := ∫ y, f y^2 ∂κ
  have hm : 0 ≤ m := integral_nonneg (fun _ => sq_nonneg _)
  have hM : 0 ≤ M := hm.trans hmean
  have hsm : s*m ≤ Amax*M := (mul_le_mul_of_nonneg_left hmean hs).trans
    (mul_le_mul_of_nonneg_right hsmax hM)
  have hbase : Integrable (fun x => Real.exp (-s*f x^2)) κ := by
    apply (integrable_const (1 : ℝ)).mono'
      (Real.measurable_exp.comp ((hfm.pow_const 2).const_mul (-s))).aestronglyMeasurable
    filter_upwards with x
    change ‖Real.exp (-s*f x^2)‖ ≤ 1
    rw [Real.norm_eq_abs, Real.abs_exp]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (f x)])
  have he (x : X) : Real.exp (-s*(f x^2-m)) = Real.exp (s*m)*Real.exp (-s*f x^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change Integrable (fun x => Real.exp (-s*(f x^2-m))) κ ∧
    (∫ x, Real.exp (-s*(f x^2-m)) ∂κ) ≤ Real.exp (Real.exp (Amax*M)*V*s^2)
  simp_rw [he]
  refine ⟨hbase.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hP := ((integrable_const (1 : ℝ)).sub (hf2.const_mul s)).add (hf4.const_mul (s^2/2))
  have hpoint (x : X) : Real.exp (-s*f x^2) ≤ 1-s*f x^2+(s^2/2)*f x^4 := by
    have hh := increment_exp_neg_le_quadratic (s*f x^2) (by positivity)
    convert hh using 1 <;> ring
  have hi := integral_mono hbase hP hpoint
  simp only [Pi.add_apply, Pi.sub_apply] at hi
  rw [integral_add (f := fun x => 1-s*f x^2)
    ((integrable_const (1 : ℝ)).sub (hf2.const_mul s)) (hf4.const_mul (s^2/2)),
    integral_sub (integrable_const _) (hf2.const_mul s), integral_const_mul,
    integral_const_mul] at hi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  have hscaled := mul_le_mul_of_nonneg_left hi (Real.exp_pos (s*m)).le
  have hpoly : Real.exp (s*m)*(1-s*m) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-s*m)) (Real.exp_pos (s*m)).le
    rw [← Real.exp_add, show s*m+-s*m = 0 by ring, Real.exp_zero] at hh
    nlinarith
  have hex := Real.exp_le_exp.mpr hsm
  have hfourterm := mul_le_mul_of_nonneg_left hfour (show 0 ≤ s^2/2 by positivity)
  have hterm := mul_le_mul_of_nonneg_left hfourterm (Real.exp_pos (s*m)).le
  have hterm2 := mul_le_mul_of_nonneg_right hex (show 0 ≤ V*s^2 by positivity)
  have hbound : Real.exp (s*m)*(∫ x, Real.exp (-s*f x^2) ∂κ) ≤
      1+Real.exp (Amax*M)*V*s^2 := by
    dsimp [m] at *
    nlinarith
  exact hbound.trans (by linarith [Real.add_one_le_exp (Real.exp (Amax*M)*V*s^2)])

/-- A square-exponential remainder on a positive interval yields a
two-sided centered-square MGF on that same interval. The centering-factor
constant is explicit. -/
theorem centered_square_mgf_of_remainder {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ) (hfm : Measurable f)
    (hf2 : Integrable (fun x => f x^2) κ) (V M Amax t : ℝ)
    (hV : 0 ≤ V) (hAmax : 0 < Amax) (ht : |t| ≤ Amax)
    (hmean : (∫ x, f x^2 ∂κ) ≤ M)
    (hrem : ∀ A : ℝ, 0 ≤ A → A ≤ Amax →
      Integrable (fun x => Real.exp (A*f x^2)) κ ∧
      (∫ x, Real.exp (A*f x^2) ∂κ)-1-A*(∫ x, f x^2 ∂κ) ≤ V*A^2) :
    Integrable (fun x => Real.exp (t*(f x^2-(∫ y, f y^2 ∂κ)))) κ ∧
    (∫ x, Real.exp (t*(f x^2-(∫ y, f y^2 ∂κ))) ∂κ) ≤
      Real.exp (Real.exp (Amax*M)*V*t^2) := by
  by_cases hpos : 0 ≤ t
  · have hh := positive_centered_square_mgf κ f V t hV hpos
      (hrem t hpos ((le_abs_self t).trans ht)).1
      (hrem t hpos ((le_abs_self t).trans ht)).2
    refine ⟨hh.1, hh.2.trans ?_⟩
    apply Real.exp_le_exp.mpr
    have hm : 0 ≤ M := (integral_nonneg (fun _ => sq_nonneg _)).trans hmean
    have he : 1 ≤ Real.exp (Amax*M) := Real.one_le_exp_iff.mpr (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right he (show 0 ≤ V*t^2 by positivity)]
  · have hneg : t < 0 := lt_of_not_ge hpos
    have htop := hrem Amax hAmax.le le_rfl
    have hfour := fourth_moment_of_square_remainder κ f hfm hf2 Amax V hAmax htop.1 htop.2
    have hh := negative_centered_square_mgf κ f hfm hf2 hfour.1 V M Amax (-t)
      hV (by linarith) (by simpa only [abs_of_neg hneg] using ht) hmean hfour.2
    simpa only [neg_neg, neg_sq] using hh

end
end SparseSGD.Logistic
