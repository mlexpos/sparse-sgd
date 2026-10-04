import SparseSGD.Logistic.IncrementQuadraticMoments

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1200000

theorem increment_exp_remainder_bound (x : ℝ) :
    Real.exp x ≤ 1+x+x^2*Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 2
  norm_num [Finset.sum_range_succ, ← Complex.ofReal_exp, ← Complex.ofReal_add,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  have he : (↑(Real.exp x) - (1 + (↑x : ℂ))) = ((Real.exp x - (1+x) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs] at h
  linarith [le_abs_self (Real.exp x-(1+x))]

/-- A centered bounded random variable retains its small actual second
moment in the global MGF remainder, before applying Hoeffding. -/
theorem bounded_centered_mgf_remainder {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ)
    (hf : MemLp f 2 κ) (hm : ∫ x, f x ∂κ = 0) (hb : ∀ x, |f x| ≤ 1) (t : ℝ) :
    Integrable (fun x => Real.exp (t*f x)) κ ∧
    1 ≤ (∫ x, Real.exp (t*f x) ∂κ) ∧
    (∫ x, Real.exp (t*f x) ∂κ)-1 ≤
      t^2*Real.exp |t| * (∫ x, f x^2 ∂κ) := by
  have hi := hf.integrable (by norm_num)
  have hsq := hf.integrable_sq
  have hmeas := hf.aestronglyMeasurable
  have he : Integrable (fun x => Real.exp (t*f x)) κ := by
    apply Integrable.of_bound (Real.continuous_exp.comp_aestronglyMeasurable (hmeas.const_mul t)) (Real.exp |t|)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hb x))
  have hupper (x : X) : Real.exp (t*f x) ≤ 1+t*f x + (t^2*Real.exp |t|)*f x^2 := by
    have hh := increment_exp_remainder_bound (t*f x)
    have hex : Real.exp |t*f x| ≤ Real.exp |t| := by
      apply Real.exp_le_exp.mpr
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hb x)
    have hx := mul_le_mul_of_nonneg_left hex (sq_nonneg (t*f x))
    nlinarith
  have hlower := integral_mono
    ((integrable_const (1 : ℝ)).add (hi.const_mul t)) he
      (fun x => by simpa [add_comm] using Real.add_one_le_exp (t*f x))
  have hineq := integral_mono he
    (((integrable_const (1 : ℝ)).add (hi.const_mul t)).add (hsq.const_mul (t^2*Real.exp |t|))) hupper
  simp only [Pi.add_apply] at hlower hineq
  rw [integral_add (integrable_const _) (hi.const_mul t), integral_const_mul, hm] at hlower
  rw [integral_add (f := fun x : X => 1+t*f x) ((integrable_const _).add (hi.const_mul t))
    (hsq.const_mul (t^2*Real.exp |t|)),
    integral_add (integrable_const _) (hi.const_mul t), integral_const_mul, hm] at hineq
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero,
    integral_const_mul] at hlower hineq
  exact ⟨he, hlower, by linarith⟩

private theorem increment_pow_remainder_le (x u : ℝ) (B : ℕ) (hx : 1 ≤ x) (hu : x ≤ u) :
    x^B-1 ≤ (B : ℝ)*(x-1)*u^B := by
  have hs : (∑ i ∈ Finset.range B, x^i) ≤ (B : ℝ)*u^B := by
    have hh := Finset.sum_le_sum (s := Finset.range B) (f := fun i => x^i) (g := fun _ => u^B)
      (fun i hi => (pow_le_pow_left₀ (by linarith : 0 ≤ x) hu i).trans
        (pow_le_pow_right₀ (hx.trans hu) (Finset.mem_range.mp hi).le))
    simpa using hh
  rw [← mul_geom_sum]
  have hh := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hx)
  nlinarith

/-- A rare *global* MGF remainder for a bounded iid average. The variance
factor appears outside the exponential. This stronger form is what allows
a Gaussian auxiliary integral to control the square of the average. -/
theorem iid_bounded_mgf_remainder {X : Type*} [MeasurableSpace X]
    (H : SparseSGD.External.HoeffdingCertificate X) (κ : Measure X) [IsProbabilityMeasure κ]
    (f : X → ℝ) (hfm : Measurable f) (hf : MemLp f 2 κ)
    (hm : ∫ x, f x ∂κ = 0) (hb : ∀ x, |f x| ≤ 1) (a s : ℝ)
    (ha : 0 ≤ a) (hvar : (∫ x, f x^2 ∂κ) ≤ a) (B : ℕ) (hB : 0 < B) :
    Integrable (fun z : Fin B → X => Real.exp (s*((B : ℝ)⁻¹*∑ i, f (z i))))
      (Measure.pi (fun _ : Fin B => κ)) ∧
    (∫ z : Fin B → X, Real.exp (s*((B : ℝ)⁻¹*∑ i, f (z i))) ∂Measure.pi (fun _ : Fin B => κ))-1 ≤
      Real.exp (1/2)*a*s^2/(B : ℝ)*Real.exp (s^2/(B : ℝ)) := by
  have hbr : (0 : ℝ) < B := by exact_mod_cast hB
  have hbr1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  let x := ∫ y, Real.exp ((s/B)*f y) ∂κ
  let u := Real.exp ((s/B)^2/2)
  have hr := bounded_centered_mgf_remainder κ f hf hm hb (s/B)
  have hh := H.centered_mgf κ f (s/B) hfm (hf.integrable (by norm_num)) hm hb
  have he (z : Fin B → X) : Real.exp (s*((B : ℝ)⁻¹*∑ i, f (z i))) =
      ∏ i, Real.exp ((s/B)*f (z i)) := by
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.mul_sum]
    simp only [div_eq_mul_inv, mul_assoc]
  simp_rw [he]
  refine ⟨Integrable.fintype_prod (fun _ => hr.1), ?_⟩
  rw [integral_fintype_prod_eq_prod (fun _ : Fin B => fun y : X => Real.exp ((s/B)*f y))]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hp := increment_pow_remainder_le x u B hr.2.1 hh.2
  have hv := mul_le_mul_of_nonneg_left hvar (show 0 ≤ (s/(B : ℝ))^2*Real.exp |s/B| by positivity)
  have hxp : x-1 ≤ (s/B)^2*Real.exp |s/B| * a := hr.2.2.trans hv
  have hup : 0 ≤ u^B := pow_nonneg (Real.exp_pos _).le _
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hxp hbr.le) hup
  have hmiddle : (B : ℝ)*((s/B)^2*Real.exp |s/B| * a)*u^B =
      a*s^2/(B : ℝ)*Real.exp (|s|/(B : ℝ)+s^2/(2*(B : ℝ))) := by
    have hpow : u^B = Real.exp (s^2/(2*(B : ℝ))) := by
      dsimp [u]
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
      <;> ring
    rw [hpow, abs_div, abs_of_pos hbr, Real.exp_add]
    field_simp
    <;> ring
  have hex : Real.exp (|s|/(B : ℝ)+s^2/(2*(B : ℝ))) ≤ Real.exp (1/2)*Real.exp (s^2/(B : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hnum : |s|+s^2/2 ≤ (B : ℝ)/2+s^2 := by
      nlinarith [sq_nonneg (|s|-1), sq_abs s]
    have hn := div_le_div_of_nonneg_right hnum hbr.le
    convert hn using 1 <;> field_simp <;> ring
  have hlast := mul_le_mul_of_nonneg_left hex (show 0 ≤ a*s^2/(B : ℝ) by positivity)
  rw [hmiddle] at hscaled
  exact hp.trans hscaled |>.trans hlast |>.trans_eq (by ring)

/-- The second algebraic remainder of a finite iid MGF product. -/
theorem increment_power_second_remainder (x u : ℝ) (B : ℕ) (hx : 1 ≤ x) (hu : x ≤ u) :
    x^B-1-(B : ℝ)*(x-1) ≤ (B : ℝ)^2*(x-1)^2*u^B := by
  have hxm : 0 ≤ x-1 := by linarith
  have hup : 0 ≤ u^B := pow_nonneg (by linarith) _
  have hs : (∑ i ∈ Finset.range B, (x^i-1)) ≤ (B : ℝ)^2*(x-1)*u^B := by
    have hh := Finset.sum_le_sum (s := Finset.range B)
      (f := fun i => x^i-1) (g := fun _ => (B : ℝ)*(x-1)*u^B) (fun i hi => by
        have hib : i ≤ B := (Finset.mem_range.mp hi).le
        have h := increment_pow_remainder_le x u i hx hu
        have hic : (i : ℝ) ≤ B := by exact_mod_cast hib
        have hiu : u^i ≤ u^B := pow_le_pow_right₀ (hx.trans hu) hib
        exact h.trans (mul_le_mul
          (mul_le_mul_of_nonneg_right hic hxm) hiu (pow_nonneg (by linarith) i)
            (mul_nonneg (Nat.cast_nonneg B) hxm)))
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_two, mul_assoc] using hh
  have h := mul_le_mul_of_nonneg_left hs hxm
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
  have hgeom := mul_geom_sum x B
  nlinarith

end
end SparseSGD.Logistic
