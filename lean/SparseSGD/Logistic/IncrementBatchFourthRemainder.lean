import SparseSGD.Logistic.IncrementFourthRemainder

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

theorem mgf_upper_of_global_remainder (x a c s : ℝ) (hc : 0 ≤ c) (ha : a ≤ 1)
    (hrem : x-1 ≤ c*a*s^2*Real.exp (3*s^2)) :
    x ≤ Real.exp ((3+c)*s^2) := by
  have hp := mul_le_mul_of_nonneg_left ha (show 0 ≤ c*s^2*Real.exp (3*s^2) by positivity)
  have he : 1 ≤ Real.exp (3*s^2) := Real.one_le_exp_iff.mpr (by positivity)
  have h1 : x ≤ (1+c*s^2)*Real.exp (3*s^2) := by nlinarith
  have h2 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (c*s^2)) (Real.exp_pos (3*s^2)).le
  rw [add_comm (c*s^2) 1] at h2
  refine h1.trans (h2.trans_eq ?_)
  rw [← Real.exp_add]
  congr 1
  ring

/-- The iid fourth-order MGF remainder has the variance orders `a²/B²`
and `a/B³`. This follows from exact finite-product integration and the
proved product remainder algebra, without a concentration certificate. -/
theorem iid_global_fourth_mgf_remainder {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ)
    (a c2 c4 c0 v s : ℝ) (ha : 0 ≤ a) (hc2 : 0 ≤ c2) (hc4 : 0 ≤ c4) (hc0 : 0 ≤ c0)
    (B : ℕ) (hB : 0 < B)
    (hmgf : ∀ t : ℝ, Integrable (fun x => Real.exp (t*f x)) κ ∧
      1 ≤ (∫ x, Real.exp (t*f x) ∂κ) ∧
      (∫ x, Real.exp (t*f x) ∂κ)-1 ≤ c2*a*t^2*Real.exp (3*t^2) ∧
      (∫ x, Real.exp (t*f x) ∂κ)-1-(t^2/2)*v ≤ c4*a*t^4*Real.exp (3*t^2) ∧
      (∫ x, Real.exp (t*f x) ∂κ) ≤ Real.exp (c0*t^2)) :
    Integrable (fun z : Fin B → X => Real.exp (s*((B : ℝ)⁻¹*∑ i, f (z i))))
      (Measure.pi (fun _ : Fin B => κ)) ∧
    (∫ z : Fin B → X, Real.exp (s*((B : ℝ)⁻¹*∑ i, f (z i))) ∂Measure.pi (fun _ : Fin B => κ))-
      1-(s^2/2)*(v/(B : ℝ)) ≤
      (c4*a/(B : ℝ)^3+c2^2*a^2/(B : ℝ)^2)*s^4*Real.exp ((c0+6)*s^2/(B : ℝ)) := by
  have hbr : (0 : ℝ) < B := by exact_mod_cast hB
  have hbr1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  let x := ∫ y, Real.exp ((s/B)*f y) ∂κ
  let u := Real.exp (c0*(s/B)^2)
  have hr := hmgf (s/B)
  have hpoint (z : Fin B → X) : Real.exp (s*((B : ℝ)⁻¹*∑ i, f (z i))) =
      ∏ i, Real.exp ((s/B)*f (z i)) := by
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.mul_sum]
    simp only [div_eq_mul_inv, mul_assoc]
  simp_rw [hpoint]
  refine ⟨Integrable.fintype_prod (fun _ => hr.1), ?_⟩
  rw [integral_fintype_prod_eq_prod (fun _ : Fin B => fun y : X => Real.exp ((s/B)*f y))]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hp := increment_power_second_remainder x u B hr.2.1 hr.2.2.2.2
  have hxp : 0 ≤ x-1 := by have hh := hr.2.1; dsimp [x]; linarith
  have hxr : x-1 ≤ c2*a*(s/B)^2*Real.exp (3*(s/B)^2) := hr.2.2.1
  have hxq : (x-1)^2 ≤ (c2*a*(s/B)^2*Real.exp (3*(s/B)^2))^2 := by
    have hh := mul_self_le_mul_self hxp hxr
    simpa only [pow_two] using hh
  have hscaled := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hxq (show 0 ≤ u^B by dsimp [u]; positivity)) (sq_nonneg (B : ℝ))
  have hfour := mul_le_mul_of_nonneg_left hr.2.2.2.1 hbr.le
  have hevar : (B : ℝ)*((s/B)^2/2)*v = (s^2/2)*(v/(B : ℝ)) := by field_simp <;> ring
  have hbase : x^B-1-(s^2/2)*(v/(B : ℝ)) ≤
      (B : ℝ)*c4*a*(s/B)^4*Real.exp (3*(s/B)^2)+
      (B : ℝ)^2*(c2*a*(s/B)^2*Real.exp (3*(s/B)^2))^2*u^B := by
    dsimp [x] at hp hxr hxp hxq hscaled ⊢
    nlinarith [hevar]
  have hsmall : (s/(B : ℝ))^2 ≤ s^2/(B : ℝ) := by
    have hinv : (B : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hbr).mpr hbr1
    have hh := mul_le_mul_of_nonneg_left hinv (show 0 ≤ s^2*(B : ℝ)⁻¹ by positivity)
    convert hh using 1 <;> simp only [div_eq_mul_inv] <;> ring
  have huPow : u^B = Real.exp (c0*s^2/(B : ℝ)) := by
    dsimp [u]
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
    <;> ring
  have hfirst : (B : ℝ)*c4*a*(s/B)^4*Real.exp (3*(s/B)^2) ≤
      (c4*a/(B : ℝ)^3)*s^4*Real.exp ((c0+6)*s^2/(B : ℝ)) := by
    have hex : Real.exp (3*(s/B)^2) ≤ Real.exp ((c0+6)*s^2/(B : ℝ)) := by
      apply Real.exp_le_exp.mpr
      rw [show (c0+6)*s^2/(B : ℝ) = c0*(s^2/(B : ℝ))+6*(s^2/(B : ℝ)) by ring]
      nlinarith [mul_nonneg hc0 (show 0 ≤ s^2/(B : ℝ) by positivity)]
    have hh := mul_le_mul_of_nonneg_left hex (show 0 ≤ (B : ℝ)*c4*a*(s/B)^4 by positivity)
    exact hh.trans_eq (by field_simp <;> ring)
  have hsecond : (B : ℝ)^2*(c2*a*(s/B)^2*Real.exp (3*(s/B)^2))^2*u^B ≤
      (c2^2*a^2/(B : ℝ)^2)*s^4*Real.exp ((c0+6)*s^2/(B : ℝ)) := by
    have hex : Real.exp (3*(s/B)^2)^2*u^B ≤ Real.exp ((c0+6)*s^2/(B : ℝ)) := by
      rw [huPow, ← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      norm_num
      rw [show (c0+6)*s^2/(B : ℝ) = c0*s^2/(B : ℝ)+6*(s^2/(B : ℝ)) by ring]
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hex
      (show 0 ≤ (B : ℝ)^2*(c2*a*(s/B)^2)^2 by positivity)
    convert hh using 1 <;> field_simp <;> ring
  exact hbase.trans ((add_le_add hfirst hsecond).trans_eq (by ring))

/-- Actual iid batch projections retain the rare fourth-order remainder,
including its `p²/B²+p/B³` coefficient. -/
theorem tame_paired_batch_projection_fourth_remainder {d B : ℕ} (p : unitInterval)
    (mu theta u : Vec d) (Q s : ℝ) (hB : 0 < B)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (hθ : ‖theta‖ ≤ Q) (hu : ‖u‖ ≤ 1) (hmu : |inner ℝ u mu| ≤ 1) :
    let W := pairedDifference (fun a : Sample d => inner ℝ u (gradient p mu theta a))
    let κ := (sampleLaw d p).prod (sampleLaw d p)
    let ν := Measure.pi (fun _ : Fin B => κ)
    let T := fun z : Fin B → Sample d × Sample d => (B : ℝ)⁻¹*∑ i, W (z i)
    MemLp T 2 ν ∧ Integrable (fun z => Real.exp (s*T z)) ν ∧
    (∫ z, Real.exp (s*T z) ∂ν)-1-(s^2/2)*(∫ z, (T z)^2 ∂ν) ≤
      (symmetricProjectionConstant Q 4*(p : ℝ)/(B : ℝ)^3+
        (symmetricProjectionConstant Q 2)^2*(p : ℝ)^2/(B : ℝ)^2)*s^4*
          Real.exp ((symmetricProjectionConstant Q 2+9)*s^2/(B : ℝ)) := by
  let W := pairedDifference (fun a : Sample d => inner ℝ u (gradient p mu theta a))
  let κ := (sampleLaw d p).prod (sampleLaw d p)
  have hWm : Measurable W := by
    have hm : Measurable (fun a : Sample d => inner ℝ u (gradient p mu theta a)) :=
      measurable_const.inner ((measurable_gradient d p mu).comp
        (f := fun a : Sample d => (theta,a)) (measurable_const.prodMk measurable_id))
    exact (hm.comp measurable_fst).sub (hm.comp measurable_snd)
  have hW2I : Integrable (fun z => (W z)^2) κ := by
    simpa only [abs_zero, zero_mul, Real.exp_zero, mul_one, sq_abs] using
      (tame_paired_projection_weighted_moment p mu theta u Q 0 2 (by omega) hp htame hθ hu hmu).1
  have hWLp : MemLp W 2 κ := by
    apply (memLp_two_iff_integrable_sq_norm hWm.aestronglyMeasurable).mpr
    simpa only [Real.norm_eq_abs, sq_abs] using hW2I
  have hWzero : (∫ z, W z ∂κ) = 0 := by
    simpa only [pow_one] using pairedDifference_odd_integral_zero (sampleLaw d p)
      (fun a => inner ℝ u (gradient p mu theta a)) 1 (by decide)
  have hTLp := SparseSGD.Probability.LeastSquares.iid_batch_average_memLp (B := B) W hWLp
  simp only [smul_eq_mul] at hTLp
  have hTv := SparseSGD.Probability.LeastSquares.iid_batch_average_variance hB W hWLp hWzero
  simp only [smul_eq_mul, Real.norm_eq_abs, sq_abs] at hTv
  have hc2 : 0 ≤ symmetricProjectionConstant Q 2 := by dsimp [symmetricProjectionConstant]; positivity
  have hc4 : 0 ≤ symmetricProjectionConstant Q 4 := by dsimp [symmetricProjectionConstant]; positivity
  have hmgf (t : ℝ) := tame_paired_projection_mgf_remainders p mu theta u Q t hp htame hθ hu hmu
  have hh := iid_global_fourth_mgf_remainder κ W (p : ℝ)
    (symmetricProjectionConstant Q 2) (symmetricProjectionConstant Q 4)
    (3+symmetricProjectionConstant Q 2) (∫ z, (W z)^2 ∂κ) s hp.le hc2 hc4 (by positivity) B hB
    (fun t => ⟨(hmgf t).1, (hmgf t).2.1, (hmgf t).2.2.1, (hmgf t).2.2.2,
      mgf_upper_of_global_remainder _ (p : ℝ) (symmetricProjectionConstant Q 2) t hc2 p.property.2 (hmgf t).2.2.1⟩)
  rw [← hTv] at hh
  refine ⟨hTLp, hh.1, hh.2.trans_eq ?_⟩
  congr 1
  congr 1
  ring

end
end SparseSGD.Logistic
