import SparseSGD.Logistic.IncrementSymmetricMoments
import SparseSGD.Logistic.SquareRemainderConvex

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

theorem increment_exp_fourth_remainder_bound (x : ℝ) :
    Real.exp x ≤ 1+x+x^2/2+x^3/6+x^4*Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 4
  have he : Complex.exp (x : ℂ)-(∑ n ∈ Finset.range 4, (x : ℂ)^n/(n.factorial : ℂ)) =
      ((Real.exp x-(1+x+x^2/2+x^3/6) : ℝ) : ℂ) := by
    norm_num [Finset.sum_range_succ, ← Complex.ofReal_exp]
  rw [he, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at h
  have ha : |x|^4 = x^4 := by
    calc
      _ = (|x|^2)^2 := by ring
      _ = (x^2)^2 := by rw [sq_abs]
      _ = _ := by ring
  rw [ha] at h
  linarith [le_abs_self (Real.exp x-(1+x+x^2/2+x^3/6))]

theorem pairedDifference_odd_integral_zero {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ) (n : ℕ) (hn : Odd n) :
    (∫ z : X × X, (pairedDifference f z)^n ∂κ.prod κ) = 0 := by
  have h := (Measure.measurePreserving_swap : MeasurePreserving (Prod.swap : X × X → X × X)
    (κ.prod κ) (κ.prod κ)).integral_comp MeasurableEquiv.prodComm.measurableEmbedding
      (fun z => (pairedDifference f z)^n)
  have he (z : X × X) : (pairedDifference f z.swap)^n = -(pairedDifference f z)^n := by
    have hh : pairedDifference f z.swap = -pairedDifference f z := by dsimp [pairedDifference]; ring
    rw [hh, hn.neg_pow]
  simp_rw [he] at h
  rw [integral_neg] at h
  linarith

/-- Taylor integration retains the exact quadratic term and cancels both
odd terms. This is an algebraic analytic lemma, not a concentration input. -/
theorem symmetric_mgf_fourth_remainder {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ) (s : ℝ)
    (hf : Integrable f κ) (hf2 : Integrable (fun x => f x^2) κ)
    (hf3 : Integrable (fun x => f x^3) κ)
    (hwe : Integrable (fun x => f x^4*Real.exp (|s| * |f x|)) κ)
    (he : Integrable (fun x => Real.exp (s*f x)) κ)
    (hm : (∫ x, f x ∂κ) = 0) (hm3 : (∫ x, f x^3 ∂κ) = 0) :
    (∫ x, Real.exp (s*f x) ∂κ)-1-(s^2/2)*(∫ x, f x^2 ∂κ) ≤
      s^4*(∫ x, f x^4*Real.exp (|s| * |f x|) ∂κ) := by
  have hp (x : X) : Real.exp (s*f x) ≤
      1+s*f x+(s^2/2)*f x^2+(s^3/6)*f x^3+s^4*(f x^4*Real.exp (|s| * |f x|)) := by
    have hh := increment_exp_fourth_remainder_bound (s*f x)
    rw [abs_mul] at hh
    nlinarith
  have h01 := (integrable_const (1 : ℝ)).add (hf.const_mul s)
  have h012 := h01.add (hf2.const_mul (s^2/2))
  have h0123 := h012.add (hf3.const_mul (s^3/6))
  have hh := integral_mono he (h0123.add (hwe.const_mul (s^4))) hp
  simp only [Pi.add_apply] at hh
  rw [integral_add (f := fun x : X => 1+s*f x+(s^2/2)*f x^2+(s^3/6)*f x^3) h0123
      (hwe.const_mul (s^4)),
    integral_add (f := fun x : X => 1+s*f x+(s^2/2)*f x^2) h012 (hf3.const_mul (s^3/6)),
    integral_add (f := fun x : X => 1+s*f x) h01 (hf2.const_mul (s^2/2)),
    integral_add (f := fun _ : X => (1 : ℝ)) (integrable_const _) (hf.const_mul s)] at hh
  simp only [integral_const_mul, hm, hm3, integral_const, probReal_univ, smul_eq_mul,
    one_mul, mul_zero, add_zero] at hh
  linarith

theorem paired_exp_integrable {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ) (hfm : Measurable f)
    (s : ℝ) (heI : Integrable (fun x => Real.exp (|s| * |f x|)) κ) :
    Integrable (fun z => Real.exp (s*pairedDifference f z)) (κ.prod κ) := by
  have hm : Measurable (pairedDifference f) := (hfm.comp measurable_fst).sub (hfm.comp measurable_snd)
  apply (heI.mul_prod heI).mono' (Real.measurable_exp.comp (measurable_const.mul hm)).aestronglyMeasurable
  filter_upwards with z
  change ‖Real.exp (s*pairedDifference f z)‖ ≤ Real.exp (|s| * |f z.1|)*Real.exp (|s| * |f z.2|)
  rw [Real.norm_eq_abs, Real.abs_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (abs_sub (f z.1) (f z.2)) (abs_nonneg s)
  have hle := le_abs_self (s*pairedDifference f z)
  rw [abs_mul] at hle
  dsimp [pairedDifference] at *
  nlinarith

theorem centered_global_mgf_remainder {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ) (s : ℝ)
    (hf : Integrable f κ)
    (hwe : Integrable (fun x => f x^2*Real.exp (|s| * |f x|)) κ)
    (he : Integrable (fun x => Real.exp (s*f x)) κ) (hm : (∫ x, f x ∂κ) = 0) :
    1 ≤ (∫ x, Real.exp (s*f x) ∂κ) ∧
    (∫ x, Real.exp (s*f x) ∂κ)-1 ≤ s^2*(∫ x, f x^2*Real.exp (|s| * |f x|) ∂κ) := by
  have hpoint (x : X) : Real.exp (s*f x) ≤ 1+s*f x+s^2*(f x^2*Real.exp (|s| * |f x|)) := by
    have hh := increment_exp_remainder_bound (s*f x)
    rw [abs_mul] at hh
    nlinarith
  have h01 := (integrable_const (1 : ℝ)).add (hf.const_mul s)
  have hl := integral_mono h01 he (fun x => by simpa [add_comm] using Real.add_one_le_exp (s*f x))
  have hu := integral_mono he (h01.add (hwe.const_mul (s^2))) hpoint
  simp only [Pi.add_apply] at hl hu
  rw [integral_add (f := fun _ : X => (1 : ℝ)) (integrable_const _) (hf.const_mul s)] at hl
  rw [integral_add (f := fun x : X => 1+s*f x) h01 (hwe.const_mul (s^2)),
    integral_add (f := fun _ : X => (1 : ℝ)) (integrable_const _) (hf.const_mul s)] at hu
  simp only [integral_const_mul, hm, integral_const, probReal_univ, smul_eq_mul,
    one_mul, mul_zero, add_zero] at hl hu
  exact ⟨hl, by linarith⟩

/-- Actual symmetrized logistic projections have a global fourth-order
MGF remainder with the rare factor `p`. -/
theorem tame_paired_projection_mgf_remainders {d : ℕ} (p : unitInterval)
    (mu theta u : Vec d) (Q s : ℝ)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (hθ : ‖theta‖ ≤ Q) (hu : ‖u‖ ≤ 1) (hmu : |inner ℝ u mu| ≤ 1) :
    let W := pairedDifference (fun a : Sample d => inner ℝ u (gradient p mu theta a))
    let κ := (sampleLaw d p).prod (sampleLaw d p)
    Integrable (fun z => Real.exp (s*W z)) κ ∧
    1 ≤ (∫ z, Real.exp (s*W z) ∂κ) ∧
    (∫ z, Real.exp (s*W z) ∂κ)-1 ≤
      symmetricProjectionConstant Q 2*(p : ℝ)*s^2*Real.exp (3*s^2) ∧
    (∫ z, Real.exp (s*W z) ∂κ)-1-(s^2/2)*(∫ z, (W z)^2 ∂κ) ≤
      symmetricProjectionConstant Q 4*(p : ℝ)*s^4*Real.exp (3*s^2) := by
  let X := fun a : Sample d => inner ℝ u (gradient p mu theta a)
  let W := pairedDifference X
  let κ := (sampleLaw d p).prod (sampleLaw d p)
  have hXm : Measurable X := measurable_const.inner ((measurable_gradient d p mu).comp
    (f := fun a : Sample d => (theta,a)) (measurable_const.prodMk measurable_id))
  have hWm : Measurable W := (hXm.comp measurable_fst).sub (hXm.comp measurable_snd)
  have hXI : Integrable X (sampleLaw d p) :=
    ((gradient_memLp_two d p mu theta).integrable (by norm_num)).const_inner (𝕜 := ℝ) u
  have hWI : Integrable W κ := (hXI.comp_fst (sampleLaw d p)).sub (hXI.comp_snd (sampleLaw d p))
  have hw (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :=
    tame_paired_projection_weighted_moment p mu theta u Q t n hn hp htame hθ hu hmu
  have hw2 : Integrable (fun z => (W z)^2*Real.exp (|s| * |W z|)) κ := by
    simpa only [sq_abs] using (hw 2 (by omega) s).1
  have hw4 : Integrable (fun z => (W z)^4*Real.exp (|s| * |W z|)) κ := by
    have hh := (hw 4 (by omega) s).1
    convert hh using 1
    funext z
    congr 1
    exact ((abs_pow (W z) 4).symm.trans (abs_of_nonneg (by positivity))).symm
  have hW2I : Integrable (fun z => (W z)^2) κ := by
    simpa only [abs_zero, zero_mul, Real.exp_zero, mul_one, sq_abs] using (hw 2 (by omega) 0).1
  have hW3I : Integrable (fun z => (W z)^3) κ := by
    have hh := (hw 3 (by omega) 0).1
    simp only [abs_zero, zero_mul, Real.exp_zero, mul_one] at hh
    apply hh.mono' (hWm.pow_const 3).aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_pow]
  have hm : (∫ z, W z ∂κ) = 0 := by
    simpa only [pow_one] using pairedDifference_odd_integral_zero (sampleLaw d p) X 1 (by decide)
  have hm3 : (∫ z, (W z)^3 ∂κ) = 0 := pairedDifference_odd_integral_zero (sampleLaw d p) X 3 (by decide)
  have hexp := paired_exp_integrable (sampleLaw d p) X hXm s
    (normalized_projection_exp_abs_bound p mu theta u s hu hmu).1
  have hsecond := centered_global_mgf_remainder κ W s hWI hw2 hexp hm
  have hfourth := symmetric_mgf_fourth_remainder κ W s hWI hW2I hW3I hw4 hexp hm hm3
  refine ⟨hexp, hsecond.1, ?_, ?_⟩
  · have hh := (hw 2 (by omega) s).2
    simp only [sq_abs] at hh
    have hs := mul_le_mul_of_nonneg_left hh (sq_nonneg s)
    exact hsecond.2.trans (hs.trans_eq (by ring))
  · have hh := (hw 4 (by omega) s).2
    have hnorm (z : Sample d × Sample d) : |W z|^4 = (W z)^4 :=
      (abs_pow (W z) 4).symm.trans (abs_of_nonneg (by positivity))
    change (∫ z, |W z|^4*Real.exp (|s| * |W z|) ∂κ) ≤ _ at hh
    simp_rw [hnorm] at hh
    have hs := mul_le_mul_of_nonneg_left hh (show 0 ≤ s^4 by positivity)
    exact hfourth.trans (hs.trans_eq (by ring))

end
end SparseSGD.Logistic
