import SparseSGD.Logistic.IncrementSquareFourth
import Mathlib.Analysis.Convex.Integral

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

/-- Jensen symmetrization for a nonnegative convex function, including
integrability of the unsymmetrized term as a conclusion. -/
theorem centered_convex_symmetrization {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ) (hfm : Measurable f)
    (hf : Integrable f κ) (hm : (∫ x, f x ∂κ) = 0)
    (g : ℝ → ℝ) (hg : Continuous g) (hconv : ConvexOn ℝ Set.univ g)
    (hgn : ∀ x, 0 ≤ g x)
    (hpair : Integrable (fun z : X × X => g (f z.1-f z.2)) (κ.prod κ)) :
    Integrable (fun x => g (f x)) κ ∧
    (∫ x, g (f x) ∂κ) ≤ (∫ z : X × X, g (f z.1-f z.2) ∂κ.prod κ) := by
  have hdom : ∀ᵐ x ∂κ, g (f x) ≤ (∫ y, g (f x-f y) ∂κ) := by
    filter_upwards [hpair.prod_right_ae] with x hx
    have hfi : Integrable (fun y => f x-f y) κ := (integrable_const (f x)).sub hf
    have hh := hconv.map_integral_le hg.continuousOn isClosed_univ
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hfi hx
    rw [integral_sub (integrable_const _) hf, integral_const, hm] at hh
    simpa using hh
  have hi : Integrable (fun x => g (f x)) κ := by
    apply hpair.integral_prod_left.mono' (hg.measurable.comp hfm).aestronglyMeasurable
    filter_upwards [hdom] with x hx
    change ‖g (f x)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (hgn _)]
    exact hx
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hpair]
  exact integral_mono_ae hi hpair.integral_prod_left hdom

/-- Transfer the fourth-order square-exponential remainder through genuine
Jensen symmetrization, retaining its quadratic cancellation. -/
theorem square_remainder_symmetrization {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 κ) (hm : (∫ x, f x ∂κ) = 0) (A C : ℝ) (hA : 0 ≤ A)
    (hpairE : Integrable (fun z : X × X => Real.exp (A*(f z.1-f z.2)^2)) (κ.prod κ))
    (hpairB : (∫ z : X × X, Real.exp (A*(f z.1-f z.2)^2) ∂κ.prod κ)-1-
      A*(∫ z : X × X, (f z.1-f z.2)^2 ∂κ.prod κ) ≤ C) :
    Integrable (fun x => Real.exp (A*f x^2)) κ ∧
    (∫ x, Real.exp (A*f x^2) ∂κ)-1-A*(∫ x, f x^2 ∂κ) ≤ C := by
  have hdLp : MemLp (fun z : X × X => f z.1-f z.2) 2 (κ.prod κ) :=
    (hf.comp_fst κ).sub (hf.comp_snd κ)
  have hdI : Integrable (fun z : X × X => (f z.1-f z.2)^2) (κ.prod κ) := hdLp.integrable_sq
  have hRpair : Integrable (fun z : X × X => squareExpRemainder A (f z.1-f z.2)) (κ.prod κ) :=
    (hpairE.sub (integrable_const (1 : ℝ))).sub (hdI.const_mul A)
  have hsym := centered_convex_symmetrization κ f hfm (hf.integrable (by norm_num)) hm
    (squareExpRemainder A) (squareExpRemainder_continuous A) (squareExpRemainder_convex A hA)
    (fun x => squareExpRemainder_nonneg A x hA) hRpair
  have hsqI := hf.integrable_sq
  have he (x : X) : Real.exp (A*f x^2) = squareExpRemainder A (f x)+1+A*f x^2 := by
    dsimp [squareExpRemainder]
    ring
  have hi : Integrable (fun x => Real.exp (A*f x^2)) κ := by
    simp_rw [he]
    exact (hsym.1.add (integrable_const _)).add (hsqI.const_mul A)
  refine ⟨hi, ?_⟩
  have hR (x : X) : squareExpRemainder A (f x) = Real.exp (A*f x^2)-1-A*f x^2 := rfl
  have hRd (z : X × X) : squareExpRemainder A (f z.1-f z.2) = Real.exp
      (A*(f z.1-f z.2)^2)-1-A*(f z.1-f z.2)^2 := rfl
  simp_rw [hR, hRd] at hsym
  rw [integral_sub (f := fun x => Real.exp (A*f x^2)-1) (hi.sub (integrable_const _)) (hsqI.const_mul A),
    integral_sub hi (integrable_const _), integral_const_mul,
    integral_sub (f := fun z : X × X => Real.exp (A*(f z.1-f z.2)^2)-1)
      (hpairE.sub (integrable_const _)) (hdI.const_mul A),
    integral_sub hpairE (integrable_const _), integral_const_mul] at hsym
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hsym
  exact hsym.2.trans hpairB

end
end SparseSGD.Logistic
