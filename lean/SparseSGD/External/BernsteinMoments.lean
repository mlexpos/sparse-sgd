import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.MGFAnalytic
import SparseSGD.Probability.GaussianProduct

open MeasureTheory ProbabilityTheory

namespace SparseSGD.External
noncomputable section

/-- The standard Bernstein moment implication (BLM 2013, Theorem 2.10),
with conservative constants after centering an uncentered variable.
The raw moment assumption implies centered moments bounded by
`n! * a * (2*c)^n` by Jensen and `|x-y|^n ≤ 2^(n-1)(|x|^n+|y|^n)`.
This reusable scalar certificate contains no logistic or batch assertion. -/
structure BernsteinMomentsCertificate (X : Type*) [MeasurableSpace X] : Prop where
  centered_mgf : ∀ (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ) (a c t : ℝ),
    Measurable f → Integrable f κ → 0 ≤ a → 0 < c →
    (∀ n : ℕ, 2 ≤ n → Integrable (fun x => |f x|^n) κ) →
    (∀ n : ℕ, 2 ≤ n → (∫ x, |f x|^n ∂κ) ≤ (n.factorial : ℝ)*a*c^n) →
    |t| * (2*c) < 1 →
    Integrable (fun x => Real.exp (t*(f x - ∫ y, f y ∂κ))) κ ∧
    (∫ x, Real.exp (t*(f x - ∫ y, f y ∂κ)) ∂κ) ≤
      Real.exp (t^2*(8*a*c^2)/(2*(1-|t| * (2*c))))

/-- Hoeffding's lemma for a centered random variable supported in `[-1,1]`.
This standard scalar input is used globally in the Laplace parameter when
turning a rare count MGF into its square-exponential bound. -/
structure HoeffdingCertificate (X : Type*) [MeasurableSpace X] : Prop where
  centered_mgf : ∀ (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ) (t : ℝ),
    Measurable f → Integrable f κ → (∫ x, f x ∂κ) = 0 → (∀ x, |f x| ≤ 1) →
    Integrable (fun x => Real.exp (t*f x)) κ ∧
    (∫ x, Real.exp (t*f x) ∂κ) ≤ Real.exp (t^2/2)

/-- Standard Gaussian quadratic exponential formulas. The first field is
the centered chi-square MGF bound (BLM 2013, Section 2.4). The second is the
elementary Gaussian integral `E[Z² exp(Z²/4)] = 2√2 ≤ 4`. Neither field
mentions logistic residuals, a random mixing variance, or a batch. -/
structure GaussianQuadraticCertificate : Prop where
  norm_mgf : ∀ (d : ℕ) (t : ℝ), 2*|t| < 1 →
    Integrable (fun z : Fin d → ℝ => Real.exp
      (t*(‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin d))‖^2-(d : ℝ))))
        (SparseSGD.Probability.standardGaussianProduct d) ∧
    (∫ z : Fin d → ℝ, Real.exp
      (t*(‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin d))‖^2-(d : ℝ)))
      ∂SparseSGD.Probability.standardGaussianProduct d) ≤
      Real.exp ((d : ℝ)*t^2/(1-2*|t|))
  tilted_second : Integrable (fun z : ℝ => z^2*Real.exp (z^2/4)) (gaussianReal 0 1) ∧
    (∫ z : ℝ, z^2*Real.exp (z^2/4) ∂gaussianReal 0 1) ≤ 4

/-- The iid averaging rule is proved from the actual finite product law.
It divides both the variance factor and scale by the batch size. -/
theorem iid_average_mgf {X : Type*} [MeasurableSpace X] (κ : Measure X)
    [IsProbabilityMeasure κ] (f : X → ℝ) (B : ℕ) (hB : 0 < B) (v M t : ℝ)
    (hM : 0 ≤ M) (ht : |t| * (M/(B : ℝ)) < 1)
    (hmgf : ∀ s : ℝ, |s| * M < 1 →
      Integrable (fun x => Real.exp (s*f x)) κ ∧
      (∫ x, Real.exp (s*f x) ∂κ) ≤ Real.exp (s^2*v/(2*(1-|s| * M)))) :
    Integrable (fun a : Fin B → X => Real.exp (t*((B : ℝ)⁻¹*∑ i, f (a i))))
      (Measure.pi (fun _ : Fin B => κ)) ∧
    (∫ a : Fin B → X, Real.exp (t*((B : ℝ)⁻¹*∑ i, f (a i)))
      ∂Measure.pi (fun _ : Fin B => κ)) ≤
      Real.exp (t^2*(v/(B : ℝ))/(2*(1-|t| * (M/(B : ℝ))))) := by
  classical
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hs : |t/(B : ℝ)| * M < 1 := by
    rw [abs_div, abs_of_pos hb]
    convert ht using 1 <;> field_simp <;> ring
  have hh := hmgf (t/B) hs
  have he (a : Fin B → X) : Real.exp (t*((B : ℝ)⁻¹*∑ i, f (a i))) =
      ∏ i, Real.exp ((t/B)*f (a i)) := by
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.mul_sum]
    simp only [div_eq_mul_inv, mul_assoc]
  simp_rw [he]
  refine ⟨Integrable.fintype_prod (fun _ => hh.1), ?_⟩
  rw [integral_fintype_prod_eq_prod (fun _ : Fin B => fun x : X => Real.exp ((t/B)*f x))]
  have hp := Finset.prod_le_prod₀ (s := Finset.univ)
    (f := fun _ : Fin B => ∫ x, Real.exp ((t/B)*f x) ∂κ)
    (g := fun _ : Fin B => Real.exp ((t/B)^2*v/(2*(1-|t/B| * M))))
    (fun _ _ => integral_nonneg (fun _ => (Real.exp_pos _).le)) (fun _ _ => hh.2)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp ⊢
  refine hp.trans_eq ?_
  rw [← Real.exp_nat_mul]
  congr 1
  rw [abs_div, abs_of_pos hb]
  field_simp
  <;> ring

end
end SparseSGD.External
