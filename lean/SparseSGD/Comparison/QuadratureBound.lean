import SparseSGD.Comparison.Geometric
import Mathlib.Analysis.Complex.RemovableSingularity

open Set
open scoped Topology ComplexOrder

namespace SparseSGD
noncomputable section

private def expSlope : ℂ → ℂ := dslope Complex.exp 0
private def expSlope₂ : ℂ → ℂ := dslope expSlope 0

private theorem expSlope_zero : expSlope 0 = 1 := by
  simp [expSlope, Complex.deriv_exp]

private theorem expSlope_differentiable : Differentiable ℂ expSlope := by
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).mpr
    Complex.differentiable_exp.differentiableOn

private theorem expSlope₂_continuous : Continuous expSlope₂ := by
  apply Differentiable.continuous (𝕜 := ℂ)
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).mpr
    expSlope_differentiable.differentiableOn

theorem exp_ne_one_of_small_im {y : ℂ} (hy : y ≠ 0)
    (him : |y.im| < 2 * Real.pi) : Complex.exp y ≠ 1 := by
  intro he
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
  have him' : |(n : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
    rw [hn] at him
    simpa [Complex.mul_im, abs_mul, abs_of_pos Real.pi_pos] using him
  have hnsmall : |(n : ℝ)| < 1 := by nlinarith [Real.pi_pos]
  have hnzero : n = 0 := by
    have h := abs_lt.mp hnsmall
    have h' : (-1 : ℤ) < n ∧ n < 1 := by exact_mod_cast h
    omega
  apply hy
  simpa [hnzero] using hn

private theorem expSlope_ne_zero {y : ℂ} (him : |y.im| < 2 * Real.pi) :
    expSlope y ≠ 0 := by
  by_cases hy : y = 0
  · simpa [hy, expSlope_zero]
  have he := exp_ne_one_of_small_im hy him
  simp [expSlope, dslope_of_ne _ hy, slope, he, hy, sub_ne_zero.mpr he]

private theorem m_eq_expSlope_inv (y : ℂ) : m y = (expSlope y)⁻¹ := by
  by_cases hy : y = 0
  · simp [hy, expSlope_zero]
  · simp [m, hy, expSlope, dslope_of_ne _ hy, slope, div_eq_mul_inv, mul_comm]

private theorem m_sub_one_factor {y : ℂ} (him : |y.im| < 2 * Real.pi) :
    m y - 1 = y * (-expSlope₂ y / expSlope y) := by
  have hs : y * expSlope₂ y = expSlope y - 1 := by
    simpa [expSlope₂, expSlope_zero] using sub_smul_dslope expSlope 0 y
  rw [m_eq_expSlope_inv]
  have he := expSlope_ne_zero him
  field_simp
  linear_combination hs

/-- The quantitative compact-strip estimate in Lemma `lem:quad`.
The constant depends only on the distance from the first nonzero aliasing poles. -/
theorem quadrature_factor_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℂ,
      |y.re| ≤ 3 → |y.im| ≤ 2 * Real.pi - δ → ‖m y - 1‖ ≤ C * ‖y‖ := by
  let K : Set ℂ := Set.Icc (-3 : ℝ) 3 ×ℂ Set.Icc (-(2 * Real.pi - δ)) (2 * Real.pi - δ)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have him {y : ℂ} (hy : y ∈ K) : |y.im| < 2 * Real.pi := by
    have hi : y.im ∈ Set.Icc (-(2 * Real.pi - δ)) (2 * Real.pi - δ) := hy.2
    have ha : |y.im| ≤ 2 * Real.pi - δ := abs_le.mpr hi
    linarith
  have hc : ContinuousOn (fun y => -expSlope₂ y / expSlope y) K :=
    expSlope₂_continuous.neg.continuousOn.div expSlope_differentiable.continuous.continuousOn
      (fun y hy => expSlope_ne_zero (him hy))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro y hre himag
  have hy : y ∈ K := ⟨abs_le.mp hre, abs_le.mp himag⟩
  rw [m_sub_one_factor (him hy), norm_mul]
  calc
    ‖y‖ * ‖-expSlope₂ y / expSlope y‖ ≤ ‖y‖ * max C 0 :=
      mul_le_mul_of_nonneg_left ((hC y hy).trans (le_max_left _ _)) (norm_nonneg _)
    _ = max C 0 * ‖y‖ := mul_comm _ _

/-- Uniform exponential-pair quadrature on a strip away from aliasing. -/
theorem exponential_pair_quadrature_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu lambda : ℂ) (h : ℝ) (k : ℕ),
      0 < h → |((lambda - mu) * (h : ℂ)).re| ≤ 3 →
      |((lambda - mu) * (h : ℂ)).im| ≤ 2 * Real.pi - δ →
      ‖sampledPairSum mu lambda (h : ℂ) k - pairIntegral mu lambda (k * h)‖ ≤
        C * h * ‖Complex.exp (lambda * ((k * h : ℝ) : ℂ)) -
          Complex.exp (mu * ((k * h : ℝ) : ℂ))‖ := by
  obtain ⟨C, hC0, hC⟩ := quadrature_factor_bound δ hδ
  refine ⟨C, hC0, ?_⟩
  intro mu lambda h k hh hre him
  let y := (lambda - mu) * (h : ℂ)
  have hyim : |y.im| < 2 * Real.pi := by dsimp [y]; linarith
  have hpole : y = 0 ∨ Complex.exp y ≠ 1 := by
    by_cases hy : y = 0
    · exact Or.inl hy
    · exact Or.inr (exp_ne_one_of_small_im hy hyim)
  rw [sampled_pair_sum_quadrature mu lambda h k hpole]
  by_cases heq : mu = lambda
  · subst lambda
    simp
  have hdiff : lambda - mu ≠ 0 := sub_ne_zero.mpr (Ne.symm heq)
  have hn : 0 < ‖lambda - mu‖ := norm_pos_iff.mpr hdiff
  rw [← sub_one_mul, norm_mul]
  apply le_trans (mul_le_mul_of_nonneg_right (hC y hre him) (norm_nonneg _))
  rw [pair_integral_closed mu lambda (k*h) heq, norm_div]
  have hy : ‖y‖ = ‖lambda - mu‖ * h := by
    simp [y, norm_mul, Complex.norm_real, abs_of_pos hh]
  rw [hy]
  apply le_of_eq
  field_simp
  <;> ring

theorem exponential_pair_quadrature_bound_stable (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu lambda : ℂ) (h : ℝ) (k : ℕ),
      mu.re ≤ 0 → lambda.re ≤ 0 → 0 < h →
      |((lambda - mu) * (h : ℂ)).re| ≤ 3 →
      |((lambda - mu) * (h : ℂ)).im| ≤ 2 * Real.pi - δ →
      ‖sampledPairSum mu lambda (h : ℂ) k - pairIntegral mu lambda (k*h)‖ ≤ 2*C*h := by
  obtain ⟨C, hC0, hC⟩ := exponential_pair_quadrature_bound δ hδ
  refine ⟨C, hC0, ?_⟩
  intro mu lambda h k hmu hlam hh hre him
  apply le_trans (hC mu lambda h k hh hre him)
  have hT : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
  have hexp (z : ℂ) (hz : z.re ≤ 0) :
      ‖Complex.exp (z * ((k*h : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simpa using mul_nonpos_of_nonpos_of_nonneg hz hT
  have hnorm : ‖Complex.exp (lambda * ((k*h : ℝ) : ℂ)) -
      Complex.exp (mu * ((k*h : ℝ) : ℂ))‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by linarith [hexp lambda hlam, hexp mu hmu])
  nlinarith [mul_le_mul_of_nonneg_left hnorm (mul_nonneg hC0 hh.le)]

end
end SparseSGD
