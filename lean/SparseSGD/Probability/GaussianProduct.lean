import SparseSGD.Probability.GaussianMoments
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Probability
noncomputable section

def standardGaussianProduct (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ : Fin d => ProbabilityTheory.gaussianReal 0 1)

instance standardGaussianProduct_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (standardGaussianProduct d) := by
  unfold standardGaussianProduct
  infer_instance

/-- Every coordinate monomial of the product Gaussian is integrable. -/
theorem standardGaussianProduct_monomial_integrable {d : ℕ} (n : Fin d → ℕ) :
    Integrable (fun x : Fin d → ℝ => ∏ i, x i ^ n i) (standardGaussianProduct d) := by
  exact Integrable.fintype_prod (fun i => gaussianReal_integrable_pow 0 1 (n i))

theorem standardGaussianProduct_integral_monomial {d : ℕ} (n : Fin d → ℕ) :
    (∫ x : Fin d → ℝ, ∏ i, x i ^ n i ∂standardGaussianProduct d) =
      ∏ i, ∫ t : ℝ, t ^ n i ∂ProbabilityTheory.gaussianReal 0 1 :=
  integral_fintype_prod_eq_prod (fun i t => t ^ n i)

theorem standardGaussianProduct_covariance {d : ℕ} (i j : Fin d) :
    ∫ x, x i * x j ∂standardGaussianProduct d = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    let f : Fin d → ℝ → ℝ := fun k t => if k = i then t ^ 2 else 1
    have hfun (x : Fin d → ℝ) : x i * x i = ∏ k, f k (x k) := by
      simp [f, pow_two]
    rw [show (fun x : Fin d → ℝ => x i * x i) = fun x => ∏ k, f k (x k) from funext hfun]
    rw [standardGaussianProduct, integral_fintype_prod_eq_prod]
    simp only
    apply Finset.prod_eq_one
    intro k hk
    by_cases hki : k = i <;> simp [f, hki, gaussianReal_standard_second_moment]
  · let f : Fin d → ℝ → ℝ := fun k t =>
      (if k = i then t else 1) * (if k = j then t else 1)
    have hfun (x : Fin d → ℝ) : x i * x j = ∏ k, f k (x k) := by
      simp only [f, Finset.prod_mul_distrib]
      simp
    rw [show (fun x : Fin d → ℝ => x i * x j) = fun x => ∏ k, f k (x k) from funext hfun]
    rw [standardGaussianProduct, integral_fintype_prod_eq_prod]
    have hprod : (∏ k : Fin d, ∫ t, f k t ∂ProbabilityTheory.gaussianReal 0 1) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [f, hij]
    simpa [hij] using hprod

theorem standardGaussianProduct_mixed_fourth {d : ℕ} (i j : Fin d) :
    ∫ x, (x i) ^ 2 * (x j) ^ 2 ∂standardGaussianProduct d = if i = j then 3 else 1 := by
  classical
  by_cases hij : i = j
  · subst j
    let f : Fin d → ℝ → ℝ := fun k t => if k = i then t ^ 4 else 1
    have hfun (x : Fin d → ℝ) : (x i) ^ 2 * (x i) ^ 2 = ∏ k, f k (x k) := by
      simp [f]
      ring
    rw [show (fun x : Fin d → ℝ => (x i) ^ 2 * (x i) ^ 2) =
      fun x => ∏ k, f k (x k) from funext hfun]
    rw [standardGaussianProduct, integral_fintype_prod_eq_prod]
    have hInt (k : Fin d) :
        (∫ t, f k t ∂ProbabilityTheory.gaussianReal 0 1) = if k = i then 3 else 1 := by
      by_cases hki : k = i <;> simp [f, hki, gaussianReal_standard_fourth_moment]
    simp_rw [hInt]
    simp
  · let f : Fin d → ℝ → ℝ := fun k t =>
      (if k = i then t ^ 2 else 1) * (if k = j then t ^ 2 else 1)
    have hfun (x : Fin d → ℝ) : (x i) ^ 2 * (x j) ^ 2 = ∏ k, f k (x k) := by
      simp only [f, Finset.prod_mul_distrib]
      simp
    rw [show (fun x : Fin d → ℝ => (x i) ^ 2 * (x j) ^ 2) =
      fun x => ∏ k, f k (x k) from funext hfun]
    rw [standardGaussianProduct, integral_fintype_prod_eq_prod]
    have hprod :
        (∏ k : Fin d, ∫ t, f k t ∂ProbabilityTheory.gaussianReal 0 1) = 1 := by
      apply Finset.prod_eq_one
      intro k hk
      by_cases hki : k = i
      · subst k
        simp [f, hij, gaussianReal_standard_second_moment]
      · by_cases hkj : k = j
        · subst k
          simp [f, Ne.symm hij, gaussianReal_standard_second_moment]
        · simp [f, hki, hkj]
    simpa [hij] using hprod

/-- The off-diagonal fourth-moment terms vanish, including repeated `i`. -/
theorem standardGaussianProduct_mixed_offDiagonal {d : ℕ} (i j k : Fin d)
    (hjk : j ≠ k) :
    ∫ x, (x i) ^ 2 * x j * x k ∂standardGaussianProduct d = 0 := by
  classical
  let f : Fin d → ℝ → ℝ := fun l t =>
    (if l = i then t ^ 2 else 1) * (if l = j then t else 1) *
      (if l = k then t else 1)
  have hfun (x : Fin d → ℝ) : (x i) ^ 2 * x j * x k = ∏ l, f l (x l) := by
    simp only [f, Finset.prod_mul_distrib]
    simp
  rw [show (fun x : Fin d → ℝ => (x i) ^ 2 * x j * x k) =
      fun x => ∏ l, f l (x l) from funext hfun]
  rw [standardGaussianProduct, integral_fintype_prod_eq_prod]
  by_cases hij : i = j
  · subst j
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [f, Ne.symm hjk]
  · apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [f, Ne.symm hij, hjk]

theorem standardGaussianProduct_mixed_integrable {d : ℕ} (i j k : Fin d) :
    Integrable (fun x : Fin d → ℝ => (x i) ^ 2 * x j * x k)
      (standardGaussianProduct d) := by
  classical
  let n : Fin d → ℕ := fun l =>
    (if l = i then 2 else 0) + (if l = j then 1 else 0) + (if l = k then 1 else 0)
  have hfun (x : Fin d → ℝ) : (x i) ^ 2 * x j * x k = ∏ l, x l ^ n l := by
    simp only [n, pow_add]
    have hi (l : Fin d) : x l ^ (if l = i then 2 else 0) =
        if l = i then (x l) ^ 2 else 1 := by split_ifs <;> simp
    have hj (l : Fin d) : x l ^ (if l = j then 1 else 0) =
        if l = j then x l else 1 := by split_ifs <;> simp
    have hk (l : Fin d) : x l ^ (if l = k then 1 else 0) =
        if l = k then x l else 1 := by split_ifs <;> simp
    simp_rw [hi, hj, hk]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp
  rw [show (fun x : Fin d → ℝ => (x i) ^ 2 * x j * x k) =
      fun x => ∏ l, x l ^ n l from funext hfun]
  exact standardGaussianProduct_monomial_integrable n

/-- The complete mixed fourth-moment formula used in the Gaussian oracle calculation. -/
theorem standardGaussianProduct_mixed_moment {d : ℕ} (i j k : Fin d) :
    (∫ x, (x i) ^ 2 * x j * x k ∂standardGaussianProduct d) =
      if j = k then (if i = j then 3 else 1) else 0 := by
  classical
  by_cases hjk : j = k
  · subst k
    simp only [ite_true]
    convert standardGaussianProduct_mixed_fourth i j using 1
    congr 1
    funext x
    ring
  · simpa [hjk] using standardGaussianProduct_mixed_offDiagonal i j k hjk

end

end SparseSGD.Probability
