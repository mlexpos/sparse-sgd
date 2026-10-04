import SparseSGD.Foundations

namespace SparseSGD

/-- A scalar renewal inequality with total kernel mass at most one. -/
theorem scalar_renewal_bound
    (h a R : ℕ → ℝ) (u phi A : ℝ)
    (hh : ∀ n, 0 ≤ h n)
    (hmass : ∀ k, (∑ n ∈ Finset.range k, h (k - n)) ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hphi : 0 ≤ phi) (hA : 0 ≤ A)
    (ha : ∀ k, a k ≤ A)
    (hrec : ∀ k, R k = a k + ∑ j ∈ Finset.range k, h (k - j) * (u * R j + phi)) :
    ∀ k, R k ≤ (A + phi) / (1 - u) := by
  let M : ℝ := (A + phi) / (1 - u)
  have hden : 0 < 1 - u := by linarith
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hM_eq : A + phi + u * M = M := by
    dsimp [M]
    field_simp
    <;> ring
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [hrec k]
    have hsum :
        (∑ j ∈ Finset.range k, h (k - j) * (u * R j + phi)) ≤
          ∑ j ∈ Finset.range k, h (k - j) * (u * M + phi) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hR : R j ≤ M := by simpa [M] using ih j hjk
      apply mul_le_mul_of_nonneg_left _ (hh (k - j))
      nlinarith
    calc
      a k + ∑ j ∈ Finset.range k, h (k - j) * (u * R j + phi)
          ≤ A + ∑ j ∈ Finset.range k, h (k - j) * (u * M + phi) := by
              exact add_le_add (ha k) hsum
      _ = A + (u * M + phi) * (∑ j ∈ Finset.range k, h (k - j)) := by
            rw [← Finset.sum_mul]
            ring
      _ ≤ A + (u * M + phi) * 1 := by
            have hp : 0 ≤ u * M + phi := by positivity
            have hprod := mul_le_mul_of_nonneg_left (hmass k) hp
            linarith
      _ = M := by linarith [hM_eq]

/-- Renewal bound for an absolute error with an additive forcing bound. -/
theorem absolute_renewal_bound
    (h D : ℕ → ℝ) (u E : ℝ)
    (hh : ∀ n, 0 ≤ h n)
    (hmass : ∀ k, (∑ n ∈ Finset.range k, h (k - n)) ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hE : 0 ≤ E)
    (hrec : ∀ k, |D k| ≤ E + u * (∑ j ∈ Finset.range k, h (k - j) * |D j|)) :
    ∀ k, |D k| ≤ E / (1 - u) := by
  let M : ℝ := E / (1 - u)
  have hden : 0 < 1 - u := by linarith
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hM_eq : E + u * M = M := by
    dsimp [M]
    field_simp
    <;> ring
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hsum :
        (∑ j ∈ Finset.range k, h (k - j) * |D j|) ≤
          ∑ j ∈ Finset.range k, h (k - j) * M := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hD : |D j| ≤ M := by simpa [M] using ih j hjk
      exact mul_le_mul_of_nonneg_left hD (hh (k - j))
    calc
      |D k| ≤ E + u * (∑ j ∈ Finset.range k, h (k - j) * |D j|) := hrec k
      _ ≤ E + u * (∑ j ∈ Finset.range k, h (k - j) * M) := by
            exact add_le_add (le_refl E) (mul_le_mul_of_nonneg_left hsum hu0)
      _ = E + u * (M * (∑ j ∈ Finset.range k, h (k - j))) := by
            rw [← Finset.sum_mul]
            ring
      _ ≤ E + u * (M * 1) := by
            have hp : 0 ≤ u * M := mul_nonneg hu0 hM0
            have hprod := mul_le_mul_of_nonneg_left (hmass k) hp
            linarith
      _ = M := by linarith [hM_eq]

end SparseSGD
