import SparseSGD.Foundations

namespace SparseSGD.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal centered errors have additive squared L2 norms. In applications
E is an L2 space; independence and centering must supply orthogonality. -/
theorem orthogonal_sum_norm_sq {B : ℕ} (v : Fin B → E)
    (hv : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · intro j _ hji
    exact hv j i hji
  · simp

/-- Exact 1/B variance reduction once the centered batch errors are pairwise
orthogonal in L2. No independence assertion is hidden in this algebraic lemma. -/
theorem batch_average_norm_sq {B : ℕ} (hB : 0 < B) (v : Fin B → E) (sigmaSq : ℝ)
    (hv : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = 0)
    (hn : ∀ i, ‖v i‖ ^ 2 = sigmaSq) :
    ‖(B : ℝ)⁻¹ • ∑ i, v i‖ ^ 2 = sigmaSq / B := by
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  rw [norm_smul, mul_pow, orthogonal_sum_norm_sq v hv]
  simp only [Real.norm_eq_abs, sq_abs]
  simp_rw [hn]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end SparseSGD.Probability
