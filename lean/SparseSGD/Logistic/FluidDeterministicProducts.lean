import SparseSGD.Logistic.FluidDeterministicFree
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1500000

def matchedJacobianProduct (J : ℕ → (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ)) :
    ℕ → (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ)
  | 0 => 1
  | n+1 => J n * matchedJacobianProduct J n

private theorem matchedJacobianProduct_duhamel
    (F : (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ))
    (J : ℕ → (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ)) (n : ℕ) :
    matchedJacobianProduct J n = F^n +
      ∑ i ∈ Finset.range n, F^(n-1-i)*((J i-F)*matchedJacobianProduct J i) := by
  induction n with
  | zero => simp [matchedJacobianProduct]
  | succ n ih =>
    have hrec : matchedJacobianProduct J (n+1) =
        F*matchedJacobianProduct J n+(J n-F)*matchedJacobianProduct J n := by
      simp only [matchedJacobianProduct,sub_mul]
      abel
    rw [hrec,ih,mul_add,Finset.mul_sum,Finset.sum_range_succ]
    have he : ∑ i ∈ Finset.range n, F*(F^(n-1-i)*((J i-F)*matchedJacobianProduct J i)) =
        ∑ i ∈ Finset.range n, F^(n+1-1-i)*((J i-F)*matchedJacobianProduct J i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have he : n+1-1-i = (n-1-i)+1 := by omega
      rw [he,pow_succ']
      simp only [mul_assoc]
    rw [he]
    simp [pow_succ',add_assoc,← ih]

private theorem matched_geometric_envelope (M e : ℝ) (n : ℕ) :
    M+M*e*(∑ i ∈ Finset.range n, M*(1+M*e)^i) = M*(1+M*e)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,pow_succ]; nlinarith

/-- A bounded fast semigroup remains uniformly bounded over a finite slow
clock after an O(e) perturbation at each step. -/
theorem matchedJacobianProduct_perturbation_bound
    (F : (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ))
    (J : ℕ → (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ))
    (M e : ℝ) (hM : 1≤M) (he : 0≤e)
    (hF : ∀ n : ℕ, ‖F^n‖≤M) (hJ : ∀ n : ℕ, ‖J n-F‖≤e) (n : ℕ) :
    ‖matchedJacobianProduct J n‖≤M*Real.exp (M*e*n) := by
  have hM0 : 0≤M := by linarith
  have ha : 0≤1+M*e := by positivity
  have hbound : ∀ n : ℕ, ‖matchedJacobianProduct J n‖≤M*(1+M*e)^n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rw [matchedJacobianProduct_duhamel F J n]
      apply (norm_add_le _ _).trans
      calc
        ‖F^n‖+‖∑ i ∈ Finset.range n, F^(n-1-i)*((J i-F)*matchedJacobianProduct J i)‖
          ≤ M+∑ i ∈ Finset.range n, M*e*(M*(1+M*e)^i) := by
            apply add_le_add (hF n)
            apply (norm_sum_le _ _).trans
            apply Finset.sum_le_sum
            intro i hi
            have hi' := Finset.mem_range.mp hi
            calc
              ‖F^(n-1-i)*((J i-F)*matchedJacobianProduct J i)‖
                ≤ ‖F^(n-1-i)‖*(‖J i-F‖*‖matchedJacobianProduct J i‖) :=
                  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
              _ ≤ M*(e*(M*(1+M*e)^i)) := by
                gcongr
                · exact hF _
                · exact hJ i
                · exact ih i hi'
              _ = M*e*(M*(1+M*e)^i) := by ring
        _ = M*(1+M*e)^n := by rw [← Finset.mul_sum,matched_geometric_envelope]
  apply (hbound n).trans
  apply mul_le_mul_of_nonneg_left _ hM0
  calc
    (1+M*e)^n ≤ (Real.exp (M*e))^n := by
      apply pow_le_pow_left₀ ha
      linarith [Real.add_one_le_exp (M*e)]
    _ = Real.exp (M*e*n) := by rw [← Real.exp_nat_mul]; congr 1; ring
end
end SparseSGD.Logistic
