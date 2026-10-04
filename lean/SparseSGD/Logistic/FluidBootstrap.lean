import SparseSGD.Foundations

/-! Deterministic quadratic-error bootstrap used in fluid estimates. -/
namespace SparseSGD.Logistic

theorem fluidBootstrap {e : ℕ → ℝ} {lambda a : ℝ} {K : ℕ}
    (he_nonneg : ∀ k, 0 ≤ e k) (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (he0 : e 0 = 0)
    (hrec : ∀ k ≤ K, (∀ j < k, e j ≤ 2 * lambda) →
      e k ≤ lambda + a * ∑ j ∈ Finset.range k, (e j) ^ 2)
    (hsmall : 4 * a * K * lambda ≤ 1) :
    ∀ k ≤ K, e k ≤ 2 * lambda := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hbase : e 0 ≤ 2 * lambda := by rw [he0]; linarith
    have hprev : ∀ j < k, e j ≤ 2 * lambda := by
      intro j hj
      by_cases hzero : j = 0
      · simpa [hzero] using hbase
      · exact ih j hj (by omega)
    have hstep := hrec k hk hprev
    have hconst : ∀ n : ℕ, (∑ j ∈ Finset.range n, (2 * lambda) ^ 2) =
        n * (4 * lambda ^ 2) := by
      intro n
      induction n with
      | zero => simp
      | succ n hn =>
        rw [Finset.sum_range_succ, hn]
        simp only [Nat.cast_succ]
        ring
    have hsum : (∑ j ∈ Finset.range k, (e j) ^ 2) ≤ k * (4 * lambda ^ 2) := by
      calc
        (∑ j ∈ Finset.range k, (e j) ^ 2) ≤
            ∑ j ∈ Finset.range k, (2 * lambda) ^ 2 := by
              apply Finset.sum_le_sum
              intro j hj
              have hjk : j < k := Finset.mem_range.mp hj
              have hjlo := he_nonneg j
              have hjhi := hprev j hjk
              nlinarith [mul_nonneg hjlo (sub_nonneg.mpr hjhi)]
        _ = k * (4 * lambda ^ 2) := hconst k
    calc
      e k ≤ lambda + a * ∑ j ∈ Finset.range k, (e j) ^ 2 := hstep
      _ ≤ lambda + a * (k * (4 * lambda ^ 2)) := by
            nlinarith [mul_le_mul_of_nonneg_left hsum ha]
      _ ≤ lambda + lambda := by
            have hk' : (k : ℝ) ≤ K := by exact_mod_cast hk
            have hprod : a * (k * (4 * lambda ^ 2)) ≤ lambda := by
              calc
                a * (k * (4 * lambda ^ 2)) ≤ a * (K * (4 * lambda ^ 2)) := by
                  gcongr
                _ = (4 * a * K * lambda) * lambda := by ring
                _ ≤ lambda := by
                  nlinarith [mul_le_mul_of_nonneg_right hsmall hlambda]
            linarith
      _ = 2 * lambda := by ring

theorem fluidBootstrap_of_parameters {e : ℕ → ℝ} {lambda Gamma L2 : ℝ} {K : ℕ}
    (he_nonneg : ∀ k, 0 ≤ e k) (hlambda : 0 ≤ lambda)
    (hGamma : 0 ≤ Gamma) (hL2 : 0 ≤ L2) (he0 : e 0 = 0)
    (hrec : ∀ k ≤ K, (∀ j < k, e j ≤ 2 * lambda) →
      e k ≤ lambda + (Gamma * L2 / 2) * ∑ j ∈ Finset.range k, (e j) ^ 2)
    (hsmall : 2 * K * Gamma * L2 * lambda ≤ 1) :
    ∀ k ≤ K, e k ≤ 2 * lambda := by
  have ha : 0 ≤ Gamma * L2 / 2 := by positivity
  apply fluidBootstrap he_nonneg hlambda ha he0
  · intro k hk hprev
    exact hrec k hk hprev
  · calc
      4 * (Gamma * L2 / 2) * K * lambda = 2 * K * Gamma * L2 * lambda := by ring
      _ ≤ 1 := hsmall

end SparseSGD.Logistic
