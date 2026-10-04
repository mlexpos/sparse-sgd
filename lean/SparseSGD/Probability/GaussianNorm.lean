import SparseSGD.Probability.GaussianProduct

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Probability

theorem standardGaussianProduct_norm_inner_sq {d : ℕ} (e : Fin d → ℝ) :
    ∫ x : Fin d → ℝ,
      (∑ i : Fin d, (x i) ^ 2) * (∑ j : Fin d, x j * e j) ^ 2
        ∂standardGaussianProduct d = (d + 2) * ∑ j : Fin d, (e j) ^ 2 := by
  classical
  let μ := standardGaussianProduct d
  let F (i j k : Fin d) (x : Fin d → ℝ) := (x k) ^ 2 * x j * e j * x i * e i
  have hF (i j k : Fin d) : Integrable (F i j k) μ := by
    simpa [F, μ, mul_assoc, mul_left_comm, mul_comm] using
      (standardGaussianProduct_mixed_integrable k j i).const_mul (e j * e i)
  have hK (i j : Fin d) : Integrable (fun x => ∑ k : Fin d, F i j k x) μ :=
    integrable_finsetSum Finset.univ (by intro k hk; exact hF i j k)
  have hJ (i : Fin d) : Integrable (fun x => ∑ j : Fin d, ∑ k : Fin d, F i j k x) μ :=
    integrable_finsetSum Finset.univ (by intro j hj; exact hK i j)
  have hI : Integrable (fun x => ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, F i j k x) μ :=
    integrable_finsetSum Finset.univ (by intro i hi; exact hJ i)
  have hexpand (x : Fin d → ℝ) :
      (∑ i : Fin d, (x i) ^ 2) * (∑ j : Fin d, x j * e j) ^ 2 =
        ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, F i j k x := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    simp [F]
    ring
  calc
    ∫ x : Fin d → ℝ,
      (∑ i : Fin d, (x i) ^ 2) * (∑ j : Fin d, x j * e j) ^ 2 ∂μ =
        ∫ x, ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, F i j k x ∂μ := by
          congr 1
          funext x
          exact hexpand x
    _ = ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∫ x, F i j k x ∂μ := by
          rw [integral_finsetSum Finset.univ (by intro i hi; exact hJ i)]
          apply Finset.sum_congr rfl
          intro i hi
          rw [integral_finsetSum Finset.univ (by intro j hj; exact hK i j)]
          apply Finset.sum_congr rfl
          intro j hj
          rw [integral_finsetSum Finset.univ (by intro k hk; exact hF i j k)]
    _ = ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
          (e j * e i) * (if j = i then (if k = j then 3 else 1) else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro k hk
          have hfactor : F i j k = fun x => (e j * e i) * ((x k) ^ 2 * x j * x i) := by
            funext x
            dsimp [F]
            ring
          rw [hfactor, integral_const_mul]
          dsimp [μ]
          rw [standardGaussianProduct_mixed_moment k j i]
    _ = (d + 2) * ∑ j : Fin d, (e j) ^ 2 := by
          have hsum (i : Fin d) :
              (∑ k : Fin d, if k = i then (e i) ^ 2 * 3 else (e i) ^ 2) =
                (d + 2) * (e i) ^ 2 := by
            calc
              _ = ∑ k : Fin d, ((e i) ^ 2 + (if k = i then 2 * (e i) ^ 2 else 0)) := by
                apply Finset.sum_congr rfl
                intro k hk
                split_ifs <;> ring
              _ = _ := by
                simp [Finset.sum_add_distrib]
                ring
          simp [Finset.sum_ite_eq', Finset.sum_ite_irrel]
          simp_rw [← pow_two, hsum]
          rw [← Finset.mul_sum]

end SparseSGD.Probability
