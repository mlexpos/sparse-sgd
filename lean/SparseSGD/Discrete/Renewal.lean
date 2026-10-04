import SparseSGD.Discrete.Algebra

namespace SparseSGD

/-- The first-coordinate response of the mean dynamics to the noise direction. -/
def kickResponse (p : Params) (n : ℕ) : ℝ := ((p.meanMatrix ^ n).mulVec kick) 0

@[simp] theorem kickResponse_zero (p : Params) : kickResponse p 0 = -1 := by
  simp [kickResponse, kick]

theorem kickResponse_one (p : Params) :
    kickResponse p 1 = -(1 + p.beta - p.w) := by
  simp [kickResponse, Params.meanMatrix, kick, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

/-- The two-dimensional mean matrix obeys its characteristic polynomial. -/
theorem Params.meanMatrix_cayleyHamilton (p : Params) :
    p.meanMatrix ^ 2 = (1 + p.beta - p.w) • p.meanMatrix -
      p.beta • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Params.meanMatrix, pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The impulse response satisfies the scalar recurrence determined by the mean matrix. -/
theorem kickResponse_recurrence (p : Params) (n : ℕ) :
    kickResponse p (n + 2) =
      (1 + p.beta - p.w) * kickResponse p (n + 1) - p.beta * kickResponse p n := by
  have hp : p.meanMatrix ^ (n + 2) =
      (1 + p.beta - p.w) • p.meanMatrix ^ (n + 1) - p.beta • p.meanMatrix ^ n := by
    rw [pow_add, p.meanMatrix_cayleyHamilton, mul_sub, mul_smul_comm,
      mul_smul_comm, mul_one, ← pow_succ]
  unfold kickResponse
  rw [hp, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
  simp

/-- Finite variation-of-constants formula for the covariance recursion. -/
theorem Params.trajectory_cov_unroll (p : Params) (s : Moments) (k : ℕ) :
    (p.trajectory s k).cov =
      (p.meanMatrix ^ k) * s.cov * (p.meanMatrix ^ k).transpose +
        ∑ j ∈ Finset.range k,
          (2 * p.w * p.eps * (p.noise * (p.trajectory s j).R + p.additive)) •
            ((p.meanMatrix ^ (k - 1 - j)) * Matrix.vecMulVec kick kick *
              (p.meanMatrix ^ (k - 1 - j)).transpose) := by
  induction k with
  | zero => simp [Params.trajectory]
  | succ k ih =>
      rw [Params.trajectory, Params.step_cov, ih]
      rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul,
        Finset.sum_range_succ]
      have hlast : k + 1 - 1 - k = 0 := by omega
      simp only [hlast, pow_zero, Matrix.transpose_one, one_mul, mul_one]
      rw [← add_assoc]
      congr 1
      congr 1
      · rw [pow_succ']
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      · apply Finset.sum_congr rfl
        intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        have hage : k + 1 - 1 - j = (k - 1 - j) + 1 := by omega
        rw [hage, pow_succ']
        simp only [mul_smul_comm, smul_mul_assoc, Matrix.transpose_mul,
          Matrix.mul_assoc]

theorem Params.trajectory_R_renewal (p : Params) (s : Moments) (k : ℕ) :
    (p.trajectory s k).R =
      ((p.meanMatrix ^ k) * s.cov * (p.meanMatrix ^ k).transpose) 0 0 +
        ∑ j ∈ Finset.range k,
          (2 * p.w * p.eps * (p.noise * (p.trajectory s j).R + p.additive)) *
            (kickResponse p (k - 1 - j)) ^ 2 := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0)
    (Params.trajectory_cov_unroll p s k)
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
    Matrix.vecMulVec_apply, smul_eq_mul] at h
  simpa [Moments.cov, kickResponse, pow_two] using h

theorem kickResponse_sq_nonneg (p : Params) (n : ℕ) : 0 ≤ (kickResponse p n) ^ 2 :=
  sq_nonneg _

theorem Params.renewal_kernel_nonneg (p : Params) (n : ℕ)
    (hw : 0 ≤ p.w) (he : 0 ≤ p.eps) :
    0 ≤ 2 * p.w * p.eps * (kickResponse p n) ^ 2 := by
  positivity [kickResponse_sq_nonneg p n]

end SparseSGD
