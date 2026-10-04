import SparseSGD.Foundations

namespace SparseSGD

theorem Params.det_meanMatrix (p : Params) : p.meanMatrix.det = p.beta := by
  simp [Params.meanMatrix, Matrix.det_fin_two]
  ring

theorem Params.step_cov (p : Params) (s : Moments) :
    (p.step s).cov = p.meanMatrix * s.cov * p.meanMatrix.transpose +
      (2 * p.w * p.eps * (p.noise * s.R + p.additive)) • Matrix.vecMulVec kick kick := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Params.step, Moments.cov, Params.meanMatrix, Params.eps, kick,
      Matrix.vecMulVec, Matrix.vecMul, dotProduct,
      Matrix.transpose_apply, Fin.sum_univ_two] <;> ring

theorem Params.trajectory_cov_noiseFree (p : Params) (s : Moments)
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (n : ℕ) :
    (p.trajectory s n).cov = (p.meanMatrix ^ n) * s.cov * (p.meanMatrix ^ n).transpose := by
  induction n with
  | zero => simp [Params.trajectory]
  | succ n ih =>
      rw [Params.trajectory, Params.step_cov, ih]
      simp only [hnoise, hadd, zero_mul, mul_zero, zero_smul, add_zero]
      rw [pow_succ']
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem Params.det_trajectory_cov_noiseFree (p : Params) (s : Moments)
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (n : ℕ) :
    ((p.trajectory s n).cov).det = p.beta ^ (2 * n) * s.cov.det := by
  rw [Params.trajectory_cov_noiseFree p s hnoise hadd n]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_pow, Params.det_meanMatrix]
  rw [show 2 * n = n + n by omega, pow_add]
  ring

/-- A deterministic outer-product start remains an outer product of the mean trajectory. -/
theorem Params.trajectory_cov_rankOne_noiseFree (p : Params) (s : Moments)
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (x : Fin 2 → ℝ)
    (hx : s.cov = Matrix.vecMulVec x x) (n : ℕ) :
    (p.trajectory s n).cov =
      Matrix.vecMulVec ((p.meanMatrix ^ n).mulVec x) ((p.meanMatrix ^ n).mulVec x) := by
  rw [Params.trajectory_cov_noiseFree p s hnoise hadd n, hx,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

/-- The risk of a noise-free rank-one start is exactly the squared mean error. -/
theorem Params.trajectory_R_rankOne_noiseFree (p : Params) (s : Moments)
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (x : Fin 2 → ℝ)
    (hx : s.cov = Matrix.vecMulVec x x) (n : ℕ) :
    (p.trajectory s n).R = ((p.meanMatrix ^ n).mulVec x 0) ^ 2 := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0)
    (Params.trajectory_cov_rankOne_noiseFree p s hnoise hadd x hx n)
  simpa [Moments.cov, Matrix.vecMulVec, pow_two] using h

end SparseSGD
