import SparseSGD.Discrete.Algebra

namespace SparseSGD

noncomputable section

def discreteMean (beta w : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - w, -beta; w, beta]

theorem discreteMean_eq_meanMatrix (p : Params) :
    discreteMean p.beta p.w = p.meanMatrix := rfl

def discreteKernelLyapunov (beta w : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let curvature := w / (2 * (1 + beta))
  let r := 1 / (2 * w * (1 - beta) * (1 - curvature))
  !![r, -w * r / (1 + beta); -w * r / (1 + beta), 2 * w * r / (1 + beta)]

theorem discrete_kernel_lyapunov_identity (beta w : ℝ)
    (hw : w ≠ 0) (heps : 1 - beta ≠ 0) (hplus : 1 + beta ≠ 0)
    (hcurv : 1 - w / (2 * (1 + beta)) ≠ 0) :
    discreteKernelLyapunov beta w -
        discreteMean beta w * discreteKernelLyapunov beta w * (discreteMean beta w).transpose =
      Matrix.vecMulVec kick kick := by
  have hden : 2 * (1 + beta) - w ≠ 0 := by
    intro hh
    apply hcurv
    field_simp [hplus]
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [discreteKernelLyapunov, discreteMean, kick, Matrix.vecMulVec,
      Matrix.vecMul, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two] <;>
    field_simp [hw, heps, hplus, hcurv, hden] <;> ring

end
end SparseSGD
