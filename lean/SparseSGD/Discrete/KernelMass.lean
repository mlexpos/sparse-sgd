import SparseSGD.Discrete.Lyapunov
import SparseSGD.Discrete.Renewal

namespace SparseSGD

noncomputable section

theorem discrete_kernel_finite_telescope (beta w : ℝ)
    (hw : w ≠ 0) (heps : 1 - beta ≠ 0) (hplus : 1 + beta ≠ 0)
    (hcurv : 1 - w / (2 * (1 + beta)) ≠ 0) (k : ℕ) :
    (∑ n ∈ Finset.range k,
      (discreteMean beta w ^ n) * Matrix.vecMulVec kick kick *
        (discreteMean beta w ^ n).transpose) =
      discreteKernelLyapunov beta w -
        (discreteMean beta w ^ k) * discreteKernelLyapunov beta w *
          (discreteMean beta w ^ k).transpose := by
  let F := discreteMean beta w
  let X := discreteKernelLyapunov beta w
  have hlyap : X - F * X * F.transpose = Matrix.vecMulVec kick kick := by
    simpa [F, X] using discrete_kernel_lyapunov_identity beta w hw heps hplus hcurv
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hterm :
          F ^ k * Matrix.vecMulVec kick kick * (F ^ k).transpose =
            F ^ k * X * (F ^ k).transpose - F ^ (k + 1) * X * (F ^ (k + 1)).transpose := by
        rw [← hlyap]
        rw [Matrix.mul_sub, Matrix.sub_mul]
        rw [pow_succ]
        simp only [Matrix.transpose_mul]
        noncomm_ring
      rw [hterm]
      rw [pow_succ]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      abel

/-- The finite scalar kernel mass is the Lyapunov mass minus its propagated remainder. -/
theorem kickResponse_sq_partial_sum (p : Params)
    (hw : p.w ≠ 0) (heps : 1 - p.beta ≠ 0) (hplus : 1 + p.beta ≠ 0)
    (hcurv : 1 - p.curvature ≠ 0) (k : ℕ) :
    (∑ n ∈ Finset.range k, (kickResponse p n) ^ 2) =
      (discreteKernelLyapunov p.beta p.w) 0 0 -
        ((p.meanMatrix ^ k) * discreteKernelLyapunov p.beta p.w *
          (p.meanMatrix ^ k).transpose) 0 0 := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0)
    (discrete_kernel_finite_telescope p.beta p.w hw heps hplus hcurv k)
  simp only [discreteMean_eq_meanMatrix, Matrix.sum_apply, Matrix.sub_apply,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
    Matrix.vecMulVec_apply] at h
  simpa only [kickResponse, pow_two] using h

/-- Power decay makes the propagated Lyapunov remainder vanish, giving the exact kernel mass. -/
theorem kickResponse_sq_hasSum (p : Params)
    (hw : p.w ≠ 0) (heps : 1 - p.beta ≠ 0) (hplus : 1 + p.beta ≠ 0)
    (hcurv : 1 - p.curvature ≠ 0)
    (hdecay : Filter.Tendsto (fun k : ℕ => p.meanMatrix ^ k)
      Filter.atTop (nhds 0)) :
    HasSum (fun n => (kickResponse p n) ^ 2)
      (1 / (2 * p.w * (1 - p.beta) * (1 - p.curvature))) := by
  have hcont : Continuous (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
      (M * discreteKernelLyapunov p.beta p.w * M.transpose) 0 0) := by
    fun_prop
  have hrem : Filter.Tendsto (fun k : ℕ =>
      ((p.meanMatrix ^ k) * discreteKernelLyapunov p.beta p.w *
        (p.meanMatrix ^ k).transpose) 0 0) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, zero_mul, Matrix.zero_apply] using
      (hcont.tendsto 0).comp hdecay
  apply (hasSum_iff_tendsto_nat_of_nonneg (kickResponse_sq_nonneg p) _).2
  have hlim := (tendsto_const_nhds (x := (discreteKernelLyapunov p.beta p.w) 0 0)).sub hrem
  simpa only [sub_zero, kickResponse_sq_partial_sum p hw heps hplus hcurv,
    discreteKernelLyapunov, Params.curvature, Matrix.of_apply, Matrix.cons_val_zero] using hlim

/-- The renewal kernel normalized by the one-step noise factor has mass `1/(1-curvature)`. -/
theorem Params.renewal_kernel_hasSum (p : Params)
    (hw : p.w ≠ 0) (heps : 1 - p.beta ≠ 0) (hplus : 1 + p.beta ≠ 0)
    (hcurv : 1 - p.curvature ≠ 0)
    (hdecay : Filter.Tendsto (fun k : ℕ => p.meanMatrix ^ k)
      Filter.atTop (nhds 0)) :
    HasSum (fun n => 2 * p.w * p.eps * (kickResponse p n) ^ 2)
      (1 / (1 - p.curvature)) := by
  have h := (kickResponse_sq_hasSum p hw heps hplus hcurv hdecay).mul_left
    (2 * p.w * p.eps)
  convert h using 1
  unfold Params.eps
  field_simp [hw, heps, hcurv]

end

end SparseSGD
