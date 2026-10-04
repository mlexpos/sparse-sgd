import SparseSGD.Foundations

/-! Hilbert-space algebra for one moment update. -/
namespace SparseSGD

def gramMoments {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e m : E) : Moments :=
  ⟨‖e‖ ^ 2, ‖m‖ ^ 2, inner ℝ e m⟩

theorem gramMoments_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Params) (e m ξ : E) (c : ℝ)
    (heξ : inner ℝ e ξ = 0) (hmξ : inner ℝ m ξ = 0)
    (hc : c ^ 2 * ‖ξ‖ ^ 2 =
      2 * p.w * p.eps * (p.noise * ‖e‖ ^ 2 + p.additive)) :
    gramMoments ((1-p.w) • e - p.beta • m - c • ξ)
        (p.w • e + p.beta • m + c • ξ) =
      p.step (gramMoments e m) := by
  apply Moments.ext
  · simp only [gramMoments, Params.step, Params.eps]
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm,
      real_inner_self_eq_norm_sq, heξ, hmξ]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [Params.eps] at hc
    nlinarith [hc]
  · simp only [gramMoments, Params.step, Params.eps]
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm,
      real_inner_self_eq_norm_sq, heξ, hmξ]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [Params.eps] at hc
    nlinarith [hc]
  · simp only [gramMoments, Params.step, Params.eps]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm,
      real_inner_self_eq_norm_sq, heξ, hmξ]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [Params.eps] at hc
    rw [hc]
    ring

end SparseSGD
