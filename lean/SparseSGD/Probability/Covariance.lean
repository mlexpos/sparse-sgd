import SparseSGD.Probability.GramStep

namespace SparseSGD

theorem gramMoments_cov_eq_gram {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e momentum : E) :
    (gramMoments e momentum).cov = Matrix.gram ℝ ![e, momentum] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramMoments, Moments.cov, Matrix.gram, real_inner_self_eq_norm_sq,
      real_inner_comm]

theorem gramMoments_psd {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e momentum : E) : (gramMoments e momentum).psd := by
  unfold Moments.psd
  rw [gramMoments_cov_eq_gram]
  exact Matrix.posSemidef_gram ℝ _

end SparseSGD
