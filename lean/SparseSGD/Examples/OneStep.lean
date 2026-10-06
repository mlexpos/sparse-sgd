import SparseSGD.Discrete.Algebra
import SparseSGD.Discrete.Positivity
import SparseSGD.Probability.GaussianMoments

namespace SparseSGD.Examples
noncomputable section

/-- A concrete autoformalization task: start with unit error and zero momentum,
retention 3/4, curvature step 1/4, noise feedback 1/8 and ambient temperature 1/16.
The next risk is 75/128 and the covariance determinant is strictly positive. -/
def sampleParams : Params := ⟨3/4, 1/4, 1/8, 1/16⟩
def coldStart : Moments := ⟨1, 0, 0⟩

theorem sample_step : sampleParams.step coldStart = ⟨75/128, 11/128, 21/128⟩ := by
  apply Moments.ext <;> norm_num [sampleParams, coldStart, Params.step, Params.eps]

theorem sample_rankDefect : (sampleParams.step coldStart).rankDefect = 3/128 := by
  rw [sample_step]
  norm_num [Moments.rankDefect]

theorem sample_full_rank : 0 < (sampleParams.step coldStart).cov.det := by
  rw [← Moments.rankDefect_eq_cov_det, sample_rankDefect]
  norm_num

end
end SparseSGD.Examples
