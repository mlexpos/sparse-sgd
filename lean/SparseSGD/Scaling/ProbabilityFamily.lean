import SparseSGD.Scaling.LeastSquaresParameters

open Filter Topology

namespace SparseSGD.Scaling
noncomputable section

def scaledProbabilityFamily (pStar kappa : ℝ) : ℕ → unitInterval := fun d =>
  ⟨min 1 (max 0 (scaledSparsity pStar kappa d)), by
    constructor
    · exact le_min (by positivity) (le_max_left _ _)
    · exact min_le_left _ _⟩

theorem scaledProbabilityFamily_pos (pStar kappa : ℝ) (d : ℕ) (hp : 0 < pStar) (hd : 0 < d) :
    0 < (scaledProbabilityFamily pStar kappa d : ℝ) := by
  change 0 < min 1 (max 0 (scaledSparsity pStar kappa d))
  have h := scaledSparsity_pos_of_pos pStar kappa d hp hd
  exact lt_min (by norm_num) (lt_of_lt_of_le h (le_max_right _ _))

theorem scaledProbabilityFamily_eq_eventually
    (pStar kappa : ℝ) (hp : 0 < pStar) (hk : 0 < kappa) :
    ∀ᶠ d : ℕ in atTop, (scaledProbabilityFamily pStar kappa d : ℝ) = scaledSparsity pStar kappa d := by
  have hpow : Tendsto (fun d : ℕ => (d : ℝ)^(-kappa)) atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop hk).comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun d : ℕ => scaledSparsity pStar kappa d) atTop (𝓝 0) := by
    simpa [scaledSparsity] using hpow.const_mul pStar
  filter_upwards [hs.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    eventually_gt_atTop (0 : ℕ)] with d hd hdNat
  have hp0 := scaledSparsity_pos_of_pos pStar kappa d hp hdNat
  change min 1 (max 0 (scaledSparsity pStar kappa d)) = scaledSparsity pStar kappa d
  rw [max_eq_right (le_of_lt hp0), min_eq_right (le_of_lt hd)]


theorem scaledProbabilityFamily_eq_eventually_fixed
    (pStar : ℝ) (hp : 0 < pStar) (hp1 : pStar ≤ 1) :
    ∀ᶠ d : ℕ in atTop, (scaledProbabilityFamily pStar 0 d : ℝ) = scaledSparsity pStar 0 d := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  have hpow : (d : ℝ)^(-(0 : ℝ)) = 1 := by
    rw [neg_zero, Real.rpow_zero]
  have hs : scaledSparsity pStar 0 d = pStar := by
    rw [scaledSparsity, hpow, mul_one]
  change min 1 (max 0 (scaledSparsity pStar 0 d)) = scaledSparsity pStar 0 d
  rw [hs, max_eq_right (le_of_lt hp), min_eq_right hp1]

end
end SparseSGD.Scaling
