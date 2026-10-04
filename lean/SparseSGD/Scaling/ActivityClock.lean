import SparseSGD.Scaling.BatchActivityLaw
import SparseSGD.Scaling.RetentionClock

open Filter Topology
namespace SparseSGD.Scaling
noncomputable section

theorem sparse_activity_retention_clock
    (pStar kappa bStar sigma epsStar gamma : ℝ)
    (hp : 0 < pStar) (hb : 0 < bStar) (hs : 0 < sigma) (hk : 0 < kappa)
    (he : 0 < epsStar) (hks : sigma < kappa) :
    Tendsto (fun d : ℕ =>
      (batchActivity (scaledProbabilityFamily pStar kappa d) (scaledBatch bStar sigma d) /
        scaledRetention epsStar gamma d) /
        ((bStar*pStar/epsStar)*(d : ℝ)^(gamma+sigma-kappa))) atTop (𝓝 1) := by
  have H1 := scaled_batch_activity_sparse_ratio_tendsto_one pStar kappa bStar sigma hp hb hs hk hks
  have H2 := scaled_batch_probability_product_ratio_tendsto_one pStar kappa bStar sigma hp hb hs hk
  have H := H1.mul H2
  simp only [mul_one] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hPB : (scaledProbabilityFamily pStar kappa d : ℝ)*(scaledBatch bStar sigma d : ℝ) ≠ 0 :=
    mul_ne_zero (scaledProbabilityFamily_pos pStar kappa d hp hd).ne'
      (by exact_mod_cast (integerBatch_pos bStar sigma d).ne')
  rw [div_mul_div_cancel₀ hPB,div_div]
  congr 1
  unfold scaledRetention
  calc
    bStar*pStar*(d : ℝ)^(sigma-kappa) =
        bStar*pStar*((d : ℝ)^(-gamma)*(d : ℝ)^(gamma+sigma-kappa)) := by
      rw [← Real.rpow_add hdR]
      congr 2
      ring
    _ = _ := by field_simp

end
end SparseSGD.Scaling
