import SparseSGD.Scaling.ActivityClock
import SparseSGD.Scaling.LSLoadLimits

open Filter Topology MeasureTheory
namespace SparseSGD.Scaling
noncomputable section
set_option maxHeartbeats 1200000

/-- Batch rounding with its correct realized constant, including sigma=0. -/
theorem scaledBatch_realized_ratio_tendsto
    (b sigma : ℝ) (hb : 0 < b) (hs : 0 ≤ sigma) :
    Tendsto (fun d : ℕ => (scaledBatch b sigma d : ℝ)/
      (realizedBatchScale b sigma*(d : ℝ)^sigma)) atTop (𝓝 1) := by
  rcases eq_or_lt_of_le hs with hz | hs
  · have hs0 : sigma=0 := hz.symm
    subst sigma
    have H (d : ℕ) : (scaledBatch b 0 d : ℝ)/(realizedBatchScale b 0*(d : ℝ)^(0 : ℝ))=1 := by
      simp only [Real.rpow_zero,mul_one,realizedBatchScale,ite_true,scaledBatch_zero_eq_fixed]
      exact div_self (by exact_mod_cast (fixedRealizedBatch_pos b).ne')
    simpa only [H] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  · simpa [realizedBatchScale,hs.ne'] using scaledBatch_ratio_tendsto b sigma hb hs

/-- Actual batch sparsity has one affine exponent on both sides of every
bookkeeping line, with the fixed-batch correction retained. -/
theorem actual_batch_product_ratio
    (pStar kappa b sigma : ℝ) (p : ℕ → unitInterval)
    (hp : 0 < pStar) (hb : 0 < b) (hs : 0 ≤ sigma)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d) :
    Tendsto (fun d => (p d : ℝ)*(scaledBatch b sigma d : ℝ)/
      (realizedBatchScale b sigma*pStar*(d : ℝ)^(sigma-kappa))) atTop (𝓝 1) := by
  apply (scaledBatch_realized_ratio_tendsto b sigma hb hs).congr'
  filter_upwards [hpd,eventually_gt_atTop (0 : ℕ)] with d hd hd0
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd0
  have hpow : (d : ℝ)^(sigma-kappa)=(d : ℝ)^sigma*(d : ℝ)^(-kappa) := by
    rw [← Real.rpow_add hdR]
    congr 1 <;> ring
  rw [hd,scaledSparsity,hpow]
  field_simp [(Real.rpow_pos_of_pos hdR (-kappa)).ne']
  <;> ring

/-- Sparse actual batches: activity has the nominal product scale for all
nonnegative integer batch exponents. -/
theorem actual_sparse_activity_ratio
    (pStar kappa b sigma : ℝ) (p : ℕ → unitInterval)
    (hp : 0 < pStar) (hb : 0 < b) (hs : 0 ≤ sigma) (hks : sigma<kappa)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d) :
    Tendsto (fun d => batchActivity (p d) (scaledBatch b sigma d)/
      (realizedBatchScale b sigma*pStar*(d : ℝ)^(sigma-kappa))) atTop (𝓝 1) := by
  have Hratio := actual_batch_product_ratio pStar kappa b sigma p hp hb hs hpd
  have hconst : 0 < realizedBatchScale b sigma*pStar := mul_pos (realizedBatchScale_pos b sigma hb) hp
  have hprod : Tendsto (fun d => (p d : ℝ)*(scaledBatch b sigma d : ℝ)) atTop (𝓝 0) := by
    have H := (powerScale_tendsto_zero (realizedBatchScale b sigma*pStar) (sigma-kappa) hconst (by linarith)).mul Hratio
    apply (show Tendsto (fun d : ℕ => (realizedBatchScale b sigma*pStar*(d : ℝ)^(sigma-kappa))*
      ((p d : ℝ)*(scaledBatch b sigma d : ℝ)/(realizedBatchScale b sigma*pStar*(d : ℝ)^(sigma-kappa)))) atTop (𝓝 0) by simpa using H).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
    exact mul_div_cancel₀ _ (by positivity)
  have hprops : ∀ᶠ d in atTop, 0 < (p d : ℝ) ∧ (p d : ℝ) ≤ 1 ∧ 0 < scaledBatch b sigma d := by
    filter_upwards [hpd,eventually_gt_atTop (0 : ℕ)] with d hd hd0
    exact ⟨by rw [hd]; exact scaledSparsity_pos_of_pos pStar kappa d hp hd0,
      (p d).property.2,integerBatch_pos b sigma d⟩
  have H := (batchActivity_ratio_tendsto_one (fun d => (p d : ℝ)) (scaledBatch b sigma) hprod hprops).mul Hratio
  apply (show Tendsto _ atTop (𝓝 (1 : ℝ)) by simpa using H).congr'
  filter_upwards [hprops] with d hd
  exact div_mul_div_cancel₀ (mul_ne_zero hd.1.ne' (by exact_mod_cast hd.2.2.ne'))

/-- Dense actual batches are active with probability tending to one. -/
theorem actual_dense_activity_tendsto_one
    (pStar kappa b sigma : ℝ) (p : ℕ → unitInterval)
    (hp : 0 < pStar) (hb : 0 < b) (hs : 0 ≤ sigma) (hks : kappa<sigma)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d) :
    Tendsto (fun d => batchActivity (p d) (scaledBatch b sigma d)) atTop (𝓝 1) := by
  have Hratio := actual_batch_product_ratio pStar kappa b sigma p hp hb hs hpd
  have hconst : 0 < realizedBatchScale b sigma*pStar := mul_pos (realizedBatchScale_pos b sigma hb) hp
  have hprod : Tendsto (fun d => (p d : ℝ)*(scaledBatch b sigma d : ℝ)) atTop atTop := by
    have H := (powerScale_tendsto_atTop (realizedBatchScale b sigma*pStar) (sigma-kappa) hconst (by linarith)).atTop_mul_pos (by norm_num : (0 : ℝ)<1) Hratio
    apply H.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
    exact mul_div_cancel₀ _ (by positivity)
  exact batchActivity_tendsto_one_of_product_atTop _ _ hprod
    (Eventually.of_forall (fun d => (p d).property))

/-- The memoryless threshold is the sign of gamma+sigma-kappa, including
fixed batches and arbitrary admissible actual probability families. -/
theorem actual_sparse_activity_clock_ratio
    (pStar kappa b sigma epsStar gamma : ℝ) (p : ℕ → unitInterval)
    (hp : 0 < pStar) (hb : 0 < b) (hs : 0 ≤ sigma) (he : 0 < epsStar)
    (hks : sigma<kappa)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d) :
    Tendsto (fun d => (batchActivity (p d) (scaledBatch b sigma d)/scaledRetention epsStar gamma d)/
      ((realizedBatchScale b sigma*pStar/epsStar)*(d : ℝ)^(gamma+sigma-kappa))) atTop (𝓝 1) := by
  apply (actual_sparse_activity_ratio pStar kappa b sigma p hp hb hs hks hpd).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [div_div]
  congr 1
  unfold scaledRetention
  calc
    realizedBatchScale b sigma*pStar*(d : ℝ)^(sigma-kappa) =
        realizedBatchScale b sigma*pStar*((d : ℝ)^(-gamma)*(d : ℝ)^(gamma+sigma-kappa)) := by
      rw [← Real.rpow_add hdR]
      congr 2
      ring
    _ = _ := by field_simp

end
end SparseSGD.Scaling
