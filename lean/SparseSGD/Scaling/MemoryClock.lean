import SparseSGD.Scaling.ActivityFamily

open Filter Topology
namespace SparseSGD.Scaling
noncomputable section

/-- General conversion from a proved power ratio to the three possible limits. -/
theorem power_ratio_sign_limits (f : ℕ → ℝ) (c e : ℝ) (hc : 0 < c)
    (h : Tendsto (fun d : ℕ => f d/(c*(d : ℝ)^e)) atTop (𝓝 1)) :
    (e<0 → Tendsto f atTop (𝓝 0)) ∧
    (e=0 → Tendsto f atTop (𝓝 c)) ∧
    (0<e → Tendsto f atTop atTop) := by
  have heq : (fun d : ℕ => (f d/(c*(d : ℝ)^e))*(c*(d : ℝ)^e)) =ᶠ[atTop] f := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
    exact div_mul_cancel₀ _ (by positivity)
  refine ⟨?_,?_,?_⟩
  · intro he
    exact product_to_zero h (powerScale_tendsto_zero c e hc he) heq
  · intro he
    subst e
    simpa using product_to_finite h (powerScale_tendsto_const c) heq
  · intro he
    exact product_to_atTop h (by norm_num) (powerScale_tendsto_atTop c e hc he) heq

/-- The actual sparse-batch memory/gap ratio changes order only in the
bookkeeping conversion, at gamma=kappa-sigma. -/
theorem actual_sparse_memory_threshold
    (pStar kappa b sigma epsStar gamma : ℝ) (p : ℕ → unitInterval)
    (hp : 0 < pStar) (hb : 0 < b) (hs : 0 ≤ sigma) (he : 0 < epsStar)
    (hks : sigma<kappa)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d) :
    (gamma<kappa-sigma →
      Tendsto (fun d => batchActivity (p d) (scaledBatch b sigma d)/scaledRetention epsStar gamma d)
        atTop (𝓝 0)) ∧
    (gamma=kappa-sigma →
      Tendsto (fun d => batchActivity (p d) (scaledBatch b sigma d)/scaledRetention epsStar gamma d)
        atTop (𝓝 (realizedBatchScale b sigma*pStar/epsStar))) ∧
    (kappa-sigma<gamma →
      Tendsto (fun d => batchActivity (p d) (scaledBatch b sigma d)/scaledRetention epsStar gamma d)
        atTop atTop) := by
  have hconst : 0 < realizedBatchScale b sigma*pStar/epsStar :=
    div_pos (mul_pos (realizedBatchScale_pos b sigma hb) hp) he
  have H := power_ratio_sign_limits _ (realizedBatchScale b sigma*pStar/epsStar) (gamma+sigma-kappa)
    hconst (actual_sparse_activity_clock_ratio pStar kappa b sigma epsStar gamma p hp hb hs he hks hpd)
  exact ⟨fun h => H.1 (by linarith),fun h => H.2.1 (by linarith),fun h => H.2.2 (by linarith)⟩

end
end SparseSGD.Scaling
