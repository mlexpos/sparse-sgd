import SparseSGD.Scaling.ActivityFamily
import SparseSGD.Scaling.MemoryClock

open Filter Topology
namespace SparseSGD.Scaling
noncomputable section

/-- If `p` vanishes and `Bp` tends to a positive constant, Bernoulli batch
activity converges to the corresponding Poisson probability. -/
theorem batchActivity_tendsto_of_product_tendsto_pos
    (p : ℕ → ℝ) (B : ℕ → ℕ) (c : ℝ)
    (hp : Tendsto p atTop (𝓝 0))
    (hprod : Tendsto (fun d => p d * (B d : ℝ)) atTop (𝓝 c))
    (hc : 0 < c)
    (hprops : ∀ᶠ d : ℕ in atTop, 0 ≤ p d ∧ p d < 1) :
    Tendsto (fun d => batchActivity (p d) (B d)) atTop (𝓝 (1-Real.exp (-c))) := by
  have hpos : ∀ᶠ d : ℕ in atTop, 0 < p d := by
    have hprodpos := hprod.eventually (Ioi_mem_nhds hc)
    filter_upwards [hprodpos,hprops] with d hd hp
    by_contra hn
    have : p d = 0 := by linarith
    simp [this] at hd
  have hlog : Tendsto (fun d : ℕ => Real.log (1-p d)/(p d)) atTop (𝓝 (-1)) := by
    have hlower : Tendsto (fun d : ℕ => -(1-p d)⁻¹) atTop (𝓝 (-1)) := by
      have hden : Tendsto (fun d : ℕ => 1-p d) atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub hp
      have hinv := hden.inv₀ (by norm_num)
      simpa using hinv.neg
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun d => -(1-p d)⁻¹)
      (h := fun _ : ℕ => -1)
    · exact hlower
    · exact tendsto_const_nhds
    · filter_upwards [hprops,hpos] with d hpD hp0
      have hbase : 0 < 1-p d := by linarith
      have : -(1-p d)⁻¹ ≤ Real.log (1-p d)/(p d) := by
        apply (le_div_iff₀ hp0).2
        have hh := Real.one_sub_inv_le_log_of_pos hbase
        have hcalc : (-(1-p d)⁻¹) * p d = 1-(1-p d)⁻¹ := by
          field_simp [ne_of_gt hbase]
          <;> ring
        rw [hcalc]
        exact hh
      exact this
    · filter_upwards [hprops,hpos] with d hpD hp0
      have hbase : 0 < 1-p d := by linarith
      have hu := Real.log_le_sub_one_of_pos hbase
      have : Real.log (1-p d)/(p d) ≤ -1 := (div_le_iff₀ hp0).2 (by nlinarith)
      exact this
  have hexp : Tendsto (fun d : ℕ => Real.exp (Real.log (1-p d)*(B d : ℝ))) atTop (𝓝 (Real.exp (-c))) := by
    have harg : Tendsto (fun d : ℕ => (Real.log (1-p d)/(p d))*(p d*(B d:ℝ))) atTop (𝓝 ((-1)*c)) := hlog.mul hprod
    have harg' : Tendsto (fun d : ℕ => Real.log (1-p d)*(B d : ℝ)) atTop (𝓝 (-c)) := by
      have harglim : (-1)*c = -c := by ring
      rw [harglim] at harg
      apply harg.congr'
      filter_upwards [hpos] with d hd
      field_simp
    exact Real.continuous_exp.continuousAt.tendsto.comp harg'
  have hpow : (fun d : ℕ => (1-p d)^(B d)) =ᶠ[atTop]
      fun d => Real.exp (Real.log (1-p d)*(B d:ℝ)) := by
    filter_upwards [hprops] with d ⟨hp0,hp1⟩
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith : 0 < 1-p d)]
  have hactivity : (fun d : ℕ => batchActivity (p d) (B d)) =ᶠ[atTop]
      fun d => 1-Real.exp (Real.log (1-p d)*(B d:ℝ)) := by
    filter_upwards [hpow] with d hd
    simp [batchActivity,hd]
  have hlim : Tendsto (fun d : ℕ => 1-Real.exp (Real.log (1-p d)*(B d:ℝ))) atTop
      (𝓝 (1-Real.exp (-c))) := by simpa using tendsto_const_nhds.sub hexp
  exact hlim.congr' hactivity.symm

/-- A positive activity limit dominates a vanishing retention rate. -/
theorem activity_over_retention_tendsto_atTop
    (activity retention : ℕ → ℝ) (c epsStar gamma : ℝ)
    (hc : 0 < c) (heps : 0 < epsStar) (hg : 0 < gamma)
    (hactivity : Tendsto activity atTop (𝓝 c))
    (hretention : Tendsto retention atTop (𝓝 0))
    (hretpos : ∀ᶠ d in atTop, 0 < retention d) :
    Tendsto (fun d => activity d/retention d) atTop atTop := by
  have hretPos : Tendsto retention atTop (𝓝[>] (0:ℝ)) :=
    (tendsto_nhdsWithin_iff.mpr ⟨hretention,hretpos⟩)
  have hinv : Tendsto (fun d => (retention d)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hretPos
  have hactpos : ∀ᶠ d in atTop, 0 < activity d := hactivity.eventually (Ioi_mem_nhds hc)
  have hprod : Tendsto (fun d => activity d * (retention d)⁻¹) atTop atTop := by
    have hh := Filter.Tendsto.atTop_mul_pos (f := fun d => (retention d)⁻¹)
      (g := activity) hc hinv hactivity
    simpa [mul_comm] using hh
  apply hprod.congr'
  filter_upwards [hretpos] with d hd
  simp [div_eq_mul_inv]

/-- At the positive-exponent critical activity line, the actual rounded batch
has its Poisson activity limit. -/
theorem actual_critical_activity_tendsto
    (pStar bStar sigma : ℝ) (p : ℕ → unitInterval)
    (hp : 0 < pStar) (hb : 0 < bStar) (hs : 0 < sigma)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d:ℝ)=scaledSparsity pStar sigma d) :
    Tendsto (fun d => batchActivity (p d) (scaledBatch bStar sigma d)) atTop
      (𝓝 (1-Real.exp (-(bStar*pStar)))) := by
  have hsparse : Tendsto (fun d:ℕ => scaledSparsity pStar sigma d) atTop (𝓝 0) := by
    have hpw : Tendsto (fun d:ℕ => (d:ℝ)^(-sigma)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
    simpa [scaledSparsity] using hpw.const_mul pStar
  have hpLim : Tendsto (fun d => (p d:ℝ)) atTop (𝓝 0) := by
    apply hsparse.congr'
    filter_upwards [hpd] with d hd
    exact hd.symm
  have hprodRatio := actual_batch_product_ratio pStar sigma bStar sigma p hp hb (le_of_lt hs) hpd
  have hscale : Tendsto (fun d : ℕ => realizedBatchScale bStar sigma*pStar*(d:ℝ)^(sigma-sigma))
      atTop (𝓝 (bStar*pStar)) := by
    have hscl : realizedBatchScale bStar sigma=bStar := by simp [realizedBatchScale,hs.ne']
    simpa [hscl,Real.rpow_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (bStar*pStar)) atTop (𝓝 (bStar*pStar)))
  have hprod : Tendsto (fun d => (p d:ℝ)*(scaledBatch bStar sigma d:ℝ)) atTop (𝓝 (bStar*pStar)) := by
    have hm := hprodRatio.mul hscale
    have hm' : Tendsto (fun d =>
        ((p d:ℝ)*(scaledBatch bStar sigma d:ℝ))/(realizedBatchScale bStar sigma*pStar) *
          (realizedBatchScale bStar sigma*pStar)) atTop (𝓝 (bStar*pStar)) := by
      simpa [Real.rpow_zero] using hm
    apply hm'.congr'
    filter_upwards [] with d
    exact div_mul_cancel₀ _ (mul_ne_zero (realizedBatchScale_pos bStar sigma hb).ne' hp.ne')
  have hprops : ∀ᶠ d : ℕ in atTop, 0 ≤ (p d:ℝ) ∧ (p d:ℝ)<1 := by
    filter_upwards [hpLim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with d hpLt
    exact ⟨(p d).property.1,hpLt⟩
  exact batchActivity_tendsto_of_product_tendsto_pos (fun d => (p d:ℝ))
    (scaledBatch bStar sigma) (bStar*pStar) hpLim hprod (mul_pos hb hp) hprops

/-- Clamped actual probabilities have the claimed Poisson limit on the
positive-exponent critical line. -/
theorem scaled_critical_activity_tendsto
    (pStar bStar sigma : ℝ) (hp : 0 < pStar) (hb : 0 < bStar)
    (hs : 0 < sigma) :
    Tendsto (fun d => batchActivity (scaledProbabilityFamily pStar sigma d)
      (scaledBatch bStar sigma d)) atTop (𝓝 (1-Real.exp (-(bStar*pStar)))) := by
  apply actual_critical_activity_tendsto pStar bStar sigma
    (scaledProbabilityFamily pStar sigma) hp hb hs
  exact scaledProbabilityFamily_eq_eventually pStar sigma hp hs

/-- At the fixed-probability, fixed-batch corner the activity is eventually
the exact Bernoulli batch probability. -/
theorem scaled_fixed_activity_tendsto
    (pStar bStar : ℝ) (hp : 0 < pStar) (hp1 : pStar ≤ 1) :
    Tendsto (fun d => batchActivity (scaledProbabilityFamily pStar 0 d)
      (scaledBatch bStar 0 d)) atTop
      (𝓝 (1-(1-pStar)^(fixedRealizedBatch bStar))) := by
  have hprob := scaledProbabilityFamily_eq_eventually_fixed pStar hp hp1
  have hbatch : ∀ d, scaledBatch bStar 0 d = fixedRealizedBatch bStar :=
    scaledBatch_zero_eq_fixed bStar
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
    1-(1-pStar)^(fixedRealizedBatch bStar)) atTop
      (𝓝 (1-(1-pStar)^(fixedRealizedBatch bStar)))).congr'
  filter_upwards [hprob] with d hd
  rw [batchActivity, hbatch d, hd]
  simp [scaledSparsity, Real.rpow_zero]

/-- A positive limiting activity divided by a vanishing positive retention
parameter diverges. -/
theorem scaled_critical_memory_ratio_tendsto_atTop
    (pStar bStar sigma epsStar gamma : ℝ)
    (hp : 0 < pStar) (hb : 0 < bStar) (he : 0 < epsStar)
    (hs : 0 < sigma) (hg : 0 < gamma) :
    Tendsto (fun d => batchActivity (scaledProbabilityFamily pStar sigma d)
      (scaledBatch bStar sigma d)/scaledRetention epsStar gamma d) atTop atTop := by
  apply activity_over_retention_tendsto_atTop
    (fun d => batchActivity (scaledProbabilityFamily pStar sigma d)
      (scaledBatch bStar sigma d))
    (scaledRetention epsStar gamma) (1-Real.exp (-(bStar*pStar))) epsStar gamma
  · have : 0 < Real.exp (-(bStar*pStar)) := Real.exp_pos _
    have hexp : Real.exp (-(bStar*pStar)) < 1 :=
      Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hb hp))
    linarith
  · exact he
  · exact hg
  · exact scaled_critical_activity_tendsto pStar bStar sigma hp hb hs
  · exact scaledRetention_tendsto_zero epsStar gamma hg
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
    unfold scaledRetention
    exact mul_pos he (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)

/-- In the dense-batch regime activity tends to one, so for every positive
retention exponent the activity clock dominates retention. -/
theorem scaled_dense_memory_ratio_tendsto_atTop
    (pStar kappa bStar sigma epsStar gamma : ℝ)
    (hp : 0 < pStar) (hb : 0 < bStar) (he : 0 < epsStar)
    (hk : 0 ≤ kappa) (hp1 : pStar ≤ 1) (hks : kappa < sigma) (hg : 0 < gamma) :
    Tendsto (fun d => batchActivity (scaledProbabilityFamily pStar kappa d)
      (scaledBatch bStar sigma d)/scaledRetention epsStar gamma d) atTop atTop := by
  apply activity_over_retention_tendsto_atTop
    (fun d => batchActivity (scaledProbabilityFamily pStar kappa d)
      (scaledBatch bStar sigma d))
    (scaledRetention epsStar gamma) 1 epsStar gamma
  · norm_num
  · exact he
  · exact hg
  · apply actual_dense_activity_tendsto_one pStar kappa bStar sigma
      (scaledProbabilityFamily pStar kappa) hp hb (le_of_lt (by linarith)) hks
    rcases eq_or_lt_of_le hk with hk0 | hkpos
    · subst kappa
      exact scaledProbabilityFamily_eq_eventually_fixed pStar hp hp1
    · exact scaledProbabilityFamily_eq_eventually pStar kappa hp hkpos
  · exact scaledRetention_tendsto_zero epsStar gamma hg
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
    unfold scaledRetention
    exact mul_pos he (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)

/-- The same memory divergence holds at the fixed-batch corner, where the
activity probability is an exact positive constant. -/
theorem scaled_fixed_memory_ratio_tendsto_atTop
    (pStar bStar epsStar gamma : ℝ)
    (hp : 0 < pStar) (hp1 : pStar ≤ 1) (hb : 0 < bStar)
    (he : 0 < epsStar) (hg : 0 < gamma) :
    Tendsto (fun d => batchActivity (scaledProbabilityFamily pStar 0 d)
      (scaledBatch bStar 0 d)/scaledRetention epsStar gamma d) atTop atTop := by
  let c := 1-(1-pStar)^(fixedRealizedBatch bStar)
  have hc : 0 < c := by
    dsimp [c]
    have hB : 0 < fixedRealizedBatch bStar := fixedRealizedBatch_pos bStar
    have hpow : (1-pStar)^(fixedRealizedBatch bStar) < 1 := by
      exact pow_lt_one₀ (by linarith) (by linarith) (by exact_mod_cast (Nat.ne_of_gt hB))
    linarith
  apply activity_over_retention_tendsto_atTop
    (fun d => batchActivity (scaledProbabilityFamily pStar 0 d)
      (scaledBatch bStar 0 d)) (scaledRetention epsStar gamma) c epsStar gamma
  · exact hc
  · exact he
  · exact hg
  · exact scaled_fixed_activity_tendsto pStar bStar hp hp1
  · exact scaledRetention_tendsto_zero epsStar gamma hg
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
    unfold scaledRetention
    exact mul_pos he (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)

end
end SparseSGD.Scaling
