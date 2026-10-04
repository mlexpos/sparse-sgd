import SparseSGD.Scaling.ProbabilityFamily
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Topology
namespace SparseSGD.Scaling
noncomputable section

def batchActivity (p : ℝ) (B : ℕ) : ℝ := 1-(1-p)^B

theorem batchActivity_union_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (B : ℕ) :
    1-(1-p)^B ≤ p*(B:ℝ) := by
  have hq0 : 0 ≤ 1-p := by linarith
  have hq1 : 1-p ≤ 1 := by linarith
  induction B with
  | zero => simp
  | succ B ih =>
    have hpowB0 : 0 ≤ (1-p)^B := pow_nonneg hq0 _
    have hpowB1 : (1-p)^B ≤ 1 := pow_le_one₀ hq0 hq1
    rw [Nat.cast_succ, pow_succ]
    have hid : 1-(1-p)^B*(1-p) = (1-(1-p)^B)+p*(1-p)^B := by ring
    rw [hid]
    have hih := ih
    nlinarith [mul_le_mul_of_nonneg_left hpowB1 hp0]

theorem batchActivity_bounds (p : ℝ) (B : ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p*(B:ℝ)/(1+p*(B:ℝ)) ≤ batchActivity p B ∧
      batchActivity p B ≤ min 1 (p*(B:ℝ)) := by
  have hq0 : 0 ≤ 1-p := by linarith
  have hq1 : 1-p ≤ 1 := by linarith
  have hpow0 : 0 ≤ (1-p)^B := pow_nonneg hq0 _
  have hpow1 : (1-p)^B ≤ 1 := (pow_le_one₀ hq0 hq1)
  have hB : 0 ≤ (B:ℝ) := Nat.cast_nonneg _
  have hbin : 1+(B:ℝ)*p ≤ (1+p)^B := by
    have := one_add_mul_le_pow (show -2 ≤ p by linarith) B
    simpa [mul_comm] using this
  have hqle : 1-p ≤ 1/(1+p) := by
    rw [le_div_iff₀ (by positivity : 0 < 1+p)]
    nlinarith [sq_nonneg p]
  have hqpow : (1-p)^B ≤ (1/(1+p))^B := pow_le_pow_left₀ hq0 hqle B
  have hinvpow : (1/(1+p))^B = 1/(1+p)^B := by rw [one_div_pow]
  have hpowle : 1/(1+p)^B ≤ 1/(1+(B:ℝ)*p) := by
    rw [div_le_div_iff₀ (by positivity : 0 < (1+p)^B) (by positivity : 0 < 1+(B:ℝ)*p)]
    nlinarith [hbin]
  have hlower : (1-p)^B ≤ 1/(1+p*(B:ℝ)) := by
    rw [show p*(B:ℝ)=(B:ℝ)*p by ring]
    exact hqpow.trans (hinvpow ▸ hpowle)
  have hl : p*(B:ℝ)/(1+p*(B:ℝ)) ≤ 1-(1-p)^B := by
    rw [div_le_iff₀ (by positivity : 0 < 1+p*(B:ℝ))]
    have hmul := mul_le_mul_of_nonneg_right hlower (by positivity : 0 ≤ 1+p*(B:ℝ))
    have hden : 1+p*(B:ℝ) ≠ 0 := by positivity
    have hmul' : (1-p)^B*(1+p*(B:ℝ)) ≤ 1 := by
      calc
        _ ≤ (1+p*(B:ℝ))⁻¹*(1+p*(B:ℝ)) := by simpa [div_eq_mul_inv] using hmul
        _ = 1 := by field_simp
    nlinarith [hmul']
  have hu1 : 1-(1-p)^B ≤ 1 := by linarith
  have huB := batchActivity_union_bound p hp0 hp1 B
  exact ⟨hl, le_min hu1 huB⟩


theorem batchActivity_ratio_tendsto_one
    (p : ℕ → ℝ) (B : ℕ → ℕ) (hBp : Tendsto (fun d => p d*(B d:ℝ)) atTop (𝓝 0))
    (hprops : ∀ᶠ d : ℕ in atTop, 0 < p d ∧ p d ≤ 1 ∧ 0 < B d) :
    Tendsto (fun d => batchActivity (p d) (B d) / (p d * B d))
      atTop (𝓝 1) := by
  let x := fun d : ℕ => p d * (B d : ℝ)
  have hx : Tendsto x atTop (𝓝 0) := by
    have heq : x =ᶠ[atTop] fun d => p d*B d := by
      filter_upwards [hprops] with d ⟨hp,hple,hB⟩
      simp [x]
    exact hBp.congr' heq.symm
  have hlow : Tendsto (fun d => 1/(1+x d)) atTop (𝓝 1) := by
    have hden : Tendsto (fun d => 1+x d) atTop (𝓝 1) := by simpa [x] using tendsto_const_nhds.add hx
    simpa using hden.inv₀ (by norm_num : (1:ℝ)≠0)
  have hratio : Tendsto (fun d => batchActivity (p d) (B d)/x d) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun d => 1/(1+x d)) (h := fun _ => 1)
    · exact hlow
    · exact tendsto_const_nhds
    · filter_upwards [hprops] with d ⟨hp,hple,hB⟩
      have hb := batchActivity_bounds (p d) (B d) hp.le hple
      have hxpos : 0 < x d := by dsimp [x]; exact mul_pos hp (by exact_mod_cast hB)
      calc
        1/(1+x d) = (x d/(1+x d))/(x d) := by field_simp
        _ ≤ batchActivity (p d) (B d)/(x d) := div_le_div_of_nonneg_right hb.1 hxpos.le
    · filter_upwards [hprops] with d ⟨hp,hple,hB⟩
      have hxpos : 0 < x d := by dsimp [x]; exact mul_pos hp (by exact_mod_cast hB)
      have hb := batchActivity_bounds (p d) (B d) hp.le hple
      have hbupper : batchActivity (p d) (B d) ≤ x d := by
        exact (le_trans hb.2 (min_le_right _ _))
      exact (div_le_one hxpos).2 hbupper
  have heq : (fun d => batchActivity (p d) (B d)/x d) =ᶠ[atTop]
      (fun d => batchActivity (p d) (B d) /
        (p d*(B d:ℝ))) := Filter.Eventually.of_forall (fun d => rfl)
  exact hratio.congr' heq.symm

theorem batchActivity_tendsto_one_of_product_atTop
    (p : ℕ → ℝ) (B : ℕ → ℕ) (hprod : Tendsto (fun d => p d*(B d:ℝ)) atTop atTop)
    (hprops : ∀ᶠ d : ℕ in atTop, 0 ≤ p d ∧ p d ≤ 1) :
    Tendsto (fun d => batchActivity (p d) (B d)) atTop (𝓝 1) := by
  have hlow : Tendsto (fun d => (p d*(B d:ℝ))/(1+p d*(B d:ℝ))) atTop (𝓝 1) := by
    have hrec : Tendsto (fun d => 1/(1+p d*(B d:ℝ))) atTop (𝓝 0) := by
      have hsum : Tendsto (fun d => 1+p d*(B d:ℝ)) atTop atTop :=
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).add_atTop hprod
      have hrecInv : Tendsto (fun d => (1+p d*(B d:ℝ))⁻¹) atTop (𝓝 0) := by
        convert (tendsto_inv_atTop_zero.comp hsum) using 1 <;> rfl
      simpa [one_div] using hrecInv
    have hid : (fun d => (p d*(B d:ℝ))/(1+p d*(B d:ℝ))) =ᶠ[atTop]
        fun d => 1-1/(1+p d*(B d:ℝ)) := by
      filter_upwards [hprops] with d ⟨hp0,hp1⟩
      have hden : 0 < 1+p d*(B d:ℝ) := by positivity
      field_simp [ne_of_gt hden]
      <;> ring
    have h := (tendsto_const_nhds.sub hrec).congr' hid.symm
    simpa using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun d => (p d*(B d:ℝ))/(1+p d*(B d:ℝ)))
    (h := fun _ => 1)
  · exact hlow
  · exact tendsto_const_nhds
  · filter_upwards [hprops] with d ⟨hp0,hp1⟩
    exact (batchActivity_bounds (p d) (B d) hp0 hp1).1
  · filter_upwards [hprops] with d ⟨hp0,hp1⟩
    exact le_trans (batchActivity_bounds (p d) (B d) hp0 hp1).2 (min_le_left _ _)


/-- The rounded batch and a clamped probability family retain the nominal
    product power whenever sigma and kappa are positive. -/
theorem scaled_batch_probability_product_ratio_tendsto_one
    (pStar kappa bStar sigma : ℝ) (hp : 0 < pStar) (hb : 0 < bStar)
    (hs : 0 < sigma) (hk : 0 < kappa) :
    Tendsto (fun d : ℕ =>
      (scaledProbabilityFamily pStar kappa d : ℝ) * (scaledBatch bStar sigma d : ℝ) /
        (bStar*pStar*(d:ℝ)^(sigma-kappa))) atTop (𝓝 1) := by
  have hbRatio := scaledBatch_ratio_tendsto bStar sigma hb hs
  have hEq : (fun d : ℕ =>
      (scaledProbabilityFamily pStar kappa d : ℝ) * (scaledBatch bStar sigma d : ℝ) /
        (bStar*pStar*(d:ℝ)^(sigma-kappa))) =ᶠ[atTop]
      (fun d => (scaledBatch bStar sigma d : ℝ)/(bStar*(d:ℝ)^sigma)) := by
    filter_upwards [scaledProbabilityFamily_eq_eventually pStar kappa hp hk,
      eventually_gt_atTop (0:ℕ)] with d hprob hd
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    have hpow : (d:ℝ)^(sigma-kappa) = (d:ℝ)^sigma * (d:ℝ)^(-kappa) := by
      rw [← Real.rpow_add hdR]; congr 1 <;> ring
    rw [hprob, scaledSparsity, hpow]
    have hrpow : (d:ℝ)^(-kappa) ≠ 0 := (Real.rpow_pos_of_pos hdR _).ne'
    have hnom : bStar*pStar ≠ 0 := mul_ne_zero hb.ne' hp.ne'
    field_simp [hrpow, hnom]
    <;> ring
  exact hbRatio.congr' hEq.symm

/-- In the sparse regime, the actual activity has the same first-order
    asymptotic as the unrounded product Bp. -/
theorem scaled_batch_activity_sparse_ratio_tendsto_one
    (pStar kappa bStar sigma : ℝ) (hp : 0 < pStar) (hb : 0 < bStar)
    (hs : 0 < sigma) (hk : 0 < kappa) (hks : sigma < kappa) :
    Tendsto (fun d : ℕ =>
      batchActivity (scaledProbabilityFamily pStar kappa d)
        (scaledBatch bStar sigma d) /
        ((scaledProbabilityFamily pStar kappa d : ℝ) * (scaledBatch bStar sigma d : ℝ)))
      atTop (𝓝 1) := by
  have hratio := scaled_batch_probability_product_ratio_tendsto_one pStar kappa bStar sigma hp hb hs hk
  have hpow : Tendsto (fun d : ℕ => (d:ℝ)^(sigma-kappa)) atTop (𝓝 0) := by
    have hpos : 0 < kappa-sigma := by linarith
    have h := (tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop
    have heq : (fun d : ℕ => (d:ℝ)^(sigma-kappa)) =ᶠ[atTop]
        (fun d => ((fun x : ℝ => x ^ (-(kappa-sigma))) ∘ (fun n : ℕ => (n:ℝ))) d) := by
      filter_upwards [] with d
      change (d:ℝ)^(sigma-kappa) = (d:ℝ)^(-(kappa-sigma))
      rw [show sigma-kappa = -(kappa-sigma) by ring]
    exact h.congr' heq.symm
  have hnom : Tendsto (fun d : ℕ => bStar*pStar*(d:ℝ)^(sigma-kappa)) atTop (𝓝 0) :=
    by simpa using hpow.const_mul (bStar*pStar)
  have hBp : Tendsto (fun d : ℕ =>
      (scaledProbabilityFamily pStar kappa d : ℝ) * (scaledBatch bStar sigma d : ℝ))
      atTop (𝓝 0) := by
    have h := hnom.mul hratio
    have heq : (fun d : ℕ => bStar*pStar*(d:ℝ)^(sigma-kappa) *
        ((scaledProbabilityFamily pStar kappa d : ℝ)*(scaledBatch bStar sigma d : ℝ)/
          (bStar*pStar*(d:ℝ)^(sigma-kappa)))) =ᶠ[atTop]
      (fun d => (scaledProbabilityFamily pStar kappa d : ℝ)*(scaledBatch bStar sigma d : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
      have hdR : (0:ℝ)<d := by exact_mod_cast hd
      have hn : bStar*pStar*(d:ℝ)^(sigma-kappa) ≠ 0 := mul_ne_zero (mul_ne_zero hb.ne' hp.ne') (Real.rpow_pos_of_pos hdR _).ne'
      field_simp
    simpa using h.congr' heq
  have hprops : ∀ᶠ d : ℕ in atTop,
      0 < (scaledProbabilityFamily pStar kappa d : ℝ) ∧
      (scaledProbabilityFamily pStar kappa d : ℝ) ≤ 1 ∧ 0 < scaledBatch bStar sigma d := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    exact ⟨scaledProbabilityFamily_pos pStar kappa d hp hd, (scaledProbabilityFamily pStar kappa d).property.2,
      integerBatch_pos bStar sigma d⟩
  exact batchActivity_ratio_tendsto_one _ _ hBp hprops

theorem batchActivity_lower_comparable (p : ℝ) (B : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    min 1 (p*(B:ℝ)) / 2 ≤ batchActivity p B := by
  have hb := batchActivity_bounds p B hp0 hp1
  have hx : 0 ≤ p*(B:ℝ) := mul_nonneg hp0 (Nat.cast_nonneg _)
  by_cases hle : p*(B:ℝ) ≤ 1
  · have hden : 0 < 1+p*(B:ℝ) := by positivity
    have hnum : p*(B:ℝ) / 2 ≤ p*(B:ℝ)/(1+p*(B:ℝ)) := by
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ)<2) hden]
      nlinarith
    rw [min_eq_right hle]
    exact hnum.trans hb.1
  · have hge : 1 ≤ p*(B:ℝ) := le_of_not_ge hle
    have hden : 0 < 1+p*(B:ℝ) := by positivity
    have hnum : (1:ℝ)/2 ≤ p*(B:ℝ)/(1+p*(B:ℝ)) := by
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ)<2) hden]
      nlinarith
    rw [min_eq_left hge]
    exact hnum.trans hb.1

end
end SparseSGD.Scaling
