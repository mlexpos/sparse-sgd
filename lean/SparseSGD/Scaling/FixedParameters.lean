import SparseSGD.Scaling.PowerParameters

open Filter Topology

namespace SparseSGD.Scaling
noncomputable section

theorem scaledRetention_gamma_zero (epsStar : ℝ) (d : ℕ) :
    scaledRetention epsStar 0 d = epsStar := by
  simp [scaledRetention]

theorem scaledMomentum_gamma_zero (epsStar : ℝ) (d : ℕ) :
    scaledMomentum epsStar 0 d = 1 - epsStar := by
  simp [scaledMomentum, scaledRetention_gamma_zero]

theorem lsCurvature_gamma_zero_power_ratio (pStar etaStar epsStar kappa alpha : ℝ)
    (d : ℕ) (hd : 0 < d) (hp : pStar ≠ 0) (he : etaStar ≠ 0) (hr : epsStar ≠ 0) :
    lsCurvature pStar etaStar epsStar kappa 0 alpha d /
      (etaStar * epsStar * pStar * (d : ℝ) ^ (-(alpha + kappa))) = 1 := by
  simpa only [add_zero] using
    lsCurvature_power_ratio pStar etaStar epsStar kappa 0 alpha d hd hp he hr

theorem lsDelta_gamma_zero_power_ratio (pStar etaStar epsStar kappa alpha : ℝ)
    (d : ℕ) (hd : 0 < d) (hp : pStar ≠ 0) (he : etaStar ≠ 0) (hr : epsStar ≠ 0) :
    lsDelta pStar etaStar epsStar kappa 0 alpha d /
      (etaStar * pStar / epsStar * (d : ℝ) ^ (-(alpha + kappa))) = 1 := by
  have hexp : 0 - alpha - kappa = -(alpha + kappa) := by ring
  simpa only [hexp] using lsDelta_power_ratio pStar etaStar epsStar kappa 0 alpha d hd hp he hr

theorem scaledBatch_zero_eq_fixed (bStar : ℝ) (d : ℕ) :
    scaledBatch bStar 0 d = integerBatch bStar 0 0 := by
  exact integerBatch_zero_exponent_eq_fixed bStar d

def fixedRealizedBatch (bStar : ℝ) : ℕ := integerBatch bStar 0 0

theorem fixedRealizedBatch_pos (bStar : ℝ) : 0 < fixedRealizedBatch bStar :=
  integerBatch_pos bStar 0 0

theorem lsNoise_sigma_zero_ratio_eq (pStar kappa etaStar alpha bStar : ℝ)
    (d : ℕ) (hd : 0 < d) (heta : etaStar ≠ 0) :
    lsNoiseLoad pStar kappa etaStar alpha bStar 0 d /
      ((etaStar / (2 * (fixedRealizedBatch bStar : ℝ))) * (d : ℝ) ^ (1 - alpha)) =
      ((d : ℝ) + 2 - scaledSparsity pStar kappa d) / (d : ℝ) := by
  let B0 : ℝ := fixedRealizedBatch bStar
  have hBpos : B0 ≠ 0 := by
    dsimp [B0, fixedRealizedBatch]
    exact_mod_cast (fixedRealizedBatch_pos bStar).ne'
  have hbatch : scaledBatch B0 0 d = fixedRealizedBatch bStar := by
    rw [scaledBatch_zero_eq_fixed B0 d]
    change integerBatch (fixedRealizedBatch bStar : ℝ) 0 0 = fixedRealizedBatch bStar
    unfold integerBatch
    rw [Real.rpow_zero, mul_one, Nat.floor_natCast]
    exact Nat.max_eq_right (Nat.one_le_iff_ne_zero.mpr (fixedRealizedBatch_pos bStar).ne')
  have h := lsNoise_power_ratio_eq pStar kappa etaStar alpha B0 0 d hd heta hBpos
  rw [hbatch, Real.rpow_zero] at h
  have hbatchOrig : scaledBatch bStar 0 d = fixedRealizedBatch bStar :=
    scaledBatch_zero_eq_fixed bStar d
  have hload : lsNoiseLoad pStar kappa etaStar alpha bStar 0 d =
      lsNoiseLoad pStar kappa etaStar alpha B0 0 d := by
    unfold lsNoiseLoad
    rw [scaledBatch_zero_eq_fixed bStar d, hbatch]
    simp [fixedRealizedBatch]

  rw [hload]
  have hfactor : B0 / (fixedRealizedBatch bStar : ℝ) = 1 := by
    dsimp [B0]
    exact div_self (by exact_mod_cast (fixedRealizedBatch_pos bStar).ne')
  rw [show B0 * 1 / (fixedRealizedBatch bStar : ℝ) = 1 by simpa using hfactor, sub_zero] at h
  simpa [B0] using h

theorem lsNoise_sigma_zero_ratio_tendsto (pStar kappa etaStar alpha bStar : ℝ)
    (hk : 0 ≤ kappa) (heta : 0 < etaStar) :
    Tendsto (fun d : ℕ => lsNoiseLoad pStar kappa etaStar alpha bStar 0 d /
      ((etaStar / (2 * (fixedRealizedBatch bStar : ℝ))) * (d : ℝ) ^ (1 - alpha)))
      atTop (𝓝 1) := by
  have hc := lsNoise_dimension_correction_tendsto_one pStar kappa hk
  have heq : (fun d : ℕ => lsNoiseLoad pStar kappa etaStar alpha bStar 0 d /
      ((etaStar / (2 * (fixedRealizedBatch bStar : ℝ))) * (d : ℝ) ^ (1 - alpha))) =ᶠ[atTop]
      fun d => ((d : ℝ) + 2 - scaledSparsity pStar kappa d) / (d : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
    exact lsNoise_sigma_zero_ratio_eq pStar kappa etaStar alpha bStar d hd heta.ne'
  exact hc.congr' heq.symm

theorem lsNoise_sigma_zero_power_tendsto (pStar kappa etaStar alpha bStar : ℝ)
    (hk : 0 ≤ kappa) (heta : 0 < etaStar) :
    Tendsto (fun d : ℕ => lsNoiseLoad pStar kappa etaStar alpha bStar 0 d /
      (d : ℝ) ^ (1 - alpha)) atTop
      (𝓝 (etaStar / (2 * (fixedRealizedBatch bStar : ℝ)))) := by
  let c : ℝ := etaStar / (2 * (fixedRealizedBatch bStar : ℝ))
  have hc : c ≠ 0 := by
    dsimp [c]
    exact div_ne_zero heta.ne' (mul_ne_zero two_ne_zero (by exact_mod_cast (fixedRealizedBatch_pos bStar).ne') )
  have hratio := lsNoise_sigma_zero_ratio_tendsto pStar kappa etaStar alpha bStar hk heta
  have hmul := (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).mul hratio
  have heq : (fun d : ℕ => lsNoiseLoad pStar kappa etaStar alpha bStar 0 d /
      (d : ℝ) ^ (1 - alpha)) =ᶠ[atTop]
      fun d => c * (lsNoiseLoad pStar kappa etaStar alpha bStar 0 d /
        (c * (d : ℝ) ^ (1 - alpha))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
    dsimp [c]
    have hdpos : 0 < (d : ℝ) ^ (1-alpha) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
    field_simp [hc, hdpos.ne', (fixedRealizedBatch_pos bStar).ne']
  have hlim := hmul.congr' heq.symm
  simpa [c] using hlim

theorem lsAdditive_sigma_zero_power_eq (etaStar alpha bStar variance : ℝ)
    (d : ℕ) (hd : 0 < d) :
    lsAdditiveLoad etaStar alpha bStar 0 variance d / (d : ℝ) ^ (1 - alpha) =
      etaStar * variance / (2 * (fixedRealizedBatch bStar : ℝ)) := by
  have hbatch : scaledBatch bStar 0 d = fixedRealizedBatch bStar :=
    scaledBatch_zero_eq_fixed bStar d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold lsAdditiveLoad scaledLearningRate
  rw [hbatch, show 1 - alpha = 1 - alpha by rfl, Real.rpow_sub hdR]
  rw [Real.rpow_neg (le_of_lt hdR), Real.rpow_one]
  field_simp [(fixedRealizedBatch_pos bStar).ne', (Real.rpow_pos_of_pos hdR alpha).ne']
  <;> ring

theorem lsAdditive_sigma_zero_power_tendsto (etaStar alpha bStar variance : ℝ) :
    Tendsto (fun d : ℕ => lsAdditiveLoad etaStar alpha bStar 0 variance d /
      (d : ℝ) ^ (1 - alpha)) atTop
      (𝓝 (etaStar * variance / (2 * (fixedRealizedBatch bStar : ℝ))) ) := by
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
    etaStar * variance / (2 * (fixedRealizedBatch bStar : ℝ))) atTop _).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  exact (lsAdditive_sigma_zero_power_eq etaStar alpha bStar variance d hd).symm

end
end SparseSGD.Scaling
