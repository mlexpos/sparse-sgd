import SparseSGD.Scaling.IntegerRounding

open Filter Topology

namespace SparseSGD.Scaling
noncomputable section

/-- Co-scaled least-squares parameters, with an actually integer-valued batch. -/
def scaledSparsity (pStar kappa : ℝ) (d : ℕ) : ℝ := pStar * (d : ℝ) ^ (-kappa)
def scaledRetention (epsStar gamma : ℝ) (d : ℕ) : ℝ := epsStar * (d : ℝ) ^ (-gamma)
def scaledMomentum (epsStar gamma : ℝ) (d : ℕ) : ℝ := 1 - scaledRetention epsStar gamma d
def scaledLearningRate (etaStar alpha : ℝ) (d : ℕ) : ℝ := etaStar * (d : ℝ) ^ (-alpha)
def scaledBatch (bStar sigma : ℝ) (d : ℕ) : ℕ := integerBatch bStar sigma d

def lsCurvature (pStar etaStar epsStar kappa gamma alpha : ℝ) (d : ℕ) : ℝ :=
  scaledLearningRate etaStar alpha d * scaledRetention epsStar gamma d * scaledSparsity pStar kappa d

def lsDelta (pStar etaStar epsStar kappa gamma alpha : ℝ) (d : ℕ) : ℝ :=
  scaledLearningRate etaStar alpha d * scaledSparsity pStar kappa d /
    scaledRetention epsStar gamma d

def lsNoiseLoad (pStar kappa etaStar alpha bStar sigma : ℝ) (d : ℕ) : ℝ :=
  scaledLearningRate etaStar alpha d * ((d : ℝ) + 2 - scaledSparsity pStar kappa d) /
    (2 * (scaledBatch bStar sigma d : ℝ))

def lsAdditiveLoad (etaStar alpha bStar sigma variance : ℝ) (d : ℕ) : ℝ :=
  scaledLearningRate etaStar alpha d * variance * (d : ℝ) /
    (2 * (scaledBatch bStar sigma d : ℝ))

def lsCurvatureLoad (pStar etaStar epsStar kappa gamma alpha : ℝ) (d : ℕ) : ℝ :=
  lsCurvature pStar etaStar epsStar kappa gamma alpha d /
    (2 * (1 + 1 - scaledRetention epsStar gamma d))


theorem lsCurvature_power_ratio (pStar etaStar epsStar kappa gamma alpha : ℝ)
    (d : ℕ) (hd : 0 < d) (hp : pStar ≠ 0) (he : etaStar ≠ 0) (hr : epsStar ≠ 0) :
    lsCurvature pStar etaStar epsStar kappa gamma alpha d /
      (etaStar * epsStar * pStar * (d : ℝ) ^ (-(alpha + gamma + kappa))) = 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold lsCurvature scaledLearningRate scaledRetention scaledSparsity
  rw [show -(alpha + gamma + kappa) = (-alpha + -gamma) + -kappa by ring]
  rw [Real.rpow_add hdR, Real.rpow_add hdR]
  field_simp [(Real.rpow_pos_of_pos hdR _).ne']
  <;> ring

theorem lsDelta_power_ratio (pStar etaStar epsStar kappa gamma alpha : ℝ)
    (d : ℕ) (hd : 0 < d) (hp : pStar ≠ 0) (he : etaStar ≠ 0) (hr : epsStar ≠ 0) :
    lsDelta pStar etaStar epsStar kappa gamma alpha d /
      (etaStar * pStar / epsStar * (d : ℝ) ^ (gamma - alpha - kappa)) = 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold lsDelta scaledLearningRate scaledRetention scaledSparsity
  rw [show gamma - alpha - kappa = gamma + (-alpha + -kappa) by ring]
  rw [Real.rpow_add hdR, Real.rpow_add hdR, Real.rpow_neg (le_of_lt hdR)]
  field_simp [(Real.rpow_pos_of_pos hdR _).ne', hp, he, hr]
  rw [← Real.rpow_add hdR]
  simp

/-- Actual integer batches have the nominal power-law ratio, for positive scaling exponent. -/
theorem scaledBatch_ratio_tendsto (bStar sigma : ℝ) (hb : 0 < bStar) (hs : 0 < sigma) :
    Tendsto (fun d : ℕ => (scaledBatch bStar sigma d : ℝ) /
      (bStar * (d : ℝ) ^ sigma)) atTop (𝓝 1) := by
  exact integerBatch_ratio_tendsto bStar sigma hb hs


theorem scaledRetention_tendsto_zero (epsStar gamma : ℝ) (hg : 0 < gamma) :
    Tendsto (fun d : ℕ => scaledRetention epsStar gamma d) atTop (𝓝 0) := by
  unfold scaledRetention
  simpa using ((tendsto_rpow_neg_atTop hg).comp tendsto_natCast_atTop_atTop).const_mul epsStar

theorem scaledMomentum_tendsto_one (epsStar gamma : ℝ) (hg : 0 < gamma) :
    Tendsto (fun d : ℕ => scaledMomentum epsStar gamma d) atTop (𝓝 1) := by
  unfold scaledMomentum
  have h := (scaledRetention_tendsto_zero epsStar gamma hg).const_sub 1
  simpa using h


theorem scaledSparsity_over_dimension_tendsto_zero (pStar kappa : ℝ) (hk : kappa ≥ 0) :
    Tendsto (fun d : ℕ => scaledSparsity pStar kappa d / (d : ℝ)) atTop (𝓝 0) := by
  have hpow := ((tendsto_rpow_neg_atTop (show 0 < kappa + 1 by linarith)).comp
    tendsto_natCast_atTop_atTop).const_mul pStar
  have hpow0 : Tendsto (fun d : ℕ => pStar * (d : ℝ) ^ (-(kappa + 1))) atTop (𝓝 0) := by
    simpa using hpow
  apply hpow0.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold scaledSparsity
  rw [show -(kappa + 1) = -kappa + -1 by ring, Real.rpow_add hdR,
    Real.rpow_neg (le_of_lt hdR)]
  rw [Real.rpow_neg (le_of_lt hdR), Real.rpow_one]
  field_simp [hdR.ne']
  <;> ring

theorem lsNoise_dimension_correction_tendsto_one (pStar kappa : ℝ) (hk : kappa ≥ 0) :
    Tendsto (fun d : ℕ => ((d : ℝ) + 2 - scaledSparsity pStar kappa d) / (d : ℝ))
      atTop (𝓝 1) := by
  have hdInv := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop :
    Tendsto (fun d : ℕ => (d : ℝ)⁻¹) atTop (𝓝 0))
  have hp := scaledSparsity_over_dimension_tendsto_zero pStar kappa hk
  have hbase : Tendsto (fun d : ℕ => (1 : ℝ) + 2 * (d : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hdInv.const_mul 2)
  have h := hbase.sub hp
  have h1 : Tendsto (fun d : ℕ => 1 + 2 * (d : ℝ)⁻¹ - scaledSparsity pStar kappa d / (d : ℝ)) atTop (𝓝 1) := by
    simpa using h
  apply h1.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp


theorem lsNoise_batch_correction_tendsto_one (bStar sigma : ℝ)
    (hb : 0 < bStar) (hs : 0 < sigma) :
    Tendsto (fun d : ℕ => (bStar * (d : ℝ) ^ sigma) /
      (scaledBatch bStar sigma d : ℝ)) atTop (𝓝 1) := by
  have h := (scaledBatch_ratio_tendsto bStar sigma hb hs).inv₀ one_ne_zero
  simpa [scaledBatch] using h


theorem lsNoise_power_ratio_eq (pStar kappa etaStar alpha bStar sigma : ℝ)
    (d : ℕ) (hd : 0 < d) (heta : etaStar ≠ 0) (hb : bStar ≠ 0) :
    lsNoiseLoad pStar kappa etaStar alpha bStar sigma d /
      ((etaStar / (2 * bStar)) * (d : ℝ) ^ (1 - sigma - alpha)) =
      (((d : ℝ) + 2 - scaledSparsity pStar kappa d) / (d : ℝ)) *
        (bStar * (d : ℝ) ^ sigma / (scaledBatch bStar sigma d : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold lsNoiseLoad scaledLearningRate
  rw [show 1-sigma-alpha=(-alpha)+1-sigma by ring,
    Real.rpow_sub hdR,Real.rpow_add hdR,Real.rpow_one]
  field_simp [heta, hb, (integerBatch_pos bStar sigma d).ne', (Real.rpow_pos_of_pos hdR _).ne']
  <;> ring

theorem lsNoise_power_ratio_tendsto (pStar kappa etaStar alpha bStar sigma : ℝ)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (heta : 0 < etaStar)
    (hb : 0 < bStar) (hs : 0 < sigma) :
    Tendsto (fun d : ℕ => lsNoiseLoad pStar kappa etaStar alpha bStar sigma d /
      ((etaStar / (2 * bStar)) * (d : ℝ) ^ (1 - sigma - alpha))) atTop (𝓝 1) := by
  have h1 := lsNoise_dimension_correction_tendsto_one pStar kappa hk
  have h2 := lsNoise_batch_correction_tendsto_one bStar sigma hb hs
  have h := h1.mul h2
  have hEq : (fun d : ℕ => lsNoiseLoad pStar kappa etaStar alpha bStar sigma d /
      ((etaStar / (2 * bStar)) * (d : ℝ) ^ (1 - sigma - alpha))) =ᶠ[atTop]
      (fun d => (((d : ℝ) + 2 - scaledSparsity pStar kappa d) / (d : ℝ)) *
        (bStar * (d : ℝ) ^ sigma / (scaledBatch bStar sigma d : ℝ))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
    exact lsNoise_power_ratio_eq pStar kappa etaStar alpha bStar sigma d hd heta.ne' hb.ne'
  simpa using h.congr' hEq.symm

/-- Ambient temperature, including the zero-label-noise case. -/
theorem lsAdditive_power_ratio_eq (etaStar alpha bStar sigma variance : ℝ)
    (d : ℕ) (hd : 0 < d) (heta : etaStar ≠ 0) (hb : bStar ≠ 0) :
    lsAdditiveLoad etaStar alpha bStar sigma variance d /
      ((etaStar/(2*bStar))*(d : ℝ)^(1-sigma-alpha)) =
      variance*(bStar*(d : ℝ)^sigma/(scaledBatch bStar sigma d : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold lsAdditiveLoad scaledLearningRate
  rw [show 1-sigma-alpha=(-alpha)+1-sigma by ring,
    Real.rpow_sub hdR,Real.rpow_add hdR,Real.rpow_one]
  field_simp [heta,hb,(integerBatch_pos bStar sigma d).ne',(Real.rpow_pos_of_pos hdR _).ne']
  <;> ring

theorem lsAdditive_power_ratio_tendsto (etaStar alpha bStar sigma variance : ℝ)
    (heta : 0 < etaStar) (hb : 0 < bStar) (hs : 0 < sigma) :
    Tendsto (fun d : ℕ => lsAdditiveLoad etaStar alpha bStar sigma variance d /
      ((etaStar/(2*bStar))*(d : ℝ)^(1-sigma-alpha))) atTop (𝓝 variance) := by
  have H := (lsNoise_batch_correction_tendsto_one bStar sigma hb hs).const_mul variance
  simp only [mul_one] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  exact (lsAdditive_power_ratio_eq etaStar alpha bStar sigma variance d hd heta.ne' hb.ne').symm

theorem lsCurvatureLoad_power_ratio_tendsto (pStar etaStar epsStar kappa gamma alpha : ℝ)
    (hp : pStar ≠ 0) (he : etaStar ≠ 0) (hr : epsStar ≠ 0) (hg : 0 < gamma) :
    Tendsto (fun d : ℕ => lsCurvatureLoad pStar etaStar epsStar kappa gamma alpha d /
      (etaStar*epsStar*pStar*(d : ℝ)^(-(alpha+gamma+kappa)))) atTop (𝓝 (1/4)) := by
  have Hden := ((scaledRetention_tendsto_zero epsStar gamma hg).const_sub 2).const_mul 2
  have H : Tendsto (fun d : ℕ => 1/(2*(2-scaledRetention epsStar gamma d))) atTop (𝓝 (1/4)) := by
    convert tendsto_const_nhds.div Hden (by norm_num : (2 : ℝ)*(2-0) ≠ 0) using 1 <;> norm_num
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  dsimp only [lsCurvatureLoad]
  have Hratio := lsCurvature_power_ratio pStar etaStar epsStar kappa gamma alpha d hd hp he hr
  calc
    _ = 1/(2*(1+1-scaledRetention epsStar gamma d)) := by norm_num
    _ = (lsCurvature pStar etaStar epsStar kappa gamma alpha d /
        (etaStar*epsStar*pStar*(d : ℝ)^(-(alpha+gamma+kappa)))) /
        (2*(1+1-scaledRetention epsStar gamma d)) := by rw [Hratio]
    _ = _ := by ring

end
end SparseSGD.Scaling
