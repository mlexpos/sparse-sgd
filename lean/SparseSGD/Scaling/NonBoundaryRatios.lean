import SparseSGD.Scaling.ActivityFamily
import SparseSGD.Scaling.LeastSquaresParameters

open Filter Topology MeasureTheory
namespace SparseSGD.Scaling
noncomputable section

/-- Exact one-step signal variance divided by the LS gradient-increment variance. -/
theorem ls_signal_to_increment_ratio {d B : ℕ} (p : unitInterval)
    (hd : 0 < d) (hB : 0 < B) (hp : (p : ℝ) ≠ 0) :
    (p : ℝ)^2 / SparseSGD.Probability.LeastSquares.vinc d B p =
      (p : ℝ) * B / ((d : ℝ) + 2 - p) := by
  unfold SparseSGD.Probability.LeastSquares.vinc
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hden : (d : ℝ) + 2 - (p : ℝ) ≠ 0 := by
    have hp1 := (p.property).2
    have : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  field_simp [hden, hBR]
  <;> ring

/-- The actual curvature-to-noise ratio is the second one-step boundary scale. -/
theorem actual_ls_curvature_to_noise_ratio
    (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta eta : ℝ)
    (hd : 0 < d) (hB : 0 < B) (hp : (p : ℝ) ≠ 0)
    (heta : eta ≠ 0) :
    (SparseSGD.Probability.LeastSquares.params d B p ν beta eta).curvature /
      (SparseSGD.Probability.LeastSquares.params d B p ν beta eta).noise =
      (1-beta)*(p : ℝ)*B / ((1+beta)*((d : ℝ)+2-p)) := by
  rw [SparseSGD.Probability.LeastSquares.params_explicit p hp ν beta eta]
  simp only [SparseSGD.Params.curvature]
  by_cases hb : 1 + beta = 0
  · have hbeta : beta = -1 := by linarith
    subst beta
    simp
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hden : (d : ℝ) + 2 - (p : ℝ) ≠ 0 := by
    have hp1 := (p.property).2
    have : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  field_simp [hden, hBR, heta, hb]
  <;> ring

/-- The dimension correction in the signal/increment ratio tends to one for
an actual probability family that eventually follows the sparse power law. -/
theorem actual_dimension_correction_tendsto_one
    (pStar kappa : ℝ) (p : ℕ → unitInterval)
    (hk : 0 ≤ kappa)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d : ℝ)=scaledSparsity pStar kappa d) :
    Tendsto (fun d : ℕ => ((d : ℝ)+2-(p d : ℝ))/(d : ℝ)) atTop (𝓝 1) := by
  have h := lsNoise_dimension_correction_tendsto_one pStar kappa hk
  apply h.congr'
  filter_upwards [hpd] with d hpd
  rw [hpd]

/-- First non-boundary ratio for an actual LS family, with the rounded batch
constant retained. -/
theorem actual_signal_increment_ratio_tendsto
    (pStar kappa b sigma : ℝ) (p : ℕ → unitInterval)
    (hpstar : 0 < pStar) (hb : 0 < b) (hs : 0 ≤ sigma) (hk : 0 ≤ kappa)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d : ℝ)=scaledSparsity pStar kappa d) :
    Tendsto (fun d =>
      ((p d : ℝ)^2 / SparseSGD.Probability.LeastSquares.vinc d (scaledBatch b sigma d) (p d)) /
        (realizedBatchScale b sigma*pStar*(d : ℝ)^(sigma-kappa-1))) atTop (𝓝 1) := by
  have hBatch := actual_batch_product_ratio pStar kappa b sigma p hpstar hb hs hpd
  have hDim := actual_dimension_correction_tendsto_one pStar kappa p hk hpd
  have hInv := hDim.inv₀ (by norm_num)
  have hInv' : Tendsto (fun d : ℕ => (((d : ℝ)+2-(p d : ℝ))/(d : ℝ))⁻¹)
      atTop (𝓝 1) := by simpa using hInv
  have hCorr : Tendsto (fun d : ℕ => (d : ℝ)/((d : ℝ)+2-(p d : ℝ))) atTop (𝓝 1) := by
    apply hInv'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    field_simp
  have hProd := hBatch.mul hCorr
  have hProd' : Tendsto (fun d : ℕ =>
      ((p d : ℝ)*(scaledBatch b sigma d : ℝ)/(realizedBatchScale b sigma*pStar*(d : ℝ)^(sigma-kappa))) *
      ((d : ℝ)/((d : ℝ)+2-(p d : ℝ)))) atTop (𝓝 1) := by simpa using hProd
  apply hProd'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), hpd] with d hd hpd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hp : (p d : ℝ) ≠ 0 := by rw [hpd]; exact scaledSparsity_pos_of_pos pStar kappa d hpstar hd |>.ne'
  have hB : 0 < scaledBatch b sigma d := integerBatch_pos b sigma d
  rw [ls_signal_to_increment_ratio (p d) hd hB hp]
  have hpow : (d : ℝ) * (d : ℝ)^(sigma-kappa-1) =
      (d : ℝ)^(sigma-kappa) := by
    calc
      (d : ℝ) * (d : ℝ)^(sigma-kappa-1) =
          (d : ℝ)^1 * (d : ℝ)^(sigma-kappa-1) := by rw [Real.rpow_one]
      _ = (d : ℝ)^(1+(sigma-kappa-1)) := (Real.rpow_add hdR 1 (sigma-kappa-1)).symm
      _ = (d : ℝ)^(sigma-kappa) := by congr 1 <;> ring
  unfold realizedBatchScale
  have hscale : 0 < realizedBatchScale b sigma := realizedBatchScale_pos b sigma hb
  have hpstar0 : pStar ≠ 0 := hpstar.ne'
  have hBprod : (p d : ℝ)*(scaledBatch b sigma d : ℝ) ≠ 0 := mul_ne_zero hp (by exact_mod_cast hB.ne')
  field_simp [hdR.ne', hscale.ne', hpstar0, hBprod]
  rw [hpow]
  <;> ring

/-- For every nonzero-sparsity LS instance, the actual parameter curvature to
noise ratio is exactly the second comparison scale. -/
theorem actual_ls_curvature_noise_ratio
    (d : ℕ) (B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta eta : ℝ)
    (hd : 0 < d) (hB : 0 < B) (hp : (p : ℝ) ≠ 0) (heta : eta ≠ 0) :
    (SparseSGD.Probability.LeastSquares.params d B p ν beta eta).curvature /
      (SparseSGD.Probability.LeastSquares.params d B p ν beta eta).noise =
      (1-beta)*(p : ℝ)*B / ((1+beta)*((d : ℝ)+2-p)) :=
  actual_ls_curvature_to_noise_ratio d B p ν beta eta hd hB hp heta

/-- Actual curvature/noise ratio on a rounded-batch LS power family. Its
normalization records the true integer-batch prefactor, including `sigma=0`. -/
theorem actual_curvature_noise_ratio_tendsto
    (pStar kappa b sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ)
    (hpstar : 0 < pStar) (hk : 0 ≤ kappa) (hb : 0 < b) (hs : 0 ≤ sigma)
    (heps : 0 < epsStar) (hg : 0 < gamma) (heta : 0 < etaStar)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d : ℝ)=scaledSparsity pStar kappa d) :
    Tendsto (fun d =>
      ((actualLSParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d).curvature /
        (actualLSParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d).noise) /
        ((epsStar*realizedBatchScale b sigma*pStar/2) *
          (d : ℝ)^(sigma-kappa-gamma-1))) atTop (𝓝 1) := by
  have hBatch := actual_batch_product_ratio pStar kappa b sigma p hpstar hb hs hpd
  have hDim := actual_dimension_correction_tendsto_one pStar kappa p hk hpd
  have hInv := hDim.inv₀ (by norm_num)
  have hInv' : Tendsto (fun d : ℕ => (((d : ℝ)+2-(p d : ℝ))/(d : ℝ))⁻¹)
      atTop (𝓝 1) := by simpa using hInv
  have hCorr : Tendsto (fun d : ℕ => (d : ℝ)/((d : ℝ)+2-(p d : ℝ))) atTop (𝓝 1) := by
    apply hInv'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    field_simp
  have hBeta := scaledMomentum_tendsto_one epsStar gamma hg
  have hDen : Tendsto (fun d : ℕ => 1+scaledMomentum epsStar gamma d) atTop (𝓝 2) := by
    have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hsum := hOne.add hBeta
    convert hsum using 1 <;> norm_num
  have hFactor : Tendsto (fun d : ℕ => 2/(1+scaledMomentum epsStar gamma d))
      atTop (𝓝 1) := by
    have hi := hDen.inv₀ (by norm_num)
    have hm := hi.const_mul 2
    simpa [div_eq_mul_inv, mul_comm] using hm
  have hProd := hBatch.mul hCorr |>.mul hFactor
  have hProd' : Tendsto (fun d : ℕ =>
      ((p d : ℝ)*(scaledBatch b sigma d : ℝ)/
        (realizedBatchScale b sigma*pStar*(d : ℝ)^(sigma-kappa))) *
      ((d : ℝ)/((d : ℝ)+2-(p d : ℝ))) *
      (2/(1+scaledMomentum epsStar gamma d))) atTop (𝓝 1) := by simpa using hProd
  apply hProd'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), hpd] with d hd hpd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hp : (p d : ℝ) ≠ 0 := by rw [hpd]; exact scaledSparsity_pos_of_pos pStar kappa d hpstar hd |>.ne'
  have hB : 0 < scaledBatch b sigma d := integerBatch_pos b sigma d
  have heta : scaledLearningRate etaStar alpha d ≠ 0 := by
    unfold scaledLearningRate
    exact (mul_pos heta (Real.rpow_pos_of_pos hdR _)).ne'
  rw [actualLSParams, actual_ls_curvature_noise_ratio d (scaledBatch b sigma d) (p d) ν
    (scaledMomentum epsStar gamma d) (scaledLearningRate etaStar alpha d) hd hB hp heta]
  have hpow : (d : ℝ) * (d : ℝ)^(sigma-kappa-gamma-1) =
      (d : ℝ)^(sigma-kappa-gamma) := by
    calc
      (d : ℝ) * (d : ℝ)^(sigma-kappa-gamma-1) =
          (d : ℝ)^1 * (d : ℝ)^(sigma-kappa-gamma-1) := by rw [Real.rpow_one]
      _ = (d : ℝ)^(1+(sigma-kappa-gamma-1)) :=
        (Real.rpow_add hdR 1 (sigma-kappa-gamma-1)).symm
      _ = (d : ℝ)^(sigma-kappa-gamma) := by congr 1 <;> ring
  have hepspow : 1-scaledMomentum epsStar gamma d = epsStar*(d : ℝ)^(-gamma) := by
    simp [scaledMomentum, scaledRetention]
  rw [hepspow]
  have hscale : 0 < realizedBatchScale b sigma := realizedBatchScale_pos b sigma hb
  have hpstar0 : pStar ≠ 0 := hpstar.ne'
  have hBprod : (p d : ℝ)*(scaledBatch b sigma d : ℝ) ≠ 0 :=
    mul_ne_zero hp (by exact_mod_cast hB.ne')
  unfold realizedBatchScale
  field_simp [hdR.ne', hscale.ne', hpstar0, hBprod]
  rw [hpow]
  rw [← Real.rpow_add hdR]
  congr 1 <;> ring

end
end SparseSGD.Scaling
