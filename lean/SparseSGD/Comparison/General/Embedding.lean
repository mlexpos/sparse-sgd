import SparseSGD.Comparison.General.Matching
import SparseSGD.Comparison.ExactEmbedding
import SparseSGD.Discrete.General.Renewal

/-!
# Exact embedding for the momentum range `β ∈ (0,1)` (v2)

This is the v2 embedding layer (paper Lemma D.3 and the matched form of Corollary E.8 (i)).
The v1 declarations in `Comparison/ExactEmbedding.lean` carry the hypothesis `1/2 ≤ β`, used
only to obtain `0 < β`.  Here they are restated under `0 < β` (with `β < 1` unchanged), as new
declarations with suffix `_v2`, proved from the v2 matching layer
(`Comparison/General/Matching.lean`) and the v2 renewal layer
(`Discrete/General/Renewal.lean`).  The v1 signatures are frozen.
-/

open scoped Matrix.Norms.Operator Matrix

namespace SparseSGD
noncomputable section

variable (p : Params) (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
  (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))

include hb0 hb1 hw0 hw1

/-- v2 (β ∈ (0,1)) form of `Params.meanMatrix_pow_matching`. -/
theorem Params.meanMatrix_pow_matching_v2 (n : ℕ) :
    p.meanMatrix^n * p.matchingMatrix =
      p.matchingSign^n • (p.matchingMatrix*p.matchedMeanFlow^n) := by
  have ⟨hd, ht, hi⟩ := p.matchedMeanFlow_invariants_v2 hb0 hb1 hw0 hw1
  have hFP := matching_first_relation p p.matchingSign p.matchedMeanFlow
    (by linarith) p.matchingSign_sq hd ht hi
  change p.meanMatrix*p.matchingMatrix = p.matchingSign •
    (p.matchingMatrix*p.matchedMeanFlow) at hFP
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, mul_smul_comm,
      ← Matrix.mul_assoc, hFP, smul_mul_assoc, smul_smul, pow_succ']
    rw [mul_comm p.matchingSign, ← pow_succ]
    simp only [Matrix.mul_assoc, pow_succ']

/-- v2 (β ∈ (0,1)) form of `Params.sampledImpulse_eq_power`. -/
theorem Params.sampledImpulse_eq_power_v2 (n : ℕ) :
    p.sampledImpulse n = (p.matchedMeanFlow^n) 0 1 := by
  simp only [Params.sampledImpulse, continuumImpulseResponse,
    continuumMeanFlow_nat_grid, Params.matchedMeanFlow]

/-- v2 (β ∈ (0,1)) form of `Params.kickResponse_matched`. -/
theorem Params.kickResponse_matched_v2 (n : ℕ) :
    kickResponse p n = (p.matchingSign^(n+1)/(p.beta*p.matchingMatrix 1 1))*
      p.sampledImpulse (n+1) := by
  let P := p.matchingMatrix
  have hPinv : P*P⁻¹ = 1 := Matrix.mul_nonsing_inv P
    (isUnit_iff_ne_zero.mpr (p.matchingMatrix_det_ne_zero_v2 hb0 hb1 hw0 hw1))
  have hk := p.exact_matching_kick_v2 hb0 hb1 hw0 hw1
  have hpow := p.meanMatrix_pow_matching_v2 hb0 hb1 hw0 hw1 n
  have hresp : (p.meanMatrix^n).mulVec kick =
      (p.matchingSign^(n+1)/(p.beta*P 1 1)) •
        ((P*p.matchedMeanFlow^(n+1)).mulVec ![0,1]) := by
    calc
      _ = (p.meanMatrix^n*P).mulVec (P⁻¹.mulVec kick) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hPinv, Matrix.mul_one]
      _ = _ := by
        rw [hk, hpow, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
          Matrix.mulVec_mulVec, Matrix.mul_assoc, ← pow_succ]
        congr 1
        rw [pow_succ]
        ring
  have h := congrFun hresp 0
  rw [p.sampledImpulse_eq_power_v2 hb0 hb1 hw0 hw1]
  have hfirst : ((P*p.matchedMeanFlow^(n+1)).mulVec ![0,1]) 0 =
      (p.matchedMeanFlow^(n+1)) 0 1 := by
    rw [← Matrix.mulVec_mulVec]
    change ((matchingP p.matchingSign p.matchedMeanFlow p).mulVec
      ((p.matchedMeanFlow^(n+1)).mulVec ![0,1])) 0 = _
    simp only [matchingP, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_one, mul_zero, one_mul, zero_mul, add_zero,
      zero_add]
  simpa only [Pi.smul_apply, smul_eq_mul, hfirst, kickResponse, P] using h

/-- v2 (β ∈ (0,1)) form of `Params.kickResponse_sq_matched`. -/
theorem Params.kickResponse_sq_matched_v2 (n : ℕ) :
    kickResponse p n^2 = p.sampledImpulse (n+1)^2 /
      (p.beta*p.matchingMatrix 1 1)^2 := by
  rw [p.kickResponse_matched_v2 hb0 hb1 hw0 hw1 n, mul_pow, div_pow]
  have hs : (p.matchingSign^(n+1))^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, p.matchingSign_sq, one_pow]
  rw [hs]
  ring

/-- v2 (β ∈ (0,1)) form of `Params.matchedCovariance_first_entry`. -/
theorem Params.matchedCovariance_first_entry_v2 (s : Moments) :
    p.matchedCovariance s 0 0 = s.R := by
  have ⟨hd, ht, hi⟩ := p.matchedMeanFlow_invariants_v2 hb0 hb1 hw0 hw1
  exact matching_cov_first_entry p s p.matchingSign p.matchedMeanFlow
    (by linarith) p.matchingSign_sq hd ht hi

/-- v2 (β ∈ (0,1)) form of `Params.matchingImpulseDenominator_ne_zero`. -/
theorem Params.matchingImpulseDenominator_ne_zero_v2 :
    p.beta*p.matchingMatrix 1 1 ≠ 0 := by
  have hdet := p.matchingMatrix_det_ne_zero_v2 hb0 hb1 hw0 hw1
  have h11 : p.matchingMatrix 1 1 ≠ 0 := by
    simpa [Params.matchingMatrix, matchingP, Matrix.det_fin_two] using hdet
  exact mul_ne_zero (by linarith) h11

/-- v2 (β ∈ (0,1)) form of `Params.sampledImpulse_sq_hasSum`. -/
theorem Params.sampledImpulse_sq_hasSum_v2 (jury : External.JuryStability) :
    HasSum (fun n : ℕ => p.sampledImpulse (n+1)^2)
      ((p.beta*p.matchingMatrix 1 1)^2/(2*p.w*p.eps*(1-p.curvature))) := by
  have hc : 0 < 1-p.curvature := by
    unfold Params.curvature
    rw [sub_pos]
    apply (div_lt_iff₀ (by linarith : 0 < 2*(1+p.beta))).2
    simpa using hw1
  have hd := p.matchingImpulseDenominator_ne_zero_v2 hb0 hb1 hw0 hw1
  have hsum := kickResponse_sq_hasSum p hw0.ne' (by linarith) (by linarith) hc.ne'
    (External.mean_powers_tendsto_zero jury p hb1 hw0 hw1)
  have H := hsum.mul_left ((p.beta*p.matchingMatrix 1 1)^2)
  convert H using 1
  · funext n
    rw [p.kickResponse_sq_matched_v2 hb0 hb1 hw0 hw1]
    exact (mul_div_cancel₀ _ (pow_ne_zero _ hd)).symm
  · unfold Params.eps
    ring

/-- v2 (β ∈ (0,1)) form of `Params.gridImpulseFactor_eq`. -/
theorem Params.gridImpulseFactor_eq_v2 (jury : External.JuryStability) :
    p.gridImpulseFactor = (1-p.curvature)*2*p.w*p.eps /
      (p.beta*p.matchingMatrix 1 1)^2 := by
  unfold Params.gridImpulseFactor
  rw [(p.sampledImpulse_sq_hasSum_v2 hb0 hb1 hw0 hw1 jury).tsum_eq, inv_div]
  ring

/-- v2 (β ∈ (0,1)) form of `Params.normalizedKernelLag_eq_sampled`. -/
theorem Params.normalizedKernelLag_eq_sampled_v2 (jury : External.JuryStability) (n : ℕ) :
    normalizedKernelLag p n = p.gridImpulseFactor*p.sampledImpulse n^2 := by
  cases n with
  | zero => simp [normalizedKernelLag, Params.sampledImpulse, continuumImpulseResponse,
      continuumMeanFlow_zero]
  | succ n =>
    rw [normalizedKernelLag, p.kickResponse_sq_matched_v2 hb0 hb1 hw0 hw1,
      p.gridImpulseFactor_eq_v2 hb0 hb1 hw0 hw1 jury]
    ring

/-- v2 (β ∈ (0,1)) form of `Params.exact_embedding_step`. -/
theorem Params.exact_embedding_step_v2 (jury : External.JuryStability) (s : Moments) :
    p.matchedCovariance (p.step s) = p.matchedMeanFlow *
      (p.matchedCovariance s +
        (p.gridImpulseFactor*(p.renormNoise*s.R+p.renormAdditive)) •
          Matrix.vecMulVec (![0,1] : Fin 2 → ℝ) ![0,1]) * p.matchedMeanFlow.transpose := by
  obtain ⟨hd, ht, hi⟩ := p.matchedMeanFlow_invariants_v2 hb0 hb1 hw0 hw1
  have H := matching_cov_step p s p.matchingSign p.matchedMeanFlow
    (by linarith) p.matchingSign_sq hd ht hi
  change p.matchedCovariance (p.step s) = p.matchedMeanFlow *
    (p.matchedCovariance s +
      ((2*p.w*p.eps*(p.noise*s.R+p.additive))/(p.beta*p.matchingMatrix 1 1)^2) •
        Matrix.vecMulVec (![0,1] : Fin 2 → ℝ) ![0,1]) * p.matchedMeanFlow.transpose at H
  rw [H]
  congr 3
  rw [p.gridImpulseFactor_eq_v2 hb0 hb1 hw0 hw1 jury]
  unfold Params.renormNoise Params.renormAdditive
  have hc : 1-p.curvature ≠ 0 := by
    unfold Params.curvature
    have hp : 0 < 2*(1+p.beta) := by linarith
    apply ne_of_gt
    rw [sub_pos]
    apply (div_lt_iff₀ hp).2
    simpa using hw1
  field_simp [hc]

/-- v2 (β ∈ (0,1)) form of `Params.freeRisk_eq_matched_grid`. -/
theorem Params.freeRisk_eq_matched_grid_v2 (s : Moments) (n : ℕ) :
    freeRisk p s n = p.matchedFreeRisk s ((n : ℝ)*p.matchedStep) := by
  let P := p.matchingMatrix
  let G := p.matchedMeanFlow
  have hPinv : P*P⁻¹ = 1 := Matrix.mul_nonsing_inv P
    (isUnit_iff_ne_zero.mpr (p.matchingMatrix_det_ne_zero_v2 hb0 hb1 hw0 hw1))
  have hpow : p.meanMatrix^n = p.matchingSign^n • (P*G^n*P⁻¹) := by
    calc
      _ = (p.meanMatrix^n*P)*P⁻¹ := by rw [Matrix.mul_assoc, hPinv, Matrix.mul_one]
      _ = _ := by rw [p.meanMatrix_pow_matching_v2 hb0 hb1 hw0 hw1, smul_mul_assoc]
  have hsign : p.matchingSign^n*p.matchingSign^n = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm, pow_mul, p.matchingSign_sq, one_pow]
  have hcov : p.meanMatrix^n*s.cov*(p.meanMatrix^n).transpose =
      P*(G^n*p.matchedCovariance s*(G^n).transpose)*P.transpose := by
    rw [hpow]
    simp only [Matrix.transpose_smul, Matrix.transpose_mul, smul_mul_assoc,
      mul_smul_comm, smul_smul, hsign, one_smul]
    simp only [Params.matchedCovariance, P, G, Matrix.mul_assoc]
  have h00 : P 0 0 = 1 := rfl
  have h01 : P 0 1 = 0 := rfl
  have hfirst (M : Matrix (Fin 2) (Fin 2) ℝ) : (P*M*P.transpose) 0 0 = M 0 0 := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      h00, h01, one_mul, zero_mul, mul_one, mul_zero, add_zero, zero_add]
  unfold freeRisk Params.matchedFreeRisk
  rw [hcov, hfirst, continuumMeanFlow_nat_grid]
  rfl

/-- v2 (β ∈ (0,1)) form of `Params.exact_embedding_renewal`. -/
theorem Params.exact_embedding_renewal_v2 (jury : External.JuryStability) (s : Moments)
    (k : ℕ) :
    (p.trajectory s k).R = p.matchedFreeRisk s ((k : ℝ)*p.matchedStep) +
      ∑ j ∈ Finset.range k,
        (p.gridImpulseFactor*p.sampledImpulse (k-j)^2)*
          (p.renormNoise*(p.trajectory s j).R+p.renormAdditive) := by
  rw [normalized_trajectory_recurrence_v2 jury p s hb0.le hb1 hw0 hw1 k,
    p.freeRisk_eq_matched_grid_v2 hb0 hb1 hw0 hw1]
  simp only [p.normalizedKernelLag_eq_sampled_v2 hb0 hb1 hw0 hw1 jury]

/-- v2 (β ∈ (0,1)) form of `Params.noiseFree_risk_eq_matched_grid`. -/
theorem Params.noiseFree_risk_eq_matched_grid_v2 (s : Moments)
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (k : ℕ) :
    (p.trajectory s k).R = p.matchedFreeRisk s ((k : ℝ)*p.matchedStep) := by
  have H := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0)
    (p.trajectory_cov_noiseFree s hnoise hadd k)
  rw [← p.freeRisk_eq_matched_grid_v2 hb0 hb1 hw0 hw1]
  simpa only [Moments.cov, Matrix.of_apply, Matrix.cons_val_zero, freeRisk] using H

/-- v2 (β ∈ (0,1)) form of `Params.sampledImpulse_sq_tsum_pos`. -/
theorem Params.sampledImpulse_sq_tsum_pos_v2 (jury : External.JuryStability) :
    0 < ∑' n : ℕ, p.sampledImpulse (n+1)^2 := by
  have hsum := p.sampledImpulse_sq_hasSum_v2 hb0 hb1 hw0 hw1 jury
  apply hsum.summable.tsum_pos (fun n => sq_nonneg _) 0
  simp only [zero_add, p.sampledImpulse_eq_power_v2 hb0 hb1 hw0 hw1, pow_one]
  exact sq_pos_of_ne_zero (p.matchedMeanFlow_impulse_ne_zero_v2 hb0 hb1 hw0 hw1)

/-- v2 (β ∈ (0,1)) form of `Params.normalizedKernelLag_eq_continuum_sampling`. -/
theorem Params.normalizedKernelLag_eq_continuum_sampling_v2
    (jury : External.JuryStability) (n : ℕ) :
    normalizedKernelLag p n =
      continuumRenewalKernel p.matchedDelta ((n : ℝ)*p.matchedStep) /
        (∑' m : ℕ, continuumRenewalKernel p.matchedDelta (((m+1 : ℕ) : ℝ)*p.matchedStep)) := by
  have hd := p.matchedDelta_pos (by linarith) hb1 hw0 hw1
  have hs := p.sampledImpulse_sq_hasSum_v2 hb0 hb1 hw0 hw1 jury
  have hS := p.sampledImpulse_sq_tsum_pos_v2 hb0 hb1 hw0 hw1 jury
  have hsum : (∑' m : ℕ, continuumRenewalKernel p.matchedDelta
      (((m+1 : ℕ) : ℝ)*p.matchedStep)) =
      (2/p.matchedDelta)*(∑' m : ℕ, p.sampledImpulse (m+1)^2) := by
    change (∑' m : ℕ, (2/p.matchedDelta)*p.sampledImpulse (m+1)^2) = _
    exact hs.summable.tsum_mul_left _
  rw [p.normalizedKernelLag_eq_sampled_v2 hb0 hb1 hw0 hw1 jury, hsum]
  unfold Params.gridImpulseFactor continuumRenewalKernel
  change (∑' m : ℕ, p.sampledImpulse (m+1)^2)⁻¹*p.sampledImpulse n^2 =
    (2/p.matchedDelta*p.sampledImpulse n^2)/
      ((2/p.matchedDelta)*(∑' m : ℕ, p.sampledImpulse (m+1)^2))
  field_simp [hd.ne', hS.ne']

/-- v2 (β ∈ (0,1)) form of `Params.sampled_continuum_kernel_normalized_hasSum`. -/
theorem Params.sampled_continuum_kernel_normalized_hasSum_v2
    (jury : External.JuryStability) :
    HasSum (fun n : ℕ =>
      continuumRenewalKernel p.matchedDelta (((n+1 : ℕ) : ℝ)*p.matchedStep) /
        (∑' m : ℕ, continuumRenewalKernel p.matchedDelta (((m+1 : ℕ) : ℝ)*p.matchedStep))) 1 := by
  have hh := normalized_kernel_lag_hasSum_v2 jury p hb0.le hb1 hw0 hw1
  have hshift : HasSum (fun n => normalizedKernelLag p (n+1)) 1 := by
    have H := (hasSum_nat_add_iff' 1).2 hh
    simpa [normalizedKernelLag] using H
  simpa only [p.normalizedKernelLag_eq_continuum_sampling_v2 hb0 hb1 hw0 hw1 jury] using hshift

end
end SparseSGD
