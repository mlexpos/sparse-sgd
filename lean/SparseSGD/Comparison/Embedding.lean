import SparseSGD.Comparison.Similarity

namespace SparseSGD

noncomputable section

/-- One step of the discrete covariance chain expressed in the matching coordinates. -/
theorem matching_cov_step (p : Params) (x : Moments) (s : ℝ)
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hb : p.beta ≠ 0) (hs : s ^ 2 = 1)
    (hdet : G.det = p.beta) (htrace : Matrix.trace G = s * (1 + p.beta - p.w))
    (h01 : G 0 1 ≠ 0) :
    let P := matchingP s G p
    P⁻¹ * (p.step x).cov * (P⁻¹).transpose =
      G * (P⁻¹ * x.cov * (P⁻¹).transpose +
        ((2 * p.w * p.eps * (p.noise * x.R + p.additive)) /
          (p.beta * P 1 1) ^ 2) • Matrix.vecMulVec (![0, 1] : Fin 2 → ℝ) ![0, 1]) * G.transpose := by
  dsimp only
  let P := matchingP s G p
  have hPdet := matchingP_det_ne p s G hb hs h01
  have hunit : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hunit
  have hF : p.meanMatrix = s • (P * G * P⁻¹) :=
    matching_similarity p s G hb hs hdet htrace h01
  have hk : P⁻¹.mulVec kick =
      (s / (p.beta * P 1 1)) • G.mulVec ![0, 1] :=
    matching_kick_relation p s G hb hs hdet htrace h01
  rw [Params.step_cov]
  have hleft : P⁻¹ * p.meanMatrix = s • (G * P⁻¹) := by
    rw [hF, mul_smul_comm]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP, one_mul]
  have hright : p.meanMatrix.transpose * P⁻¹.transpose =
      s • (P⁻¹.transpose * G.transpose) := by
    rw [← Matrix.transpose_mul, hleft, Matrix.transpose_smul, Matrix.transpose_mul]
  have hbase :
      P⁻¹ * (p.meanMatrix * x.cov * p.meanMatrix.transpose) * P⁻¹.transpose =
        G * (P⁻¹ * x.cov * P⁻¹.transpose) * G.transpose := by
    calc
      _ = (P⁻¹ * p.meanMatrix) * x.cov *
          (p.meanMatrix.transpose * P⁻¹.transpose) := by
        simp only [Matrix.mul_assoc]
      _ = (s • (G * P⁻¹)) * x.cov * (s • (P⁻¹.transpose * G.transpose)) := by
        rw [hleft, hright]
      _ = (s * s) • (G * (P⁻¹ * x.cov * P⁻¹.transpose) * G.transpose) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.mul_assoc]
      _ = _ := by rw [← pow_two, hs, one_smul]
  have houter : P⁻¹ * Matrix.vecMulVec kick kick * P⁻¹.transpose =
      Matrix.vecMulVec (P⁻¹.mulVec kick) (P⁻¹.mulVec kick) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  have htarget : G * Matrix.vecMulVec (![0, 1] : Fin 2 → ℝ) ![0, 1] * G.transpose =
      Matrix.vecMulVec (G.mulVec ![0, 1]) (G.mulVec ![0, 1]) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  have hscalar :
      (2 * p.w * p.eps * (p.noise * x.R + p.additive)) *
          (s / (p.beta * P 1 1)) ^ 2 =
        (2 * p.w * p.eps * (p.noise * x.R + p.additive)) /
          (p.beta * P 1 1) ^ 2 := by
    rw [div_pow, hs]
    simp only [div_eq_mul_inv, one_mul]
  change P⁻¹ * (p.meanMatrix * x.cov * p.meanMatrix.transpose +
      (2 * p.w * p.eps * (p.noise * x.R + p.additive)) • Matrix.vecMulVec kick kick) *
        P⁻¹.transpose =
      G * (P⁻¹ * x.cov * P⁻¹.transpose +
        ((2 * p.w * p.eps * (p.noise * x.R + p.additive)) /
          (p.beta * P 1 1) ^ 2) • Matrix.vecMulVec (![0, 1] : Fin 2 → ℝ) ![0, 1]) * G.transpose
  simp only [Matrix.mul_add, Matrix.add_mul, mul_smul_comm, smul_mul_assoc]
  rw [hbase, houter, hk, htarget]
  congr 1
  rw [Matrix.vecMulVec_smul, Matrix.smul_vecMulVec, smul_smul, smul_smul]
  rw [mul_assoc _ (s / (p.beta * P 1 1)) (s / (p.beta * P 1 1)),
    ← pow_two, hscalar]

/-- The matching coordinates preserve the first covariance entry. -/
theorem matching_cov_first_entry (p : Params) (x : Moments) (s : ℝ)
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hb : p.beta ≠ 0) (hs : s ^ 2 = 1)
    (_hdet : G.det = p.beta) (_htrace : Matrix.trace G = s * (1 + p.beta - p.w))
    (h01 : G 0 1 ≠ 0) :
    ((matchingP s G p)⁻¹ * x.cov * ((matchingP s G p)⁻¹).transpose) 0 0 = x.R := by
  let P := matchingP s G p
  have hPdet := matchingP_det_ne p s G hb hs h01
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr (by
    simpa [P] using hPdet))
  have h01P : P 0 1 = 0 := by simp [P, matchingP]
  have h00P : P 0 0 = 1 := by simp [P, matchingP]
  have hQ01 : P⁻¹ 0 1 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hQP
    have h11P : P 1 1 ≠ 0 := by
      have hd : P.det ≠ 0 := by simpa [P] using hPdet
      simpa [P, matchingP, Matrix.det_fin_two] using hd
    have heq : P⁻¹ 0 1 * P 1 1 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, h01P] using h
    exact (mul_eq_zero.mp heq).resolve_right h11P
  have h00Q : P⁻¹ 0 0 = 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hQP
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hQ01, h00P] using h
  simp [Matrix.mul_apply, Matrix.transpose_apply, Moments.cov, Fin.sum_univ_two,
    P, h00Q, hQ01]

end
end SparseSGD
