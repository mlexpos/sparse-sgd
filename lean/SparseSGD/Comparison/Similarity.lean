import SparseSGD.Discrete.Algebra

namespace SparseSGD

open scoped Matrix

noncomputable section

def matchingP (s : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ) (p : Params) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; (1 - p.w - s * G 0 0) / p.beta, -s * G 0 1 / p.beta]

theorem matchingP_first_row (p : Params) (s : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ) :
    (matchingP s G p) 0 = ![1, 0] := by
  rfl

theorem matchingP_lowerTriangular (p : Params) (s : ℝ)
    (G : Matrix (Fin 2) (Fin 2) ℝ) : (matchingP s G p).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  fin_cases i <;> fin_cases j <;> simp_all [matchingP]

theorem matchingP_det (p : Params) (s : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ)
    (_hb : p.beta ≠ 0) (_hs : s ^ 2 = 1) (_h01 : G 0 1 ≠ 0) :
    (matchingP s G p).det = -s * G 0 1 / p.beta := by
  simp [matchingP, Matrix.det_fin_two]

theorem matchingP_det_ne (p : Params) (s : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hb : p.beta ≠ 0) (hs : s ^ 2 = 1) (h01 : G 0 1 ≠ 0) :
    (matchingP s G p).det ≠ 0 := by
  rw [matchingP_det p s G hb hs h01]
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hs0) h01) hb

theorem matching_first_relation (p : Params) (s : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hb : p.beta ≠ 0) (hs : s ^ 2 = 1)
    (hdet : G.det = p.beta) (htrace : Matrix.trace G = s * (1 + p.beta - p.w))
    (h01 : G 0 1 ≠ 0) :
    p.meanMatrix * matchingP s G p = s • (matchingP s G p * G) := by
  have hdet' : G 0 0 * G 1 1 - G 0 1 * G 1 0 = p.beta := by
    simpa [Matrix.det_fin_two] using hdet
  have htrace' : G 0 0 + G 1 1 = s * (1 + p.beta - p.w) := by
    simpa [Matrix.trace] using htrace
  have ht : s * (G 0 0 + G 1 1) = 1 + p.beta - p.w := by
    linear_combination s * htrace' + (1 + p.beta - p.w) * hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Params.meanMatrix, matchingP, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, dotProduct] <;> field_simp [hb]
  · ring
  · linear_combination s * G 0 0 * ht - s ^ 2 * hdet' - p.beta * hs
  · linear_combination s * ht

theorem matching_similarity (p : Params) (s : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hb : p.beta ≠ 0) (hs : s ^ 2 = 1)
    (hdet : G.det = p.beta) (htrace : Matrix.trace G = s * (1 + p.beta - p.w))
    (h01 : G 0 1 ≠ 0) :
    p.meanMatrix = s • (matchingP s G p * G * (matchingP s G p)⁻¹) := by
  have hPdet := matchingP_det_ne p s G hb hs h01
  have hInv := Matrix.mul_nonsing_inv (matchingP s G p)
    (isUnit_iff_ne_zero.mpr hPdet)
  have hFP := matching_first_relation p s G hb hs hdet htrace h01
  calc
    p.meanMatrix = p.meanMatrix * (matchingP s G p * (matchingP s G p)⁻¹) := by
      rw [hInv, Matrix.mul_one]
    _ = (p.meanMatrix * matchingP s G p) * (matchingP s G p)⁻¹ := by rw [Matrix.mul_assoc]
    _ = (s • (matchingP s G p * G)) * (matchingP s G p)⁻¹ := by rw [hFP]
    _ = s • (matchingP s G p * G * (matchingP s G p)⁻¹) := by
      exact smul_mul_assoc s (matchingP s G p * G) (matchingP s G p)⁻¹

theorem matching_kick_relation (p : Params) (s : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hb : p.beta ≠ 0) (hs : s ^ 2 = 1)
    (hdet : G.det = p.beta) (htrace : Matrix.trace G = s * (1 + p.beta - p.w))
    (h01 : G 0 1 ≠ 0) :
    (matchingP s G p)⁻¹ *ᵥ kick =
      (s / (p.beta * (matchingP s G p) 1 1)) • (G *ᵥ ![0, 1]) := by
  have hPdet := matchingP_det_ne p s G hb hs h01
  have h11 : (matchingP s G p) 1 1 ≠ 0 := by
    simpa [matchingP, Matrix.det_fin_two] using hPdet
  have hden : p.beta * (matchingP s G p) 1 1 ≠ 0 := mul_ne_zero hb h11
  have hPe : matchingP s G p *ᵥ ![0, 1] =
      (matchingP s G p) 1 1 • (![0, 1] : Fin 2 → ℝ) := by
    ext i
    fin_cases i <;> simp [matchingP, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hFe : p.meanMatrix *ᵥ ![0, 1] = p.beta • kick := by
    ext i
    fin_cases i <;> simp [Params.meanMatrix, kick, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  have hresp : s • ((matchingP s G p * G) *ᵥ ![0, 1]) =
      (p.beta * (matchingP s G p) 1 1) • kick := by
    rw [← Matrix.smul_mulVec, ← matching_first_relation p s G hb hs hdet htrace h01,
      ← Matrix.mulVec_mulVec, hPe, Matrix.mulVec_smul, hFe, smul_smul, mul_comm]
  have hpre : matchingP s G p *ᵥ
      ((s / (p.beta * (matchingP s G p) 1 1)) • (G *ᵥ ![0, 1])) = kick := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, div_eq_mul_inv,
      mul_comm s, ← smul_smul, hresp, smul_smul, inv_mul_cancel₀ hden, one_smul]
  rw [← hpre, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hPdet), Matrix.one_mulVec]

end
end SparseSGD
