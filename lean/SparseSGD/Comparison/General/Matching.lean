import SparseSGD.Comparison.ExactMatching

/-!
# Matching layer for the momentum range `β ∈ (0,1)` (v2)

This is the v2 matching layer (paper Definition D.1 / Lemma D.2, live chunk
`source/v2/chunks/03_master_theorem.tex`).  The v1 declarations in
`Comparison/ExactMatching.lean` carry the hypothesis `1/2 ≤ β`, used only to obtain `0 < β`.
Here they are restated under `0 < β` (with `β < 1` unchanged), as new declarations with
suffix `_v2`.  The v1 signatures are frozen.
-/

open scoped Matrix.Norms.Operator Matrix

namespace SparseSGD
noncomputable section

/-- v2 (β ∈ (0,1)) form of `Params.matchedMeanFlow_invariants`. -/
theorem Params.matchedMeanFlow_invariants_v2 (p : Params)
    (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) :
    p.matchedMeanFlow.det = p.beta ∧
    p.matchedMeanFlow.trace = p.matchingSign*(1+p.beta-p.w) ∧
    p.matchedMeanFlow 0 1 ≠ 0 := by
  have hb : 0 < p.beta := hb0
  have ht := p.matchedStep_pos hb hb1
  have hd := p.matchedDelta_pos hb hb1 hw0 hw1
  have finish (C S : ℝ → ℝ)
      (hform : p.matchedMeanFlow = oscillatorFormula p.matchedDelta C S p.matchedStep)
      (hC : C p.matchedStep = |p.traceCosine|)
      (hid : C p.matchedStep^2-(1/4-p.matchedDelta)*S p.matchedStep^2 = 1)
      (hS : S p.matchedStep ≠ 0) :
      p.matchedMeanFlow.det = p.beta ∧
      p.matchedMeanFlow.trace = p.matchingSign*(1+p.beta-p.w) ∧
      p.matchedMeanFlow 0 1 ≠ 0 := by
    constructor
    · rw [hform, oscillatorFormula_det _ _ _ _ hid, p.exp_neg_matchedStep hb]
    constructor
    · rw [hform, oscillatorFormula_trace, hC, p.matched_trace_normalization hb]
    · rw [hform]
      simp only [oscillatorFormula, Matrix.smul_apply, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]
      exact mul_ne_zero (Real.exp_ne_zero _) (mul_ne_zero (neg_ne_zero.mpr hd.ne') hS)
  by_cases hc : |p.traceCosine| = 1
  · refine finish (fun _ => 1) id ?_ ?_ ?_ ?_
    · unfold Params.matchedMeanFlow
      rw [p.matchedDelta_critical hc]
      apply continuumMeanFlow_eq_oscillatorFormula
      · rfl
      · rfl
      · intro t
        simpa using hasDerivAt_const t (1 : ℝ)
      · intro t
        exact hasDerivAt_id t
      · exact ht.le
    · exact hc.symm
    · simp [p.matchedDelta_critical hc]
    · exact ht.ne'
  by_cases hcLt : |p.traceCosine| < 1
  · let omega := p.foldedAngle/p.matchedStep
    have hangle : 0 < p.foldedAngle := Real.arccos_pos.mpr hcLt
    have ho : 0 < omega := div_pos hangle ht
    have hdform : p.matchedDelta = 1/4+omega^2 := by
      simp [Params.matchedDelta, hcLt.le, omega]
    have hsq : omega^2 = p.matchedDelta-1/4 := by linarith
    have harg : p.matchedStep*omega = p.foldedAngle := by
      dsimp [omega]
      field_simp
    refine finish (fun x => Real.cos (x*omega)) (fun x => Real.sin (x*omega)/omega) ?_ ?_ ?_ ?_
    · exact continuumMeanFlow_oscillatory _ _ _ ho.ne' hsq ht.le
    · rw [harg]
      exact Real.cos_arccos (by linarith [abs_nonneg p.traceCosine]) hcLt.le
    · have hx : 1/4-p.matchedDelta = -omega^2 := by linarith
      rw [hx, div_pow (Real.sin (p.matchedStep*omega)) omega 2]
      rw [neg_mul, mul_div_cancel₀ _ (pow_ne_zero _ ho.ne')]
      nlinarith [Real.sin_sq_add_cos_sq (p.matchedStep*omega)]
    · rw [harg]
      apply div_ne_zero _ ho.ne'
      exact (Real.sin_pos_of_pos_of_lt_pi hangle
        (by linarith [p.foldedAngle_bounds.2, Real.pi_pos])).ne'
  · have hcGt : 1 < |p.traceCosine| := by
      have hn := le_of_not_gt hcLt
      exact lt_of_le_of_ne hn (Ne.symm hc)
    let a := Real.arcosh |p.traceCosine|/p.matchedStep
    have ha : 0 < a := div_pos (Real.arcosh_pos hcGt) ht
    have hdform : p.matchedDelta = 1/4-a^2 := by
      simp [Params.matchedDelta, not_le_of_gt hcGt, a]
    have hsq : a^2 = 1/4-p.matchedDelta := by linarith
    have harg : p.matchedStep*a = Real.arcosh |p.traceCosine| := by
      dsimp [a]
      field_simp
    refine finish (fun x => Real.cosh (x*a)) (fun x => Real.sinh (x*a)/a) ?_ ?_ ?_ ?_
    · exact continuumMeanFlow_hyperbolic _ _ _ ha.ne' hsq ht.le
    · rw [harg]
      exact Real.cosh_arcosh hcGt.le
    · rw [← hsq, div_pow (Real.sinh (p.matchedStep*a)) a 2]
      rw [mul_div_cancel₀ _ (pow_ne_zero _ ha.ne')]
      nlinarith [Real.cosh_sq_sub_sinh_sq (p.matchedStep*a)]
    · rw [harg]
      exact div_ne_zero ((Real.sinh_pos_iff).2 (Real.arcosh_pos hcGt)).ne' ha.ne'

/-- v2 (β ∈ (0,1)) form of `Params.matchedMeanFlow_det`. -/
theorem Params.matchedMeanFlow_det_v2 (p : Params)
    (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) :
    p.matchedMeanFlow.det = p.beta := (p.matchedMeanFlow_invariants_v2 hb0 hb1 hw0 hw1).1

/-- v2 (β ∈ (0,1)) form of `Params.matchedMeanFlow_trace`. -/
theorem Params.matchedMeanFlow_trace_v2 (p : Params)
    (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) :
    p.matchedMeanFlow.trace = p.matchingSign*(1+p.beta-p.w) :=
  (p.matchedMeanFlow_invariants_v2 hb0 hb1 hw0 hw1).2.1

/-- v2 (β ∈ (0,1)) form of `Params.matchedMeanFlow_impulse_ne_zero`. -/
theorem Params.matchedMeanFlow_impulse_ne_zero_v2 (p : Params)
    (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) :
    p.matchedMeanFlow 0 1 ≠ 0 := (p.matchedMeanFlow_invariants_v2 hb0 hb1 hw0 hw1).2.2

/-- v2 (β ∈ (0,1)) form of `Params.exact_matching_similarity`. -/
theorem Params.exact_matching_similarity_v2 (p : Params)
    (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) :
    p.meanMatrix = p.matchingSign •
      (p.matchingMatrix * p.matchedMeanFlow * p.matchingMatrix⁻¹) := by
  obtain ⟨hd, ht, hi⟩ := p.matchedMeanFlow_invariants_v2 hb0 hb1 hw0 hw1
  exact matching_similarity p p.matchingSign p.matchedMeanFlow
    (by linarith) p.matchingSign_sq hd ht hi

/-- v2 (β ∈ (0,1)) form of `Params.exact_matching_kick`. -/
theorem Params.exact_matching_kick_v2 (p : Params)
    (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) :
    p.matchingMatrix⁻¹ *ᵥ kick =
      (p.matchingSign/(p.beta*p.matchingMatrix 1 1)) •
        (p.matchedMeanFlow *ᵥ ![0, 1]) := by
  obtain ⟨hd, ht, hi⟩ := p.matchedMeanFlow_invariants_v2 hb0 hb1 hw0 hw1
  exact matching_kick_relation p p.matchingSign p.matchedMeanFlow
    (by linarith) p.matchingSign_sq hd ht hi

/-- v2 (β ∈ (0,1)) form of `Params.matchingMatrix_unique`. -/
theorem Params.matchingMatrix_unique_v2 (p : Params) (P : Matrix (Fin 2) (Fin 2) ℝ)
    (hb0 : 0 < p.beta) (hrow : P 0 = ![1, 0])
    (hinter : p.meanMatrix*P = p.matchingSign • (P*p.matchedMeanFlow)) :
    P = p.matchingMatrix := matchingP_unique p p.matchingSign p.matchedMeanFlow P
      (by linarith) hrow hinter

/-- v2 (β ∈ (0,1)) form of `Params.matchingMatrix_det_ne_zero`. -/
theorem Params.matchingMatrix_det_ne_zero_v2 (p : Params)
    (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) : p.matchingMatrix.det ≠ 0 :=
  matchingP_det_ne p p.matchingSign p.matchedMeanFlow (by linarith) p.matchingSign_sq
    (p.matchedMeanFlow_impulse_ne_zero_v2 hb0 hb1 hw0 hw1)

/-- v2 (β ∈ (0,1)) form of `Params.exact_matching_existsUnique`. -/
theorem Params.exact_matching_existsUnique_v2 (p : Params)
    (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) :
    ∃! P : Matrix (Fin 2) (Fin 2) ℝ,
      P 0 = ![1, 0] ∧ P.IsLowerTriangular ∧ P.det ≠ 0 ∧
      p.meanMatrix = p.matchingSign • (P*p.matchedMeanFlow*P⁻¹) := by
  refine ⟨p.matchingMatrix, ?_, ?_⟩
  · exact ⟨matchingP_first_row p p.matchingSign p.matchedMeanFlow,
      matchingP_lowerTriangular p p.matchingSign p.matchedMeanFlow,
      p.matchingMatrix_det_ne_zero_v2 hb0 hb1 hw0 hw1,
      p.exact_matching_similarity_v2 hb0 hb1 hw0 hw1⟩
  · intro P hP
    apply p.matchingMatrix_unique_v2 P hb0 hP.1
    rw [hP.2.2.2, smul_mul_assoc]
    simp only [Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hP.2.2.1), Matrix.mul_one]

end
end SparseSGD
