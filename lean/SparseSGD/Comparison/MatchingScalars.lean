import SparseSGD.Comparison.MatchedParameters

namespace SparseSGD
noncomputable section

theorem Params.exp_neg_half_matchedStep (p : Params) (hb : 0 < p.beta) :
    Real.exp (-p.matchedStep / 2) = Real.sqrt p.beta := by
  have he : Real.exp (-p.matchedStep / 2)^2 = p.beta := by
    rw [pow_two, ← Real.exp_add]
    convert p.exp_neg_matchedStep hb using 1 <;> congr 1 <;> ring
  have hs : Real.sqrt p.beta = Real.exp (-p.matchedStep / 2) := by
    rw [← he, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hs.symm

theorem Params.cosh_half_matchedStep (p : Params) (hb : 0 < p.beta) :
    Real.cosh (p.matchedStep / 2) = (1+p.beta)/(2*Real.sqrt p.beta) := by
  have hs : Real.sqrt p.beta ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  have he := p.exp_neg_half_matchedStep hb
  have he' : Real.exp (p.matchedStep/2) = (Real.sqrt p.beta)⁻¹ := by
    rw [← he, ← Real.exp_neg]
    congr 1
    ring
  rw [Real.cosh_eq, he']
  rw [show -(p.matchedStep/2) = -p.matchedStep/2 by ring, he]
  field_simp
  nlinarith [Real.sq_sqrt hb.le]

theorem Params.traceCosine_abs_lt_cosh (p : Params) (hb : 0 < p.beta)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) :
    |p.traceCosine| < Real.cosh (p.matchedStep/2) := by
  rw [p.cosh_half_matchedStep hb, Params.traceCosine, abs_div,
    abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) (Real.sqrt_pos.mpr hb))]
  apply (div_lt_div_iff_of_pos_right (by positivity : 0 < 2*Real.sqrt p.beta)).mpr
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem Params.arcosh_traceCosine_lt_half_step (p : Params)
    (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) (hc : 1 < |p.traceCosine|) :
    Real.arcosh |p.traceCosine| < p.matchedStep/2 := by
  have hh : 0 < p.matchedStep/2 := div_pos (p.matchedStep_pos hb0 hb1) (by norm_num)
  have h := (Real.arcosh_lt_arcosh (by linarith : 0 < |p.traceCosine|)
    (Real.cosh_pos _)).mpr (p.traceCosine_abs_lt_cosh hb0 hw0 hw1)
  rwa [Real.arcosh_cosh hh.le] at h

theorem Params.matchedDelta_pos (p : Params) (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) : 0 < p.matchedDelta := by
  by_cases hc : |p.traceCosine| ≤ 1
  · exact p.matchedDelta_underdamped hc
  have hc' : 1 < |p.traceCosine| := lt_of_not_ge hc
  have hh := p.matchedStep_pos hb0 hb1
  have ha := Real.arcosh_nonneg hc'.le
  have hupper := p.arcosh_traceCosine_lt_half_step hb0 hb1 hw0 hw1 hc'
  have hquot : Real.arcosh |p.traceCosine| / p.matchedStep < 1/2 := by
    apply (div_lt_iff₀ hh).mpr
    linarith
  have hquot0 : 0 ≤ Real.arcosh |p.traceCosine| / p.matchedStep := div_nonneg ha hh.le
  simp only [Params.matchedDelta, hc, ite_false]
  nlinarith

end
end SparseSGD
