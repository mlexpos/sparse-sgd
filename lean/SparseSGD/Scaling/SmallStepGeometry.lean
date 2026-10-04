import SparseSGD.Scaling.MatchingTaylor
import SparseSGD.Scaling.RetentionClock

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1000000

theorem Params.small_step_bounds (p : Params) (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1) :
    0 < p.eps ∧ p.eps ≤ 1/2 ∧ p.eps ≤ p.matchedStep ∧
    p.matchedStep ≤ p.eps+2*p.eps^2 ∧ p.matchedStep ≤ 2*p.eps ∧
    1/2 ≤ Real.sqrt p.beta ∧ Real.sqrt p.beta < 1 := by
  have he : 0 < p.eps := by dsimp [Params.eps]; linarith
  have he1 : p.eps ≤ 1/2 := by dsimp [Params.eps]; linarith
  have H := Scaling.retentionClock_bounds p.eps he he1
  have hh : Scaling.retentionClock p.eps=p.matchedStep := by simp [Scaling.retentionClock,Params.eps,Params.matchedStep]
  rw [hh] at H
  have hs0 := Real.sqrt_nonneg p.beta
  have hs2 := Real.sq_sqrt (show 0≤p.beta by linarith)
  exact ⟨he,he1,H.1,H.2,by nlinarith,by nlinarith,by nlinarith⟩

theorem Params.small_step_trace (p : Params) (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 ≤ p.w) (hw1 : p.w ≤ 1/16) :
    0 < p.traceCosine ∧ 1-p.traceCosine ≤ p.w := by
  obtain ⟨_,_,_,_,_,hs,_⟩ := p.small_step_bounds hb0 hb1
  have hs0 : 0 < Real.sqrt p.beta := by linarith
  have hs2 := Real.sq_sqrt (show 0≤p.beta by linarith)
  constructor
  · exact div_pos (by linarith : 0<1+p.beta-p.w) (by positivity)
  · have H : 1-p.w ≤ p.traceCosine := by
      apply (le_div_iff₀ (show 0<2*Real.sqrt p.beta by positivity)).mpr
      nlinarith [sq_nonneg (Real.sqrt p.beta-1),mul_nonneg hw0 (show 0≤2*Real.sqrt p.beta-1 by linarith)]
    linarith

/-- Small physical curvature makes the folded angle small, without excluding
critical damping. -/
theorem Params.small_step_angle (p : Params) (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 ≤ p.w) (hw1 : p.w ≤ 1/16) (hc : |p.traceCosine| ≤ 1) :
    p.foldedAngle^2 ≤ 8*p.w ∧ p.foldedAngle ≤ 1 := by
  obtain ⟨hq,hqerr⟩ := p.small_step_trace hb0 hb1 hw0 hw1
  obtain ⟨ha0,ha1⟩ := p.foldedAngle_bounds
  have hq1 : p.traceCosine ≤ 1 := by simpa only [abs_of_pos hq] using hc
  have hcos : Real.cos p.foldedAngle=p.traceCosine := by
    unfold Params.foldedAngle
    rw [abs_of_pos hq,Real.cos_arccos (by linarith) hq1]
  have H := Real.cos_le_one_sub_mul_cos_sq (show |p.foldedAngle|≤Real.pi by
    rw [abs_of_nonneg ha0]; linarith [Real.pi_pos])
  rw [hcos] at H
  have hp : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have Hmul := mul_le_mul_of_nonneg_right H hp.le
  have hmul : (1-2/Real.pi^2*p.foldedAngle^2)*Real.pi^2=Real.pi^2-2*p.foldedAngle^2 := by field_simp
  rw [hmul] at Hmul
  have hpi : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_pos,Real.pi_lt_four]
  have Hpi := mul_le_mul_of_nonneg_right hpi (show 0≤1-p.traceCosine by linarith)
  have Ha : p.foldedAngle^2 ≤ 8*p.w := by nlinarith only [Hmul,Hpi,hqerr]
  exact ⟨Ha,by nlinarith⟩

/-- The exact trace displacement in raw retention coordinates. -/
theorem Params.small_step_trace_identity (p : Params) (Delta : ℝ)
    (hb0 : 0 < p.beta) (hw : p.w=Delta*p.eps^2) :
    p.traceCosine-1=p.eps^2/(2*Real.sqrt p.beta)*
      (1/(1+Real.sqrt p.beta)^2-Delta) := by
  have hs := Real.sq_sqrt hb0.le
  have hs0 := Real.sqrt_pos.mpr hb0
  have he : p.eps=(1-Real.sqrt p.beta)*(1+Real.sqrt p.beta) := by dsimp [Params.eps]; nlinarith only [hs]
  rw [Params.traceCosine,hw,he]
  have hplus : 1+Real.sqrt p.beta ≠ 0 := by positivity
  field_simp
  nlinarith only [hs]

end
end SparseSGD
