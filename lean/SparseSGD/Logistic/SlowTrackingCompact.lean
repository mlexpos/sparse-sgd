import SparseSGD.Logistic.SlowTrackingResidual
namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 1600000

def slowCompactCurvature (M : ℝ) : ℝ := Real.exp ((M^2+M)/2)
def slowCompactSignalError (r M : ℝ) : ℝ := 6*slowCompactCurvature M*M+2*|r|
def slowCompactMovement (r Phi M : ℝ) : ℝ :=
  let E := slowCompactCurvature M
  let Cg := slowCompactSignalError r M
  let Cf := slowFrozenConstant E M Phi
  4+(E*M+|r|)+2*(E*M)+6*Phi+2*(4*E*M)+Cg+2*Cf

theorem alpha_le_slowPosition_ball (r M : ℝ) (y : DynamicState)
    (hM : 0 ≤ M) (hy : ‖slowPosition y‖ ≤ M) :
    alpha (y 0) (y 2) r ≤ slowCompactCurvature M := by
  have ht : |y 0| ≤ M := (norm_fst_le (slowPosition y)).trans hy
  have hR : |y 2| ≤ M := (norm_snd_le (slowPosition y)).trans hy
  unfold alpha slowCompactCurvature
  apply Real.exp_le_exp.mpr
  have hs : y 0^2 ≤ M^2 := by nlinarith [sq_abs (y 0),abs_nonneg (y 0)]
  nlinarith [le_abs_self (y 2),sq_nonneg r]

/-- Compact slow-state bounds yield quantitative movement, fast tracking
and slow Euler residual bounds. Fast coordinates themselves need not lie
in the slow-state ball. -/
theorem slowCoefficientStep_compact_bounds (r Phi M : ℝ) (hPhi : 0 ≤ Phi) (hM : 0 ≤ M)
    (L : ℝ≥0) (hLip : LipschitzOnWith L (slowTargetMap r) (Metric.closedBall 0 M))
    (h z a b d0 xi rho e : ℝ) (y : DynamicState)
    (hh : 0 < h) (hh1 : h ≤ 1) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (he : 0 ≤ e) (he1 : e ≤ 1/2) (ha0 : 0 ≤ a)
    (ha : |a-alpha (y 0) (y 2) r| ≤ 6*alpha (y 0) (y 2) r*e)
    (hb : |b+1| ≤ 2*e) (hd0 : |d0-1| ≤ 6*e) (hxi : |xi| ≤ 24*Phi*e)
    (hrho : |rho| ≤ 1) (hy : ‖slowPosition y‖ ≤ M)
    (hsmall : 48*z*slowCompactCurvature M ≤ h) :
    let yn := slowCoefficientStep r h z Phi a b d0 xi rho y
    let K := slowCompactMovement r Phi M
    let Cg := slowCompactSignalError r M
    let Cf := slowFrozenConstant (slowCompactCurvature M) M Phi
    ‖slowPosition yn-slowPosition y‖ ≤ z*K*(1+slowTrackingError r h Phi y) ∧
    ‖slowPosition yn-(slowPosition y+z • slowField r Phi (y 0) (y 2))‖ ≤
      z*(3*slowTrackingError r h Phi y+(Cg+12*slowCompactCurvature M*M+Cf)*e+Cf*z) ∧
    (‖slowPosition yn‖ ≤ M → 8*(L:ℝ)*z*K ≤ h →
      slowTrackingError r h Phi yn ≤ (1-h/4)*slowTrackingError r h Phi y+
        (Cg+Cf+2*(L:ℝ)*K)*(z+h*e)) := by
  let E := slowCompactCurvature M
  let Cg := slowCompactSignalError r M
  let Cf := slowFrozenConstant E M Phi
  let K := slowCompactMovement r Phi M
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hc0 : 0 ≤ alpha (y 0) (y 2) r := (Real.exp_pos _).le
  have hcE : alpha (y 0) (y 2) r ≤ E := alpha_le_slowPosition_ball r M y hM hy
  have htheta : |y 0| ≤ M := (norm_fst_le (slowPosition y)).trans hy
  have hR : |y 2| ≤ M := (norm_snd_le (slowPosition y)).trans hy
  have hCg : 0 ≤ Cg := by dsimp [Cg,slowCompactSignalError]; positivity
  have hCf : 0 ≤ Cf := by dsimp [Cf,slowFrozenConstant]; positivity
  have hK : 0 ≤ K := by dsimp [K,slowCompactMovement]; positivity
  have haE : |a| ≤ 4*E := by
    have hs := abs_add_le (a-alpha (y 0) (y 2) r) (alpha (y 0) (y 2) r)
    rw [sub_add_cancel,abs_of_nonneg hc0] at hs
    nlinarith
  have hcsmall : 12*z*a ≤ h := by
    have hb := mul_le_mul_of_nonneg_left ((le_abs_self a).trans haE) (show 0 ≤ 12*z by positivity)
    nlinarith only [hb,hsmall]
  have herr : |a*y 0+b*r-(alpha (y 0) (y 2) r*y 0-r)| ≤ Cg*e := by
    have hid : a*y 0+b*r-(alpha (y 0) (y 2) r*y 0-r) =
      (a-alpha (y 0) (y 2) r)*y 0+(b+1)*r := by ring
    rw [hid]
    have ht := abs_add_le ((a-alpha (y 0) (y 2) r)*y 0) ((b+1)*r)
    rw [abs_mul,abs_mul] at ht
    have hae : |a-alpha (y 0) (y 2) r| ≤ 6*E*e := ha.trans (by gcongr)
    have h1 : |a-alpha (y 0) (y 2) r| *|y 0| ≤ (6*E*e)*M :=
      mul_le_mul hae htheta (abs_nonneg _) (by positivity)
    have h2 := mul_le_mul_of_nonneg_right hb (abs_nonneg r)
    dsimp [Cg,slowCompactSignalError]
    nlinarith only [ht,h1,h2]
  have hcurv : |(a-alpha (y 0) (y 2) r)*y 2| ≤ 6*E*M*e := by
    rw [abs_mul]
    have hbnd : |a-alpha (y 0) (y 2) r| ≤ 6*E*e := ha.trans (by gcongr)
    have hm := mul_le_mul hbnd hR (abs_nonneg (y 2)) (by positivity : 0 ≤ 6*E*e)
    nlinarith only [hm]
  have hfrozen := slowFastStep_target_tame_bound h z Phi a d0 xi rho (alpha (y 0) (y 2) r)
    (y 2) E M e hh.le hh1 hz hPhi hE hM he he1 hc0 hcE hR ha hd0 hxi hrho
  have hg : |alpha (y 0) (y 2) r*y 0-r| ≤ E*M+|r| := by
    have ht := abs_sub (alpha (y 0) (y 2) r*y 0) r
    rw [abs_mul,abs_of_nonneg hc0] at ht
    exact ht.trans (add_le_add (mul_le_mul hcE htheta (abs_nonneg _) hE) le_rfl)
  have hj : |alpha (y 0) (y 2) r*y 2| ≤ E*M := by
    rw [abs_mul,abs_of_nonneg hc0]
    exact mul_le_mul hcE hR (abs_nonneg _) hE
  have haR : |a*y 2| ≤ 4*E*M := by
    rw [abs_mul]
    exact mul_le_mul haE hR (abs_nonneg _) (by positivity)
  have hmove0 := slowCoefficientStep_position_increment r h z Phi a b d0 xi rho
    (E*M+|r|) (E*M) (4*E*M) (Cg*e) (Cf*(z+h*e)) y hh hh1 hz hPhi ha0 hcsmall
    hg hj haR herr hfrozen
  have hhe : h*e ≤ 1/2 := (mul_le_of_le_one_left he hh1).trans he1
  have hforce : Cf*(z+h*e) ≤ 2*Cf := by nlinarith only [hCf,hz1,hhe]
  have hsig : Cg*e ≤ Cg := by nlinarith only [hCg,he1]
  have hmove : ‖slowPosition (slowCoefficientStep r h z Phi a b d0 xi rho y)-slowPosition y‖ ≤
      z*K*(1+slowTrackingError r h Phi y) := by
    apply hmove0.trans
    have hn := slowTrackingError_nonneg r h Phi y
    have hK4 : 4 ≤ K := by
      have hn : 0 ≤ K-4 := by dsimp [K,slowCompactMovement]; ring_nf; positivity
      linarith
    have hm := mul_le_mul_of_nonneg_left hforce hz
    have hs := mul_le_mul_of_nonneg_left hsig hz
    have ht := mul_le_mul_of_nonneg_left hK4 (mul_nonneg hz hn)
    rw [show K=4+(E*M+|r|)+2*(E*M)+6*Phi+2*(4*E*M)+Cg+2*Cf from rfl] at ht ⊢
    nlinarith only [hm,hs,ht,hz]
  refine ⟨hmove,?_,?_⟩
  · have hr := slowCoefficientStep_slow_residual r h z Phi a b d0 xi rho (Cg*e)
      (6*E*M*e) (Cf*(z+h*e)) y hh hh1 hz ha0 hcsmall herr hcurv hfrozen
    apply hr.trans
    have hf := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left he hh1) hCf) hz
    nlinarith only [hf]
  · intro hyn habsorb
    exact slowCoefficientStep_tracking_absorb r h z Phi a b d0 xi rho M K Cg Cf e L y
      hh hh1 hz ha0 hcsmall hK hCg hCf he habsorb hLip hy hyn herr hfrozen hmove

end
end SparseSGD.Logistic
