import SparseSGD.Logistic.SlowTrackingCoupled
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

/-- The exact slow update is an Euler step plus the fast tracking defect,
the coefficient defect and the frozen fast forcing. -/
theorem slowCoefficientStep_slow_residual (r h z Phi a b d0 xi rho H D F : ℝ)
    (y : DynamicState) (hh : 0 < h) (hh1 : h ≤ 1) (hz : 0 ≤ z)
    (ha : 0 ≤ a) (hsmall : 12*z*a ≤ h)
    (herr : |a*y 0+b*r-(alpha (y 0) (y 2) r*y 0-r)| ≤ H)
    (hcurv : |(a-alpha (y 0) (y 2) r)*y 2| ≤ D)
    (hfrozen : slowFastNorm (slowFastStep h z Phi a d0 xi rho (y 2)
        (slowFastTarget (1-h) Phi (alpha (y 0) (y 2) r) (y 2))-
        slowFastTarget (1-h) Phi (alpha (y 0) (y 2) r) (y 2)) ≤ F) :
    ‖slowPosition (slowCoefficientStep r h z Phi a b d0 xi rho y)-
      (slowPosition y+z • slowField r Phi (y 0) (y 2))‖ ≤
      z*(3*slowTrackingError r h Phi y+H+2*D+F) := by
  let yn := slowCoefficientStep r h z Phi a b d0 xi rho y
  let g := alpha (y 0) (y 2) r*y 0-r
  let target := slowFastTarget (1-h) Phi (alpha (y 0) (y 2) r) (y 2)
  let eb := slowFastNorm ((y 4,y 3)-target)
  let es := |y 1-g|
  have heb : 0 ≤ eb := by dsimp [eb,slowFastNorm]; positivity
  have hes : 0 ≤ es := abs_nonneg _
  have hH : 0 ≤ H := (abs_nonneg _).trans herr
  have hD : 0 ≤ D := (abs_nonneg _).trans hcurv
  have hbeta : 0 ≤ 1-h := by linarith
  have hyid : yn 1-g=(1-h)*(y 1-g)+h*(a*y 0+b*r-g) := by
    dsimp [yn,slowCoefficientStep,g]; ring
  have hys : |yn 1-g| ≤ es+H := by
    rw [hyid]
    have ht := abs_add_le ((1-h)*(y 1-g)) (h*(a*y 0+b*r-g))
    rw [abs_mul,abs_mul,abs_of_nonneg hbeta,abs_of_pos hh] at ht
    have he1 : (1-h)*es ≤ es := by nlinarith only [hes,hh.le]
    have he2 : h*|a*y 0+b*r-g| ≤ H :=
      (mul_le_mul_of_nonneg_left herr hh.le).trans (mul_le_of_le_one_left hH hh1)
    dsimp [es] at he1
    linarith
  have hp := slowFastStep_tracking h z Phi a d0 xi rho (alpha (y 0) (y 2) r) (y 2)
    (alpha (y 0) (y 2) r) (y 2) (y 4,y 3) hh hh1 hz ha hsmall
  have hpair : slowFastStep h z Phi a d0 xi rho (y 2) (y 4,y 3)=(yn 4,yn 3) := by
    ext <;> simp [slowFastStep,yn,slowCoefficientStep]
  rw [hpair,sub_self,abs_zero,add_zero] at hp
  have hwerr : |yn 3-target.2| ≤ eb+F := by
    have hw := show |yn 3-target.2| ≤ slowFastNorm ((yn 4,yn 3)-target) by
      dsimp [slowFastNorm]; nlinarith only [abs_nonneg (yn 4-target.1),abs_nonneg (yn 3-target.2)]
    have he1 : (1-h/2)*eb ≤ eb := by nlinarith only [heb,hh.le]
    dsimp [target,eb] at hw he1 ⊢
    linarith
  have hec : |y 4-target.1| ≤ eb := by
    dsimp [eb,slowFastNorm]; nlinarith only [abs_nonneg (y 3-target.2)]
  have hr := slow_bulk_residual_identity r h z Phi a b d0 xi rho (alpha (y 0) (y 2) r) y hh1
  have hs := slow_signal_residual_identity r h z Phi a b d0 xi rho (alpha (y 0) (y 2) r) y
  have hd0 : |yn 0-y 0-z*(r-alpha (y 0) (y 2) r*y 0)| ≤ z*(es+H) := by
    rw [hs,abs_mul,abs_neg,abs_of_nonneg hz]
    exact mul_le_mul_of_nonneg_left hys hz
  have hd2 : |yn 2-y 2-z*(2*Phi-2*alpha (y 0) (y 2) r*y 2)| ≤ z*(3*eb+2*D+F) := by
    rw [hr,abs_mul,abs_of_nonneg hz]
    apply mul_le_mul_of_nonneg_left _ hz
    have ht := (abs_add_le (-2*(1-h)*(y 4-target.1)-2*h*(a-alpha (y 0) (y 2) r)*y 2)
        (h*(yn 3-target.2))).trans
      (add_le_add (abs_sub (-2*(1-h)*(y 4-target.1)) (2*h*(a-alpha (y 0) (y 2) r)*y 2)) le_rfl)
    simp only [abs_mul,abs_neg,abs_of_nonneg hbeta,abs_of_pos hh] at ht
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)] at ht

    have hc1 : 2*(1-h)*|y 4-target.1| ≤ 2*eb := by
      have hb : (1-h)*|y 4-target.1| ≤ |y 4-target.1| := by nlinarith only [hh.le,abs_nonneg (y 4-target.1)]
      linarith
    have hc2 : 2*h*|(a-alpha (y 0) (y 2) r)*y 2| ≤ 2*D := by
      have hb := mul_le_of_le_one_left (abs_nonneg ((a-alpha (y 0) (y 2) r)*y 2)) hh1
      linarith
    have hc3 : h*|yn 3-target.2| ≤ eb+F :=
      (mul_le_of_le_one_left (abs_nonneg _) hh1).trans hwerr
    rw [abs_mul] at hc2
    dsimp [target] at ht hc1 hc3
    linarith only [ht,hc1,hc2,hc3]
  have hn : ‖slowPosition yn-(slowPosition y+z • slowField r Phi (y 0) (y 2))‖ ≤
      |yn 0-y 0-z*(r-alpha (y 0) (y 2) r*y 0)|+
      |yn 2-y 2-z*(2*Phi-2*alpha (y 0) (y 2) r*y 2)| := by
    change max |yn 0-(y 0+z*(r-alpha (y 0) (y 2) r*y 0))|
      |yn 2-(y 2+z*(2*(Phi-alpha (y 0) (y 2) r*y 2)))| ≤ _
    have h0 : yn 0-(y 0+z*(r-alpha (y 0) (y 2) r*y 0))=yn 0-y 0-z*(r-alpha (y 0) (y 2) r*y 0) := by ring
    have h2 : yn 2-(y 2+z*(2*(Phi-alpha (y 0) (y 2) r*y 2)))=yn 2-y 2-z*(2*Phi-2*alpha (y 0) (y 2) r*y 2) := by ring
    rw [h0,h2]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  have herrid : slowTrackingError r h Phi y=es+eb := by rfl
  change ‖slowPosition yn-(slowPosition y+z • slowField r Phi (y 0) (y 2))‖ ≤ _
  rw [herrid]
  nlinarith only [hn,hd0,hd2,mul_nonneg hz hes]

end
end SparseSGD.Logistic
