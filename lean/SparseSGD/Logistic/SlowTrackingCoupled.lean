import SparseSGD.Logistic.SlowTrackingBounds
namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 1600000

/-- The two smooth scalar targets driving fast tracking. -/
def slowTargetMap (r : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (alpha s.1 s.2 r*s.1-r,alpha s.1 s.2 r*s.2)

def slowPosition (y : DynamicState) : ℝ × ℝ := (y 0,y 2)

def slowTrackingError (r h Phi : ℝ) (y : DynamicState) : ℝ :=
  |y 1-(slowTargetMap r (slowPosition y)).1|+
    slowFastNorm ((y 4,y 3)-slowFastTarget (1-h) Phi
      (alpha (y 0) (y 2) r) (y 2))

theorem slowTargetMap_contDiff (r : ℝ) : ContDiff ℝ ⊤ (slowTargetMap r) := by
  change ContDiff ℝ ⊤ (fun s : ℝ × ℝ =>
    (Real.exp ((s.1^2+s.2-r^2)/2)*s.1-r,Real.exp ((s.1^2+s.2-r^2)/2)*s.2))
  fun_prop

theorem slowTargetMap_lipschitz_closedBall (r M : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L (slowTargetMap r) (Metric.closedBall 0 M) := by
  exact (slowTargetMap_contDiff r).contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall 0 M) (isCompact_closedBall 0 M)

/-- Exact one-step coupling of the signal and bulk fast tracking errors.
Only elementary coefficient errors and movement of the smooth slow targets
remain on the right-hand side. -/
theorem slowCoefficientStep_tracking (r h z Phi a b d0 xi rho : ℝ)
    (y : DynamicState) (hh : 0 < h) (hh1 : h ≤ 1) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hsmall : 12*z*a ≤ h) :
    let yn := slowCoefficientStep r h z Phi a b d0 xi rho y
    slowTrackingError r h Phi yn ≤ (1-h/2)*slowTrackingError r h Phi y+
      h*|a*y 0+b*r-(alpha (y 0) (y 2) r*y 0-r)|+
      slowFastNorm (slowFastStep h z Phi a d0 xi rho (y 2)
        (slowFastTarget (1-h) Phi (alpha (y 0) (y 2) r) (y 2))-
        slowFastTarget (1-h) Phi (alpha (y 0) (y 2) r) (y 2))+
      |(slowTargetMap r (slowPosition yn)).1-(slowTargetMap r (slowPosition y)).1|+
      |(slowTargetMap r (slowPosition yn)).2-(slowTargetMap r (slowPosition y)).2| := by
  let yn := slowCoefficientStep r h z Phi a b d0 xi rho y
  let g := alpha (y 0) (y 2) r*y 0-r
  have hb : 0 ≤ 1-h := by linarith
  have hid : yn 1-g=(1-h)*(y 1-g)+h*(a*y 0+b*r-g) := by dsimp [yn,slowCoefficientStep,g]; ring
  have hy : |yn 1-g| ≤ (1-h)*|y 1-g|+h*|a*y 0+b*r-g| := by
    rw [hid]
    calc
      _ ≤ |(1-h)*(y 1-g)|+|h*(a*y 0+b*r-g)| := abs_add_le _ _
      _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg hb,abs_of_pos hh]
  have hs : |yn 1-(slowTargetMap r (slowPosition yn)).1| ≤
      (1-h/2)*|y 1-g|+h*|a*y 0+b*r-g|+
      |(slowTargetMap r (slowPosition yn)).1-(slowTargetMap r (slowPosition y)).1| := by
    have hi : yn 1-(slowTargetMap r (slowPosition yn)).1 =
      (yn 1-g)+(g-(slowTargetMap r (slowPosition yn)).1) := by ring
    rw [hi]
    have ht := abs_add_le (yn 1-g) (g-(slowTargetMap r (slowPosition yn)).1)
    have heq : |g-(slowTargetMap r (slowPosition yn)).1| =
        |(slowTargetMap r (slowPosition yn)).1-(slowTargetMap r (slowPosition y)).1| := by
      change |g-(slowTargetMap r (slowPosition yn)).1| = |(slowTargetMap r (slowPosition yn)).1-g|
      exact abs_sub_comm _ _
    rw [heq] at ht
    have hbeta : (1-h)*|y 1-g| ≤ (1-h/2)*|y 1-g| := by gcongr; linarith
    linarith
  have hf := slowFastStep_tracking h z Phi a d0 xi rho (alpha (y 0) (y 2) r) (y 2)
    (alpha (yn 0) (yn 2) r) (yn 2) (y 4,y 3) hh hh1 hz ha hsmall
  have hpair : slowFastStep h z Phi a d0 xi rho (y 2) (y 4,y 3)=(yn 4,yn 3) := by
    ext <;> simp [slowFastStep,yn,slowCoefficientStep]
  rw [hpair] at hf
  have hprod : |alpha (y 0) (y 2) r*y 2-alpha (yn 0) (yn 2) r*yn 2| =
      |(slowTargetMap r (slowPosition yn)).2-(slowTargetMap r (slowPosition y)).2| := by
    exact abs_sub_comm _ _
  rw [hprod] at hf
  dsimp only [slowTrackingError,slowTargetMap,slowPosition,yn,g] at hs hf ⊢
  nlinarith only [hs,hf]

/-- Explicit uniform forcing constant for the bulk fast target. -/
def slowFrozenConstant (E M Phi : ℝ) : ℝ :=
  let A := 4*E
  6*E*M+3*(2*A*(E*M+2*Phi)+A^2*M)+3*(12*Phi+24*Phi*M)

theorem slowFastStep_target_tame_bound (h z Phi a d0 xi rho curvature R E M e : ℝ)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hz : 0 ≤ z) (hPhi : 0 ≤ Phi)
    (hE : 0 ≤ E) (hM : 0 ≤ M) (he : 0 ≤ e) (he1 : e ≤ 1/2)
    (hc0 : 0 ≤ curvature) (hcE : curvature ≤ E) (hR : |R| ≤ M)
    (ha : |a-curvature| ≤ 6*curvature*e) (hd0 : |d0-1| ≤ 6*e)
    (hxi : |xi| ≤ 24*Phi*e) (hrho : |rho| ≤ 1) :
    slowFastNorm (slowFastStep h z Phi a d0 xi rho R (slowFastTarget (1-h) Phi curvature R)-
      slowFastTarget (1-h) Phi curvature R) ≤ slowFrozenConstant E M Phi*(z+h*e) := by
  let A := 4*E
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbeta : 0 ≤ 1-h := by linarith
  have hbeta1 : 1-h ≤ 1 := by linarith
  have hden : 0 < 1+(1-h) := by linarith
  have haA : |a| ≤ A := by
    have hs := abs_add_le (a-curvature) curvature
    rw [sub_add_cancel,abs_of_nonneg hc0] at hs
    dsimp [A]
    nlinarith
  have ha2 : a^2 ≤ A^2 := by nlinarith [sq_abs a,abs_nonneg a]
  have hw0 : |2*Phi/(1+(1-h))| ≤ 2*Phi := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 2*Phi/(1+(1-h)))]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hct : |(slowFastTarget (1-h) Phi curvature R).1| ≤ E*M+2*Phi := by
    have hs := abs_sub (curvature*R) (2*Phi/(1+(1-h)))
    rw [abs_mul,abs_of_nonneg hc0] at hs
    have hb : curvature*|R| ≤ E*M := mul_le_mul hcE hR (abs_nonneg R) hE
    exact hs.trans (by linarith)
  have hinner : |2*Phi*(d0-1)+z*a^2*rho*R+xi*R| ≤
      2*Phi*|d0-1|+z*a^2*|rho| *|R|+|xi| *|R| := by
    calc
      _ ≤ |2*Phi*(d0-1)|+|z*a^2*rho*R|+|xi*R| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = _ := by simp [abs_mul,abs_of_nonneg hPhi,abs_of_nonneg hz]
  have hw : |slowFrozenVarianceError h z Phi a d0 xi rho curvature R| ≤
      (2*A*(E*M+2*Phi)+A^2*M)*z+(12*Phi+24*Phi*M)*h*e := by
    have hp : |2*(1-h)*z*a*(slowFastTarget (1-h) Phi curvature R).1| ≤
        2*z*A*(E*M+2*Phi) := by
      rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_of_nonneg hbeta,abs_of_nonneg hz]
      norm_num
      gcongr
      linarith
    have hi : |2*Phi*(d0-1)+z*a^2*rho*R+xi*R| ≤
        12*Phi*e+z*A^2*M+24*Phi*e*M := by
      have h1 : 2*Phi*|d0-1| ≤ 2*Phi*(6*e) := mul_le_mul_of_nonneg_left hd0 (by positivity)
      have h2 : z*a^2*|rho| *|R| ≤ z*A^2*1*M := by gcongr
      have h3 : |xi| *|R| ≤ (24*Phi*e)*M := mul_le_mul hxi hR (abs_nonneg R) (by positivity)
      nlinarith only [hinner,h1,h2,h3]
    have hs := abs_add_le (2*(1-h)*z*a*(slowFastTarget (1-h) Phi curvature R).1)
      (h*(2*Phi*(d0-1)+z*a^2*rho*R+xi*R))
    rw [abs_mul h (2*Phi*(d0-1)+z*a^2*rho*R+xi*R),abs_of_nonneg hh] at hs
    have hhi := mul_le_mul_of_nonneg_left hi hh
    have hhz : h*(z*A^2*M) ≤ z*A^2*M := by
      exact mul_le_of_le_one_left (by positivity) hh1
    dsimp only [slowFrozenVarianceError]
    nlinarith only [hs,hp,hhi,hhz]
  have hb := slowFastStep_target_bound h z Phi a d0 xi rho curvature R hh hh1
  apply hb.trans
  have hae : |a-curvature| ≤ 6*E*e := ha.trans (by gcongr)
  have hmain : h*|a-curvature| *|R| ≤ h*(6*E*e)*M :=
    mul_le_mul (mul_le_mul_of_nonneg_left hae hh) hR (abs_nonneg R) (by positivity)
  have hrem : (h+2)*|slowFrozenVarianceError h z Phi a d0 xi rho curvature R| ≤
      3*((2*A*(E*M+2*Phi)+A^2*M)*z+(12*Phi+24*Phi*M)*h*e) := by gcongr; linarith
  dsimp [slowFrozenConstant,A] at *
  nlinarith only [hmain,hrem,mul_nonneg hz (show 0 ≤ 6*E*M+3*(12*Phi+24*Phi*M) by positivity),
    mul_nonneg (mul_nonneg hh he) (show 0 ≤ 3*(2*(4*E)*(E*M+2*Phi)+(4*E)^2*M) by positivity)]


theorem slowTrackingError_nonneg (r h Phi : ℝ) (y : DynamicState) :
    0 ≤ slowTrackingError r h Phi y := by
  unfold slowTrackingError slowFastNorm
  positivity

/-- Slow movement is bounded by the fast tracking error and elementary
bounded-target data. The next bulk variance is controlled through contraction,
so no a priori bound on the next iterate is required. -/
theorem slowCoefficientStep_position_increment (r h z Phi a b d0 xi rho G J A H F : ℝ)
    (y : DynamicState) (hh : 0 < h) (hh1 : h ≤ 1) (hz : 0 ≤ z)
    (hPhi : 0 ≤ Phi) (ha : 0 ≤ a) (hsmall : 12*z*a ≤ h)
    (hg : |alpha (y 0) (y 2) r*y 0-r| ≤ G)
    (hj : |alpha (y 0) (y 2) r*y 2| ≤ J) (haR : |a*y 2| ≤ A)
    (herr : |a*y 0+b*r-(alpha (y 0) (y 2) r*y 0-r)| ≤ H)
    (hfrozen : slowFastNorm (slowFastStep h z Phi a d0 xi rho (y 2)
        (slowFastTarget (1-h) Phi (alpha (y 0) (y 2) r) (y 2))-
        slowFastTarget (1-h) Phi (alpha (y 0) (y 2) r) (y 2)) ≤ F) :
    ‖slowPosition (slowCoefficientStep r h z Phi a b d0 xi rho y)-slowPosition y‖ ≤
      z*(4*slowTrackingError r h Phi y+G+2*J+6*Phi+2*A+H+F) := by
  let yn := slowCoefficientStep r h z Phi a b d0 xi rho y
  let g := alpha (y 0) (y 2) r*y 0-r
  let target := slowFastTarget (1-h) Phi (alpha (y 0) (y 2) r) (y 2)
  let eb := slowFastNorm ((y 4,y 3)-target)
  let es := |y 1-g|
  have heb : 0 ≤ eb := by dsimp [eb,slowFastNorm]; positivity
  have hes : 0 ≤ es := abs_nonneg _
  have hG : 0 ≤ G := (abs_nonneg _).trans hg
  have hJ : 0 ≤ J := (abs_nonneg _).trans hj
  have hA : 0 ≤ A := (abs_nonneg _).trans haR
  have hH : 0 ≤ H := (abs_nonneg _).trans herr
  have hbeta : 0 ≤ 1-h := by linarith
  have hden : 0 < 1+(1-h) := by linarith
  have hwtarget : |target.2| ≤ 2*Phi := by
    dsimp [target,slowFastTarget]
    rw [abs_of_nonneg (by positivity : 0 ≤ 2*Phi/(1+(1-h)))]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hctarget : |target.1| ≤ J+2*Phi := by
    exact (abs_sub _ _).trans (add_le_add hj hwtarget)
  have hc : |y 4| ≤ eb+J+2*Phi := by
    have ht := abs_add_le (y 4-target.1) target.1
    rw [sub_add_cancel] at ht
    have hec : |y 4-target.1| ≤ eb := by dsimp [eb,slowFastNorm]; nlinarith only [abs_nonneg (y 3-target.2)]
    linarith
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
  have hYn : |yn 1| ≤ es+H+G := by
    have ht := abs_add_le (yn 1-g) g
    rw [sub_add_cancel] at ht
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
  have hWn : |yn 3| ≤ eb+F+2*Phi := by
    have ht := abs_add_le (yn 3-target.2) target.2
    rw [sub_add_cancel] at ht
    linarith
  have hid0 : yn 0-y 0 = -z*yn 1 := by dsimp [yn,slowCoefficientStep]; ring
  have hid2 : yn 2-y 2 = -2*z*(1-h)*y 4-2*z*h*(a*y 2)+z*h*yn 3 := by
    dsimp [yn,slowCoefficientStep]; ring
  have hd0 : |yn 0-y 0| ≤ z*(es+H+G) := by
    rw [hid0,abs_mul,abs_neg,abs_of_nonneg hz]
    exact mul_le_mul_of_nonneg_left hYn hz
  have hd2 : |yn 2-y 2| ≤ z*(3*eb+2*J+6*Phi+2*A+F) := by
    rw [hid2]
    have ht := (abs_add_le (-2*z*(1-h)*y 4-2*z*h*(a*y 2)) (z*h*yn 3)).trans
      (add_le_add (abs_sub (-2*z*(1-h)*y 4) (2*z*h*(a*y 2))) le_rfl)
    simp only [abs_mul,abs_neg,abs_of_nonneg hz,abs_of_nonneg hbeta,abs_of_pos hh,
      ] at ht
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)] at ht
    rw [← abs_mul a (y 2)] at ht
    have hc1 : 2*z*(1-h)*|y 4| ≤ 2*z*(eb+J+2*Phi) := by
      have hb : (1-h)*|y 4| ≤ |y 4| := by nlinarith only [hh.le,abs_nonneg (y 4)]
      nlinarith only [mul_le_mul_of_nonneg_left (hb.trans hc) (show 0 ≤ 2*z by positivity)]
    have hc2 : 2*z*h*|a*y 2| ≤ 2*z*A := by
      have hb : h*|a*y 2| ≤ |a*y 2| := mul_le_of_le_one_left (abs_nonneg _) hh1
      nlinarith only [mul_le_mul_of_nonneg_left (hb.trans haR) (show 0 ≤ 2*z by positivity)]
    have hc3 : z*h*|yn 3| ≤ z*(eb+F+2*Phi) := by
      have hn : 0 ≤ eb+F+2*Phi := (abs_nonneg _).trans hWn
      exact (mul_le_mul_of_nonneg_left hWn (mul_nonneg hz hh.le)).trans
        (by nlinarith only [mul_le_of_le_one_left hn hh1,hz])
    nlinarith only [ht,hc1,hc2,hc3]
  have hn : ‖slowPosition yn-slowPosition y‖ ≤ |yn 0-y 0|+|yn 2-y 2| := by
    change max |yn 0-y 0| |yn 2-y 2| ≤ _
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  have herrid : slowTrackingError r h Phi y=es+eb := by rfl
  change ‖slowPosition yn-slowPosition y‖ ≤ _
  rw [herrid]
  nlinarith only [hn,hd0,hd2,mul_nonneg hz hes,mul_nonneg hz heb]


/-- Movement of the two smooth targets is absorbed by retention when
`z/h` is small. No limit of the retention coefficient itself is required. -/
theorem slowCoefficientStep_tracking_absorb (r h z Phi a b d0 xi rho M K Cg Cf e : ℝ)
    (L : ℝ≥0) (y : DynamicState)
    (hh : 0 < h) (hh1 : h ≤ 1) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hsmall : 12*z*a ≤ h) (hK : 0 ≤ K) (hCg : 0 ≤ Cg) (_hCf : 0 ≤ Cf)
    (he : 0 ≤ e) (habsorb : 8*(L:ℝ)*z*K ≤ h)
    (hLip : LipschitzOnWith L (slowTargetMap r) (Metric.closedBall 0 M))
    (hy : ‖slowPosition y‖ ≤ M)
    (hyn : ‖slowPosition (slowCoefficientStep r h z Phi a b d0 xi rho y)‖ ≤ M)
    (herr : |a*y 0+b*r-(alpha (y 0) (y 2) r*y 0-r)| ≤ Cg*e)
    (hfrozen : slowFastNorm (slowFastStep h z Phi a d0 xi rho (y 2)
        (slowFastTarget (1-h) Phi (alpha (y 0) (y 2) r) (y 2))-
        slowFastTarget (1-h) Phi (alpha (y 0) (y 2) r) (y 2)) ≤ Cf*(z+h*e))
    (hmove : ‖slowPosition (slowCoefficientStep r h z Phi a b d0 xi rho y)-slowPosition y‖ ≤
      z*K*(1+slowTrackingError r h Phi y)) :
    slowTrackingError r h Phi (slowCoefficientStep r h z Phi a b d0 xi rho y) ≤
      (1-h/4)*slowTrackingError r h Phi y+(Cg+Cf+2*(L:ℝ)*K)*(z+h*e) := by
  let yn := slowCoefficientStep r h z Phi a b d0 xi rho y
  have ht := slowCoefficientStep_tracking r h z Phi a b d0 xi rho y hh hh1 hz ha hsmall
  have hl : ‖slowTargetMap r (slowPosition yn)-slowTargetMap r (slowPosition y)‖ ≤
      (L:ℝ)*(z*K*(1+slowTrackingError r h Phi y)) :=
    (hLip.norm_sub_le (by simpa [yn] using hyn) (by simpa using hy)).trans
      (mul_le_mul_of_nonneg_left hmove L.coe_nonneg)
  have hl1 : |(slowTargetMap r (slowPosition yn)).1-(slowTargetMap r (slowPosition y)).1| ≤
      (L:ℝ)*(z*K*(1+slowTrackingError r h Phi y)) :=
    (norm_fst_le (slowTargetMap r (slowPosition yn)-slowTargetMap r (slowPosition y))).trans hl
  have hl2 : |(slowTargetMap r (slowPosition yn)).2-(slowTargetMap r (slowPosition y)).2| ≤
      (L:ℝ)*(z*K*(1+slowTrackingError r h Phi y)) :=
    (norm_snd_le (slowTargetMap r (slowPosition yn)-slowTargetMap r (slowPosition y))).trans hl
  have hab := mul_le_mul_of_nonneg_right habsorb (slowTrackingError_nonneg r h Phi y)
  have hcoef := mul_le_mul_of_nonneg_left herr hh.le
  have hcz : 0 ≤ Cg*z := mul_nonneg hCg hz
  have hle : 0 ≤ 2*(L:ℝ)*K*(h*e) := by positivity
  dsimp only [yn] at hl1 hl2 ⊢
  nlinarith only [ht,hl1,hl2,hab,hcoef,hfrozen,hcz,hle]

end
end SparseSGD.Logistic
