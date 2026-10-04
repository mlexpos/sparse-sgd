import SparseSGD.Logistic.SlowLimitSource
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000

theorem slowTracking_norm_bound (r Phi M h J : ℝ) (y : DynamicState)
    (hPhi : 0≤Phi) (hM : 0≤M) (hh : 0<h) (hh1 : h≤1)
    (hy : ‖slowPosition y‖≤M) (hJ : slowTrackingError r h Phi y≤J) :
    ‖y‖≤M+J+2*slowCompactCurvature M*M+|r|+4*Phi := by
  let E := slowCompactCurvature M
  let floor := 2*Phi/(1+(1-h))
  have hE : 0≤E := (Real.exp_pos _).le
  have ha : 0≤alpha (y 0) (y 2) r := (Real.exp_pos _).le
  have haE := alpha_le_slowPosition_ball r M y hM hy
  have h0 : |y 0|≤M := (norm_fst_le (slowPosition y)).trans hy
  have h2 : |y 2|≤M := (norm_snd_le (slowPosition y)).trans hy
  have hf0 : 0≤floor := by dsimp [floor]; positivity
  have hf : |floor|≤2*Phi := by
    rw [abs_of_nonneg hf0]
    apply (div_le_iff₀ (by linarith : 0<1+(1-h))).mpr
    nlinarith
  have hg : |alpha (y 0) (y 2) r*y 0-r|≤E*M+|r| := by
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg ha]
    have H := mul_le_mul haE h0 (abs_nonneg _) hE
    nlinarith
  have hc : |alpha (y 0) (y 2) r*y 2-floor|≤E*M+2*Phi := by
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg ha]
    have H := mul_le_mul haE h2 (abs_nonneg _) hE
    nlinarith
  have heq : slowTrackingError r h Phi y =
      |y 1-(alpha (y 0) (y 2) r*y 0-r)|+
        |y 4-(alpha (y 0) (y 2) r*y 2-floor)|+2*|y 3-floor| := by
    simp [slowTrackingError,slowTargetMap,slowPosition,slowFastNorm,slowFastTarget,floor]
    ring
  rw [heq] at hJ
  have hJ0 : 0≤J := (slowTrackingError_nonneg r h Phi y).trans (by rwa [heq])
  have h1 : |y 1|≤J+E*M+|r| := by
    have H := abs_sub_le (y 1) (alpha (y 0) (y 2) r*y 0-r) 0
    simp only [sub_zero] at H
    nlinarith [abs_nonneg (y 4-(alpha (y 0) (y 2) r*y 2-floor)),abs_nonneg (y 3-floor)]
  have h4 : |y 4|≤J+E*M+2*Phi := by
    have H := abs_sub_le (y 4) (alpha (y 0) (y 2) r*y 2-floor) 0
    simp only [sub_zero] at H
    nlinarith [abs_nonneg (y 1-(alpha (y 0) (y 2) r*y 0-r)),abs_nonneg (y 3-floor)]
  have h3 : |y 3|≤J+2*Phi := by
    have H := abs_sub_le (y 3) floor 0
    simp only [sub_zero] at H
    nlinarith [abs_nonneg (y 1-(alpha (y 0) (y 2) r*y 0-r)),abs_nonneg (y 4-(alpha (y 0) (y 2) r*y 2-floor)),abs_nonneg (y 3-floor)]
  apply (pi_norm_le_iff_of_nonneg (by dsimp [E] at *; positivity)).mpr
  intro i
  fin_cases i <;> simp only [Real.norm_eq_abs]
  all_goals dsimp [E] at *
  all_goals nlinarith [mul_nonneg hE hM,abs_nonneg r]
theorem slow_LR2_local_tame_containment (r0 Phi M T : ℝ) (hPhi : 0 ≤ Phi) (hM : 2 ≤ M) (hT : 0 ≤ T)
    (y : ℝ → ℝ × ℝ)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (slowVectorField r0 Phi (y t)) t)
    (hyM : ∀ t ∈ Set.Icc 0 T, ‖y t‖ ≤ M-2) :
    ∃ C A : ℝ, 0 < C ∧ 0≤A ∧ ∀ {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
      (mu : Vec d) (theta : ℕ → Vec d) (x : ℕ → DynamicState) (N : ℕ) (e : ℝ),
      r mu=r0 → dynamicSourceLoad d B eta=Phi →
      0 < (p:ℝ) → 0 < B → 2 ≤ d → 0 ≤ eta →
      0 < 1-beta → 1-beta ≤ 1 → 0 ≤ e → e ≤ 1/2 →
      (N:ℝ)*(eta*(p:ℝ)) ≤ T → slowPosition (x 0)=y 0 →
      x 0 1=0 → x 0 3=0 → x 0 4=0 →
      (∀ n < N, ‖theta n‖^2=x n 0^2+x n 2) →
      (∀ n < N, ‖slowPosition (x n)‖≤M → tameError p mu (theta n) ≤ e) →
      (∀ n < N, x (n+1)=slowDriftMap (B:=B) eta beta p mu (theta n) (x n)) →
      C*(eta*(p:ℝ)/(1-beta)+eta*(p:ℝ)+e) ≤ 1 →
      ∀ n ≤ N, ‖x n‖≤A := by
  obtain ⟨Lt,hLt⟩ := slowTargetMap_lipschitz_closedBall r0 M
  obtain ⟨Lf,F,hF,hLf,hFb⟩ := slowVectorField_compact_bounds r0 Phi M
  let E := slowCompactCurvature M
  let Cg := slowCompactSignalError r0 M
  let Cf := slowFrozenConstant E M Phi
  let K := slowCompactMovement r0 Phi M
  let J0 := 2*E*M+|r0|+6*Phi
  let Ctr := Cg+Cf+2*(Lt:ℝ)*K
  let Cres := 3+Cg+12*E*M+Cf
  let Ce := (4*Cres*J0+T*(Cres*(4*Ctr+1)+(Lf:ℝ)*F))*Real.exp (T*(Lf:ℝ))
  let C := 1+48*E+8*(Lt:ℝ)*K+K*(1+J0+4*Ctr)+2*Ce
  have hM0 : 0 ≤ M := by linarith
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hCg : 0 ≤ Cg := by dsimp [Cg,slowCompactSignalError]; positivity
  have hCf : 0 ≤ Cf := by dsimp [Cf,slowFrozenConstant]; positivity
  have hK : 0 ≤ K := by dsimp [K,slowCompactMovement]; positivity
  have hJ0 : 0 ≤ J0 := by dsimp [J0]; positivity
  have hCtr : 0 ≤ Ctr := by dsimp [Ctr]; positivity
  have hCres : 0 ≤ Cres := by dsimp [Cres]; positivity
  have hCe : 0 ≤ Ce := by dsimp [Ce]; positivity
  have hC1 : 1 ≤ C := by dsimp [C]; nlinarith only [hE,hCe,mul_nonneg Lt.coe_nonneg hK,mul_nonneg hK (show 0 ≤ 1+J0+4*Ctr by positivity)]
  have hCE : 48*E ≤ C := by dsimp [C]; linarith [mul_nonneg Lt.coe_nonneg hK,mul_nonneg hK (show 0 ≤ 1+J0+4*Ctr by positivity)]
  have hCL : 8*(Lt:ℝ)*K ≤ C := by dsimp [C]; linarith [mul_nonneg hK (show 0 ≤ 1+J0+4*Ctr by positivity)]
  have hCK : K*(1+J0+4*Ctr) ≤ C := by dsimp [C]; linarith [mul_nonneg Lt.coe_nonneg hK]
  have hCCe : 2*Ce ≤ C := by dsimp [C]; linarith [mul_nonneg Lt.coe_nonneg hK,mul_nonneg hK (show 0 ≤ 1+J0+4*Ctr by positivity)]
  let A := M+(J0+4*Ctr)+2*E*M+|r0|+4*Phi
  have hA : 0≤A := by dsimp [A]; positivity
  refine ⟨C,A,lt_of_lt_of_le (by norm_num) hC1,hA,?_⟩
  intro d B eta beta p mu theta x N e hr hload hp hB hd heta hh hh1 he he1 hNz hinit hY hW hColdC hgeom htame hrec hsmall n hn
  let z := eta*(p:ℝ)
  let h := 1-beta
  let delta := z/h
  let S := delta+z+e
  have hz : 0 ≤ z := mul_nonneg heta hp.le
  have hdelta : 0 ≤ delta := div_nonneg hz hh.le
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hS1 : S ≤ 1 := by
    have hs := mul_le_mul_of_nonneg_right hC1 hS
    change C*S ≤ 1 at hsmall
    nlinarith only [hs,hsmall]
  have hzS : z ≤ S := by dsimp [S]; linarith
  have hdeS : delta+e ≤ S := by dsimp [S]; linarith
  have hz1 : z ≤ 1 := hzS.trans hS1
  have hdelS : delta ≤ S := by dsimp [S]; linarith
  have hdh : delta*h=z := div_mul_cancel₀ z hh.ne'
  have hsmallE : 48*z*E ≤ h := by
    have he1 := (mul_le_mul_of_nonneg_right hCE hS).trans hsmall
    have he2 := mul_le_mul_of_nonneg_left hdelS (show 0 ≤ 48*E by positivity)
    have he3 := mul_le_mul_of_nonneg_right (he2.trans he1) hh.le
    rw [mul_assoc,hdh] at he3
    nlinarith only [he3]
  have habsorb : 8*(Lt:ℝ)*z*K ≤ h := by
    have he1 := (mul_le_mul_of_nonneg_right hCL hS).trans hsmall
    have he2 := mul_le_mul_of_nonneg_left hdelS (show 0 ≤ 8*(Lt:ℝ)*K by positivity)
    have he3 := mul_le_mul_of_nonneg_right (he2.trans he1) hh.le
    have hid : 8*(Lt:ℝ)*K*delta*h=8*(Lt:ℝ)*z*K := by rw [mul_assoc,hdh]; ring
    rw [hid] at he3
    simpa using he3
  have hmove : z*K*(1+J0+4*Ctr*(z/h+e)) ≤ 1 := by
    have hde1 : delta+e ≤ 1 := hdeS.trans hS1
    have hb := mul_le_mul_of_nonneg_left hde1 (show 0 ≤ 4*Ctr by positivity)
    have hf := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1+J0)) hb) (mul_nonneg hz hK)
    have hs := mul_le_mul_of_nonneg_left hzS (show 0 ≤ K*(1+J0+4*Ctr) by positivity)
    have hc := (mul_le_mul_of_nonneg_right hCK hS).trans hsmall
    dsimp [delta] at hb hf
    nlinarith only [hf,hs,hc]
  let D := 4*Ctr*(delta+e)
  let BB := (4*z*(Cres*J0)/h+T*(Cres*(D+z+e)+(Lf:ℝ)*F*z))*Real.exp (T*(Lf:ℝ))
  have hBB : BB ≤ Ce*S := by
    have hbD : D+z+e ≤ (4*Ctr+1)*S := by
      have hb := mul_le_mul_of_nonneg_left hdeS (show 0 ≤ 4*Ctr by positivity)
      dsimp [D,S] at *
      nlinarith only [hb,hdelta]
    have hb1 := mul_le_mul_of_nonneg_left hdelS (show 0 ≤ 4*Cres*J0 by positivity)
    have hb2 := mul_le_mul_of_nonneg_left hbD hCres
    have hb3 := mul_le_mul_of_nonneg_left hzS (mul_nonneg Lf.coe_nonneg hF)
    have hb23 := mul_le_mul_of_nonneg_left (add_le_add hb2 hb3) hT
    have hb := mul_le_mul_of_nonneg_right (add_le_add hb1 hb23) (Real.exp_pos (T*(Lf:ℝ))).le
    dsimp [BB,Ce,delta] at hb ⊢
    convert hb using 1 <;> ring
  have hBB1 : BB ≤ 1 := by
    have hs := mul_le_mul_of_nonneg_right hCCe hS
    have hceS : 0 ≤ Ce*S := mul_nonneg hCe hS
    have hce : Ce*S ≤ 1 := by nlinarith only [hs,hsmall,hceS]
    exact hBB.trans hce
  have hinitM : ‖slowPosition (x 0)‖ ≤ M := by
    rw [hinit]
    exact (hyM 0 ⟨le_rfl,hT⟩).trans (by linarith)
  have hfast0 := slow_cold_start_tracking r0 Phi M h (x 0) hPhi hM0 hh hh1 hinitM hY hW hColdC
  have hlocal : ∀ j < N, ‖slowPosition (x j)‖ ≤ M →
      ‖slowPosition (x (j+1))-slowPosition (x j)‖ ≤ z*K*(1+slowTrackingError r0 h Phi (x j)) ∧
      ‖slowPosition (x (j+1))-(slowPosition (x j)+z • slowVectorField r0 Phi (slowPosition (x j)))‖ ≤
        z*Cres*(slowTrackingError r0 h Phi (x j)+z+e) ∧
      (‖slowPosition (x (j+1))‖ ≤ M →
        slowTrackingError r0 h Phi (x (j+1)) ≤ (1-h/4)*slowTrackingError r0 h Phi (x j)+Ctr*(z+h*e)) := by
    intro j hj hjM
    have hs := slowDriftMap_compact_bounds r0 Phi M hPhi hM0 Lt hLt eta beta p mu (theta j) (x j)
      hr hload hp hB hd heta hh hh1 hz1 e he he1 (htame j hj hjM) (hgeom j hj) hjM hsmallE
    rw [← hrec j hj] at hs
    refine ⟨hs.1,?_,?_⟩
    · apply hs.2.1.trans
      have hfast := slowTrackingError_nonneg r0 h Phi (x j)
      have hC3 : 3 ≤ Cres := by dsimp [Cres]; nlinarith only [hCg,hCf,mul_nonneg hE hM0]
      have hCe : Cg+12*E*M+Cf ≤ Cres := by dsimp [Cres]; linarith
      have hCcf : Cf ≤ Cres := by dsimp [Cres]; nlinarith only [hCg,mul_nonneg hE hM0]
      have hb1 := mul_le_mul_of_nonneg_right hC3 hfast
      have hb2 := mul_le_mul_of_nonneg_right hCe he
      have hb3 := mul_le_mul_of_nonneg_right hCcf hz
      have hb := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hb1 hb2) hb3) hz
      nlinarith only [hb]
    · intro hjnext
      exact hs.2.2 hjnext habsorb
  have hg := slow_grid_error_of_tracking r0 Phi M T h z e J0 K Ctr Cres F Lf N x y
    hM hT hh hh1 hz he hJ0 hK hCtr hCres hF hLf hFb hy hyM hinit hfast0 hNz hlocal hmove hBB1 n hn
  have htime : (n:ℝ)*z∈Set.Icc 0 T := ⟨by positivity,
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hz).trans hNz⟩
  have hslow : ‖slowPosition (x n)‖≤M := by
    calc
      _ ≤ ‖slowPosition (x n)-y ((n:ℝ)*z)‖+‖y ((n:ℝ)*z)‖ := norm_le_norm_sub_add _ _
      _ ≤ 1+(M-2) := add_le_add (hg.1.trans hBB1) (hyM _ htime)
      _ ≤ M := by linarith
  have hq : (1-h/4)^n≤1 := pow_le_one₀ (by linarith) (by linarith)
  have htr : slowTrackingError r0 h Phi (x n)≤J0+4*Ctr := by
    have H1 := mul_le_mul_of_nonneg_right hq hJ0
    have H2 := mul_le_mul_of_nonneg_left (show delta+e≤1 from hdeS.trans hS1) (show 0≤4*Ctr by positivity)
    nlinarith [hg.2]
  exact slowTracking_norm_bound r0 Phi M h (J0+4*Ctr) (x n) hPhi hM0 hh hh1 hslow htr

end
end SparseSGD.Logistic
