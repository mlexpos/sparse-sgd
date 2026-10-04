import SparseSGD.Logistic.FluidDeterministicSlowContainmentCore
import SparseSGD.Logistic.FluidDeterministicSlowLoadGrid
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000

theorem slow_LR2_local_tame_load_containment (r0 Phi M T : ℝ) (hPhi : 0 ≤ Phi) (hM : 2 ≤ M) (hT : 0 ≤ T)
    (y : ℝ → ℝ × ℝ)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (slowVectorField r0 Phi (y t)) t)
    (hyM : ∀ t ∈ Set.Icc 0 T, ‖y t‖ ≤ M-2) :
    ∃ C A : ℝ, 0 < C ∧ 0≤A ∧ ∀ {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
      (mu : Vec d) (theta : ℕ → Vec d) (x : ℕ → DynamicState) (N : ℕ) (e Pa : ℝ),
      r mu=r0 → dynamicSourceLoad d B eta=Pa → 0≤Pa → Pa≤Phi+1 → |Pa-Phi|≤e →
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
  let Cf := slowFrozenConstant E M (Phi+1)
  let K := slowCompactMovement r0 (Phi+1) M
  let J0 := 2*E*M+|r0|+6*(Phi+1)
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
  have hCres : 0 ≤ Cres := by dsimp [Cres]; nlinarith only [hCg,hCf,mul_nonneg hE hM0]
  have hCe : 0 ≤ Ce := by dsimp [Ce]; positivity
  have hC1 : 1 ≤ C := by dsimp [C]; nlinarith only [hE,hCe,mul_nonneg Lt.coe_nonneg hK,mul_nonneg hK (show 0 ≤ 1+J0+4*Ctr by positivity)]
  have hCE : 48*E ≤ C := by dsimp [C]; linarith [mul_nonneg Lt.coe_nonneg hK,mul_nonneg hK (show 0 ≤ 1+J0+4*Ctr by positivity)]
  have hCL : 8*(Lt:ℝ)*K ≤ C := by dsimp [C]; linarith [mul_nonneg hK (show 0 ≤ 1+J0+4*Ctr by positivity)]
  have hCK : K*(1+J0+4*Ctr) ≤ C := by dsimp [C]; linarith [mul_nonneg Lt.coe_nonneg hK]
  have hCCe : 2*Ce ≤ C := by dsimp [C]; linarith [mul_nonneg Lt.coe_nonneg hK,mul_nonneg hK (show 0 ≤ 1+J0+4*Ctr by positivity)]
  let A := M+(J0+4*Ctr)+2*E*M+|r0|+4*(Phi+1)
  have hA : 0≤A := by dsimp [A]; positivity
  refine ⟨C,A,lt_of_lt_of_le (by norm_num) hC1,hA,?_⟩
  intro d B eta beta p mu theta x N e Pa hr hload hPa hPaUp hPaErr hp hB hd heta hh hh1 he he1 hNz hinit hY hW hColdC hgeom htame hrec hsmall n hn
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
  have hfast00 := slow_cold_start_tracking r0 Pa M h (x 0) hPa hM0 hh hh1 hinitM hY hW hColdC
  have hfast0 : slowTrackingError r0 h Pa (x 0)≤J0 := hfast00.trans (by dsimp [J0]; linarith)
  have hCfPa : slowFrozenConstant E M Pa≤Cf := by
    dsimp [Cf,slowFrozenConstant]
    gcongr
  have hKPa : slowCompactMovement r0 Pa M≤K := by
    dsimp [K,slowCompactMovement,slowFrozenConstant]
    gcongr
  have hparam (w : DynamicState) : ‖slowField r0 Pa (w 0) (w 2)-slowField r0 Phi (w 0) (w 2)‖≤2*e := by
    have heq : slowField r0 Pa (w 0) (w 2)-slowField r0 Phi (w 0) (w 2)=(0,2*(Pa-Phi)) := by
      ext <;> simp [slowField] <;> ring
    rw [heq]
    simp only [Prod.norm_def,Real.norm_eq_abs,abs_zero,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),max_eq_right (by positivity : 0≤2*|Pa-Phi|)]
    linarith
  have hlocal : ∀ j < N, ‖slowPosition (x j)‖ ≤ M →
      ‖slowPosition (x (j+1))-slowPosition (x j)‖ ≤ z*K*(1+slowTrackingError r0 h Pa (x j)) ∧
      ‖slowPosition (x (j+1))-(slowPosition (x j)+z • slowVectorField r0 Phi (slowPosition (x j)))‖ ≤
        z*Cres*(slowTrackingError r0 h Pa (x j)+z+e) ∧
      (‖slowPosition (x (j+1))‖ ≤ M →
        slowTrackingError r0 h Pa (x (j+1)) ≤ (1-h/4)*slowTrackingError r0 h Pa (x j)+Ctr*(z+h*e)) := by
    intro j hj hjM
    have hs := slowDriftMap_compact_bounds r0 Pa M hPa hM0 Lt hLt eta beta p mu (theta j) (x j)
      hr hload hp hB hd heta hh hh1 hz1 e he he1 (htame j hj hjM) (hgeom j hj) hjM hsmallE
    rw [← hrec j hj] at hs
    have hfast := slowTrackingError_nonneg r0 h Pa (x j)
    refine ⟨?_,?_,?_⟩
    · exact hs.1.trans (by
        have H := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKPa (by linarith : 0≤1+slowTrackingError r0 h Pa (x j))) hz
        convert H using 1 <;> ring)
    · have hp' : ‖(slowPosition (x j)+z • slowField r0 Pa (x j 0) (x j 2))-
          (slowPosition (x j)+z • slowField r0 Phi (x j 0) (x j 2))‖≤z*(2*e) := by
        rw [add_sub_add_left_eq_sub,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hz]
        exact mul_le_mul_of_nonneg_left (hparam (x j)) hz
      have H := (norm_sub_le_norm_sub_add_norm_sub (slowPosition (x (j+1)))
        (slowPosition (x j)+z • slowField r0 Pa (x j 0) (x j 2))
        (slowPosition (x j)+z • slowField r0 Phi (x j 0) (x j 2))).trans (add_le_add hs.2.1 hp')
      apply H.trans
      have hC3 : 3≤Cres := by dsimp [Cres]; nlinarith only [hCg,hCf,mul_nonneg hE hM0]
      have hCe : Cg+12*E*M+slowFrozenConstant E M Pa+2≤Cres := by dsimp [Cres]; linarith only [hCfPa]
      have hCf : slowFrozenConstant E M Pa≤Cres := by dsimp [Cres]; nlinarith only [hCfPa,hCg,mul_nonneg hE hM0]
      have H1 := mul_le_mul_of_nonneg_right hC3 hfast
      have H2 := mul_le_mul_of_nonneg_right hCe he
      have H3 := mul_le_mul_of_nonneg_right hCf hz
      have HH := mul_le_mul_of_nonneg_left (add_le_add (add_le_add H1 H2) H3) hz
      simpa [slowVectorField,slowPosition] using (show _≤_ from by nlinarith only [HH])
    · intro hjnext
      have habs : 8*(Lt:ℝ)*z*slowCompactMovement r0 Pa M≤h := by
        have H := mul_le_mul_of_nonneg_left hKPa (show 0≤8*(Lt:ℝ)*z by positivity)
        nlinarith only [H,habsorb]
      have H := hs.2.2 hjnext habs
      apply H.trans
      have hCtr : Cg+slowFrozenConstant E M Pa+2*(Lt:ℝ)*slowCompactMovement r0 Pa M≤Ctr := by
        have HK := mul_le_mul_of_nonneg_left hKPa (show 0≤2*(Lt:ℝ) by positivity)
        dsimp [Ctr]
        linarith only [hCfPa,HK]
      have HH := mul_le_mul_of_nonneg_right hCtr (show 0≤z+h*e by positivity)
      linarith only [H,HH]
  have hg := slow_grid_error_of_distinct_tracking_load r0 Phi Pa M T h z e J0 K Ctr Cres F Lf N x y
    hM hT hh hh1 hz he hJ0 hK hCtr hCres hF hLf hFb hy hyM hinit hfast0 hNz hlocal hmove hBB1 n hn
  have htime : (n:ℝ)*z∈Set.Icc 0 T := ⟨by positivity,
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hz).trans hNz⟩
  have hslow : ‖slowPosition (x n)‖≤M := by
    calc
      _ ≤ ‖slowPosition (x n)-y ((n:ℝ)*z)‖+‖y ((n:ℝ)*z)‖ := norm_le_norm_sub_add _ _
      _ ≤ 1+(M-2) := add_le_add (hg.1.trans hBB1) (hyM _ htime)
      _ ≤ M := by linarith
  have hq : (1-h/4)^n≤1 := pow_le_one₀ (by linarith) (by linarith)
  have htr : slowTrackingError r0 h Pa (x n)≤J0+4*Ctr := by
    have H1 := mul_le_mul_of_nonneg_right hq hJ0
    have H2 := mul_le_mul_of_nonneg_left (show delta+e≤1 from hdeS.trans hS1) (show 0≤4*Ctr by positivity)
    nlinarith only [hg.2,H1,H2]
  have H := slowTracking_norm_bound r0 Pa M h (J0+4*Ctr) (x n) hPa hM0 hh hh1 hslow htr
  exact H.trans (by dsimp [A]; linarith only [hPaUp])

end
end SparseSGD.Logistic
