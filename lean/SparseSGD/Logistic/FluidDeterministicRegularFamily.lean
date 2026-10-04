import SparseSGD.Logistic.FluidDeterministicTransport
namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 2400000

/-- Compact containment of the actual matched drift in the regular cells.
The reference is an actual limiting ODE solution on its compact existence
interval. State/tame bounds of the numerical path are proved by bootstrap. -/
theorem matched_regular_family_containment (r0 delta Phi M T : ℝ)
    (hdelta : 0<delta) (hPhi : 0≤Phi) (hM : 1≤M) (hT : 0≤T)
    (v : ℝ→DynamicState)
    (hv : ∀ t∈Set.Icc 0 T, HasDerivAt v (dynamicField r0 delta Phi (v t)) t)
    (hvM : ∀ t∈Set.Icc 0 T, ‖v t‖≤M-1) :
    ∃ C : ℝ, 0<C ∧ ∀ {d B : ℕ}
      (S : SparseSGD.External.GaussianSteinCertificate 2)
      (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (y : ℕ→Fin 5→ℝ) (K : ℕ),
      2≤d → 0<B → 0<r mu → r mu=r0 → 0<(p:ℝ) →
      0<eta → 0<1-beta → 1-beta≤1 →
      |eta*(p:ℝ)/(1-beta)-delta|≤delta/2 → |dynamicSourceLoad d B eta-Phi|≤1 →
      matchedPhysical (y 0) → matchedToDynamic (eta*(p:ℝ)/(1-beta)) (y 0)=v 0 →
      (∀ n, y (n+1)=matchedDriftMap (B:=B) eta beta p mu (y n)) →
      (K:ℝ)*(1-beta)≤T →
      (p:ℝ)*stoppedTameConstant mu (Real.sqrt (M^2+M))≤1/2 →
      C*((1-beta)+(p:ℝ)*stoppedTameConstant mu (Real.sqrt (M^2+M))+
        |eta*(p:ℝ)/(1-beta)-delta|+|dynamicSourceLoad d B eta-Phi|)≤1 →
      ∀ n≤K, ‖matchedToDynamic (eta*(p:ℝ)/(1-beta)) (y n)‖≤M ∧
        ‖y n‖≤(1+2*delta+4*delta^2)*M := by
  have hM0 : 0≤M := by linarith
  let a := delta/2
  let N := 2*(|Phi|+1)/a
  let P := (2*M+1)*(1+2/a+2*|Phi|/a^2)
  have ha : 0<a := by dsimp [a]; positivity
  have hN : 0≤N := by dsimp [N]; positivity
  have hP : 0≤P := by dsimp [P]; positivity
  obtain ⟨Cs,hCs,hcons⟩ := dynamicDriftMap_uniform_consistency r0 M (2*delta) N hM0 (by positivity) hN
  obtain ⟨L,F,hF,hL,hFb⟩ := dynamicField_compact_bounds r0 delta Phi M
  let C := 1+T*(Cs+P+(L:ℝ)*F)*Real.exp (T*(L:ℝ))
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro d B S eta beta p mu y K hd hB hr hr0 hp heta hh hh1 hdeltaerr hPhierr hy0 hi hrec hclock htamesmall hsmall
  let da := eta*(p:ℝ)/(1-beta)
  let Pa := dynamicSourceLoad d B eta
  let q := |da-delta|+|Pa-Phi|
  let x := fun n =>matchedToDynamic da (y n)
  have hda : a≤da := by dsimp [a,da]; linarith [(abs_le.mp hdeltaerr).1]
  have hda0 : 0<da := ha.trans_le hda
  have hda2 : da≤2*delta := by dsimp [da]; linarith [(abs_le.mp hdeltaerr).2]
  have hPa : |Pa|≤|Phi|+1 := by
    have H := abs_add_le (Pa-Phi) Phi
    rw [sub_add_cancel] at H
    dsimp [Pa] at *
    linarith
  let e := (p:ℝ)*stoppedTameConstant mu (Real.sqrt (M^2+M))
  have he : 0≤e := mul_nonneg hp.le (stoppedTameConstant_pos mu _).le
  have hphysical := matchedDriftOrbit_physical S hd hB eta beta p mu hr y hy0 hrec
  have hex (n : ℕ) := exists_parameter_of_physical_state mu hd hr (y n) (hphysical n)
  choose theta ht hgeom using hex
  have hxp : ∀ n, ‖theta n‖^2=(x n 0)^2+x n 2 := by
    intro n;simpa [x,matchedToDynamic] using hgeom n
  have hxrec : ∀ n, x (n+1)=dynamicDriftMap (B:=B) eta beta p mu (theta n) (x n) := by
    intro n
    dsimp [x,da]
    rw [hrec]
    exact matchedToDynamic_drift eta beta p mu (theta n) (y n) hr hp.ne' heta.ne' hh.ne'
      (by exact_mod_cast Nat.ne_of_gt hB) (ht n) (hgeom n)
  have htame : ∀ n, ‖x n‖≤M → tameError p mu (theta n)≤e := by
    intro n hn
    have h0 : |x n 0|≤M := by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (x n) 0).trans hn
    have h2 : |x n 2|≤M := by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (x n) 2).trans hn
    have hnorm : ‖theta n‖≤Real.sqrt (M^2+M) := by
      apply (Real.le_sqrt (norm_nonneg _) (by positivity : 0≤M^2+M)).mpr
      rw [hxp n]
      nlinarith [(abs_le.mp h0).1,(abs_le.mp h0).2,le_abs_self (x n 2)]
    exact tameError_le_stoppedNorm p mu (theta n) _ (by positivity) hnorm
  have hnoise : dynamicNoiseRate d B (1-beta) (p:ℝ)≤N := by
    rw [dynamicNoiseRate_eq_source d B eta (1-beta) (p:ℝ) heta.ne' hh.ne' hp.ne'
      (by exact_mod_cast Nat.ne_of_gt hB)]
    change 2*Pa/da≤N
    dsimp [N]
    calc
      _ ≤ 2*|Pa|/da := by gcongr;exact le_abs_self Pa
      _ ≤ _ := by gcongr
  have hparam (w : DynamicState) (hw : ‖w‖≤M) :
      ‖dynamicField r0 da Pa w-dynamicField r0 delta Phi w‖≤P*q := by
    apply (dynamicField_parameter_error r0 da Pa delta Phi M w hM0 hw).trans
    have H := dynamicNoiseRate_parameter_error da Pa delta Phi a ha hda (by dsimp [a]; linarith)
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤2*M+1)
    dsimp [P,q]
    have h1 : 0≤2/a := by positivity
    have h2 : 0≤2*|Phi|/a^2 := by positivity
    nlinarith [abs_nonneg (da-delta),abs_nonneg (Pa-Phi),
      mul_nonneg h1 (abs_nonneg (da-delta)),mul_nonneg h2 (abs_nonneg (Pa-Phi))]
  have hlocal : ∀ n<K, ‖x n‖≤M →
      ‖x (n+1)-(x n+(1-beta) • dynamicField r0 delta Phi (x n))‖≤(1-beta)*(Cs*((1-beta)+e)+P*q) := by
    intro n hn hxn
    have H := hcons eta beta p mu (theta n) (x n) hr0 hp hB hd heta.ne' hh hh1
      ((htame n hxn).trans htamesmall) (hxp n) hxn
      (by change |da|≤2*delta;rw [abs_of_pos hda0];exact hda2) hnoise
    rw [← hxrec] at H
    change ‖x (n+1)-(x n+(1-beta) • dynamicField r0 da Pa (x n))‖≤_ at H
    have HC : ‖x (n+1)-(x n+(1-beta) • dynamicField r0 da Pa (x n))‖≤
        (1-beta)*(Cs*((1-beta)+e)) := by
      apply H.trans
      have HH := mul_le_mul_of_nonneg_left (add_le_add_left (htame n hxn) (1-beta)) (mul_nonneg hCs hh.le)
      convert HH using 1 <;> ring
    have HP : ‖(x n+(1-beta) • dynamicField r0 da Pa (x n))-
        (x n+(1-beta) • dynamicField r0 delta Phi (x n))‖≤(1-beta)*(P*q) := by
      rw [add_sub_add_left_eq_sub,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hh]
      exact mul_le_mul_of_nonneg_left (hparam _ hxn) hh.le
    have HH := (norm_sub_le_norm_sub_add_norm_sub (x (n+1)) (x n+(1-beta) • dynamicField r0 da Pa (x n))
      (x n+(1-beta) • dynamicField r0 delta Phi (x n))).trans (add_le_add HC HP)
    convert HH using 1 <;> ring
  have hsmall' : (‖x 0-v 0‖+T*(Cs*((1-beta)+e)+P*q+(L:ℝ)*F*(1-beta)))*Real.exp (T*(L:ℝ))≤1 := by
    have hq : 0≤q := by dsimp [q]; positivity
    have heps : 0≤1-beta := hh.le
    have HCs := mul_le_mul_of_nonneg_left (show (1-beta)+e≤(1-beta)+e+q by linarith) hCs
    have HP := mul_le_mul_of_nonneg_left (show q≤(1-beta)+e+q by linarith) hP
    have HLF := mul_le_mul_of_nonneg_left (show (1-beta)≤(1-beta)+e+q by linarith) (mul_nonneg L.coe_nonneg hF)
    have hsum : T*(Cs*((1-beta)+e)+P*q+(L:ℝ)*F*(1-beta))*Real.exp (T*(L:ℝ))≤C*((1-beta)+e+q) := by
      have H' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add (add_le_add HCs HP) HLF) hT)
        (Real.exp_pos (T*(L:ℝ))).le
      dsimp [C]
      nlinarith
    have hsmallq : C*((1-beta)+e+q)≤1 := by simpa [e,q,da,Pa,add_assoc] using hsmall
    have hinit : x 0=v 0 := hi
    rw [hinit,sub_self,norm_zero,zero_add]
    exact hsum.trans hsmallq
  have H := dynamic_grid_error_of_local_residual r0 delta Phi M F (1-beta)
    (Cs*((1-beta)+e)+P*q) T L K x v hh.le (by positivity) hF hclock hv hvM hL hFb hlocal hsmall'
  intro n hn
  have htime : (n:ℝ)*(1-beta)∈Set.Icc 0 T :=
    ⟨by positivity,(mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hh.le).trans hclock⟩
  have hxM : ‖x n‖≤M := by
    calc
      _ ≤ ‖x n-v ((n:ℝ)*(1-beta))‖+‖v ((n:ℝ)*(1-beta))‖ := norm_le_norm_sub_add _ _
      _ ≤ 1+(M-1) := add_le_add ((H n hn).trans hsmall') (hvM _ htime)
      _ = M := by ring
  refine ⟨hxM,?_⟩
  rw [← dynamicToMatched_matchedToDynamic da hda0.ne' (y n)]
  have HB := dynamicToMatched_norm_bound da M (x n) hM0 hxM
  apply HB.trans
  rw [abs_of_pos hda0]
  have hd2 : da^2≤4*delta^2 := by nlinarith
  nlinarith
end
end SparseSGD.Logistic
