import SparseSGD.Logistic.FluidDeterministicTransport
namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 2400000

/-- Compact containment of the actual matched drift in the regular cells.
The reference is an actual limiting ODE solution on its compact existence
interval. State/tame bounds of the numerical path are proved by bootstrap. -/
theorem matched_regular_reference_containment (r0 delta Phi M T : ℝ)
    (hdelta : 0<delta) (hPhi : 0≤Phi) (hM : 1≤M) (hT : 0≤T)
    (v : ℝ→DynamicState)
    (hv : ∀ t∈Set.Icc 0 T, HasDerivAt v (dynamicField r0 delta Phi (v t)) t)
    (hvM : ∀ t∈Set.Icc 0 T, ‖v t‖≤M-1) :
    ∃ C : ℝ, 0<C ∧ ∀ {d B : ℕ}
      (S : SparseSGD.External.GaussianSteinCertificate 2)
      (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (y : ℕ→Fin 5→ℝ) (K : ℕ),
      2≤d → 0<B → 0<r mu → r mu=r0 → 0<(p:ℝ) →
      0<eta → 0<1-beta → 1-beta≤1 →
      eta*(p:ℝ)/(1-beta)=delta → dynamicSourceLoad d B eta=Phi →
      matchedPhysical (y 0) → matchedToDynamic delta (y 0)=v 0 →
      (∀ n, y (n+1)=matchedDriftMap (B:=B) eta beta p mu (y n)) →
      (K:ℝ)*(1-beta)≤T →
      (p:ℝ)*stoppedTameConstant mu (Real.sqrt (M^2+M))≤1/2 →
      C*((1-beta)+(p:ℝ)*stoppedTameConstant mu (Real.sqrt (M^2+M)))≤1 →
      ∀ n≤K, ‖matchedToDynamic delta (y n)‖≤M ∧
        ‖y n‖≤(1+|delta|+delta^2)*M := by
  have hM0 : 0≤M := by linarith
  have hN : 0≤2*Phi/delta := by positivity
  obtain ⟨Cs,hCs,hcons⟩ := dynamicDriftMap_uniform_consistency r0 M delta (2*Phi/delta) hM0 hdelta.le hN
  obtain ⟨L,F,hF,hL,hFb⟩ := dynamicField_compact_bounds r0 delta Phi M
  let C := 1+T*(Cs+(L:ℝ)*F)*Real.exp (T*(L:ℝ))
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro d B S eta beta p mu y K hd hB hr hr0 hp heta hh hh1 heq hload hy0 hi hrec hclock htamesmall hsmall
  let x := fun n =>matchedToDynamic delta (y n)
  let e := (p:ℝ)*stoppedTameConstant mu (Real.sqrt (M^2+M))
  have he : 0≤e := mul_nonneg hp.le (stoppedTameConstant_pos mu _).le
  have hphysical := matchedDriftOrbit_physical S hd hB eta beta p mu hr y hy0 hrec
  have hex (n : ℕ) := exists_parameter_of_physical_state mu hd hr (y n) (hphysical n)
  choose theta ht hgeom using hex
  have hxp : ∀ n, ‖theta n‖^2=(x n 0)^2+x n 2 := by
    intro n;simpa [x,matchedToDynamic] using hgeom n
  have hxrec : ∀ n, x (n+1)=dynamicDriftMap (B:=B) eta beta p mu (theta n) (x n) := by
    intro n
    dsimp [x]
    rw [hrec,← heq]
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
  have hnoise : dynamicNoiseRate d B (1-beta) (p:ℝ)=2*Phi/delta := by
    rw [dynamicNoiseRate_eq_source d B eta (1-beta) (p:ℝ) heta.ne' hh.ne' hp.ne'
      (by exact_mod_cast Nat.ne_of_gt hB),heq,hload]
  have hlocal : ∀ n<K, ‖x n‖≤M →
      ‖x (n+1)-(x n+(1-beta) • dynamicField r0 delta Phi (x n))‖≤(1-beta)*(Cs*((1-beta)+e)) := by
    intro n hn hxn
    have H := hcons eta beta p mu (theta n) (x n) hr0 hp hB hd heta.ne' hh hh1
      ((htame n hxn).trans htamesmall) (hxp n) hxn
      (by rw [heq,abs_of_pos hdelta]) (by rw [hnoise])
    rw [← hxrec,heq,hload] at H
    apply H.trans
    have HH := mul_le_mul_of_nonneg_left (add_le_add_left (htame n hxn) (1-beta)) (mul_nonneg hCs hh.le)
    convert HH using 1 <;> ring
  have hsmall' : (‖x 0-v 0‖+T*(Cs*((1-beta)+e)+(L:ℝ)*F*(1-beta)))*Real.exp (T*(L:ℝ))≤1 := by
    have hsum : T*(Cs*((1-beta)+e)+(L:ℝ)*F*(1-beta))*Real.exp (T*(L:ℝ))≤C*((1-beta)+e) := by
      have H : (L:ℝ)*F*(1-beta)≤(L:ℝ)*F*((1-beta)+e) := by gcongr; linarith
      have H' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H hT) (Real.exp_pos (T*(L:ℝ))).le
      dsimp [C]
      nlinarith
    change C*((1-beta)+e)≤1 at hsmall
    have hinit : x 0=v 0 := hi
    rw [hinit,sub_self,norm_zero,zero_add]
    exact hsum.trans hsmall
  have H := dynamic_grid_error_of_local_residual r0 delta Phi M F (1-beta)
    (Cs*((1-beta)+e)) T L K x v hh.le (by positivity) hF hclock hv hvM hL hFb hlocal hsmall'
  intro n hn
  have htime : (n:ℝ)*(1-beta)∈Set.Icc 0 T :=
    ⟨by positivity,(mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hh.le).trans hclock⟩
  have hxM : ‖x n‖≤M := by
    calc
      _ ≤ ‖x n-v ((n:ℝ)*(1-beta))‖+‖v ((n:ℝ)*(1-beta))‖ := norm_le_norm_sub_add _ _
      _ ≤ 1+(M-1) := add_le_add ((H n hn).trans hsmall') (hvM _ htime)
      _ = M := by ring
  refine ⟨hxM,?_⟩
  rw [← dynamicToMatched_matchedToDynamic delta hdelta.ne' (y n)]
  exact dynamicToMatched_norm_bound delta M (x n) hM0 hxM
end
end SparseSGD.Logistic
