import SparseSGD.Logistic.FluidDeterministicSlowTransport
import SparseSGD.Logistic.FluidDeterministicSlowContainmentCore
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 2400000

/-- Cold-start containment in cell 2 for the actual matched drift, including
its fast layer. The numerical path is not assumed tame or bounded. -/
theorem matched_slow_reference_containment (r0 Phi M T : ℝ)
    (hPhi : 0≤Phi) (hM : 2≤M) (hT : 0≤T)
    (v : ℝ→ℝ×ℝ)
    (hv : ∀ t∈Set.Icc 0 T, HasDerivAt v (slowVectorField r0 Phi (v t)) t)
    (hvM : ∀ t∈Set.Icc 0 T, ‖v t‖≤M-2) :
    ∃ C A : ℝ, 0<C ∧ 0≤A ∧ ∀ {d B : ℕ}
      (S : SparseSGD.External.GaussianSteinCertificate 2)
      (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (y : ℕ→Fin 5→ℝ) (K : ℕ),
      2≤d → 0<B → 0<r mu → r mu=r0 → 0<(p:ℝ) →
      0<eta → 0<1-beta → 1-beta≤1 →
      dynamicSourceLoad d B eta=Phi → matchedPhysical (y 0) →
      (y 0 0,y 0 2)=v 0 → y 0 1=0 → y 0 3=0 → y 0 4=0 →
      (∀ n, y (n+1)=matchedDriftMap (B:=B) eta beta p mu (y n)) →
      (K:ℝ)*(eta*(p:ℝ))≤T →
      (p:ℝ)*stoppedTameConstant mu (Real.sqrt (M^2+M))≤1/2 →
      C*(eta*(p:ℝ)/(1-beta)+eta*(p:ℝ)+
        (p:ℝ)*stoppedTameConstant mu (Real.sqrt (M^2+M)))≤1 →
      ∀ n≤K, ‖y n‖≤2*A := by
  obtain ⟨C0,A,hC0,hA,hcore⟩ := slow_LR2_local_tame_containment r0 Phi M T hPhi hM hT v hv hvM
  refine ⟨1+C0,A,by positivity,hA,?_⟩
  intro d B S eta beta p mu y K hd hB hr hr0 hp heta hh hh1 hload hy0 hi hY hC hV hrec hclock htamesmall hsmall
  let delta := eta*(p:ℝ)/(1-beta)
  let x := fun n=>matchedToSlow delta (y n)
  let e := (p:ℝ)*stoppedTameConstant mu (Real.sqrt (M^2+M))
  have hd0 : 0<delta := by dsimp [delta]; positivity
  have he : 0≤e := mul_nonneg hp.le (stoppedTameConstant_pos mu _).le
  have hz : 0≤eta*(p:ℝ) := by positivity
  have hsum0 : 0≤delta+eta*(p:ℝ)+e := by positivity
  have hsmall0 : C0*(delta+eta*(p:ℝ)+e)≤1 := by
    change (1+C0)*(delta+eta*(p:ℝ)+e)≤1 at hsmall
    nlinarith
  have hd1 : delta≤1 := by
    change (1+C0)*(delta+eta*(p:ℝ)+e)≤1 at hsmall
    nlinarith
  have hphysical := matchedDriftOrbit_physical S hd hB eta beta p mu hr y hy0 hrec
  have hex (n : ℕ) := exists_parameter_of_physical_state mu hd hr (y n) (hphysical n)
  choose theta ht hgeom using hex
  have hxp : ∀ n, ‖theta n‖^2=(x n 0)^2+x n 2 := by
    intro n;simpa [x,matchedToSlow] using hgeom n
  have hxrec : ∀ n, x (n+1)=slowDriftMap (B:=B) eta beta p mu (theta n) (x n) := by
    intro n
    dsimp [x,delta]
    rw [hrec]
    exact matchedToSlow_drift eta beta p mu (theta n) (y n) hr hp.ne' heta.ne' hh.ne'
      (by exact_mod_cast Nat.ne_of_gt hB) (ht n) (hgeom n)
  have htame : ∀ n, ‖slowPosition (x n)‖≤M → tameError p mu (theta n)≤e := by
    intro n hn
    have h0 : |x n 0|≤M := (norm_fst_le (slowPosition (x n))).trans hn
    have h2 : |x n 2|≤M := (norm_snd_le (slowPosition (x n))).trans hn
    have hnorm : ‖theta n‖≤Real.sqrt (M^2+M) := by
      apply (Real.le_sqrt (norm_nonneg _) (by nlinarith : 0≤M^2+M)).mpr
      rw [hxp n]
      nlinarith [(abs_le.mp h0).1,(abs_le.mp h0).2,le_abs_self (x n 2)]
    exact tameError_le_stoppedNorm p mu (theta n) _ (by positivity) hnorm
  have hxinit : slowPosition (x 0)=v 0 := by simpa [x,slowPosition,matchedToSlow] using hi
  have hxY : x 0 1=0 := by simp [x,matchedToSlow,hY]
  have hxW : x 0 3=0 := by simp [x,matchedToSlow,hV]
  have hxC : x 0 4=0 := by simp [x,matchedToSlow,hC]
  have H := hcore eta beta p mu theta x K e hr0 hload hp hB hd heta.le hh hh1 he htamesmall
    hclock hxinit hxY hxW hxC (fun n _=>hxp n) (fun n _ hn=>htame n hn)
    (fun n _=>hxrec n) hsmall0
  intro n hn
  rw [← slowToMatched_matchedToSlow delta hd0.ne' (y n)]
  have HB := slowToMatched_norm_bound delta A (x n) hA (H n hn)
  apply HB.trans
  rw [abs_of_pos hd0]
  nlinarith
end
end SparseSGD.Logistic
