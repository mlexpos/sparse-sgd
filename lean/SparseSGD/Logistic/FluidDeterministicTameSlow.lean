import SparseSGD.Logistic.FluidDeterministicSlowEventually
namespace SparseSGD.Logistic
noncomputable section
open Filter
set_option maxHeartbeats 2000000

/-- A fixed positive rarity cap suffices for cold cell-2 containment. The
load may vary and no rare-probability limit or path bound is assumed. -/
theorem matched_slow_small_probability_eventually_bounded (r0 Phi M T : ℝ)
    (hPhi : 0≤Phi) (hM : 2≤M) (hT : 0≤T)
    (v : ℝ→ℝ×ℝ)
    (hv : ∀ t∈Set.Icc 0 T, HasDerivAt v (slowVectorField r0 Phi (v t)) t)
    (hvM : ∀ t∈Set.Icc 0 T, ‖v t‖≤M-2)
    (S : SparseSGD.External.GaussianSteinCertificate 2)
    : ∃ pCap A : ℝ, 0<pCap ∧ 0≤A ∧ ∀
    (eta beta : ℕ→ℝ) (p : ℕ→unitInterval) (mu : ∀d,Vec d) (B K : ℕ→ℕ)
    (y : ∀d,ℕ→Fin 5→ℝ)
    (hparams : ∀ᶠ d in atTop, 0<B d ∧ 0<r (mu d) ∧ r (mu d)=r0 ∧ 0<(p d:ℝ) ∧
      0<eta d ∧ 0<1-beta d ∧ 1-beta d≤1)
    (hinit : ∀ᶠ d in atTop, matchedPhysical (y d 0) ∧
      (y d 0 0,y d 0 2)=v 0 ∧ y d 0 1=0 ∧ y d 0 3=0 ∧ y d 0 4=0)
    (hrec : ∀ᶠ d in atTop, ∀ n, y d (n+1)=matchedDriftMap (B:=B d) (eta d) (beta d) (p d) (mu d) (y d n))
    (hclock : ∀ᶠ d in atTop, (K d:ℝ)*min (eta d*(p d:ℝ)) (1-beta d)≤T)
    (hdlim : Tendsto (fun d=>eta d*(p d:ℝ)/(1-beta d)) atTop (nhds 0))
    (hzlim : Tendsto (fun d=>eta d*(p d:ℝ)) atTop (nhds 0))
    (hPlim : Tendsto (fun d=>dynamicSourceLoad d (B d) (eta d)) atTop (nhds Phi))
    (hpp : ∀ᶠ d in atTop, (p d:ℝ)≤pCap),
    ∀ᶠ d in atTop, ∀ n≤K d, ‖y d n‖≤A := by
  obtain ⟨C,A,hC,hA,hcontain⟩ := matched_slow_family_containment r0 Phi M T hPhi hM hT v hv hvM
  let Q := Real.sqrt (M^2+M)
  let Ct := Real.exp (2*Q^2)+Real.exp (3*Q^2/2)+(1+Real.exp (Q^2/2))*Real.exp (Q*r0)
  have hCt : 0<Ct := by dsimp [Ct]; positivity
  let pCap := min (1/(4*Ct)) (1/(4*C*Ct))
  have hpcap : 0<pCap := by dsimp [pCap]; positivity
  refine ⟨pCap,2*A,hpcap,by positivity,?_⟩
  intro eta beta p mu B K y hparams hinit hrec hclock hdlim hzlim hPlim hpp
  have hPabs : Tendsto (fun d=>|dynamicSourceLoad d (B d) (eta d)-Phi|) atTop (nhds 0) := by
    simpa using (hPlim.sub_const Phi).abs
  have hsmalllim : Tendsto (fun d=>C*(eta d*(p d:ℝ)/(1-beta d)+eta d*(p d:ℝ)+
      |dynamicSourceLoad d (B d) (eta d)-Phi|)) atTop (nhds 0) := by
    simpa using ((hdlim.add hzlim).add hPabs).const_mul C
  have hdaevent : ∀ᶠ d in atTop, eta d*(p d:ℝ)/(1-beta d)≤1 :=
    (hdlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h=>h.le)
  have hPaevent : ∀ᶠ d in atTop, |dynamicSourceLoad d (B d) (eta d)-Phi|≤1/4 :=
    (hPabs.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/4))).mono (fun _ h=>h.le)
  have hsevent : ∀ᶠ d in atTop, C*(eta d*(p d:ℝ)/(1-beta d)+eta d*(p d:ℝ)+
      |dynamicSourceLoad d (B d) (eta d)-Phi|)≤1/2 :=
    (hsmalllim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))).mono (fun _ h=>h.le)
  filter_upwards [hparams,hinit,hrec,hclock,hdaevent,hPaevent,hsevent,hpp,eventually_ge_atTop 2]
    with d hp hi hr hc hda hPa hse hpp hd
  rcases hp with ⟨hB,hrpos,hr0,hp0,heta,heps,heps1⟩
  have hCtEq : stoppedTameConstant (mu d) (Real.sqrt (M^2+M))=Ct := by simp [stoppedTameConstant,Ct,Q,hr0]
  have hte : (p d:ℝ)*Ct≤1/4 := by
    have H := hpp.trans (min_le_left _ _)
    have HH := (le_div_iff₀ (show 0<4*Ct by positivity)).mp H
    nlinarith only [HH]
  have hCte : C*((p d:ℝ)*Ct)≤1/4 := by
    have H := hpp.trans (min_le_right _ _)
    have HH := (le_div_iff₀ (show 0<4*C*Ct by positivity)).mp H
    nlinarith only [HH]
  have hlow : eta d*(p d:ℝ)≤1-beta d := (div_le_one heps).mp hda
  have hcl := min_clock_learning_of_small_delta _ _ _ _ hlow hc
  exact hcontain S (eta d) (beta d) (p d) (mu d) (y d) (K d) hd hB hrpos hr0 hp0 heta heps heps1
    (hPa.trans (by norm_num : (1:ℝ)/4≤1)) hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2 hr hcl
    (by rw [hCtEq]; change (p d:ℝ)*Ct+|dynamicSourceLoad d (B d) (eta d)-Phi|≤1/2; linarith)
    (by rw [hCtEq]; change C*(eta d*(p d:ℝ)/(1-beta d)+eta d*(p d:ℝ)+
      (p d:ℝ)*Ct+|dynamicSourceLoad d (B d) (eta d)-Phi|)≤1; nlinarith only [hCte,hse])
end
end SparseSGD.Logistic
