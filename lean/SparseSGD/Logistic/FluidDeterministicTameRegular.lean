import SparseSGD.Logistic.FluidDeterministicRegularEventually
namespace SparseSGD.Logistic
noncomputable section
open Filter
set_option maxHeartbeats 2000000

/-- A fixed positive rarity cap suffices for regular-cell containment. Both the
cap and the orbit bound are chosen before dimension-indexed parameter families. -/
theorem matched_regular_small_probability_eventually_bounded (r0 delta Phi M T : ℝ)
    (hdelta : 0<delta) (hPhi : 0≤Phi) (hM : 1≤M) (hT : 0≤T)
    (v : ℝ→DynamicState)
    (hv : ∀ t∈Set.Icc 0 (T*max 1 (1/(delta/2))), HasDerivAt v (dynamicField r0 delta Phi (v t)) t)
    (hvM : ∀ t∈Set.Icc 0 (T*max 1 (1/(delta/2))), ‖v t‖≤M-1)
    (S : SparseSGD.External.GaussianSteinCertificate 2)
    : ∃ pCap A : ℝ, 0<pCap ∧ 0≤A ∧ ∀
    (eta beta : ℕ→ℝ) (p : ℕ→unitInterval) (mu : ∀d,Vec d) (B K : ℕ→ℕ)
    (y : ∀d,ℕ→Fin 5→ℝ)
    (hparams : ∀ᶠ d in atTop, 0<B d ∧ 0<r (mu d) ∧ r (mu d)=r0 ∧ 0<(p d:ℝ) ∧
      0<eta d ∧ 0<1-beta d ∧ 1-beta d≤1)
    (hinit : ∀ᶠ d in atTop, matchedPhysical (y d 0) ∧
      matchedToDynamic (eta d*(p d:ℝ)/(1-beta d)) (y d 0)=v 0)
    (hrec : ∀ᶠ d in atTop, ∀ n, y d (n+1)=matchedDriftMap (B:=B d) (eta d) (beta d) (p d) (mu d) (y d n))
    (hclock : ∀ᶠ d in atTop, (K d:ℝ)*min (eta d*(p d:ℝ)) (1-beta d)≤T)
    (hdlim : Tendsto (fun d=>eta d*(p d:ℝ)/(1-beta d)) atTop (nhds delta))
    (hPlim : Tendsto (fun d=>dynamicSourceLoad d (B d) (eta d)) atTop (nhds Phi))
    (hepslim : Tendsto (fun d=>1-beta d) atTop (nhds 0))
    (hpp : ∀ᶠ d in atTop, (p d:ℝ)≤pCap),
    ∀ᶠ d in atTop, ∀ n≤K d, ‖y d n‖≤A := by
  have hH : 0≤T*max 1 (1/(delta/2)) := by positivity
  obtain ⟨C,hC,hcontain⟩ := matched_regular_family_containment r0 delta Phi M
    (T*max 1 (1/(delta/2))) hdelta hPhi hM hH v hv hvM
  let Q := Real.sqrt (M^2+M)
  let Ct := Real.exp (2*Q^2)+Real.exp (3*Q^2/2)+(1+Real.exp (Q^2/2))*Real.exp (Q*r0)
  have hCt : 0<Ct := by dsimp [Ct]; positivity
  let pCap := min (1/(4*Ct)) (1/(4*C*Ct))
  have hpcap : 0<pCap := by dsimp [pCap]; positivity
  refine ⟨pCap,(1+2*delta+4*delta^2)*M,hpcap,by nlinarith [sq_nonneg delta],?_⟩
  intro eta beta p mu B K y hparams hinit hrec hclock hdlim hPlim hepslim hpp
  have hdabs : Tendsto (fun d=>|eta d*(p d:ℝ)/(1-beta d)-delta|) atTop (nhds 0) := by
    simpa using (hdlim.sub_const delta).abs
  have hPabs : Tendsto (fun d=>|dynamicSourceLoad d (B d) (eta d)-Phi|) atTop (nhds 0) := by
    simpa using (hPlim.sub_const Phi).abs
  have hsmalllim : Tendsto (fun d=>C*((1-beta d)+
      |eta d*(p d:ℝ)/(1-beta d)-delta|+|dynamicSourceLoad d (B d) (eta d)-Phi|)) atTop (nhds 0) := by
    simpa using ((hepslim.add hdabs).add hPabs).const_mul C
  have hdaevent : ∀ᶠ d in atTop, |eta d*(p d:ℝ)/(1-beta d)-delta|≤delta/2 :=
    (hdabs.eventually (Iio_mem_nhds (by positivity : (0:ℝ)<delta/2))).mono (fun _ h=>h.le)
  have hPaevent : ∀ᶠ d in atTop, |dynamicSourceLoad d (B d) (eta d)-Phi|≤1 :=
    (hPabs.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h=>h.le)
  have hsevent : ∀ᶠ d in atTop, C*((1-beta d)+
      |eta d*(p d:ℝ)/(1-beta d)-delta|+|dynamicSourceLoad d (B d) (eta d)-Phi|)≤1/2 :=
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
  have hlow : delta/2≤eta d*(p d:ℝ)/(1-beta d) := by linarith [(abs_le.mp hda).1]
  have hcl := min_clock_retention_horizon_le_cap (eta d*(p d:ℝ)) (1-beta d) T (delta/2) (K d)
    (mul_pos heta hp0) heps hc (by positivity) hlow
  have H := hcontain S (eta d) (beta d) (p d) (mu d) (y d) (K d) hd hB hrpos hr0 hp0 heta heps heps1
    hda hPa hi.1 hi.2 hr hcl (by simpa [Q,hCtEq] using (hte.trans (by norm_num : (1:ℝ)/4≤1/2)))
    (by rw [hCtEq]; change C*((1-beta d)+(p d:ℝ)*Ct+|eta d*(p d:ℝ)/(1-beta d)-delta|+|dynamicSourceLoad d (B d) (eta d)-Phi|)≤1; nlinarith only [hCte,hse])
  exact fun n hn=>(H n hn).2
end
end SparseSGD.Logistic
