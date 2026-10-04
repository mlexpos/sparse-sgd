import SparseSGD.Logistic.FluidDeterministicRegularFamily
import SparseSGD.Logistic.FluidClockCaps
namespace SparseSGD.Logistic
noncomputable section
open Filter
set_option maxHeartbeats 2000000

/-- Actual dimension-indexed regular-cell mean paths have a uniform compact
bound on the manuscript's min clock. Parameter convergence and integer-batch
load discrepancies are allowed; numerical containment is not a premise. -/
theorem matched_regular_eventually_bounded (r0 delta Phi M T : ℝ)
    (hdelta : 0<delta) (hPhi : 0≤Phi) (hM : 1≤M) (hT : 0≤T)
    (v : ℝ→DynamicState)
    (hv : ∀ t∈Set.Icc 0 (T*max 1 (1/(delta/2))), HasDerivAt v (dynamicField r0 delta Phi (v t)) t)
    (hvM : ∀ t∈Set.Icc 0 (T*max 1 (1/(delta/2))), ‖v t‖≤M-1)
    (S : SparseSGD.External.GaussianSteinCertificate 2)
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
    (hplim : Tendsto (fun d=>(p d:ℝ)) atTop (nhds 0)) :
    ∃ A : ℝ, 0≤A ∧ ∀ᶠ d in atTop, ∀ n≤K d, ‖y d n‖≤A := by
  have hH : 0≤T*max 1 (1/(delta/2)) := by positivity
  obtain ⟨C,hC,hcontain⟩ := matched_regular_family_containment r0 delta Phi M
    (T*max 1 (1/(delta/2))) hdelta hPhi hM hH v hv hvM
  let Q := Real.sqrt (M^2+M)
  let Ct := Real.exp (2*Q^2)+Real.exp (3*Q^2/2)+(1+Real.exp (Q^2/2))*Real.exp (Q*r0)
  have hCt : 0<Ct := by dsimp [Ct]; positivity
  have htame : Tendsto (fun d=>(p d:ℝ)*Ct) atTop (nhds 0) := by
    simpa using hplim.mul_const Ct
  have hdabs : Tendsto (fun d=>|eta d*(p d:ℝ)/(1-beta d)-delta|) atTop (nhds 0) := by
    simpa using (hdlim.sub_const delta).abs
  have hPabs : Tendsto (fun d=>|dynamicSourceLoad d (B d) (eta d)-Phi|) atTop (nhds 0) := by
    simpa using (hPlim.sub_const Phi).abs
  have hsmalllim : Tendsto (fun d=>C*((1-beta d)+(p d:ℝ)*Ct+
      |eta d*(p d:ℝ)/(1-beta d)-delta|+|dynamicSourceLoad d (B d) (eta d)-Phi|)) atTop (nhds 0) := by
    simpa using (((hepslim.add htame).add hdabs).add hPabs).const_mul C
  have hdaevent : ∀ᶠ d in atTop, |eta d*(p d:ℝ)/(1-beta d)-delta|≤delta/2 :=
    (hdabs.eventually (Iio_mem_nhds (by positivity : (0:ℝ)<delta/2))).mono (fun _ h=>h.le)
  have hPaevent : ∀ᶠ d in atTop, |dynamicSourceLoad d (B d) (eta d)-Phi|≤1 :=
    (hPabs.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h=>h.le)
  have htevent : ∀ᶠ d in atTop, (p d:ℝ)*Ct≤1/2 :=
    (htame.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))).mono (fun _ h=>h.le)
  have hsevent : ∀ᶠ d in atTop, C*((1-beta d)+(p d:ℝ)*Ct+
      |eta d*(p d:ℝ)/(1-beta d)-delta|+|dynamicSourceLoad d (B d) (eta d)-Phi|)≤1 :=
    (hsmalllim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h=>h.le)
  refine ⟨(1+2*delta+4*delta^2)*M,by nlinarith [sq_nonneg delta],?_⟩
  filter_upwards [hparams,hinit,hrec,hclock,hdaevent,hPaevent,htevent,hsevent,eventually_ge_atTop 2] with d hp hi hr hc hda hPa hte hse hd
  rcases hp with ⟨hB,hrpos,hr0,hp0,heta,heps,heps1⟩
  have hCtEq : stoppedTameConstant (mu d) Q=Ct := by simp [stoppedTameConstant,Ct,hr0]
  have hlow : delta/2≤eta d*(p d:ℝ)/(1-beta d) := by linarith [(abs_le.mp hda).1]
  have hcl := min_clock_retention_horizon_le_cap (eta d*(p d:ℝ)) (1-beta d) T (delta/2) (K d)
    (mul_pos heta hp0) heps hc (by positivity) hlow
  have H := hcontain S (eta d) (beta d) (p d) (mu d) (y d) (K d) hd hB hrpos hr0 hp0 heta heps heps1
    hda hPa hi.1 hi.2 hr hcl (by simpa [Q,hCtEq] using hte) (by simpa [Q,hCtEq] using hse)
  exact fun n hn=>(H n hn).2
end
end SparseSGD.Logistic
