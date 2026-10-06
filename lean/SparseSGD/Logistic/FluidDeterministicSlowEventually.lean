import SparseSGD.Logistic.FluidDeterministicSlowFamily
import SparseSGD.Logistic.FluidClockCaps
namespace SparseSGD.Logistic
noncomputable section
open Filter
set_option maxHeartbeats 2000000

/-- Cell-2 actual mean-path containment for dimension-indexed families on the
source min clock. Actual rounded-batch temperatures may converge to the fixed temperature. -/
theorem matched_slow_eventually_bounded (r0 Phi M T : ℝ)
    (hPhi : 0≤Phi) (hM : 2≤M) (hT : 0≤T)
    (v : ℝ→ℝ×ℝ)
    (hv : ∀ t∈Set.Icc 0 T, HasDerivAt v (slowVectorField r0 Phi (v t)) t)
    (hvM : ∀ t∈Set.Icc 0 T, ‖v t‖≤M-2)
    (S : SparseSGD.External.GaussianSteinCertificate 2)
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
    (hplim : Tendsto (fun d=>(p d:ℝ)) atTop (nhds 0)) :
    ∃ A : ℝ, 0≤A ∧ ∀ᶠ d in atTop, ∀ n≤K d, ‖y d n‖≤A := by
  obtain ⟨C,A,hC,hA,hcontain⟩ := matched_slow_family_containment r0 Phi M T hPhi hM hT v hv hvM
  let Q := Real.sqrt (M^2+M)
  let Ct := Real.exp (2*Q^2)+Real.exp (3*Q^2/2)+(1+Real.exp (Q^2/2))*Real.exp (Q*r0)
  have hCt : 0<Ct := by dsimp [Ct]; positivity
  have htame : Tendsto (fun d=>(p d:ℝ)*Ct) atTop (nhds 0) := by
    simpa using hplim.mul_const Ct
  have hPabs : Tendsto (fun d=>|dynamicSourceLoad d (B d) (eta d)-Phi|) atTop (nhds 0) := by
    simpa using (hPlim.sub_const Phi).abs
  have helim : Tendsto (fun d=>(p d:ℝ)*Ct+|dynamicSourceLoad d (B d) (eta d)-Phi|) atTop (nhds 0) := by
    simpa using htame.add hPabs
  have hsmalllim : Tendsto (fun d=>C*(eta d*(p d:ℝ)/(1-beta d)+eta d*(p d:ℝ)+
      (p d:ℝ)*Ct+|dynamicSourceLoad d (B d) (eta d)-Phi|)) atTop (nhds 0) := by
    simpa using (((hdlim.add hzlim).add htame).add hPabs).const_mul C
  have hdaevent : ∀ᶠ d in atTop, eta d*(p d:ℝ)/(1-beta d)≤1 :=
    (hdlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h=>h.le)
  have hPaevent : ∀ᶠ d in atTop, |dynamicSourceLoad d (B d) (eta d)-Phi|≤1 :=
    (hPabs.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h=>h.le)
  have heevent : ∀ᶠ d in atTop, (p d:ℝ)*Ct+|dynamicSourceLoad d (B d) (eta d)-Phi|≤1/2 :=
    (helim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))).mono (fun _ h=>h.le)
  have hsevent : ∀ᶠ d in atTop, C*(eta d*(p d:ℝ)/(1-beta d)+eta d*(p d:ℝ)+
      (p d:ℝ)*Ct+|dynamicSourceLoad d (B d) (eta d)-Phi|)≤1 :=
    (hsmalllim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h=>h.le)
  refine ⟨2*A,by positivity,?_⟩
  filter_upwards [hparams,hinit,hrec,hclock,hdaevent,hPaevent,heevent,hsevent,eventually_ge_atTop 2] with d hp hi hr hc hda hPa he hse hd
  rcases hp with ⟨hB,hrpos,hr0,hp0,heta,heps,heps1⟩
  have hCtEq : stoppedTameConstant (mu d) Q=Ct := by simp [stoppedTameConstant,Ct,hr0]
  have hlow : eta d*(p d:ℝ)≤1-beta d := (div_le_one heps).mp hda
  have hcl := min_clock_learning_of_small_delta (eta d*(p d:ℝ)) (1-beta d) T (K d) hlow hc
  exact hcontain S (eta d) (beta d) (p d) (mu d) (y d) (K d) hd hB hrpos hr0 hp0 heta heps heps1
    hPa hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2 hr hcl
    (by simpa [Q,hCtEq] using he) (by simpa [Q,hCtEq] using hse)
end
end SparseSGD.Logistic
