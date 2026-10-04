import SparseSGD.Logistic.FluidDeterministicWarmComparison
import SparseSGD.Logistic.FluidDeterministicSlowEventually
import SparseSGD.Logistic.WarmCoordinates
import SparseSGD.Logistic.WarmDriftBounds
namespace SparseSGD.Logistic
noncomputable section
open Filter
set_option maxHeartbeats 2400000

/-- Actual warm-start cell-2 mean paths remain bounded on every fixed min-clock
horizon. The initial fast displacement is retained through the effective
position; neither fast coordinates nor numerical containment are assumed small. -/
theorem matched_warm_slow_eventually_bounded (r0 Phi M T W : ℝ)
    (hr0 : 0≤r0) (hPhi : 0≤Phi) (hM : 2≤M) (hT : 0≤T) (hW : 0≤W)
    (v : ℝ→ℝ×ℝ)
    (hv : ∀ t∈Set.Icc 0 T, HasDerivAt v (slowVectorField r0 Phi (v t)) t)
    (hvM : ∀ t∈Set.Icc 0 T, ‖v t‖≤M-2)
    (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (S2 : SparseSGD.External.GaussianSteinCertificate 2)
    (eta beta : ℕ→ℝ) (p : ℕ→unitInterval) (mu : ∀d,Vec d) (B K : ℕ→ℕ)
    (y : ∀d,ℕ→Fin 5→ℝ)
    (hparams : ∀ᶠ d in atTop, 0<B d ∧ 0<r (mu d) ∧ r (mu d)=r0 ∧ 0<(p d:ℝ) ∧
      0<eta d ∧ 0<1-beta d ∧ 1-beta d≤1)
    (hinit : ∀ᶠ d in atTop, matchedPhysical (y d 0) ∧ ‖y d 0‖≤W ∧
      matchedEffectiveSlow (beta d) (y d 0)=v 0)
    (hrec : ∀ᶠ d in atTop, ∀ n, y d (n+1)=matchedDriftMap (B:=B d) (eta d) (beta d) (p d) (mu d) (y d n))
    (hclock : ∀ᶠ d in atTop, (K d:ℝ)*min (eta d*(p d:ℝ)) (1-beta d)≤T)
    (hdlim : Tendsto (fun d=>eta d*(p d:ℝ)/(1-beta d)) atTop (nhds 0))
    (hzlim : Tendsto (fun d=>eta d*(p d:ℝ)) atTop (nhds 0))
    (hPlim : Tendsto (fun d=>dynamicSourceLoad d (B d) (eta d)) atTop (nhds Phi))
    (hplim : Tendsto (fun d=>(p d:ℝ)) atTop (nhds 0)) :
    ∃ A : ℝ, 0≤A ∧ ∀ᶠ d in atTop, ∀ n≤K d, ‖y d n‖≤A := by
  let c := fun d n=>(matchedDriftMap (B:=B d) (eta d) (beta d) (p d) (mu d))^[n]
    (matchedColdEffective (beta d) (y d 0))
  have hc0 (d : ℕ) : c d 0=matchedColdEffective (beta d) (y d 0) := rfl
  have hcrec : ∀ d n, c d (n+1)=matchedDriftMap (B:=B d) (eta d) (beta d) (p d) (mu d) (c d n) :=
    fun d n=>Function.iterate_succ_apply' _ _ _
  have hcinit : ∀ᶠ d in atTop, matchedPhysical (c d 0) ∧
      (c d 0 0,c d 0 2)=v 0 ∧ c d 0 1=0 ∧ c d 0 3=0 ∧ c d 0 4=0 := by
    filter_upwards [hinit] with d hd
    refine ⟨matchedColdEffective_physical _ _ hd.1,?_,?_,?_,?_⟩
    · simpa [hc0,matchedColdEffective] using hd.2.2
    all_goals simp [hc0,matchedColdEffective]
  obtain ⟨Ref,hRef,href⟩ := matched_slow_eventually_bounded r0 Phi M T hPhi hM hT v hv hvM S2
    eta beta p mu B K c hparams hcinit (Eventually.of_forall hcrec) hclock hdlim hzlim hPlim hplim
  let R := Ref+5*W+1
  let P := r0+2*(Phi+1)+2
  have hR : 0≤R := by dsimp [R]; positivity
  have hP : 0≤P := by dsimp [P]; positivity
  obtain ⟨C,hC,hLipschitz⟩ := matchedDriftMap_uniform_free_lipschitz S1 r0 R P hR hP
  have hsmalllim : Tendsto (fun d=>(4*C*(eta d*(p d:ℝ))* (5*W)/(1-beta d))*Real.exp (4*C*T))
      atTop (nhds 0) := by
    have hh := hdlim.const_mul (4*C*(5*W)*Real.exp (4*C*T))
    convert hh using 1 <;> ext d <;> ring
  have hsmall : ∀ᶠ d in atTop, (4*C*(eta d*(p d:ℝ))* (5*W)/(1-beta d))*Real.exp (4*C*T)≤1 :=
    (hsmalllim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h=>h.le)
  have hDelta : ∀ᶠ d in atTop, eta d*(p d:ℝ)/(1-beta d)≤1 :=
    (hdlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h=>h.le)
  have hz : ∀ᶠ d in atTop, eta d*(p d:ℝ)≤1 :=
    (hzlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h=>h.le)
  have hpHalf : ∀ᶠ d in atTop, (p d:ℝ)≤1/2 :=
    (hplim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))).mono (fun _ h=>h.le)
  have hPhiCap : ∀ᶠ d in atTop, dynamicSourceLoad d (B d) (eta d)≤Phi+1 :=
    (hPlim.eventually (Iio_mem_nhds (by linarith : Phi<Phi+1))).mono (fun _ h=>h.le)
  refine ⟨R,hR,?_⟩
  filter_upwards [hparams,hinit,hrec,hclock,href,hsmall,hDelta,hz,hpHalf,hPhiCap,eventually_ge_atTop 2]
    with d hp hi hr hc hcRef hs hda hz1 hpH hPc hd
  rcases hp with ⟨hB,hrpos,hrEq,hp0,heta,heps,heps1⟩
  have hb0 : 0≤beta d := by linarith
  have hb1 : beta d<1 := by linarith
  have hlow : eta d*(p d:ℝ)≤1-beta d := (div_le_one heps).mp hda
  have hcl := min_clock_learning_of_small_delta _ _ _ _ hlow hc
  have hyphysical := matchedDriftOrbit_physical S2 hd hB (eta d) (beta d) (p d) (mu d) hrpos (y d) hi.1 hr
  have hcphysical := matchedDriftOrbit_physical S2 hd hB (eta d) (beta d) (p d) (mu d) hrpos (c d)
    (matchedColdEffective_physical _ _ hi.1) (hcrec d)
  have hpar : ‖matchedDimensionlessParameters (B:=B d) (eta d) (beta d) (p d) (mu d)‖≤P := by
    simpa [P,hrEq] using matchedDimensionlessParameters_norm_le (eta d) (beta d) (p d) (mu d) (Phi+1)
      hd hB heta.le hb0 hb1.le hz1 hPc
  let diff := fun n=>y d n-c d n
  let e := fun n=>matchedDriftMap (B:=B d) (eta d) (beta d) (p d) (mu d) (y d n)-
    matchedDriftMap (B:=B d) (eta d) (beta d) (p d) (mu d) (c d n)-matchedFreeOperator (beta d) (diff n)
  have hdiffrec : ∀ n, diff (n+1)=matchedFreeOperator (beta d) (diff n)+e n := by
    intro n;dsimp [diff,e];rw [hr,hcrec];module
  have hdiffinit : ∀ n, ‖((matchedFreeOperator (beta d))^n) (diff 0)‖≤5*W*(beta d)^n := by
    intro n; exact matchedColdEffective_free_decay _ _ _ _ hb0 hb1.le hi.2.1
  have hdiffLocal : ∀ n<K d, ‖diff n‖≤5*W+1 → ‖e n‖≤C*(eta d*(p d:ℝ))*‖diff n‖ := by
    intro n hn he
    have hyR : ‖y d n‖≤R := by
      calc
        _ ≤ ‖y d n-c d n‖+‖c d n‖ := norm_le_norm_sub_add _ _
        _ ≤ (5*W+1)+Ref := add_le_add he (hcRef n hn.le)
        _ = R := by dsimp [R];ring
    exact hLipschitz (eta d) (beta d) (p d) (mu d) hrEq heta.le hp0 hpH hpar
      (y d n) (c d n) (hyphysical n) (hcphysical n) hyR ((hcRef n hn.le).trans (by dsimp [R];linarith))
  have HD := warm_local_perturbation_bound (matchedFreeOperator (beta d)) diff e (beta d)
    (eta d*(p d:ℝ)) C (5*W) T (K d) hb0 hb1 (mul_nonneg heta.le hp0.le) hC (by positivity)
    hcl (matchedFreeOperator_pow_norm_le_four _ hb0 hb1.le) hdiffinit hdiffrec hdiffLocal hs
  intro n hn
  have H := HD n hn
  have hbpow : (beta d)^n≤1 := pow_le_one₀ hb0 hb1.le
  have HH := mul_le_mul_of_nonneg_left hbpow (show 0≤5*W by positivity)
  have hdiff : ‖diff n‖≤5*W+1 := by linarith
  calc
    _ ≤ ‖y d n-c d n‖+‖c d n‖ := norm_le_norm_sub_add _ _
    _ ≤ (5*W+1)+Ref := add_le_add hdiff (hcRef n hn)
    _ = R := by dsimp [R];ring
end
end SparseSGD.Logistic
