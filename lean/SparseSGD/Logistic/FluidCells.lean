import SparseSGD.Logistic.FluidFamily
import SparseSGD.Logistic.FluidDeterministicRegularEventually
import SparseSGD.Logistic.FluidDeterministicSlowEventually
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency.types false

def coldState (d : ℕ) : State d := (0,0)

@[simp] theorem matchedSummary_coldState {d : ℕ} (eta beta : ℝ) (mu : Vec d) :
    matchedSummary eta beta mu (coldState d) = 0 := by
  ext i
  fin_cases i <;> simp [matchedSummary,coldState,signalCoord,bulkPart]

/-- On a compact existence interval, an actual ODE reference is bounded.
No numerical-path containment is being assumed. -/
private theorem compact_reference_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E) (T : ℝ) (dv : ℝ → E)
    (hv : ∀ t ∈ Set.Icc 0 T, HasDerivAt v (dv t) t) :
    ∃ A : ℝ, 0 < A ∧ ∀ t ∈ Set.Icc 0 T, ‖v t‖ ≤ A := by
  have hcont : ContinuousOn v (Set.Icc 0 T) := fun t ht => (hv t ht).continuousAt.continuousWithinAt
  obtain ⟨A,hA,ha⟩ := ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) T)).image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  exact ⟨A,hA,fun t ht => ha _ ⟨t,ht,rfl⟩⟩

/-- Actual cold-start LR fluid limit in the regular cells 3 and 4, on the
manuscript's min clock. The ODE reference is an actual solution on its compact
existence interval. Actual mean-path containment, Jacobian stability,
physical Taylor estimates, A3 and stochastic bootstrap are all proved. -/
theorem actual_fluid_cells_three_four
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : ∀ n, SparseSGD.External.GaussianSteinCertificate n)
    (B : ℕ → ℕ)
    (F : ∀ d, SparseSGD.External.MartingaleBernsteinCertificate (World d (B d)))
    (eta beta : ℕ → ℝ) (p : ℕ → unitInterval) (mu : ∀ d, Vec d) (N : ℕ → ℕ)
    (teacherNorm delta Phi T q : ℝ)
    (hr : 0 < teacherNorm) (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) (hT : 0 ≤ T) (hq : 0 ≤ q+14)
    (v : ℝ → DynamicState) (hv0 : v 0=0)
    (hv : ∀ t ∈ Set.Icc 0 (T*max 1 (1/(delta/2))), HasDerivAt v (dynamicField teacherNorm delta Phi (v t)) t)
    (hparams : ∀ᶠ d : ℕ in atTop, 0 < B d ∧ 0 < r (mu d) ∧ r (mu d)=teacherNorm ∧ 0 < (p d : ℝ) ∧
      0 < eta d ∧ 0 < 1-beta d ∧ 1-beta d ≤ 1)
    (hclock : ∀ᶠ d : ℕ in atTop, (N d : ℝ)*min (eta d*(p d : ℝ)) (1-beta d) ≤ T)
    (hdlim : Tendsto (fun d => eta d*(p d : ℝ)/(1-beta d)) atTop (𝓝 delta))
    (hPlim : Tendsto (fun d => dynamicSourceLoad d (B d) (eta d)) atTop (𝓝 Phi))
    (hepslim : Tendsto (fun d => 1-beta d) atTop (𝓝 0))
    (hplim : Tendsto (fun d => (p d : ℝ)) atTop (𝓝 0))
    (hetaSize : Tendsto (fun d => eta d*Real.sqrt (Real.log d/(d : ℝ))) atTop (𝓝 0))
    (hN : ∀ᶠ d : ℕ in atTop, 0 < N d)
    (hpoly : ∀ᶠ d : ℕ in atTop, (N d : ℝ) ≤ (d : ℝ)^q) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ENNReal.ofReal (1-((d : ℝ)^10)⁻¹) ≤
        (worldLaw (B := B d) (p d) (Measure.dirac (coldState d))) {ω | ∀ k ≤ N d,
          ‖matchedProcess (eta d) (beta d) (p d) (mu d) k ω-
            matchedOrbit (B := B d) (eta d) (beta d) (p d) (mu d) (coldState d) k‖ ≤
              C*Real.sqrt (Real.log d/(d : ℝ))} := by
  obtain ⟨A,hA,ha⟩ := compact_reference_bound v (T*max 1 (1/(delta/2)))
    (fun t => dynamicField teacherNorm delta Phi (v t)) hv
  let y := fun d => matchedOrbit (B := B d) (eta d) (beta d) (p d) (mu d) (coldState d)
  have hinit : ∀ᶠ d : ℕ in atTop, matchedPhysical (y d 0) ∧
      matchedToDynamic (eta d*(p d : ℝ)/(1-beta d)) (y d 0)=v 0 := by
    filter_upwards with d
    constructor
    · exact matchedSummary_physical _ _ _ _
    · simp [y,matchedOrbit,matchedToDynamic,hv0]
  have hrec : ∀ᶠ d : ℕ in atTop, ∀ n, y d (n+1)=matchedDriftMap (B := B d) (eta d) (beta d) (p d) (mu d) (y d n) :=
    Filter.Eventually.of_forall (fun d => matchedOrbit_succ _ _ _ _ _)
  obtain ⟨RefBound,hRef,href⟩ := matched_regular_eventually_bounded teacherNorm delta Phi (A+1) T hdelta hPhi
    (by linarith) hT v hv (fun t ht => by simpa using ha t ht) (S 2) eta beta p mu B N y hparams hinit hrec
    hclock hdlim hPlim hepslim hplim
  have hdomain : ∀ᶠ d : ℕ in atTop, 0 < B d ∧ 0 ≤ eta d ∧ (0 ≤ beta d ∧ beta d < 1) ∧
      0 < (p d : ℝ) ∧ r (mu d)=teacherNorm := by
    filter_upwards [hparams] with d hp
    rcases hp with ⟨hb,hm,hmu,hp,he,heps,heps1⟩
    exact ⟨hb,he.le,⟨by linarith,by linarith⟩,hp,hmu⟩
  have hzlim : Tendsto (fun d => eta d*(p d : ℝ)) atTop (𝓝 0) := by
    have heq : (fun d => (1-beta d)*(eta d*(p d : ℝ)/(1-beta d))) =ᶠ[atTop]
        (fun d => eta d*(p d : ℝ)) := by
      filter_upwards [hparams] with d hp
      have he : 1-beta d ≠ 0 := ne_of_gt hp.2.2.2.2.2.1
      field_simp [he]
    have ht := hepslim.mul hdlim
    simpa using ht.congr' heq
  have hdeltaCap : ∀ᶠ d : ℕ in atTop, eta d*(p d : ℝ)/(1-beta d) ≤ delta+1 :=
    (hdlim.eventually (gt_mem_nhds (by linarith : delta < delta+1))).mono (fun _ h => h.le)
  have hclockCap : ∀ᶠ d : ℕ in atTop, (N d : ℝ)*(eta d*(p d : ℝ)) ≤ T*max 1 (delta+1) := by
    filter_upwards [hparams,hclock,hdeltaCap] with d hp hc hd
    exact min_clock_learning_horizon_le_cap _ _ _ _ _ (mul_pos hp.2.2.2.2.1 hp.2.2.2.1)
      hp.2.2.2.2.2.1 hc hd
  have hloadCap : ∀ᶠ d : ℕ in atTop, logisticPhi d (B d) (eta d) ≤ Phi+1 := by
    have hh := hPlim.eventually (gt_mem_nhds (by linarith : Phi < Phi+1))
    filter_upwards [hh] with d hd
    exact hd.le
  exact actual_matched_fluid_family H Ho G S B F eta beta p mu (fun d => coldState d) N teacherNorm RefBound (Phi+1)
    (T*max 1 (delta+1)) q hr hRef (by linarith) (by positivity) hq
    (hdomain.mono (fun d h => h.1)) (hdomain.mono (fun d h => h.2.1))
    (hdomain.mono (fun d h => h.2.2.1)) (hdomain.mono (fun d h => h.2.2.2.1))
    (hdomain.mono (fun d h => h.2.2.2.2)) hloadCap hplim hzlim hetaSize hN hpoly hclockCap href
/-- Actual cold-start LR fluid limit in cell 2, on the min clock. The
limiting slow ODE supplies the compact reference; its boundedness and actual
five-coordinate numerical containment are derived rather than assumed. -/
theorem actual_fluid_cell_two
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : ∀ n, SparseSGD.External.GaussianSteinCertificate n)
    (B : ℕ → ℕ)
    (F : ∀ d, SparseSGD.External.MartingaleBernsteinCertificate (World d (B d)))
    (eta beta : ℕ → ℝ) (p : ℕ → unitInterval) (mu : ∀ d, Vec d) (N : ℕ → ℕ)
    (teacherNorm Phi T q : ℝ)
    (hr : 0 < teacherNorm) (hPhi : 0 ≤ Phi) (hT : 0 ≤ T) (hq : 0 ≤ q+14)
    (v : ℝ → ℝ×ℝ) (hv0 : v 0=0)
    (hv : ∀ t ∈ Set.Icc 0 T, HasDerivAt v (slowVectorField teacherNorm Phi (v t)) t)
    (hparams : ∀ᶠ d : ℕ in atTop, 0 < B d ∧ 0 < r (mu d) ∧ r (mu d)=teacherNorm ∧ 0 < (p d : ℝ) ∧
      0 < eta d ∧ 0 < 1-beta d ∧ 1-beta d ≤ 1)
    (hclock : ∀ᶠ d : ℕ in atTop, (N d : ℝ)*min (eta d*(p d : ℝ)) (1-beta d) ≤ T)
    (hdlim : Tendsto (fun d => eta d*(p d : ℝ)/(1-beta d)) atTop (𝓝 0))
    (hzlim : Tendsto (fun d => eta d*(p d : ℝ)) atTop (𝓝 0))
    (hPlim : Tendsto (fun d => dynamicSourceLoad d (B d) (eta d)) atTop (𝓝 Phi))
    (hplim : Tendsto (fun d => (p d : ℝ)) atTop (𝓝 0))
    (hetaSize : Tendsto (fun d => eta d*Real.sqrt (Real.log d/(d : ℝ))) atTop (𝓝 0))
    (hN : ∀ᶠ d : ℕ in atTop, 0 < N d)
    (hpoly : ∀ᶠ d : ℕ in atTop, (N d : ℝ) ≤ (d : ℝ)^q) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ENNReal.ofReal (1-((d : ℝ)^10)⁻¹) ≤
        (worldLaw (B := B d) (p d) (Measure.dirac (coldState d))) {ω | ∀ k ≤ N d,
          ‖matchedProcess (eta d) (beta d) (p d) (mu d) k ω-
            matchedOrbit (B := B d) (eta d) (beta d) (p d) (mu d) (coldState d) k‖ ≤
              C*Real.sqrt (Real.log d/(d : ℝ))} := by
  obtain ⟨A,hA,ha⟩ := compact_reference_bound v T
    (fun t => slowVectorField teacherNorm Phi (v t)) hv
  let y := fun d => matchedOrbit (B := B d) (eta d) (beta d) (p d) (mu d) (coldState d)
  have hinit : ∀ᶠ d : ℕ in atTop, matchedPhysical (y d 0) ∧
      (y d 0 0,y d 0 2)=v 0 ∧ y d 0 1=0 ∧ y d 0 3=0 ∧ y d 0 4=0 := by
    filter_upwards with d
    refine ⟨matchedSummary_physical _ _ _ _, ?_⟩
    simp [y,matchedOrbit,hv0]
  have hrec : ∀ᶠ d : ℕ in atTop, ∀ n, y d (n+1)=matchedDriftMap (B := B d) (eta d) (beta d) (p d) (mu d) (y d n) :=
    Filter.Eventually.of_forall (fun d => matchedOrbit_succ _ _ _ _ _)
  obtain ⟨RefBound,hRef,href⟩ := matched_slow_eventually_bounded teacherNorm Phi (A+2) T hPhi
    (by linarith) hT v hv (fun t ht => by simpa using ha t ht) (S 2) eta beta p mu B N y hparams hinit hrec
    hclock hdlim hzlim hPlim hplim
  have hdomain : ∀ᶠ d : ℕ in atTop, 0 < B d ∧ 0 ≤ eta d ∧ (0 ≤ beta d ∧ beta d < 1) ∧
      0 < (p d : ℝ) ∧ r (mu d)=teacherNorm := by
    filter_upwards [hparams] with d hp
    rcases hp with ⟨hb,hm,hmu,hp,he,heps,heps1⟩
    exact ⟨hb,he.le,⟨by linarith,by linarith⟩,hp,hmu⟩
  have hdeltaCap : ∀ᶠ d : ℕ in atTop, eta d*(p d : ℝ)/(1-beta d) ≤ 1 :=
    (hdlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h => h.le)
  have hclockCap : ∀ᶠ d : ℕ in atTop, (N d : ℝ)*(eta d*(p d : ℝ)) ≤ T := by
    filter_upwards [hparams,hclock,hdeltaCap] with d hp hc hd
    apply min_clock_learning_of_small_delta _ _ _ _ _ hc
    exact (div_le_iff₀ hp.2.2.2.2.2.1).mp hd |>.trans_eq (one_mul _)
  have hloadCap : ∀ᶠ d : ℕ in atTop, logisticPhi d (B d) (eta d) ≤ Phi+1 := by
    have hh := hPlim.eventually (gt_mem_nhds (by linarith : Phi < Phi+1))
    filter_upwards [hh] with d hd
    exact hd.le
  exact actual_matched_fluid_family H Ho G S B F eta beta p mu (fun d => coldState d) N teacherNorm RefBound (Phi+1)
    T q hr hRef (by linarith) hT hq
    (hdomain.mono (fun d h => h.1)) (hdomain.mono (fun d h => h.2.1))
    (hdomain.mono (fun d h => h.2.2.1)) (hdomain.mono (fun d h => h.2.2.2.1))
    (hdomain.mono (fun d h => h.2.2.2.2)) hloadCap hplim hzlim hetaSize hN hpoly hclockCap href
end
end SparseSGD.Logistic
