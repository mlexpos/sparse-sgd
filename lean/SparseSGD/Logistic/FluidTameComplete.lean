import SparseSGD.Logistic.FluidTameFamily
import SparseSGD.Logistic.DynamicGlobal
import SparseSGD.Logistic.SlowLimitGlobalExistence
import SparseSGD.Logistic.FluidDeterministicTameRegular
import SparseSGD.Logistic.FluidDeterministicTameWarm
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency.types false

private theorem tame_compact_reference_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E) (T : ℝ) (dv : ℝ → E)
    (hv : ∀ t ∈ Set.Icc 0 T, HasDerivAt v (dv t) t) :
    ∃ A : ℝ, 0 < A ∧ ∀ t ∈ Set.Icc 0 T, ‖v t‖ ≤ A := by
  have hcont : ContinuousOn v (Set.Icc 0 T) := fun t ht => (hv t ht).continuousAt.continuousWithinAt
  obtain ⟨A,hA,ha⟩ := ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) T)).image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  exact ⟨A,hA,fun t ht => ha _ ⟨t,ht,rfl⟩⟩

/-- A probability cap chosen before the actual SGD families yields the full
finite-horizon fluid bound, including fixed small probabilities. -/
theorem cor_fluid_tame_cells_three_four
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : ∀ n, SparseSGD.External.GaussianSteinCertificate n)
    (teacherNorm delta Phi T q : ℝ)
    (hr : 0 < teacherNorm) (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) (hT : 0 ≤ T) (hq : 0 ≤ q+14)
    (y0 : DynamicState) (hy0 : dynamicPhysical y0) :
    ∃ pCap : ℝ, 0<pCap ∧ ∀
    (B : ℕ → ℕ)
    (F : ∀ d, SparseSGD.External.MartingaleBernsteinCertificate (World d (B d)))
    (eta beta : ℕ → ℝ) (p : ℕ → unitInterval) (mu : ∀ d, Vec d) (N : ℕ → ℕ) (s0 : ∀ d, State d)
    (hparams : ∀ᶠ d : ℕ in atTop, 0 < B d ∧ 0 < r (mu d) ∧ r (mu d)=teacherNorm ∧ 0 < (p d : ℝ) ∧
      0 < eta d ∧ 0 < 1-beta d ∧ 1-beta d ≤ 1)
    (hinitial : ∀ᶠ d : ℕ in atTop,
      matchedToDynamic (eta d*(p d : ℝ)/(1-beta d)) (matchedSummary (eta d) (beta d) (mu d) (s0 d))=y0)
    (hclock : ∀ᶠ d : ℕ in atTop, (N d : ℝ)*min (eta d*(p d : ℝ)) (1-beta d) ≤ T)
    (hdlim : Tendsto (fun d => eta d*(p d : ℝ)/(1-beta d)) atTop (𝓝 delta))
    (hPlim : Tendsto (fun d => dynamicSourceLoad d (B d) (eta d)) atTop (𝓝 Phi))
    (hepslim : Tendsto (fun d => 1-beta d) atTop (𝓝 0))
    (hetaSize : Tendsto (fun d => eta d*Real.sqrt (Real.log d/(d : ℝ))) atTop (𝓝 0))
    (hN : ∀ᶠ d : ℕ in atTop, 0 < N d)
    (hpoly : ∀ᶠ d : ℕ in atTop, (N d : ℝ) ≤ (d : ℝ)^q)
    (hpp : ∀ᶠ d : ℕ in atTop, (p d : ℝ)≤pCap),
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ENNReal.ofReal (1-((d : ℝ)^10)⁻¹) ≤
        (worldLaw (B := B d) (p d) (Measure.dirac (s0 d))) {ω | ∀ k ≤ N d,
          ‖matchedProcess (eta d) (beta d) (p d) (mu d) k ω-
            matchedOrbit (B := B d) (eta d) (beta d) (p d) (mu d) (s0 d) k‖ ≤
              C*Real.sqrt (Real.log d/(d : ℝ))} := by
  obtain ⟨v,hv0,hv,hphysical⟩ := dynamic_solution_exists_on_finite_horizon teacherNorm delta Phi
    (T*max 1 (1/(delta/2))) y0 hdelta hPhi (by positivity) hy0
  obtain ⟨A,hA,ha⟩ := tame_compact_reference_bound v (T*max 1 (1/(delta/2)))
    (fun t => dynamicField teacherNorm delta Phi (v t)) hv
  obtain ⟨pc,RefBound,hpc,hRef,hcontain⟩ := matched_regular_small_probability_eventually_bounded
    teacherNorm delta Phi (A+1) T hdelta hPhi (by linarith) hT v hv
    (fun t ht => by simpa using ha t ht) (S 2)
  obtain ⟨ps,hps,hstochastic⟩ := actual_matched_fluid_tame_family H Ho G S teacherNorm RefBound (Phi+1)
    (T*max 1 (delta+1)) q hr hRef (by linarith) (by positivity) hq
  refine ⟨min pc ps,lt_min hpc hps,?_⟩
  intro B F eta beta p mu N s0 hparams hinitial hclock hdlim hPlim hepslim hetaSize hN hpoly hpp
  let y := fun d => matchedOrbit (B := B d) (eta d) (beta d) (p d) (mu d) (s0 d)
  have hinit : ∀ᶠ d : ℕ in atTop, matchedPhysical (y d 0) ∧
      matchedToDynamic (eta d*(p d : ℝ)/(1-beta d)) (y d 0)=v 0 := by
    filter_upwards [hinitial] with d hi
    refine ⟨matchedSummary_physical _ _ _ _, ?_⟩
    simpa [y,matchedOrbit,hv0] using hi
  have hrec : ∀ᶠ d : ℕ in atTop, ∀ n, y d (n+1)=matchedDriftMap (B := B d) (eta d) (beta d) (p d) (mu d) (y d n) :=
    Filter.Eventually.of_forall (fun d => matchedOrbit_succ _ _ _ _ _)
  have href := hcontain eta beta p mu B N y hparams hinit hrec hclock hdlim hPlim hepslim
    (hpp.mono (fun _ h => h.trans (min_le_left _ _)))
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
  exact hstochastic B F eta beta p mu s0 N
    (hdomain.mono (fun d h => h.1)) (hdomain.mono (fun d h => h.2.1))
    (hdomain.mono (fun d h => h.2.2.1)) (hdomain.mono (fun d h => h.2.2.2.1))
    (hdomain.mono (fun d h => h.2.2.2.2)) hloadCap
    (hpp.mono (fun _ h => h.trans (min_le_right _ _))) hzlim hetaSize hN hpoly hclockCap href

/-- A probability cap chosen before the actual SGD families yields the full
finite-horizon fluid bound, including fixed small probabilities. -/
theorem cor_fluid_tame_cell_two_warm
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : ∀ n, SparseSGD.External.GaussianSteinCertificate n)
    (teacherNorm Phi T q W : ℝ)
    (hr : 0 < teacherNorm) (hPhi : 0 ≤ Phi) (hT : 0 ≤ T) (hq : 0 ≤ q+14) (hW : 0 ≤ W)
    (y0 : ℝ×ℝ) (hy0 : 0 ≤ y0.2) :
    ∃ pCap : ℝ, 0<pCap ∧ ∀
    (B : ℕ → ℕ)
    (F : ∀ d, SparseSGD.External.MartingaleBernsteinCertificate (World d (B d)))
    (eta beta : ℕ → ℝ) (p : ℕ → unitInterval) (mu : ∀ d, Vec d) (N : ℕ → ℕ) (s0 : ∀ d, State d)
    (hparams : ∀ᶠ d : ℕ in atTop, 0 < B d ∧ 0 < r (mu d) ∧ r (mu d)=teacherNorm ∧ 0 < (p d : ℝ) ∧
      0 < eta d ∧ 0 < 1-beta d ∧ 1-beta d ≤ 1)
    (hinitial : ∀ᶠ d : ℕ in atTop,
      ‖matchedSummary (eta d) (beta d) (mu d) (s0 d)‖≤W ∧
      matchedEffectiveSlow (beta d) (matchedSummary (eta d) (beta d) (mu d) (s0 d))=y0)
    (hclock : ∀ᶠ d : ℕ in atTop, (N d : ℝ)*min (eta d*(p d : ℝ)) (1-beta d) ≤ T)
    (hdlim : Tendsto (fun d => eta d*(p d : ℝ)/(1-beta d)) atTop (𝓝 0))
    (hzlim : Tendsto (fun d => eta d*(p d : ℝ)) atTop (𝓝 0))
    (hPlim : Tendsto (fun d => dynamicSourceLoad d (B d) (eta d)) atTop (𝓝 Phi))
    (hetaSize : Tendsto (fun d => eta d*Real.sqrt (Real.log d/(d : ℝ))) atTop (𝓝 0))
    (hN : ∀ᶠ d : ℕ in atTop, 0 < N d)
    (hpoly : ∀ᶠ d : ℕ in atTop, (N d : ℝ) ≤ (d : ℝ)^q)
    (hpp : ∀ᶠ d : ℕ in atTop, (p d : ℝ)≤pCap),
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ENNReal.ofReal (1-((d : ℝ)^10)⁻¹) ≤
        (worldLaw (B := B d) (p d) (Measure.dirac (s0 d))) {ω | ∀ k ≤ N d,
          ‖matchedProcess (eta d) (beta d) (p d) (mu d) k ω-
            matchedOrbit (B := B d) (eta d) (beta d) (p d) (mu d) (s0 d) k‖ ≤
              C*Real.sqrt (Real.log d/(d : ℝ))} := by
  obtain ⟨v,hv0,hvglobal⟩ := slow_global_solution_exists teacherNorm Phi y0 hr.le hPhi hy0
  have hv : ∀ t ∈ Set.Icc 0 T, HasDerivAt v (slowVectorField teacherNorm Phi (v t)) t :=
    fun t ht => hvglobal t ht.1
  obtain ⟨A,hA,ha⟩ := tame_compact_reference_bound v T
    (fun t => slowVectorField teacherNorm Phi (v t)) hv
  obtain ⟨pc,RefBound,hpc,hRef,hcontain⟩ := matched_warm_slow_small_probability_eventually_bounded
    teacherNorm Phi (A+2) T W hr.le hPhi (by linarith) hT hW v hv
    (fun t ht => by simpa using ha t ht) (S 1) (S 2)
  obtain ⟨ps,hps,hstochastic⟩ := actual_matched_fluid_tame_family H Ho G S teacherNorm RefBound (Phi+1)
    T q hr hRef (by linarith) hT hq
  refine ⟨min pc ps,lt_min hpc hps,?_⟩
  intro B F eta beta p mu N s0 hparams hinitial hclock hdlim hzlim hPlim hetaSize hN hpoly hpp
  let y := fun d => matchedOrbit (B := B d) (eta d) (beta d) (p d) (mu d) (s0 d)
  have hinit : ∀ᶠ d : ℕ in atTop, matchedPhysical (y d 0) ∧
      ‖y d 0‖≤W ∧ matchedEffectiveSlow (beta d) (y d 0)=v 0 := by
    filter_upwards [hinitial] with d hi
    refine ⟨matchedSummary_physical _ _ _ _, ?_⟩
    simpa [y,matchedOrbit,hv0] using hi
  have hrec : ∀ᶠ d : ℕ in atTop, ∀ n, y d (n+1)=matchedDriftMap (B := B d) (eta d) (beta d) (p d) (mu d) (y d n) :=
    Filter.Eventually.of_forall (fun d => matchedOrbit_succ _ _ _ _ _)
  have href := hcontain eta beta p mu B N y hparams hinit hrec hclock hdlim hzlim hPlim
    (hpp.mono (fun _ h => h.trans (min_le_left _ _)))
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
  exact hstochastic B F eta beta p mu s0 N
    (hdomain.mono (fun d h => h.1)) (hdomain.mono (fun d h => h.2.1))
    (hdomain.mono (fun d h => h.2.2.1)) (hdomain.mono (fun d h => h.2.2.2.1))
    (hdomain.mono (fun d h => h.2.2.2.2)) hloadCap
    (hpp.mono (fun _ h => h.trans (min_le_right _ _))) hzlim hetaSize hN hpoly hclockCap href

end
end SparseSGD.Logistic
