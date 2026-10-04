import SparseSGD.Logistic.FluidTameComplete
import SparseSGD.Logistic.FluidCells
import SparseSGD.Scaling.FluidPowerTameParameters
import SparseSGD.Scaling.FluidGrid
import SparseSGD.Scaling.FluidHorizonDegree
import SparseSGD.Logistic.FluidAsymptotics

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 3200000

open SparseSGD.Scaling

private theorem fixed_fluid_actual_delta_eq
    (pStar b sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : MeasureTheory.Measure ℝ)
    (hp : 0 < pStar)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d : ℝ)=scaledSparsity pStar 0 d) :
    (fun d : ℕ => scaledLearningRate etaStar alpha d*(p d:ℝ)/
        (1-scaledMomentum epsStar gamma d)) =ᶠ[atTop]
      fun d => rawDelta (actualLSParams pStar 0 b sigma epsStar gamma etaStar alpha p ν d) := by
  have hraw := actualLSParams_rawDelta_eq_lsDelta_eventually pStar 0 b sigma
    epsStar gamma etaStar alpha p ν hp hpd
  filter_upwards [hpd,hraw,eventually_gt_atTop (0:ℕ)] with d hpD hrawD hd
  have hp0 : (p d:ℝ) ≠ 0 := by
    rw [hpD]
    exact (scaledSparsity_pos_of_pos pStar 0 d hp hd).ne'
  have hstep := actualLSParams_rawDelta pStar 0 b sigma epsStar gamma etaStar alpha
    p ν d hp0 hpD
  have heps := actualLSParams_eps pStar 0 b sigma epsStar gamma etaStar alpha p ν d hp0 hpD
  rw [heps] at hstep
  have hb : 1-scaledMomentum epsStar gamma d=scaledRetention epsStar gamma d := by
    simp [scaledMomentum]
  rw [hb,hstep,hrawD]

/-- Fixed-positive sparsity cell 2. The small-probability cap comes from the
warm fluid theorem before `pStar` is chosen.  The initialization is the cold
state, so its matched energy and effective slow state are both zero. -/
theorem actual_fluid_power_tame_cell_two
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : ∀ n, SparseSGD.External.GaussianSteinCertificate n)
    (etaStar alpha bStar sigma epsStar gamma teacherNorm T : ℝ)
    (mu : ∀ d, Vec d) (ν : MeasureTheory.Measure ℝ)
    (heta : 0 < etaStar) (ha : 0 < alpha) (hb : 0 < bStar) (hs : 0 ≤ sigma)
    (heps : 0 < epsStar) (hg : 0 ≤ gamma) (hga : gamma < alpha)
    (hr : 0 < teacherNorm) (hT : 0 < T)
    (hPhi : 1-sigma-alpha < 0 ∨ 1-sigma-alpha = 0)
    (hfixed : gamma = 0 → epsStar ≤ 1/2)
    (hmu : ∀ᶠ d : ℕ in atTop, r (mu d) = teacherNorm)
    (F : ∀ d, SparseSGD.External.MartingaleBernsteinCertificate
      (World d (scaledBatch bStar sigma d))) :
    ∃ pCap : ℝ, 0<pCap ∧ ∀ (pStar : ℝ) (p : ℕ → unitInterval),
      (0 < pStar ∧ pStar ≤ min (1:ℝ) pCap) →
      (∀ᶠ d : ℕ in atTop, (p d : ℝ)=scaledSparsity pStar 0 d) →
    ∃ C : ℝ, 0<C ∧ ∀ᶠ d : ℕ in atTop,
    ENNReal.ofReal (1-((d:ℝ)^10)⁻¹) ≤
      (worldLaw (B:=scaledBatch bStar sigma d) (p d) (Measure.dirac (coldState d)))
        {ω | ∀ k≤fluidGridHorizon T etaStar pStar alpha 0 epsStar gamma d,
          ‖matchedProcess (scaledLearningRate etaStar alpha d)
              (scaledMomentum epsStar gamma d) (p d) (mu d) k ω-
            matchedOrbit (B:=scaledBatch bStar sigma d)
              (scaledLearningRate etaStar alpha d) (scaledMomentum epsStar gamma d)
              (p d) (mu d) (coldState d) k‖ ≤ C*Real.sqrt (Real.log d/(d:ℝ))} := by
  let Phi := if 1-sigma-alpha<0 then 0 else etaStar/(2*realizedBatchScale bStar sigma)
  let q := fluidHorizonDegree alpha 0 gamma
  have hq : 0≤q := by dsimp [q,fluidHorizonDegree]; linarith [le_max_right (alpha+0) gamma]
  have hPhi0 : 0≤Phi := by
    by_cases hn : 1-sigma-alpha<0
    · simp [Phi,hn]
    · simp [Phi,hn]
      exact div_nonneg heta.le (le_of_lt (mul_pos (by norm_num)
        (realizedBatchScale_pos bStar sigma hb)))
  obtain ⟨cap,hcap,huniv⟩ := cor_fluid_tame_cell_two_warm H Ho G S teacherNorm Phi T q 0
    hr hPhi0 hT.le (by linarith) (by norm_num) (0,0) (by norm_num)
  refine ⟨cap,hcap,?_⟩
  intro pStar p hp hpD
  have hpPos := hp.1
  have hpLe : pStar≤cap := le_trans hp.2 (min_le_right _ _)
  have hpars := actual_fluid_fixed_sparsity_parameter_limits pStar bStar sigma epsStar gamma
    etaStar alpha p ν hpPos (le_trans hp.2 (min_le_left _ _)) hb hs heps hg heta ha
    hfixed hpD cap hpLe hPhi (Or.inl (by linarith))
  rcases hpars with ⟨hvalid,hpLim,hstepLim,hPhiLim,hDeltaLim⟩
  let B := scaledBatch bStar sigma
  let eta := scaledLearningRate etaStar alpha
  let beta := scaledMomentum epsStar gamma
  let N := fluidGridHorizon T etaStar pStar alpha 0 epsStar gamma
  have hparams : ∀ᶠ d : ℕ in atTop,
      0<B d ∧ 0<r (mu d) ∧ r (mu d)=teacherNorm ∧ 0<(p d:ℝ) ∧
      0<eta d ∧ 0<1-beta d ∧ 1-beta d≤1 := by
    filter_upwards [hvalid,hpD,eventually_gt_atTop (0:ℕ),hmu] with d hv hpd hd hmuD
    have hp0 : 0<(p d:ℝ) := by rw [hpd]; exact scaledSparsity_pos_of_pos pStar 0 d hpPos hd
    have heta0 : 0<eta d := by dsimp [eta,scaledLearningRate]; positivity
    have hbLow : (1:ℝ)/2≤beta d := hv.1
    have hbUp : beta d<1 := hv.2.1
    exact ⟨integerBatch_pos bStar sigma d,by rw [hmuD]; exact hr,
      hmuD,hp0,heta0,by linarith,by linarith⟩
  have hN : ∀ᶠ d : ℕ in atTop, 0<N d := by
    simpa [N] using actual_fluidGridHorizon_eventually_pos T etaStar pStar alpha 0 epsStar gamma
      hT heta hpPos heps (by linarith)
  have hpolyN : ∀ᶠ d : ℕ in atTop, (N d:ℝ)≤(d:ℝ)^q := by
    simpa [N,q] using fluidGridHorizon_eventually_le_degree T etaStar pStar alpha 0 epsStar gamma
      hT.le heta hpPos heps (by linarith) hg
  have hclock : ∀ᶠ d : ℕ in atTop,
      (N d:ℝ)*min (eta d*(p d:ℝ)) (1-beta d)≤T := by
    filter_upwards [hpD,eventually_gt_atTop (0:ℕ)] with d hpd hd
    rw [← show fluidClock etaStar pStar alpha 0 epsStar gamma d =
      min (eta d*(p d:ℝ)) (1-beta d) by simp [fluidClock,fluidLearningStep,eta,beta,
        scaledMomentum,scaledRetention,hpd]]
    exact actual_fluidGridHorizon_le T etaStar pStar alpha 0 epsStar gamma d hT.le (by
      unfold fluidClock fluidLearningStep scaledLearningRate scaledSparsity scaledRetention
      positivity)
  have hdelta : Tendsto (fun d => eta d*(p d:ℝ)/(1-beta d)) atTop (𝓝 0) := by
    have hEq := fixed_fluid_actual_delta_eq pStar bStar sigma epsStar gamma etaStar alpha p ν
      hpPos hpD
    have hd0 : Tendsto (fun d => rawDelta (actualLSParams pStar 0 bStar sigma epsStar gamma etaStar alpha p ν d))
        atTop (𝓝 0) := by simpa [show gamma-alpha<0 by linarith] using hDeltaLim
    exact hd0.congr' hEq.symm
  have hz : Tendsto (fun d => eta d*(p d:ℝ)) atTop (𝓝 0) := hstepLim
  have hPhiActual : Tendsto (fun d => dynamicSourceLoad d (B d) (eta d)) atTop (𝓝 Phi) := by
    have heq : (fun d => dynamicSourceLoad d (B d) (eta d)) =ᶠ[atTop]
        fun d => logisticPhi d (B d) (eta d) := by
      filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
      simp [dynamicSourceLoad,logisticPhi]
    have hp0 : Tendsto (fun d => logisticPhi d (B d) (eta d)) atTop (𝓝 Phi) := by
      by_cases hn : 1-sigma-alpha<0
      · simpa [Phi,hn,B,eta] using hPhiLim
      · simpa [Phi,hn,B,eta] using hPhiLim
    exact hp0.congr' heq.symm
  have hetaSize : Tendsto (fun d => eta d*Real.sqrt (Real.log d/(d:ℝ))) atTop (𝓝 0) := by
    simpa [eta,scaledLearningRate] using fluid_power_learning_absorption etaStar alpha heta.le
      (by linarith : -(1/2:ℝ)<alpha)
  have hpp : ∀ᶠ d : ℕ in atTop, (p d:ℝ)≤cap := hvalid.mono fun d h => h.2.2
  have hinit : ∀ᶠ d : ℕ in atTop,
      ‖matchedSummary (eta d) (beta d) (mu d) (coldState d)‖≤0 ∧
      matchedEffectiveSlow (beta d) (matchedSummary (eta d) (beta d) (mu d) (coldState d))=(0,0) := by
    filter_upwards with d
    simp [matchedSummary_coldState,matchedEffectiveSlow]
  have hclock' := hclock
  exact huniv B F eta beta p mu N (fun d => coldState d) hparams hinit hclock' hdelta hz
    hPhiActual hetaSize hN hpolyN hpp

/-- Fixed-positive sparsity in cells 3 and 4. The positive raw-Delta limit
is chosen before the probability cap. For each allowed `pStar`, retention has
prefactor `etaStar*pStar/delta`, so the actual raw-Delta limit stays fixed. -/
theorem actual_fluid_power_tame_cells_three_four
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : ∀ n, SparseSGD.External.GaussianSteinCertificate n)
    (etaStar alpha bStar sigma delta teacherNorm T : ℝ)
    (mu : ∀ d, Vec d) (ν : MeasureTheory.Measure ℝ)
    (heta : 0 < etaStar) (ha : 0 < alpha) (hb : 0 < bStar) (hs : 0 ≤ sigma)
    (hdelta : 0 < delta)
    (hr : 0 < teacherNorm) (hT : 0 < T)
    (hPhi : 1-sigma-alpha < 0 ∨ 1-sigma-alpha = 0)
    (hmu : ∀ᶠ d : ℕ in atTop, r (mu d) = teacherNorm)
    (F : ∀ d, SparseSGD.External.MartingaleBernsteinCertificate
      (World d (scaledBatch bStar sigma d))) :
    ∃ pCap : ℝ, 0<pCap ∧ ∀ (pStar : ℝ) (p : ℕ → unitInterval),
      (0 < pStar ∧ pStar ≤ min (1:ℝ) pCap) →
      (∀ᶠ d : ℕ in atTop, (p d : ℝ)=scaledSparsity pStar 0 d) →
    ∃ C : ℝ, 0<C ∧ ∀ᶠ d : ℕ in atTop,
    ENNReal.ofReal (1-((d:ℝ)^10)⁻¹) ≤
      (worldLaw (B:=scaledBatch bStar sigma d) (p d) (Measure.dirac (coldState d)))
        {ω | ∀ k≤fluidGridHorizon T etaStar pStar alpha 0 (etaStar*pStar/delta) alpha d,
          ‖matchedProcess (scaledLearningRate etaStar alpha d)
              (scaledMomentum (etaStar*pStar/delta) alpha d) (p d) (mu d) k ω-
            matchedOrbit (B:=scaledBatch bStar sigma d)
              (scaledLearningRate etaStar alpha d) (scaledMomentum (etaStar*pStar/delta) alpha d)
              (p d) (mu d) (coldState d) k‖ ≤ C*Real.sqrt (Real.log d/(d:ℝ))} := by
  let Phi := if 1-sigma-alpha<0 then 0 else etaStar/(2*realizedBatchScale bStar sigma)
  let q := fluidHorizonDegree alpha 0 alpha
  have hq : 0≤q := by dsimp [q,fluidHorizonDegree]; linarith [le_max_right (alpha+0) alpha]
  have hPhi0 : 0≤Phi := by
    by_cases hn : 1-sigma-alpha<0
    · simp [Phi,hn]
    · simp [Phi,hn]
      exact div_nonneg heta.le (le_of_lt (mul_pos (by norm_num)
        (realizedBatchScale_pos bStar sigma hb)))
  obtain ⟨cap,hcap,huniv⟩ := cor_fluid_tame_cells_three_four H Ho G S teacherNorm delta Phi T q
    hr hdelta hPhi0 hT.le (by linarith) (0 : DynamicState) (by simp [dynamicPhysical])
  refine ⟨cap,hcap,?_⟩
  intro pStar p hp hpD
  have hpPos := hp.1
  let epsStar := etaStar*pStar/delta
  have heps : 0<epsStar := by dsimp [epsStar]; positivity
  have hpLe : pStar≤cap := le_trans hp.2 (min_le_right _ _)
  have hpars := actual_fluid_fixed_sparsity_parameter_limits pStar bStar sigma epsStar alpha
    etaStar alpha p ν hpPos (le_trans hp.2 (min_le_left _ _)) hb hs heps ha.le heta ha
    (by intro h; linarith) hpD cap hpLe hPhi (Or.inr (by ring))
  rcases hpars with ⟨hvalid,hpLim,hstepLim,hPhiLim,hDeltaLim⟩
  let B := scaledBatch bStar sigma
  let eta := scaledLearningRate etaStar alpha
  let beta := scaledMomentum epsStar alpha
  let N := fluidGridHorizon T etaStar pStar alpha 0 epsStar alpha
  have hparams : ∀ᶠ d : ℕ in atTop,
      0<B d ∧ 0<r (mu d) ∧ r (mu d)=teacherNorm ∧ 0<(p d:ℝ) ∧
      0<eta d ∧ 0<1-beta d ∧ 1-beta d≤1 := by
    filter_upwards [hvalid,hpD,eventually_gt_atTop (0:ℕ),hmu] with d hv hpd hd hmuD
    have hp0 : 0<(p d:ℝ) := by rw [hpd]; exact scaledSparsity_pos_of_pos pStar 0 d hpPos hd
    have heta0 : 0<eta d := by dsimp [eta,scaledLearningRate]; positivity
    have hbLow : (1:ℝ)/2≤beta d := hv.1
    have hbUp : beta d<1 := hv.2.1
    exact ⟨integerBatch_pos bStar sigma d,by rw [hmuD]; exact hr,
      hmuD,hp0,heta0,by linarith,by linarith⟩
  have hN : ∀ᶠ d : ℕ in atTop, 0<N d := by
    simpa [N] using actual_fluidGridHorizon_eventually_pos T etaStar pStar alpha 0 epsStar alpha
      hT heta hpPos heps (by linarith)
  have hpolyN : ∀ᶠ d : ℕ in atTop, (N d:ℝ)≤(d:ℝ)^q := by
    simpa [N,q] using fluidGridHorizon_eventually_le_degree T etaStar pStar alpha 0 epsStar alpha
      hT.le heta hpPos heps (by linarith) ha.le
  have hclock : ∀ᶠ d : ℕ in atTop,
      (N d:ℝ)*min (eta d*(p d:ℝ)) (1-beta d)≤T := by
    filter_upwards [hpD,eventually_gt_atTop (0:ℕ)] with d hpd hd
    rw [← show fluidClock etaStar pStar alpha 0 epsStar alpha d =
      min (eta d*(p d:ℝ)) (1-beta d) by simp [fluidClock,fluidLearningStep,eta,beta,
        scaledMomentum,scaledRetention,hpd]]
    exact actual_fluidGridHorizon_le T etaStar pStar alpha 0 epsStar alpha d hT.le (by
      unfold fluidClock fluidLearningStep scaledLearningRate scaledSparsity scaledRetention
      positivity)
  have hdeltaLim : Tendsto (fun d => eta d*(p d:ℝ)/(1-beta d)) atTop (𝓝 delta) := by
    have hEq := fixed_fluid_actual_delta_eq pStar bStar sigma epsStar alpha etaStar alpha p ν
      hpPos hpD
    have hdeltaEq : etaStar*pStar/epsStar=delta := by
      dsimp [epsStar]
      field_simp [hdelta.ne',heta.ne',hpPos.ne']
    have hd0 : Tendsto (fun d => rawDelta (actualLSParams pStar 0 bStar sigma epsStar alpha etaStar alpha p ν d))
        atTop (𝓝 delta) := by simpa [hdeltaEq] using hDeltaLim
    exact hd0.congr' hEq.symm
  have hepsLim : Tendsto (fun d => 1-beta d) atTop (𝓝 0) := by
    simpa [beta,scaledMomentum] using scaledRetention_tendsto_zero epsStar alpha ha
  have hPhiActual : Tendsto (fun d => dynamicSourceLoad d (B d) (eta d)) atTop (𝓝 Phi) := by
    have heq : (fun d => dynamicSourceLoad d (B d) (eta d)) =ᶠ[atTop]
        fun d => logisticPhi d (B d) (eta d) := by
      filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
      simp [dynamicSourceLoad,logisticPhi]
    have hp0 : Tendsto (fun d => logisticPhi d (B d) (eta d)) atTop (𝓝 Phi) := by
      by_cases hn : 1-sigma-alpha<0
      · simpa [Phi,hn,B,eta] using hPhiLim
      · simpa [Phi,hn,B,eta] using hPhiLim
    exact hp0.congr' heq.symm
  have hetaSize : Tendsto (fun d => eta d*Real.sqrt (Real.log d/(d:ℝ))) atTop (𝓝 0) := by
    simpa [eta,scaledLearningRate] using fluid_power_learning_absorption etaStar alpha heta.le
      (by linarith : -(1/2:ℝ)<alpha)
  have hpp : ∀ᶠ d : ℕ in atTop, (p d:ℝ)≤cap := hvalid.mono fun d h => h.2.2
  have hinit : ∀ᶠ d : ℕ in atTop,
      matchedToDynamic (eta d*(p d:ℝ)/(1-beta d))
        (matchedSummary (eta d) (beta d) (mu d) (coldState d))=0 := by
    filter_upwards with d
    simp [matchedSummary_coldState,matchedToDynamic]
  have hclock' := hclock
  exact huniv B F eta beta p mu N (fun d => coldState d) hparams hinit hclock' hdeltaLim hPhiActual hepsLim hetaSize hN hpolyN hpp


end
end SparseSGD.Logistic
