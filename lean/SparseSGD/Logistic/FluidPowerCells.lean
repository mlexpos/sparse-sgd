import SparseSGD.Logistic.FluidCells
import SparseSGD.Logistic.FluidComplete
import SparseSGD.Logistic.FluidAsymptotics
import SparseSGD.Scaling.FluidPowerParameters
import SparseSGD.Scaling.FluidGrid

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 3200000

private theorem fluid_power_actual_delta_eq
    (pStar kappa b sigma epsStar gamma etaStar alpha : ℝ)
    (p : ℕ → unitInterval) (ν : MeasureTheory.Measure ℝ)
    (hp : 0 < pStar)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d:ℝ)=Scaling.scaledSparsity pStar kappa d) :
    (fun d : ℕ => Scaling.scaledLearningRate etaStar alpha d*(p d:ℝ)/
        (1-Scaling.scaledMomentum epsStar gamma d)) =ᶠ[atTop]
      fun d => Scaling.rawDelta
        (Scaling.actualLSParams pStar kappa b sigma epsStar gamma etaStar alpha p ν d) := by
  have hraw := Scaling.actualLSParams_rawDelta_eq_lsDelta_eventually pStar kappa b sigma
    epsStar gamma etaStar alpha p ν hp hpd
  filter_upwards [hpd,hraw,eventually_gt_atTop (0:ℕ)] with d hpd hraw hd
  have hp0 : (p d:ℝ) ≠ 0 := by
    rw [hpd]
    exact (Scaling.scaledSparsity_pos_of_pos pStar kappa d hp hd).ne'
  have hstep := Scaling.actualLSParams_rawDelta pStar kappa b sigma epsStar gamma etaStar alpha
    p ν d hp0 hpd
  have heps := Scaling.actualLSParams_eps pStar kappa b sigma epsStar gamma etaStar alpha p ν d hp0 hpd
  rw [heps] at hstep
  have hbeta : 1-Scaling.scaledMomentum epsStar gamma d = Scaling.scaledRetention epsStar gamma d := by
    simp [Scaling.scaledMomentum]
  rw [hbeta]
  rw [hstep,hraw]

end

open SparseSGD.Scaling

/-- Actual power-family specialization of cell 2. The sparse LS probability is
only required to agree with its power law eventually; the batch is the actual
integer-rounded batch and the horizon is the floor of the actual minimum
learning/retention clock. -/
theorem actual_fluid_power_cell_two
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : ∀ n, SparseSGD.External.GaussianSteinCertificate n)
    (pStar kappa bStar sigma epsStar gamma etaStar alpha teacherNorm T : ℝ)
    (p : ℕ → unitInterval) (mu : ∀ d, Vec d) (ν : MeasureTheory.Measure ℝ)
    (hp : 0 < pStar) (hk : 0 < kappa) (hb : 0 < bStar) (hs : 0 ≤ sigma)
    (heps : 0 < epsStar) (hg : 0 ≤ gamma) (heta : 0 < etaStar)
    (ha : 0 < alpha+kappa) (halpha : -(1/2:ℝ)<alpha) (hT : 0<T)
    (hfixed : gamma=0 → epsStar≤1/2)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d:ℝ)=scaledSparsity pStar kappa d)
    (hDelta : gamma-alpha-kappa<0)
    (hPhi : 1-sigma-alpha<0 ∨ 1-sigma-alpha=0)
    (hr : 0 < teacherNorm) (hmu : ∀ᶠ d : ℕ in atTop, r (mu d)=teacherNorm)
    (F : ∀ d, SparseSGD.External.MartingaleBernsteinCertificate
      (World d (scaledBatch bStar sigma d))) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ d : ℕ in atTop,
      ENNReal.ofReal (1-((d:ℝ)^10)⁻¹) ≤
        (worldLaw (B:=scaledBatch bStar sigma d) (p d) (Measure.dirac (coldState d)))
          {ω | ∀ k'≤fluidGridHorizon T etaStar pStar alpha kappa epsStar gamma d,
            ‖matchedProcess (scaledLearningRate etaStar alpha d)
                (scaledMomentum epsStar gamma d) (p d) (mu d) k' ω-
              matchedOrbit (B:=scaledBatch bStar sigma d) (scaledLearningRate etaStar alpha d)
                (scaledMomentum epsStar gamma d) (p d) (mu d) (coldState d) k'‖ ≤
              C*Real.sqrt (Real.log d/(d:ℝ))} := by
  let B := scaledBatch bStar sigma
  let eta := scaledLearningRate etaStar alpha
  let beta := scaledMomentum epsStar gamma
  let N := fluidGridHorizon T etaStar pStar alpha kappa epsStar gamma
  let Phi := if 1-sigma-alpha<0 then 0 else etaStar/(2*realizedBatchScale bStar sigma)
  obtain ⟨q,hqNonneg,hpoly0⟩ := fluidGridHorizon_eventually_le_polynomial
    T etaStar pStar alpha kappa epsStar gamma hT.le heta hp heps (le_of_lt ha) hg
  have hbetaActual := actual_fluid_beta_eventually_valid pStar kappa bStar sigma epsStar gamma
    etaStar alpha p ν heps hg hfixed
  have hbeta : ∀ᶠ d : ℕ in atTop, 0≤beta d ∧ beta d<1 := by
    filter_upwards [hbetaActual] with d hh
    have heq : (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).beta=
        beta d := rfl
    rw [← heq]
    exact ⟨by linarith [hh.1],hh.2⟩
  have hparams : ∀ᶠ d : ℕ in atTop,
      0<B d ∧ 0<r (mu d) ∧ r (mu d)=teacherNorm ∧ 0<(p d:ℝ) ∧
      0<eta d ∧ 0<1-beta d ∧ 1-beta d≤1 := by
    filter_upwards [eventually_gt_atTop (0:ℕ),hpd,hbeta,hmu] with d hd hpd hbt hm
    have hp0 : 0<(p d:ℝ) := by rw [hpd]; exact scaledSparsity_pos_of_pos pStar kappa d hp hd
    have heta0 : 0<eta d := by
      dsimp [eta,scaledLearningRate]
      exact mul_pos heta (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)
    rcases hbt with ⟨hb0,hb1⟩
    exact ⟨integerBatch_pos bStar sigma d,by rw [hm]; exact hr,hm,hp0,heta0,
      by linarith,by linarith⟩
  have hN : ∀ᶠ d : ℕ in atTop, 0<N d := by
    simpa [N] using actual_fluidGridHorizon_eventually_pos T etaStar pStar alpha kappa epsStar gamma
      hT heta hp heps ha
  have hpoly : ∀ᶠ d : ℕ in atTop, (N d:ℝ)≤(d:ℝ)^q := by
    simpa [N] using hpoly0
  have hclock : ∀ᶠ d : ℕ in atTop, (N d:ℝ)*min (eta d*(p d:ℝ)) (1-beta d)≤T := by
    filter_upwards [hpd,eventually_gt_atTop (0:ℕ)] with d hpd hd
    have hc : fluidClock etaStar pStar alpha kappa epsStar gamma d =
        min (eta d*(p d:ℝ)) (1-beta d) := by
      simp [fluidClock,fluidLearningStep,eta,beta,scaledMomentum,scaledRetention,hpd]
    rw [← hc]
    exact actual_fluidGridHorizon_le T etaStar pStar alpha kappa epsStar gamma d hT.le (by
      unfold fluidClock fluidLearningStep scaledLearningRate scaledSparsity scaledRetention
      positivity)
  have hSparse := actual_fluid_sparse_limits pStar kappa etaStar alpha p hp hk heta ha hpd
  have hPhiLim : Tendsto (fun d : ℕ => logisticPhi d (B d) (eta d)) atTop (𝓝 Phi) := by
    have hl : Tendsto (fun d : ℕ => logisticPhi d (scaledBatch bStar sigma d)
        (scaledLearningRate etaStar alpha d)) atTop (𝓝 Phi) := by
      by_cases hn : 1-sigma-alpha<0
      · simp [Phi,hn]
        exact actual_fluid_phi_tendsto_zero etaStar alpha bStar sigma heta hb hs hn
      · have hz : 1-sigma-alpha=0 := by
          rcases hPhi with hneg | heq
          · exact (hn hneg).elim
          · exact heq
        simp [Phi,hn]
        exact actual_fluid_phi_tendsto_critical etaStar alpha bStar sigma heta hb hs hz
    have heq : (fun d : ℕ => dynamicSourceLoad d (B d) (eta d)) =ᶠ[atTop]
        fun d => logisticPhi d (B d) (eta d) := by
      filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
      simp [dynamicSourceLoad,logisticPhi]
    exact hl.congr' heq.symm
  have hDeltaLim : Tendsto (fun d : ℕ => eta d*(p d:ℝ)/(1-beta d)) atTop (𝓝 0) := by
    have hd := actual_rawDelta_tendsto_zero pStar kappa bStar sigma epsStar gamma etaStar alpha
      p ν hp heta heps hpd hDelta
    exact hd.congr' (fluid_power_actual_delta_eq pStar kappa bStar sigma epsStar gamma etaStar alpha
      p ν hp hpd).symm
  have hetaSize : Tendsto (fun d : ℕ => eta d*Real.sqrt (Real.log d/(d:ℝ))) atTop (𝓝 0) := by
    simpa [eta,scaledLearningRate] using fluid_power_learning_absorption etaStar alpha heta.le halpha
  have hPhi0 : 0≤Phi := by
    by_cases hn : 1-sigma-alpha<0
    · simp [Phi,hn]
    · simp [Phi,hn]
      exact div_nonneg heta.le (le_of_lt (mul_pos (by norm_num) (realizedBatchScale_pos bStar sigma hb)))
  have hq : 0≤q+14 := by linarith
  exact cor_fluid_cell_two H Ho G S B F eta beta p mu N teacherNorm Phi T q hr hPhi0 hT.le hq
    hparams hclock hDeltaLim hSparse.2 hPhiLim hSparse.1 hetaSize hN hpoly

/-- Actual power-family specialization of regular cells 3 and 4, with the
critical raw-Delta limit and the actual floor of the minimum clock. -/
theorem actual_fluid_power_cells_three_four
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : ∀ n, SparseSGD.External.GaussianSteinCertificate n)
    (pStar kappa bStar sigma epsStar gamma etaStar alpha teacherNorm T : ℝ)
    (p : ℕ → unitInterval) (mu : ∀ d, Vec d) (ν : MeasureTheory.Measure ℝ)
    (hp : 0 < pStar) (hk : 0 < kappa) (hb : 0 < bStar) (hs : 0 ≤ sigma)
    (heps : 0 < epsStar) (hg : 0 < gamma) (heta : 0 < etaStar)
    (ha : 0 < alpha+kappa) (halpha : -(1/2:ℝ)<alpha) (hT : 0<T)
    (hpd : ∀ᶠ d : ℕ in atTop, (p d:ℝ)=scaledSparsity pStar kappa d)
    (hDelta : gamma-alpha-kappa=0)
    (hPhi : 1-sigma-alpha<0 ∨ 1-sigma-alpha=0)
    (hr : 0 < teacherNorm) (hmu : ∀ᶠ d : ℕ in atTop, r (mu d)=teacherNorm)
    (F : ∀ d, SparseSGD.External.MartingaleBernsteinCertificate
      (World d (scaledBatch bStar sigma d))) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ d : ℕ in atTop,
      ENNReal.ofReal (1-((d:ℝ)^10)⁻¹) ≤
        (worldLaw (B:=scaledBatch bStar sigma d) (p d) (Measure.dirac (coldState d)))
          {ω | ∀ k'≤fluidGridHorizon T etaStar pStar alpha kappa epsStar gamma d,
            ‖matchedProcess (scaledLearningRate etaStar alpha d)
                (scaledMomentum epsStar gamma d) (p d) (mu d) k' ω-
              matchedOrbit (B:=scaledBatch bStar sigma d) (scaledLearningRate etaStar alpha d)
                (scaledMomentum epsStar gamma d) (p d) (mu d) (coldState d) k'‖ ≤
              C*Real.sqrt (Real.log d/(d:ℝ))} := by
  let B := scaledBatch bStar sigma
  let eta := scaledLearningRate etaStar alpha
  let beta := scaledMomentum epsStar gamma
  let N := fluidGridHorizon T etaStar pStar alpha kappa epsStar gamma
  let delta := etaStar*pStar/epsStar
  let Phi := if 1-sigma-alpha<0 then 0 else etaStar/(2*realizedBatchScale bStar sigma)
  obtain ⟨q,hqNonneg,hpoly0⟩ := fluidGridHorizon_eventually_le_polynomial
    T etaStar pStar alpha kappa epsStar gamma hT.le heta hp heps (le_of_lt ha) hg.le
  have hbetaActual := actual_fluid_beta_eventually_valid pStar kappa bStar sigma epsStar gamma
    etaStar alpha p ν heps hg.le (by intro h; linarith)
  have hbeta : ∀ᶠ d : ℕ in atTop, 0≤beta d ∧ beta d<1 := by
    filter_upwards [hbetaActual] with d hh
    have heq : (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar alpha p ν d).beta=
        beta d := rfl
    rw [← heq]
    exact ⟨by linarith [hh.1],hh.2⟩
  have hparams : ∀ᶠ d : ℕ in atTop,
      0<B d ∧ 0<r (mu d) ∧ r (mu d)=teacherNorm ∧ 0<(p d:ℝ) ∧
      0<eta d ∧ 0<1-beta d ∧ 1-beta d≤1 := by
    filter_upwards [eventually_gt_atTop (0:ℕ),hpd,hbeta,hmu] with d hd hpd hbt hm
    have hp0 : 0<(p d:ℝ) := by rw [hpd]; exact scaledSparsity_pos_of_pos pStar kappa d hp hd
    have heta0 : 0<eta d := by
      dsimp [eta,scaledLearningRate]
      exact mul_pos heta (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)
    rcases hbt with ⟨hb0,hb1⟩
    exact ⟨integerBatch_pos bStar sigma d,by rw [hm]; exact hr,hm,hp0,heta0,
      by linarith,by linarith⟩
  have hN : ∀ᶠ d : ℕ in atTop, 0<N d := by
    simpa [N] using actual_fluidGridHorizon_eventually_pos T etaStar pStar alpha kappa epsStar gamma
      hT heta hp heps ha
  have hpoly : ∀ᶠ d : ℕ in atTop, (N d:ℝ)≤(d:ℝ)^q := by simpa [N] using hpoly0
  have hclock : ∀ᶠ d : ℕ in atTop, (N d:ℝ)*min (eta d*(p d:ℝ)) (1-beta d)≤T := by
    filter_upwards [hpd,eventually_gt_atTop (0:ℕ)] with d hpd hd
    have hc : fluidClock etaStar pStar alpha kappa epsStar gamma d =
        min (eta d*(p d:ℝ)) (1-beta d) := by
      simp [fluidClock,fluidLearningStep,eta,beta,scaledMomentum,scaledRetention,hpd]
    rw [← hc]
    exact actual_fluidGridHorizon_le T etaStar pStar alpha kappa epsStar gamma d hT.le (by
      unfold fluidClock fluidLearningStep scaledLearningRate scaledSparsity scaledRetention
      positivity)
  have hSparse := actual_fluid_sparse_limits pStar kappa etaStar alpha p hp hk heta ha hpd
  have hPhiLim : Tendsto (fun d : ℕ => logisticPhi d (B d) (eta d)) atTop (𝓝 Phi) := by
    have hl : Tendsto (fun d : ℕ => logisticPhi d (scaledBatch bStar sigma d)
        (scaledLearningRate etaStar alpha d)) atTop (𝓝 Phi) := by
      by_cases hn : 1-sigma-alpha<0
      · simp [Phi,hn]
        exact actual_fluid_phi_tendsto_zero etaStar alpha bStar sigma heta hb hs hn
      · have hz : 1-sigma-alpha=0 := by
          rcases hPhi with hneg | heq
          · exact (hn hneg).elim
          · exact heq
        simp [Phi,hn]
        exact actual_fluid_phi_tendsto_critical etaStar alpha bStar sigma heta hb hs hz
    have heq : (fun d : ℕ => dynamicSourceLoad d (B d) (eta d)) =ᶠ[atTop]
        fun d => logisticPhi d (B d) (eta d) := by
      filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
      simp [dynamicSourceLoad,logisticPhi]
    exact hl.congr' heq.symm
  have hDeltaLim : Tendsto (fun d : ℕ => eta d*(p d:ℝ)/(1-beta d)) atTop (𝓝 delta) := by
    have hd := actual_rawDelta_tendsto_critical pStar kappa bStar sigma epsStar gamma etaStar alpha
      p ν hp heta heps hpd hDelta
    exact hd.congr' (fluid_power_actual_delta_eq pStar kappa bStar sigma epsStar gamma etaStar alpha
      p ν hp hpd).symm
  have hepslim : Tendsto (fun d : ℕ => 1-beta d) atTop (𝓝 0) := by
    simpa [beta,scaledMomentum] using scaledRetention_tendsto_zero epsStar gamma hg
  have hetaSize : Tendsto (fun d : ℕ => eta d*Real.sqrt (Real.log d/(d:ℝ))) atTop (𝓝 0) := by
    simpa [eta,scaledLearningRate] using fluid_power_learning_absorption etaStar alpha heta.le halpha
  have hPhi0 : 0≤Phi := by
    by_cases hn : 1-sigma-alpha<0
    · simp [Phi,hn]
    · simp [Phi,hn]
      exact div_nonneg heta.le (le_of_lt (mul_pos (by norm_num) (realizedBatchScale_pos bStar sigma hb)))
  have hdelta : 0<delta := by dsimp [delta]; exact div_pos (mul_pos heta hp) heps
  have hq : 0≤q+14 := by linarith
  exact cor_fluid_cells_three_four H Ho G S B F eta beta p mu N teacherNorm delta Phi T q
    hr hdelta hPhi0 hT.le hq hparams hclock hDeltaLim hPhiLim hepslim
    hSparse.1 hetaSize hN hpoly

end SparseSGD.Logistic
