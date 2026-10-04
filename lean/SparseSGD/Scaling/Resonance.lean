import SparseSGD.Scaling.ColdRegular
import SparseSGD.Scaling.ResonanceParameters
import SparseSGD.Scaling.LSFamily

open Filter Topology MeasureTheory
namespace SparseSGD.Scaling
noncomputable section
set_option maxHeartbeats 1600000

/-- The raw matched curvature is exactly constant on the resonance line. -/
theorem lsDelta_resonant_constant (pStar etaStar epsStar kappa gamma alpha : ℝ)
    (hp : 0 < pStar) (heta : 0 < etaStar) (he : 0 < epsStar)
    (hline : gamma-alpha-kappa=0) (d : ℕ) (hd : 0 < d) :
    lsDelta pStar etaStar epsStar kappa gamma alpha d=etaStar*pStar/epsStar := by
  have H := lsDelta_power_ratio pStar etaStar epsStar kappa gamma alpha d hd hp.ne' heta.ne' he.ne'
  rw [hline,Real.rpow_zero,mul_one] at H
  exact (div_eq_one_iff_eq (show etaStar*pStar/epsStar ≠ 0 by positivity)).mp H

/-- Corrected source resonance rate for actual positive-exponent integer batch
families. Integer rounding contributes the `d^(-sigma)` term. -/
theorem cor_resonance_rate
    (pStar kappa bStar sigma epsStar gamma etaStar R : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (jury : External.JuryStability)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (hb : 0 < bStar) (hs : 0 < sigma)
    (he : 0 < epsStar) (hg : 0 < gamma) (heta : 0 < etaStar)
    (hline : gamma=1-sigma+kappa)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hR : 0 ≤ R) (hu1 : etaStar/(2*bStar) < 1) :
    ∃ C > 0, ∀ᶠ d in atTop, ∀ k : ℕ,
      let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar (1-sigma) p ν d
      |(P.trajectory ⟨R,0,0⟩ k).R-
        (continuumFlow (etaStar*pStar/epsStar) (etaStar/(2*bStar))
          (SparseSGD.Probability.LeastSquares.labelVariance ν*(etaStar/(2*bStar)))
          ⟨R,0,0⟩ ((k : ℝ)*P.matchedStep)).R| ≤
      C*((d : ℝ)^(-gamma)+(d : ℝ)^(-1 : ℝ)+(d : ℝ)^(-sigma)) := by
  let D := etaStar*pStar/epsStar
  let u := etaStar/(2*bStar)
  let variance := SparseSGD.Probability.LeastSquares.labelVariance ν
  let phi := variance*u
  let margin := (1-u)/2
  let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar (1-sigma) p ν
  have hD : 0 < D := by dsimp [D]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hvar : 0 ≤ variance := labelVariance_nonneg ν
  have hphi : 0 ≤ phi := mul_nonneg hvar hu.le
  have hm : 0 < margin := by dsimp [margin,u]; linarith
  have huM : u < 1-margin := by dsimp [margin,u]; linarith
  obtain ⟨eps0,heps0,A,hA,Hmain⟩ := regular_cold_raw_rate D margin hD hm
  have heps := scaledRetention_tendsto_zero epsStar gamma hg
  have halg := actualLSFamily_algebra pStar kappa bStar sigma epsStar gamma etaStar (1-sigma)
    p ν hp hb he hg heta hpd
  have htuple : ∀ᶠ d in atTop, P d=lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar (1-sigma) variance d := by
    filter_upwards [hpd,eventually_gt_atTop (0 : ℕ)] with d hd hd0
    have hp0 : (p d : ℝ) ≠ 0 := by rw [hd]; exact (scaledSparsity_pos_of_pos pStar kappa d hp hd0).ne'
    exact actualLSParams_eq_lsPowerParams pStar kappa bStar sigma epsStar gamma etaStar (1-sigma) p ν d hp0 hd
  have hnoiseRaw := lsNoiseLoad_tendsto_critical pStar kappa etaStar (1-sigma) bStar sigma hp hk heta hb hs (by ring)
  have haddRaw := lsAdditiveLoad_tendsto_critical etaStar (1-sigma) bStar sigma variance heta hb hs (by ring)
  have hnoise : Tendsto (fun d => (P d).noise) atTop (𝓝 u) := by
    apply hnoiseRaw.congr'
    filter_upwards [htuple] with d hd
    rw [hd]
    rfl
  have hadd : Tendsto (fun d => (P d).additive) atTop (𝓝 phi) := by
    apply haddRaw.congr'
    filter_upwards [htuple] with d hd
    rw [hd]
    rfl
  have hcurv : Tendsto (fun d => (P d).curvature) atTop (𝓝 0) :=
    actualLSParams_curvature_tendsto_zero pStar kappa bStar sigma epsStar gamma etaStar (1-sigma)
      p ν hp he heta hg hpd (by linarith)
  have hnu : Tendsto (fun d => (P d).renormNoise) atTop (𝓝 u) := renorm_load_tendsto _ _ u hnoise hcurv
  have hph : Tendsto (fun d => (P d).renormAdditive) atTop (𝓝 phi) := renorm_load_tendsto _ _ phi hadd hcurv
  have hraw : ∀ᶠ d in atTop, (P d).w=D*(P d).eps^2 ∧ (P d).eps=scaledRetention epsStar gamma d := by
    filter_upwards [halg,eventually_gt_atTop (0 : ℕ)] with d hd hd0
    refine ⟨?_,hd.2.2.1⟩
    rw [hd.2.2.2.2.1,lsDelta_resonant_constant pStar etaStar epsStar kappa gamma (1-sigma) hp heta he (by linarith) d hd0]
  have hepsP : Tendsto (fun d => (P d).eps) atTop (𝓝 0) := by
    apply heps.congr'
    filter_upwards [hraw] with d hd
    exact hd.2.symm
  have hwlim : Tendsto (fun d => (P d).w) atTop (𝓝 0) := by
    have H : Tendsto (fun d => D*(P d).eps^2) atTop (𝓝 0) := by simpa using (hepsP.pow 2).const_mul D
    apply H.congr'
    filter_upwards [hraw] with d hd
    exact hd.1.symm
  let K := (1+2*D*(u+phi))*epsStar+8*u+4*(u+phi)/bStar+1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨A*K*(R+phi+2),by positivity,?_⟩
  filter_upwards [halg,hraw,hpd,eventually_gt_atTop (0 : ℕ),
    hepsP.eventually (eventually_lt_nhds heps0),
    hwlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/16)),
    hcurv.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/2)),
    hnu.eventually (eventually_lt_nhds huM),
    hph.eventually (eventually_lt_nhds (by linarith : phi<phi+1)),
    (powerLaw_tendsto_atTop bStar sigma hb hs).eventually (eventually_ge_atTop (2 : ℝ))]
    with d halg hraw hpd hd hepsSmall hwSmall hcSmall hnuSmall hphSmall hbatch
  obtain ⟨hb0,hb1,hepsEq,hDelta,hwDelta,hn0,ha0⟩ := halg
  have hepspos := (Params.small_step_bounds (P d) hb0 hb1).1
  have hepshalf := (Params.small_step_bounds (P d) hb0 hb1).2.1
  have hwpos : 0 < (P d).w := by rw [hraw.1]; positivity
  have hcurv0 : 0 ≤ (P d).curvature := by unfold Params.curvature; positivity
  have hcurvw : (P d).curvature ≤ (P d).w := by
    unfold Params.curvature
    apply (div_le_iff₀ (show 0 < 2*(1+(P d).beta) by linarith)).mpr
    nlinarith
  have hcurve : (P d).curvature ≤ D*(P d).eps := by
    have H : (P d).eps^2 ≤ (P d).eps := by nlinarith
    have HH := mul_le_mul_of_nonneg_left H hD.le
    rw [hraw.1] at hcurvw
    exact hcurvw.trans HH
  have hp0 : (p d : ℝ) ≠ 0 := by rw [hpd]; exact (scaledSparsity_pos_of_pos pStar kappa d hp hd).ne'
  have Hnoise := resonantNoiseLoad_error_bound etaStar bStar sigma p d (by omega) heta hb hbatch
  have Hadd := resonantAdditiveLoad_error_bound etaStar bStar sigma variance d (by omega) heta hb hvar hbatch
  rw [← actualLSParams_resonant_noise_eq pStar kappa bStar sigma epsStar gamma etaStar p ν d hp0] at Hnoise
  rw [← actualLSParams_resonant_additive_eq pStar kappa bStar sigma epsStar gamma etaStar p ν d hp0] at Hadd
  have Hnu := renorm_load_difference_bound (P d).noise (P d).curvature u hcurv0 hcSmall.le
  have Hph := renorm_load_difference_bound (P d).additive (P d).curvature phi hcurv0 hcSmall.le
  rw [abs_of_pos hu] at Hnu
  rw [abs_of_nonneg hphi] at Hph
  change |(P d).noise-u| ≤ u*(4/(d : ℝ)+2/(bStar*(d : ℝ)^sigma)) at Hnoise
  change |(P d).additive-phi| ≤ phi*(2/(bStar*(d : ℝ)^sigma)) at Hadd
  change |(P d).renormNoise-u| ≤ _ at Hnu
  change |(P d).renormAdditive-phi| ≤ _ at Hph
  have Hcurv := mul_le_mul_of_nonneg_left hcurve (show 0 ≤ 2*(u+phi) by positivity)
  have Herr : (P d).eps+|(P d).renormNoise-u|+|(P d).renormAdditive-phi| ≤
      (1+2*D*(u+phi))*(P d).eps+8*u/(d : ℝ)+4*(u+phi)/(bStar*(d : ℝ)^sigma) := by
    simp only [div_eq_mul_inv,mul_inv_rev] at Hnoise Hadd Hnu Hph Hcurv ⊢
    nlinarith only [Hnoise,Hadd,Hnu,Hph,Hcurv]
  let S := (d : ℝ)^(-gamma)+(d : ℝ)^(-1 : ℝ)+(d : ℝ)^(-sigma)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hs1 : 0 ≤ (d : ℝ)^(-gamma) := (Real.rpow_pos_of_pos hdR _).le
  have hs2 : 0 ≤ (d : ℝ)^(-1 : ℝ) := (Real.rpow_pos_of_pos hdR _).le
  have hs3 : 0 ≤ (d : ℝ)^(-sigma) := (Real.rpow_pos_of_pos hdR _).le
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have H1 : (d : ℝ)^(-gamma) ≤ S := by dsimp [S]; linarith
  have H2 : (d : ℝ)^(-1 : ℝ) ≤ S := by dsimp [S]; linarith
  have H3 : (d : ℝ)^(-sigma) ≤ S := by dsimp [S]; linarith
  have Hnorm : (P d).eps+|(P d).renormNoise-u|+|(P d).renormAdditive-phi| ≤ K*S := by
    have HE := mul_le_mul_of_nonneg_left H1 (show 0 ≤ (1+2*D*(u+phi))*epsStar by positivity)
    have HN := mul_le_mul_of_nonneg_left H2 (show 0 ≤ 8*u by positivity)
    have HP := mul_le_mul_of_nonneg_left H3 (show 0 ≤ 4*(u+phi)/bStar by positivity)
    rw [hepsEq] at Herr
    have hpow1 : (d : ℝ)^(-1 : ℝ)=1/(d : ℝ) := by simp [Real.rpow_neg hdR.le]
    have hpows : 1/(bStar*(d : ℝ)^sigma)=(1/bStar)*(d : ℝ)^(-sigma) := by rw [Real.rpow_neg hdR.le]; ring
    dsimp [scaledRetention] at Herr
    rw [div_eq_mul_one_div (8*u),div_eq_mul_one_div (4*(u+phi)),← hpow1,hpows] at Herr
    rw [hepsEq]
    dsimp [K,scaledRetention]
    simp only [div_eq_mul_inv] at HP Herr ⊢
    nlinarith only [Herr,HE,HN,HP,hS]
  obtain ⟨hnu0,hph0⟩ := renorm_nonneg_of_curvature_lt_one (P d) hn0 ha0 (by linarith)
  intro k
  have H := Hmain (P d) R u phi hb0 hb1 hwpos hwSmall.le hraw.1 hepsSmall.le jury hR
    hnu0 hnuSmall.le hu.le huM.le hph0 k
  have HS := mul_le_mul Hnorm (show R+(P d).renormAdditive+1 ≤ R+phi+2 by linarith)
    (by positivity : 0 ≤ R+(P d).renormAdditive+1) (mul_nonneg hK.le hS)
  have HA := mul_le_mul_of_nonneg_left HS hA.le
  exact H.trans (by convert HA using 1 <;> ring)

/-- The three independent error scales give the corrected minimum exponent. -/
theorem resonance_power_sum_bound (gamma sigma : ℝ) (d : ℕ) (hd : 1 ≤ d) :
    (d : ℝ)^(-gamma)+(d : ℝ)^(-1 : ℝ)+(d : ℝ)^(-sigma) ≤
      3*(d : ℝ)^(-min gamma (min 1 sigma)) := by
  have hdR : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have H1 := Real.rpow_le_rpow_of_exponent_le hdR (neg_le_neg (min_le_left gamma (min 1 sigma)))
  have H2 := Real.rpow_le_rpow_of_exponent_le hdR (neg_le_neg ((min_le_right gamma (min 1 sigma)).trans (min_le_left 1 sigma)))
  have H3 := Real.rpow_le_rpow_of_exponent_le hdR (neg_le_neg ((min_le_right gamma (min 1 sigma)).trans (min_le_right 1 sigma)))
  linarith

/-- Source resonance error, with the integer-rounding exponent retained. -/
theorem cor_resonance_rate_min
    (pStar kappa bStar sigma epsStar gamma etaStar R : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (jury : External.JuryStability)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (hb : 0 < bStar) (hs : 0 < sigma)
    (he : 0 < epsStar) (hg : 0 < gamma) (heta : 0 < etaStar)
    (hline : gamma=1-sigma+kappa)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hR : 0 ≤ R) (hu1 : etaStar/(2*bStar) < 1) :
    ∃ C > 0, ∀ᶠ d in atTop, ∀ k : ℕ,
      let P := actualLSParams pStar kappa bStar sigma epsStar gamma etaStar (1-sigma) p ν d
      |(P.trajectory ⟨R,0,0⟩ k).R-
        (continuumFlow (etaStar*pStar/epsStar) (etaStar/(2*bStar))
          (SparseSGD.Probability.LeastSquares.labelVariance ν*(etaStar/(2*bStar)))
          ⟨R,0,0⟩ ((k : ℝ)*P.matchedStep)).R| ≤
      C*(d : ℝ)^(-min gamma (min 1 sigma)) := by
  obtain ⟨C,hC,H⟩ := cor_resonance_rate pStar kappa bStar sigma epsStar gamma etaStar R
    p ν jury hp hk hb hs he hg heta hline hpd hR hu1
  refine ⟨3*C,by positivity,?_⟩
  filter_upwards [H,eventually_ge_atTop (1 : ℕ)] with d hd hd1
  intro k
  apply (hd k).trans
  have Hsum := mul_le_mul_of_nonneg_left (resonance_power_sum_bound gamma sigma d hd1) hC.le
  convert Hsum using 1 <;> ring

end
end SparseSGD.Scaling
