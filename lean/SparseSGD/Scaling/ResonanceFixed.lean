import SparseSGD.Scaling.Resonance
import SparseSGD.Scaling.LSLearningFamily

open Filter Topology MeasureTheory
namespace SparseSGD.Scaling
noncomputable section
set_option maxHeartbeats 1600000

theorem resonantFixed_noise_identity (eta b : ℝ) (p : ℕ → unitInterval) (d : ℕ)
    (hd : 0 < d) :
    resonantNoiseLoad eta b 0 p d=(eta/(2*(fixedRealizedBatch b : ℝ)))*
      (((d : ℝ)+2-(p d : ℝ))/(d : ℝ)) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hB : (fixedRealizedBatch b : ℝ) ≠ 0 := by exact_mod_cast (fixedRealizedBatch_pos b).ne'
  unfold resonantNoiseLoad scaledLearningRate
  rw [scaledBatch_zero_eq_fixed]
  norm_num only [sub_zero,Real.rpow_neg_one]
  change eta * (d : ℝ)⁻¹ * ((d : ℝ) + 2 - (p d : ℝ)) / (2 * (fixedRealizedBatch b : ℝ)) = _
  field_simp

theorem resonantFixed_noise_error (eta b : ℝ) (p : ℕ → unitInterval) (d : ℕ)
    (hd : 0 < d) (heta : 0 < eta) :
    |resonantNoiseLoad eta b 0 p d-eta/(2*(fixedRealizedBatch b : ℝ))| ≤
      2*(eta/(2*(fixedRealizedBatch b : ℝ)))/(d : ℝ) := by
  let u := eta/(2*(fixedRealizedBatch b : ℝ))
  have hB : 0 < (fixedRealizedBatch b : ℝ) := by exact_mod_cast fixedRealizedBatch_pos b
  have hu : 0 < u := by dsimp [u]; positivity
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have Hid : resonantNoiseLoad eta b 0 p d-u=u*((2-(p d : ℝ))/(d : ℝ)) := by
    rw [resonantFixed_noise_identity eta b p d hd]
    dsimp [u]
    field_simp
    <;> ring
  change |resonantNoiseLoad eta b 0 p d-u| ≤ 2*u/(d : ℝ)
  rw [Hid,abs_of_nonneg (mul_nonneg hu.le (div_nonneg (by linarith [(p d).property.2]) hdR.le))]
  have HP : 2-(p d : ℝ) ≤ 2 := by linarith [(p d).property.1]
  have H := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right HP hdR.le) hu.le
  convert H using 1 <;> ring

theorem resonantFixed_additive_identity (eta b variance : ℝ) (d : ℕ) (hd : 0 < d) :
    resonantAdditiveLoad eta b 0 variance d=variance*(eta/(2*(fixedRealizedBatch b : ℝ))) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hB : (fixedRealizedBatch b : ℝ) ≠ 0 := by exact_mod_cast (fixedRealizedBatch_pos b).ne'
  unfold resonantAdditiveLoad scaledLearningRate
  rw [scaledBatch_zero_eq_fixed]
  norm_num only [sub_zero,Real.rpow_neg_one]
  change eta * (d : ℝ)⁻¹ * variance * (d : ℝ) / (2 * (fixedRealizedBatch b : ℝ)) = _
  field_simp

/-- Actual resonance rate on the fixed integer batch edge. -/
theorem cor_resonance_fixed_rate
    (pStar kappa bStar epsStar gamma etaStar R : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (jury : External.JuryStability)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (hb : 0 < bStar) 
    (he : 0 < epsStar) (hg : 0 < gamma) (heta : 0 < etaStar)
    (hline : gamma=1+kappa)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hR : 0 ≤ R) (hu1 : etaStar/(2*(fixedRealizedBatch bStar : ℝ)) < 1) :
    ∃ C > 0, ∀ᶠ d in atTop, ∀ k : ℕ,
      let P := actualLSParams pStar kappa bStar 0 epsStar gamma etaStar (1) p ν d
      |(P.trajectory ⟨R,0,0⟩ k).R-
        (continuumFlow (etaStar*pStar/epsStar) (etaStar/(2*(fixedRealizedBatch bStar : ℝ)))
          (SparseSGD.Probability.LeastSquares.labelVariance ν*(etaStar/(2*(fixedRealizedBatch bStar : ℝ))))
          ⟨R,0,0⟩ ((k : ℝ)*P.matchedStep)).R| ≤
      C*((d : ℝ)^(-gamma)+(d : ℝ)^(-1 : ℝ)) := by
  let D := etaStar*pStar/epsStar
  let u := etaStar/(2*(fixedRealizedBatch bStar : ℝ))
  let variance := SparseSGD.Probability.LeastSquares.labelVariance ν
  let phi := variance*u
  let margin := (1-u)/2
  let P := actualLSParams pStar kappa bStar 0 epsStar gamma etaStar (1) p ν
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 < (fixedRealizedBatch bStar : ℝ) := by exact_mod_cast fixedRealizedBatch_pos bStar
  have hu : 0 < u := by dsimp [u]; positivity
  have hvar : 0 ≤ variance := labelVariance_nonneg ν
  have hphi : 0 ≤ phi := mul_nonneg hvar hu.le
  have hm : 0 < margin := by dsimp [margin,u]; linarith
  have huM : u < 1-margin := by dsimp [margin,u]; linarith
  obtain ⟨eps0,heps0,A,hA,Hmain⟩ := regular_cold_raw_rate D margin hD hm
  have heps := scaledRetention_tendsto_zero epsStar gamma hg
  have halg := actualLSFamily_algebra pStar kappa bStar 0 epsStar gamma etaStar (1)
    p ν hp hb he hg heta hpd
  have htuple : ∀ᶠ d in atTop, P d=lsPowerParams pStar kappa bStar 0 epsStar gamma etaStar (1) variance d := by
    filter_upwards [hpd,eventually_gt_atTop (0 : ℕ)] with d hd hd0
    have hp0 : (p d : ℝ) ≠ 0 := by rw [hd]; exact (scaledSparsity_pos_of_pos pStar kappa d hp hd0).ne'
    exact actualLSParams_eq_lsPowerParams pStar kappa bStar 0 epsStar gamma etaStar (1) p ν d hp0 hd
  obtain ⟨hnoiseRaw,haddRaw⟩ := ls_fixed_batch_load_limits pStar kappa etaStar 1 bStar variance u hk heta
    (Or.inr ⟨by ring, rfl⟩)
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
    actualLSParams_curvature_tendsto_zero pStar kappa bStar 0 epsStar gamma etaStar (1)
      p ν hp he heta hg hpd (by linarith)
  have hnu : Tendsto (fun d => (P d).renormNoise) atTop (𝓝 u) := renorm_load_tendsto _ _ u hnoise hcurv
  have hph : Tendsto (fun d => (P d).renormAdditive) atTop (𝓝 phi) := renorm_load_tendsto _ _ phi hadd hcurv
  have hraw : ∀ᶠ d in atTop, (P d).w=D*(P d).eps^2 ∧ (P d).eps=scaledRetention epsStar gamma d := by
    filter_upwards [halg,eventually_gt_atTop (0 : ℕ)] with d hd hd0
    refine ⟨?_,hd.2.2.1⟩
    rw [hd.2.2.2.2.1,lsDelta_resonant_constant pStar etaStar epsStar kappa gamma (1) hp heta he (by linarith) d hd0]
  have hepsP : Tendsto (fun d => (P d).eps) atTop (𝓝 0) := by
    apply heps.congr'
    filter_upwards [hraw] with d hd
    exact hd.2.symm
  have hwlim : Tendsto (fun d => (P d).w) atTop (𝓝 0) := by
    have H : Tendsto (fun d => D*(P d).eps^2) atTop (𝓝 0) := by simpa using (hepsP.pow 2).const_mul D
    apply H.congr'
    filter_upwards [hraw] with d hd
    exact hd.1.symm
  let K := (1+2*D*(u+phi))*epsStar+4*u+1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨A*K*(R+phi+2),by positivity,?_⟩
  filter_upwards [halg,hraw,hpd,eventually_gt_atTop (0 : ℕ),
    hepsP.eventually (eventually_lt_nhds heps0),
    hwlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/16)),
    hcurv.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/2)),
    hnu.eventually (eventually_lt_nhds huM),
    hph.eventually (eventually_lt_nhds (by linarith : phi<phi+1))]
    with d halg hraw hpd hd hepsSmall hwSmall hcSmall hnuSmall hphSmall
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
  have Hnoise := resonantFixed_noise_error etaStar bStar p d hd heta
  have Hadd := resonantFixed_additive_identity etaStar bStar variance d hd
  rw [← actualLSParams_resonant_noise_eq pStar kappa bStar 0 epsStar gamma etaStar p ν d hp0] at Hnoise
  rw [← actualLSParams_resonant_additive_eq pStar kappa bStar 0 epsStar gamma etaStar p ν d hp0] at Hadd
  have Hnu := renorm_load_difference_bound (P d).noise (P d).curvature u hcurv0 hcSmall.le
  have Hph := renorm_load_difference_bound (P d).additive (P d).curvature phi hcurv0 hcSmall.le
  rw [abs_of_pos hu] at Hnu
  rw [abs_of_nonneg hphi] at Hph
  simp only [sub_zero] at Hnoise Hadd
  change |(P d).noise-u| ≤ 2*u/(d : ℝ) at Hnoise
  change (P d).additive=phi at Hadd
  have Hadd0 : |(P d).additive-phi|=0 := by rw [Hadd,sub_self,abs_zero]
  rw [Hadd0] at Hph
  change |(P d).renormNoise-u| ≤ _ at Hnu
  change |(P d).renormAdditive-phi| ≤ _ at Hph
  have Hcurv := mul_le_mul_of_nonneg_left hcurve (show 0 ≤ 2*(u+phi) by positivity)
  have Herr : (P d).eps+|(P d).renormNoise-u|+|(P d).renormAdditive-phi| ≤
      (1+2*D*(u+phi))*(P d).eps+4*u/(d : ℝ) := by
    simp only [div_eq_mul_inv,mul_inv_rev] at Hnoise Hnu Hph Hcurv ⊢
    nlinarith only [Hnoise,Hnu,Hph,Hcurv]
  let S := (d : ℝ)^(-gamma)+(d : ℝ)^(-1 : ℝ)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hs1 : 0 ≤ (d : ℝ)^(-gamma) := (Real.rpow_pos_of_pos hdR _).le
  have hs2 : 0 ≤ (d : ℝ)^(-1 : ℝ) := (Real.rpow_pos_of_pos hdR _).le
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have H1 : (d : ℝ)^(-gamma) ≤ S := by dsimp [S]; linarith
  have H2 : (d : ℝ)^(-1 : ℝ) ≤ S := by dsimp [S]; linarith
  have Hnorm : (P d).eps+|(P d).renormNoise-u|+|(P d).renormAdditive-phi| ≤ K*S := by
    have HE := mul_le_mul_of_nonneg_left H1 (show 0 ≤ (1+2*D*(u+phi))*epsStar by positivity)
    have HN := mul_le_mul_of_nonneg_left H2 (show 0 ≤ 4*u by positivity)
    rw [hepsEq] at Herr
    have hpow1 : (d : ℝ)^(-1 : ℝ)=1/(d : ℝ) := by simp [Real.rpow_neg hdR.le]
    dsimp [scaledRetention] at Herr
    rw [div_eq_mul_one_div (4*u),← hpow1] at Herr
    rw [hepsEq]
    dsimp [K,scaledRetention]
    nlinarith only [Herr,HE,HN,hS]
  obtain ⟨hnu0,hph0⟩ := renorm_nonneg_of_curvature_lt_one (P d) hn0 ha0 (by linarith)
  intro k
  have H := Hmain (P d) R u phi hb0 hb1 hwpos hwSmall.le hraw.1 hepsSmall.le jury hR
    hnu0 hnuSmall.le hu.le huM.le hph0 k
  have HS := mul_le_mul Hnorm (show R+(P d).renormAdditive+1 ≤ R+phi+2 by linarith)
    (by positivity : 0 ≤ R+(P d).renormAdditive+1) (mul_nonneg hK.le hS)
  have HA := mul_le_mul_of_nonneg_left HS hA.le
  exact H.trans (by convert HA using 1 <;> ring)


/-- Fixed-batch resonance has the source minimum exponent. -/
theorem cor_resonance_fixed_rate_min
    (pStar kappa bStar epsStar gamma etaStar R : ℝ)
    (p : ℕ → unitInterval) (ν : Measure ℝ) (jury : External.JuryStability)
    (hp : 0 < pStar) (hk : 0 ≤ kappa) (hb : 0 < bStar) 
    (he : 0 < epsStar) (hg : 0 < gamma) (heta : 0 < etaStar)
    (hline : gamma=1+kappa)
    (hpd : ∀ᶠ d in atTop, (p d : ℝ)=scaledSparsity pStar kappa d)
    (hR : 0 ≤ R) (hu1 : etaStar/(2*(fixedRealizedBatch bStar : ℝ)) < 1) :
    ∃ C > 0, ∀ᶠ d in atTop, ∀ k : ℕ,
      let P := actualLSParams pStar kappa bStar 0 epsStar gamma etaStar (1) p ν d
      |(P.trajectory ⟨R,0,0⟩ k).R-
        (continuumFlow (etaStar*pStar/epsStar) (etaStar/(2*(fixedRealizedBatch bStar : ℝ)))
          (SparseSGD.Probability.LeastSquares.labelVariance ν*(etaStar/(2*(fixedRealizedBatch bStar : ℝ))))
          ⟨R,0,0⟩ ((k : ℝ)*P.matchedStep)).R| ≤
      C*(d : ℝ)^(-min gamma 1) := by
  obtain ⟨C,hC,H⟩ := cor_resonance_fixed_rate pStar kappa bStar epsStar gamma etaStar R
    p ν jury hp hk hb he hg heta hline hpd hR hu1
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H,eventually_ge_atTop (1 : ℕ)] with d hd hd1
  intro k
  apply (hd k).trans
  have hdR : 1 ≤ (d : ℝ) := by exact_mod_cast hd1
  have H1 := Real.rpow_le_rpow_of_exponent_le hdR (neg_le_neg (min_le_left gamma 1))
  have H2 := Real.rpow_le_rpow_of_exponent_le hdR (neg_le_neg (min_le_right gamma 1))
  have Hsum := mul_le_mul_of_nonneg_left (show (d : ℝ)^(-gamma)+(d : ℝ)^(-1 : ℝ) ≤ 2*(d : ℝ)^(-min gamma 1) by linarith) hC.le
  convert Hsum using 1 <;> ring

end
end SparseSGD.Scaling
