import SparseSGD.Logistic.IncrementGaussianComplement
import SparseSGD.Logistic.IncrementMGFAlgebra

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

def complementWeight {k B : ℕ} (p : unitInterval) (mu theta : Vec k)
    (a : Batch k B) (i : Fin B) : ℝ :=
  (B : ℝ)⁻¹*(sigma (inner ℝ theta (feature mu (a i))+bias p mu)-labelReal (a i).1)

def residualGaussianComplement {k m B : ℕ} (p : unitInterval) (mu theta : Vec k)
    (a : Batch k B) (z : Fin B → NoiseVec m) : Vec m :=
  ∑ i, complementWeight p mu theta a i • WithLp.toLp 2 (z i)

theorem complementWeight_variance {k B : ℕ} (p : unitInterval) (mu theta : Vec k) (a : Batch k B) :
    (∑ i, (complementWeight p mu theta a i)^2) = batchResidualEnergy p mu theta a := by
  simp only [complementWeight, mul_pow, batchResidualEnergy, sampleResidualSquare]
  rw [← Finset.mul_sum]
  rw [inv_pow]

theorem measurable_batchResidualEnergy {k B : ℕ} (p : unitInterval) (mu theta : Vec k) :
    Measurable (batchResidualEnergy (B := B) p mu theta) := by
  exact measurable_const.mul (Finset.measurable_sum _ (fun i _ =>
    (measurable_sampleResidualSquare p mu theta).comp (measurable_pi_apply i)))

theorem measurable_residualGaussianComplement {k m B : ℕ}
    (p : unitInterval) (mu theta : Vec k) :
    Measurable (fun z : Batch k B × (Fin B → NoiseVec m) => residualGaussianComplement p mu theta z.1 z.2) := by
  have hc (i : Fin B) : Measurable (fun a : Batch k B => complementWeight p mu theta a i) := by
    exact measurable_const.mul ((measurable_sigma.comp
      ((measurable_const.inner ((measurable_feature k mu).comp (measurable_pi_apply i))).add measurable_const)).sub
      (measurable_labelReal.comp (measurable_fst.comp (measurable_pi_apply i))))
  exact Finset.measurable_sum _ (fun i _ => (hc i).comp measurable_fst |>.smul
    (show Measurable (fun z : Batch k B × (Fin B → NoiseVec m) => (WithLp.toLp 2 (z.2 i) : Vec m)) by fun_prop))

/-- The Gaussian-complement quadratic MGF for the actual logistic residual
weights. Its two terms retain both the rare count variance and the
high-dimensional chi-square variance. The displayed scalar restrictions
are elementary admissibility conditions on the MGF parameter. -/
theorem tame_residualGaussianComplement_mgf {k m B : ℕ}
    (H : SparseSGD.External.BernsteinMomentsCertificate (Sample k))
    (J : SparseSGD.External.HoeffdingCertificate (Sample k))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (p : unitInterval) (mu theta : Vec k) (t : ℝ) (hB : 0 < B)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (ht : 2*|t|/(B : ℝ) < 1)
    (hcount : |2*t*(m : ℝ)| * (2/(B : ℝ)^2) < 1)
    (hsquare : 4*((m : ℝ)*t^2/(1-2*|t|/(B : ℝ))) ≤ (B : ℝ)^3/8) :
    Integrable (fun z : Batch k B × (Fin B → NoiseVec m) => Real.exp
      (t*(‖residualGaussianComplement p mu theta z.1 z.2‖^2-(m : ℝ)*coefD0 p mu theta/B)))
      ((batchLaw k B p).prod (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m))) ∧
    (∫ z : Batch k B × (Fin B → NoiseVec m), Real.exp
      (t*(‖residualGaussianComplement p mu theta z.1 z.2‖^2-(m : ℝ)*coefD0 p mu theta/B))
      ∂((batchLaw k B p).prod (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)))) ≤
      Real.exp (2*((m : ℝ)*t^2/(1-2*|t|/(B : ℝ)))*(coefD0 p mu theta/B)^2 +
        (2*t*(m : ℝ))^2*(16*(p : ℝ)/(B : ℝ)^3)/(2*(1-|2*t*(m : ℝ)| * (2/(B : ℝ)^2))) +
        64*Real.exp (1/2)*(p : ℝ)*((m : ℝ)*t^2/(1-2*|t|/(B : ℝ)))/(B : ℝ)^3) := by
  have hbr : (0 : ℝ) < B := by exact_mod_cast hB
  have hd : 0 < 1-2*|t|/(B : ℝ) := by linarith
  let K := (m : ℝ)*t^2/(1-2*|t|/(B : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let q := batchResidualEnergy (B := B) p mu theta
  let Y := fun a : Batch k B => q a-coefD0 p mu theta/B
  have hqm : Measurable q := measurable_batchResidualEnergy p mu theta
  have hYm : Measurable Y := hqm.sub measurable_const
  let Cf := (2*t*(m : ℝ))^2*(16*(p : ℝ)/(B : ℝ)^3)/(2*(1-|2*t*(m : ℝ)| * (2/(B : ℝ)^2)))
  let Cg := 64*Real.exp (1/2)*(p : ℝ)*K/(B : ℝ)^3
  have hCf : 0 ≤ Cf := by dsimp [Cf]; positivity
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hc := tame_batchResidualEnergy_mgf H p mu theta (2*t*(m : ℝ)) hB hp htame hcount
  have hs := tame_batchResidualEnergy_square_mgf J G p mu theta (4*K) hB hp htame (by positivity) hsquare
  have hcf (a : Batch k B) : 2*(t*(m : ℝ)*Y a) = (2*t*(m : ℝ))*(q a-coefD0 p mu theta/B) := by dsimp [Y]; ring
  have hcg (a : Batch k B) : 2*(2*K*(Y a)^2) = (4*K)*(q a-coefD0 p mu theta/B)^2 := by dsimp [Y]; ring
  have hcfI : Integrable (fun a => Real.exp (2*(t*(m : ℝ)*Y a))) (batchLaw k B p) := by simpa only [hcf] using hc.1
  have hcgI : Integrable (fun a => Real.exp (2*(2*K*(Y a)^2))) (batchLaw k B p) := by simpa only [hcg] using hs.1
  have hcfB : (∫ a, Real.exp (2*(t*(m : ℝ)*Y a)) ∂batchLaw k B p) ≤ Real.exp Cf := by simpa only [hcf] using hc.2
  have hcgB : (∫ a, Real.exp (2*(2*K*(Y a)^2)) ∂batchLaw k B p) ≤ Real.exp Cg := by
    simp_rw [hcg]
    exact hs.2.trans_eq (by congr 1; dsimp [Cg]; ring)
  have hprefix := exp_add_integrable_bound (batchLaw k B p)
    (fun a => t*(m : ℝ)*Y a) (fun a => 2*K*(Y a)^2)
    (measurable_const.mul hYm) (measurable_const.mul (hYm.pow_const 2)) Cf Cg hCf hCg hcfI hcgI hcfB hcgB
  let M := fun a : Batch k B => Real.exp (2*K*(coefD0 p mu theta/B)^2)*
    Real.exp (t*(m : ℝ)*Y a+2*K*(Y a)^2)
  have hMI : Integrable M (batchLaw k B p) := hprefix.1.const_mul _
  let F := fun z : Batch k B × (Fin B → NoiseVec m) => Real.exp
    (t*(‖residualGaussianComplement p mu theta z.1 z.2‖^2-(m : ℝ)*coefD0 p mu theta/B))
  have hFm : Measurable F := by
    exact Real.measurable_exp.comp (measurable_const.mul
      (((measurable_residualGaussianComplement p mu theta).norm.pow_const 2).sub measurable_const))
  have hslice (a : Batch k B) : Integrable (fun z => F (a,z))
      (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)) ∧
      (∫ z, F (a,z) ∂Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)) ≤ M a := by
    have hq0 := batchResidualEnergy_nonneg p mu theta a
    have hq1 := batchResidualEnergy_le p mu theta hB a
    have hparam : 2*|t| * q a < 1 := by
      have hh := mul_le_mul_of_nonneg_left hq1 (show 0 ≤ 2*|t| by positivity)
      exact hh.trans_lt (by simpa [div_eq_mul_inv, mul_assoc] using ht)
    have hh := gaussian_weighted_sum_norm_mgf G m B (complementWeight p mu theta a) t
      (by simpa only [complementWeight_variance] using hparam)
    simp only [complementWeight_variance] at hh
    have he (z : Fin B → NoiseVec m) : F (a,z) = Real.exp (t*(m : ℝ)*Y a)*
        Real.exp (t*(‖residualGaussianComplement p mu theta a z‖^2-(m : ℝ)*q a)) := by
      rw [← Real.exp_add]
      dsimp [F, Y]
      congr 1
      ring
    simp_rw [he]
    refine ⟨hh.1.const_mul _, ?_⟩
    rw [integral_const_mul]
    have hden : 1-2*|t|/(B : ℝ) ≤ 1-2*|t| * q a := by
      have hh := mul_le_mul_of_nonneg_left hq1 (show 0 ≤ 2*|t| by positivity)
      exact sub_le_sub_left (by simpa only [div_eq_mul_inv] using hh) 1
    have hex : Real.exp ((m : ℝ)*t^2*(q a)^2/(1-2*|t| * q a)) ≤ Real.exp (K*(q a)^2) := by
      apply Real.exp_le_exp.mpr
      have hh := div_le_div_of_nonneg_left (show 0 ≤ (m : ℝ)*t^2*(q a)^2 by positivity) hd hden
      exact hh.trans_eq (by dsimp [K]; ring)
    have hbound := mul_le_mul_of_nonneg_left (hh.2.trans hex) (Real.exp_pos (t*(m : ℝ)*Y a)).le
    refine hbound.trans ?_
    dsimp [M]
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq : (q a)^2 ≤ 2*(coefD0 p mu theta/B)^2+2*(Y a)^2 := by
      dsimp [Y]
      nlinarith [sq_nonneg (q a-2*(coefD0 p mu theta/B))]
    nlinarith [mul_le_mul_of_nonneg_left hsq hK]
  have hFI : Integrable F ((batchLaw k B p).prod
      (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m))) := by
    apply (integrable_prod_iff hFm.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun a => (hslice a).1), ?_⟩
    apply hMI.mono' hFm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards with a
    have he (z : Fin B → NoiseVec m) : ‖F (a,z)‖ = F (a,z) := by simp only [F, Real.norm_eq_abs, Real.abs_exp]
    simp_rw [he]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun z => (Real.exp_pos _).le))]
    exact (hslice a).2
  refine ⟨hFI, ?_⟩
  rw [integral_prod F hFI]
  have hh := integral_mono hFI.integral_prod_left hMI (fun a => (hslice a).2)
  refine hh.trans ?_
  change (∫ a, Real.exp (2*K*(coefD0 p mu theta/B)^2)*
    Real.exp (t*(m : ℝ)*Y a+2*K*(Y a)^2) ∂batchLaw k B p) ≤ _
  rw [integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left hprefix.2
    (Real.exp_pos (2*K*(coefD0 p mu theta/B)^2)).le
  refine hh.trans_eq ?_
  rw [← Real.exp_add]
  congr 1
  dsimp [Cf, Cg, K]
  ring

end
end SparseSGD.Logistic
