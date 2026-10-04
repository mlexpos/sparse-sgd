import SparseSGD.Logistic.IncrementComplementMGF
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

def complementQuadraticScale (m B : ℕ) : ℝ := 32/(B : ℝ)+32*(m : ℝ)/(B : ℝ)^2

def complementQuadraticVariance (p : unitInterval) (m B : ℕ) : ℝ :=
  (m : ℝ)*(p : ℝ)^2/(B : ℝ)^2+(m : ℝ)^2*(p : ℝ)/(B : ℝ)^3

theorem complement_parameter_bounds (m B : ℕ) (t : ℝ) (hB : 0 < B)
    (ht : |t| * complementQuadraticScale m B ≤ 1) :
    2*|t|/(B : ℝ) ≤ 1/2 ∧
    |2*t*(m : ℝ)| * (2/(B : ℝ)^2) ≤ 1/2 ∧
    4*((m : ℝ)*t^2/(1-2*|t|/(B : ℝ))) ≤ (B : ℝ)^3/8 := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hm : 0 ≤ (m : ℝ) := by positivity
  have ha : 0 ≤ |t| := abs_nonneg t
  have h1 : 32*|t|/(B : ℝ) ≤ 1 := by
    have hrest : 0 ≤ |t| * (32*(m : ℝ)/(B : ℝ)^2) := by positivity
    dsimp [complementQuadraticScale] at ht
    have he : |t| * (32/(B : ℝ)+32*(m : ℝ)/(B : ℝ)^2) =
      32*|t|/(B : ℝ)+|t| * (32*(m : ℝ)/(B : ℝ)^2) := by ring
    rw [he] at ht
    linarith
  have h2 : 32*|t| * (m : ℝ)/(B : ℝ)^2 ≤ 1 := by
    dsimp [complementQuadraticScale] at ht
    have hrest : 0 ≤ |t| * (32/(B : ℝ)) := by positivity
    have he : |t| * (32/(B : ℝ)+32*(m : ℝ)/(B : ℝ)^2) =
      |t| * (32/(B : ℝ))+32*|t| * (m : ℝ)/(B : ℝ)^2 := by ring
    rw [he] at ht
    linarith
  have h1' : 32*|t| ≤ (B : ℝ) := (div_le_one hb).mp h1
  have h2' : 32*|t| * (m : ℝ) ≤ (B : ℝ)^2 := (div_le_one (sq_pos_of_pos hb)).mp h2
  have hfirst : 2*|t|/(B : ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hb).mpr
    nlinarith
  have hcount : |2*t*(m : ℝ)| * (2/(B : ℝ)^2) ≤ 1/2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hm]
    have hh : 4*|t| * (m : ℝ)/(B : ℝ)^2 ≤ 1/2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hb)).mpr
      nlinarith
    convert hh using 1 <;> ring
  refine ⟨hfirst, hcount, ?_⟩
  have hd : 0 < 1-2*|t|/(B : ℝ) := by linarith
  have hK : (m : ℝ)*t^2/(1-2*|t|/(B : ℝ)) ≤ 2*(m : ℝ)*t^2 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0 ≤ (m : ℝ)*t^2 by positivity)
      (show 0 ≤ 1/2-2*|t|/(B : ℝ) by linarith)]
  have hprod := mul_le_mul h1' h2' (by positivity) hb.le
  have hp : 1024*(m : ℝ)*t^2 ≤ (B : ℝ)^3 := by
    rw [show (32*|t|)*(32*|t| * (m : ℝ)) = 1024*(m : ℝ)*t^2 by rw [← sq_abs]; ring] at hprod
    nlinarith
  nlinarith [pow_nonneg hb.le 3]
theorem complement_exponent_bound (m B : ℕ) (p a t : ℝ) (hB : 0 < B)
    (hp : 0 ≤ p) (ha : 0 ≤ a) (ha2 : a ≤ 2*p)
    (hchi : 2*|t|/(B : ℝ) ≤ 1/2)
    (hcount : |2*t*(m : ℝ)| * (2/(B : ℝ)^2) ≤ 1/2) :
    2*((m : ℝ)*t^2/(1-2*|t|/(B : ℝ)))*(a/B)^2+
      (2*t*(m : ℝ))^2*(16*p/(B : ℝ)^3)/(2*(1-|2*t*(m : ℝ)| * (2/(B : ℝ)^2)))+
      64*Real.exp (1/2)*p*((m : ℝ)*t^2/(1-2*|t|/(B : ℝ)))/(B : ℝ)^3 ≤
      256*Real.exp (1/2)*((m : ℝ)*p^2/(B : ℝ)^2+(m : ℝ)^2*p/(B : ℝ)^3)*t^2 := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hd : 0 < 1-2*|t|/(B : ℝ) := by linarith
  have hK : (m : ℝ)*t^2/(1-2*|t|/(B : ℝ)) ≤ 2*(m : ℝ)*t^2 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0 ≤ (m : ℝ)*t^2 by positivity)
      (show 0 ≤ 1/2-2*|t|/(B : ℝ) by linarith)]
  have hD : (a/(B : ℝ))^2 ≤ 4*p^2/(B : ℝ)^2 := by
    rw [div_pow]
    apply div_le_div_of_nonneg_right _ (sq_nonneg (B : ℝ))
    nlinarith
  have hfirst := mul_le_mul hK hD (sq_nonneg (a/(B : ℝ))) (by positivity : 0 ≤ 2*(m : ℝ)*t^2)
  have hfirst' : 2*((m : ℝ)*t^2/(1-2*|t|/(B : ℝ)))*(a/B)^2 ≤
      16*((m : ℝ)*p^2/(B : ℝ)^2)*t^2 := by
    convert mul_le_mul_of_nonneg_left hfirst (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  have hcountden : 1 ≤ 2*(1-|2*t*(m : ℝ)| * (2/(B : ℝ)^2)) := by linarith
  have hsecond : (2*t*(m : ℝ))^2*(16*p/(B : ℝ)^3)/(2*(1-|2*t*(m : ℝ)| * (2/(B : ℝ)^2))) ≤
      64*((m : ℝ)^2*p/(B : ℝ)^3)*t^2 := by
    have hh := div_le_self (show 0 ≤ (2*t*(m : ℝ))^2*(16*p/(B : ℝ)^3) by positivity) hcountden
    exact hh.trans_eq (by ring)
  have hmsq : (m : ℝ) ≤ (m : ℝ)^2 := by
    by_cases hm : m = 0
    · simp [hm]
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
      nlinarith
  have hthird : 64*Real.exp (1/2)*p*((m : ℝ)*t^2/(1-2*|t|/(B : ℝ)))/(B : ℝ)^3 ≤
      128*Real.exp (1/2)*((m : ℝ)^2*p/(B : ℝ)^3)*t^2 := by
    have h1 := mul_le_mul_of_nonneg_left hK
      (show 0 ≤ 64*Real.exp (1/2)*p/(B : ℝ)^3 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hmsq
      (show 0 ≤ 128*Real.exp (1/2)*p*t^2/(B : ℝ)^3 by positivity)
    have h1' : 64*Real.exp (1/2)*p*((m : ℝ)*t^2/(1-2*|t|/(B : ℝ)))/(B : ℝ)^3 ≤
        128*Real.exp (1/2)*((m : ℝ)*p/(B : ℝ)^3)*t^2 := by
      convert h1 using 1 <;> ring
    have h2' : 128*Real.exp (1/2)*((m : ℝ)*p/(B : ℝ)^3)*t^2 ≤
        128*Real.exp (1/2)*((m : ℝ)^2*p/(B : ℝ)^3)*t^2 := by
      convert h2 using 1 <;> ring
    exact h1'.trans h2'
  have he : 1 ≤ Real.exp (1/2) := Real.one_le_exp_iff.mpr (by norm_num)
  have hv1 : 0 ≤ (m : ℝ)*p^2/(B : ℝ)^2*t^2 := by positivity
  have hv2 : 0 ≤ (m : ℝ)^2*p/(B : ℝ)^3*t^2 := by positivity
  have he1 := mul_le_mul_of_nonneg_right he hv1
  have he2 := mul_le_mul_of_nonneg_right he hv2
  nlinarith

/-- Actual Gaussian-complement MGF in the two source variance orders,
with a single explicit radius proportional to `(1/B+m/B²)⁻¹`. -/
theorem tame_residualGaussianComplement_simple_mgf {k m B : ℕ}
    (H : SparseSGD.External.BernsteinMomentsCertificate (Sample k))
    (J : SparseSGD.External.HoeffdingCertificate (Sample k))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (p : unitInterval) (mu theta : Vec k) (t : ℝ) (hB : 0 < B)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (ht : |t| * complementQuadraticScale m B ≤ 1) :
    Integrable (fun z : Batch k B × (Fin B → NoiseVec m) => Real.exp
      (t*(‖residualGaussianComplement p mu theta z.1 z.2‖^2-(m : ℝ)*coefD0 p mu theta/B)))
      ((batchLaw k B p).prod (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m))) ∧
    (∫ z : Batch k B × (Fin B → NoiseVec m), Real.exp
      (t*(‖residualGaussianComplement p mu theta z.1 z.2‖^2-(m : ℝ)*coefD0 p mu theta/B))
      ∂((batchLaw k B p).prod (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)))) ≤
      Real.exp (256*Real.exp (1/2)*complementQuadraticVariance p m B*t^2) := by
  have hparams := complement_parameter_bounds m B t hB ht
  have hh := tame_residualGaussianComplement_mgf H J G p mu theta t hB hp htame
    (hparams.1.trans_lt (by norm_num)) (hparams.2.1.trans_lt (by norm_num)) hparams.2.2
  refine ⟨hh.1, hh.2.trans ?_⟩
  apply Real.exp_le_exp.mpr
  have hD : 0 ≤ coefD0 p mu theta := by
    rw [← sampleResidualSquare_integral p mu theta]
    exact integral_nonneg (fun a => sampleResidualSquare_nonneg p mu theta a)
  exact complement_exponent_bound m B (p : ℝ) (coefD0 p mu theta) t hB hp.le hD
    (tame_residualSquare_mean_le p mu theta hp htame) hparams.1 hparams.2.1

/-- A standard two-sided Bernstein format for the actual complement. -/
theorem tame_residualGaussianComplement_bernstein_mgf {k m B : ℕ}
    (H : SparseSGD.External.BernsteinMomentsCertificate (Sample k))
    (J : SparseSGD.External.HoeffdingCertificate (Sample k))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (p : unitInterval) (mu theta : Vec k) (t : ℝ) (hB : 0 < B)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (ht : |t| * complementQuadraticScale m B < 1) :
    Integrable (fun z : Batch k B × (Fin B → NoiseVec m) => Real.exp
      (t*(‖residualGaussianComplement p mu theta z.1 z.2‖^2-(m : ℝ)*coefD0 p mu theta/B)))
      ((batchLaw k B p).prod (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m))) ∧
    (∫ z : Batch k B × (Fin B → NoiseVec m), Real.exp
      (t*(‖residualGaussianComplement p mu theta z.1 z.2‖^2-(m : ℝ)*coefD0 p mu theta/B))
      ∂((batchLaw k B p).prod (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)))) ≤
      Real.exp (t^2*(512*Real.exp (1/2)*complementQuadraticVariance p m B)/
        (2*(1-|t| * complementQuadraticScale m B))) := by
  have hh := tame_residualGaussianComplement_simple_mgf H J G p mu theta t hB hp htame ht.le
  refine ⟨hh.1, hh.2.trans ?_⟩
  apply Real.exp_le_exp.mpr
  have hd : 0 < 2*(1-|t| * complementQuadraticScale m B) := by linarith
  have hs : 0 ≤ complementQuadraticScale m B := by dsimp [complementQuadraticScale]; positivity
  have hv : 0 ≤ complementQuadraticVariance p m B := by dsimp [complementQuadraticVariance]; positivity
  have hden : 2*(1-|t| * complementQuadraticScale m B) ≤ 2 := by nlinarith [abs_nonneg t]
  have hdiv := div_le_div_of_nonneg_left
    (show 0 ≤ t^2*(512*Real.exp (1/2)*complementQuadraticVariance p m B) by positivity) hd hden
  exact (show 256*Real.exp (1/2)*complementQuadraticVariance p m B*t^2 =
    t^2*(512*Real.exp (1/2)*complementQuadraticVariance p m B)/2 by ring).le.trans hdiv

end
end SparseSGD.Logistic
