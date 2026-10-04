import SparseSGD.Logistic.IncrementBoundedMGF

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false

/-- Gaussian auxiliary integration turns a global rare MGF remainder into
a rare square exponential bound. All integrability is proved before using
Fubini; the only external input is a scalar Gaussian tilted second moment. -/
theorem square_mgf_of_global_remainder {X : Type*} [MeasurableSpace X]
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ) (hfm : Measurable f)
    (c k A : ℝ) (hc : 0 ≤ c) (hA : 0 ≤ A) (hkA : 2*k*A ≤ 1/4)
    (hint : ∀ s : ℝ, Integrable (fun x => Real.exp (s*f x)) κ)
    (hrem : ∀ s : ℝ, (∫ x, Real.exp (s*f x) ∂κ)-1 ≤ c*s^2*Real.exp (k*s^2)) :
    Integrable (fun x => Real.exp (A*f x^2)) κ ∧
    (∫ x, Real.exp (A*f x^2) ∂κ) ≤ Real.exp (8*c*A) := by
  let F : ℝ × X → ℝ := fun z => Real.exp (Real.sqrt (2*A)*z.1*f z.2)
  have hmF : Measurable F := by
    exact Real.measurable_exp.comp
      ((measurable_const.mul measurable_fst).mul (hfm.comp measurable_snd))
  have hs (x : X) : (∫ z : ℝ, F (z,x) ∂gaussianReal 0 1) = Real.exp (A*f x^2) := by
    have hg := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1))
      (Real.sqrt (2*A)*f x)
    simp only [mgf, zero_mul, NNReal.coe_one, one_mul, zero_add] at hg
    have he (z : ℝ) : F (z,x) = Real.exp ((Real.sqrt (2*A)*f x)*z) := by
      dsimp [F]
      congr 1
      ring
    simp_rw [he]
    rw [hg]
    congr 1
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2*A)]
    ring
  have hbound (z : ℝ) : (∫ x, F (z,x) ∂κ) ≤
      1+(2*c*A)*(z^2*Real.exp (z^2/4)) := by
    have hh := hrem (Real.sqrt (2*A)*z)
    have he : (Real.sqrt (2*A)*z)^2 = 2*A*z^2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2*A)]
    rw [he] at hh
    have hex : Real.exp (k*(2*A*z^2)) ≤ Real.exp (z^2/4) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hkA (sq_nonneg z)
      nlinarith
    have hh' := mul_le_mul_of_nonneg_left hex (show 0 ≤ c*(2*A*z^2) by positivity)
    dsimp [F]
    nlinarith
  have hpair : Integrable F ((gaussianReal 0 1).prod κ) := by
    apply (integrable_prod_iff hmF.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun z => hint (Real.sqrt (2*A)*z)), ?_⟩
    have hmajor := (integrable_const (1 : ℝ)).add (G.tilted_second.1.const_mul (2*c*A))
    apply hmajor.mono' hmF.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards with z
    have he (x : X) : ‖F (z,x)‖ = F (z,x) := by
      simp only [F, Real.norm_eq_abs, Real.abs_exp]
    simp_rw [he]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (integral_nonneg (fun x => (Real.exp_pos _).le))]
    exact hbound z
  have htarget := hpair.integral_prod_right
  simp_rw [hs] at htarget
  refine ⟨htarget, ?_⟩
  have hswap := integral_integral_swap (f := fun z x => F (z,x)) hpair
  simp_rw [hs] at hswap
  rw [← hswap]
  have hh := integral_mono hpair.integral_prod_left
    ((integrable_const (1 : ℝ)).add (G.tilted_second.1.const_mul (2*c*A))) hbound
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) (G.tilted_second.1.const_mul (2*c*A)),
    integral_const_mul] at hh
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
  have hv := mul_le_mul_of_nonneg_left G.tilted_second.2 (show 0 ≤ 2*c*A by positivity)
  exact hh.trans ((by nlinarith : 1+(2*c*A)*(∫ z : ℝ, z^2*Real.exp (z^2/4)
    ∂gaussianReal 0 1) ≤ 1+8*c*A).trans (by simpa [add_comm] using Real.add_one_le_exp (8*c*A)))

/-- Square exponential estimate for an actual bounded iid average, retaining
the small one-sample variance. -/
theorem iid_bounded_square_mgf {X : Type*} [MeasurableSpace X]
    (H : SparseSGD.External.HoeffdingCertificate X)
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 κ) (hm : ∫ x, f x ∂κ = 0) (hb : ∀ x, |f x| ≤ 1)
    (a A : ℝ) (ha : 0 ≤ a) (hA : 0 ≤ A) (hvar : (∫ x, f x^2 ∂κ) ≤ a)
    (B : ℕ) (hB : 0 < B) (hAB : A ≤ (B : ℝ)/8) :
    Integrable (fun z : Fin B → X => Real.exp
      (A*((B : ℝ)⁻¹*∑ i, f (z i))^2)) (Measure.pi (fun _ : Fin B => κ)) ∧
    (∫ z : Fin B → X, Real.exp (A*((B : ℝ)⁻¹*∑ i, f (z i))^2)
      ∂Measure.pi (fun _ : Fin B => κ)) ≤ Real.exp (8*Real.exp (1/2)*a*A/(B : ℝ)) := by
  have hbr : (0 : ℝ) < B := by exact_mod_cast hB
  have hmeas : Measurable (fun z : Fin B → X => (B : ℝ)⁻¹*∑ i, f (z i)) := by
    exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => hfm.comp (measurable_pi_apply i)))
  have hh := square_mgf_of_global_remainder G (Measure.pi (fun _ : Fin B => κ))
    (fun z => (B : ℝ)⁻¹*∑ i, f (z i)) hmeas
    (Real.exp (1/2)*a/(B : ℝ)) (1/(B : ℝ)) A (by positivity) hA
    (by
      have he : 2*(1/(B : ℝ))*A = (2*A)/(B : ℝ) := by ring
      rw [he]
      apply (div_le_iff₀ hbr).mpr
      nlinarith)
    (fun s => (iid_bounded_mgf_remainder H κ f hfm hf hm hb a s ha hvar B hB).1)
    (fun s => by
      have hh := (iid_bounded_mgf_remainder H κ f hfm hf hm hb a s ha hvar B hB).2
      convert hh using 1 <;> congr 1 <;> ring)
  convert hh using 1 <;> congr 1 <;> ring

/-- Actual rare square exponential control for the Gaussian-complement
variance `B⁻² ∑ residual²`. No residual-count concentration is assumed. -/
theorem tame_batchResidualEnergy_square_mgf {d B : ℕ}
    (H : SparseSGD.External.HoeffdingCertificate (Sample d))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (p : unitInterval) (mu theta : Vec d) (A : ℝ) (hB : 0 < B)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (hA : 0 ≤ A) (hAB : A ≤ (B : ℝ)^3/8) :
    Integrable (fun a : Batch d B => Real.exp
      (A*(batchResidualEnergy p mu theta a-coefD0 p mu theta/B)^2)) (batchLaw d B p) ∧
    (∫ a : Batch d B, Real.exp (A*(batchResidualEnergy p mu theta a-coefD0 p mu theta/B)^2)
      ∂batchLaw d B p) ≤ Real.exp (16*Real.exp (1/2)*(p : ℝ)*A/(B : ℝ)^3) := by
  have hbr : (0 : ℝ) < B := by exact_mod_cast hB
  let f : Sample d → ℝ := fun a => sampleResidualSquare p mu theta a-coefD0 p mu theta
  have hfm : Measurable f := (measurable_sampleResidualSquare p mu theta).sub measurable_const
  have hf : MemLp f 2 (sampleLaw d p) := (sampleResidualSquare_memLp_two p mu theta).sub (memLp_const _)
  have hm : ∫ a, f a ∂sampleLaw d p = 0 := by
    rw [integral_sub ((sampleResidualSquare_memLp_two p mu theta).integrable (by norm_num)) (integrable_const _),
      sampleResidualSquare_integral]
    simp
  have hmean0 := residualSquare_mean_nonneg p mu theta
  have hmean1 : coefD0 p mu theta ≤ 1 := by
    rw [← sampleResidualSquare_integral]
    have hh := integral_mono ((sampleResidualSquare_memLp_two p mu theta).integrable (by norm_num))
      (integrable_const (1 : ℝ)) (sampleResidualSquare_le_one p mu theta)
    simpa using hh
  have hb (a : Sample d) : |f a| ≤ 1 := by
    apply abs_le.mpr
    dsimp [f]
    constructor <;> linarith [sampleResidualSquare_nonneg p mu theta a,
      sampleResidualSquare_le_one p mu theta a]
  have hv : (∫ a, f a^2 ∂sampleLaw d p) ≤ 2*(p : ℝ) := by
    have hn := SparseSGD.Probability.LeastSquares.integral_norm_sq_sub_mean
      (sampleResidualSquare p mu theta) (sampleResidualSquare_memLp_two p mu theta)
      (coefD0 p mu theta) (sampleResidualSquare_integral p mu theta)
    simp only [Real.norm_eq_abs, sq_abs] at hn
    dsimp [f]
    linarith [residualSquare_second_moment_le_mean p mu theta,
      tame_residualSquare_mean_le p mu theta hp htame, sq_nonneg (coefD0 p mu theta)]
  have hsmall : A/(B : ℝ)^2 ≤ (B : ℝ)/8 := by
    apply (div_le_iff₀ (sq_pos_of_pos hbr)).mpr
    nlinarith
  have hh := iid_bounded_square_mgf H G (sampleLaw d p) f hfm hf hm hb
    (2*(p : ℝ)) (A/(B : ℝ)^2) (by positivity) (by positivity) hv B hB hsmall
  have he (a : Batch d B) :
      (A/(B : ℝ)^2)*((B : ℝ)⁻¹*∑ i, f (a i))^2 =
        A*(batchResidualEnergy p mu theta a-coefD0 p mu theta/B)^2 := by
    dsimp [f, batchResidualEnergy]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    <;> ring
  simp_rw [he] at hh
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  congr 1
  field_simp
  <;> ring

end
end SparseSGD.Logistic
