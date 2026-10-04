import SparseSGD.Logistic.GaussianStein
import SparseSGD.Probability.MomentReduction

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1200000

private abbrev γ (d : ℕ) := SparseSGD.Probability.standardGaussianProduct d
private abbrev Z {d : ℕ} (z : Fin d → ℝ) : Vec d := WithLp.toLp 2 z

private theorem drift_measurable_logit {d : ℕ} (theta : Vec d) (c : ℝ) :
    Measurable (fun z : Fin d → ℝ => ∑ j, theta j * z j + c) := by fun_prop

private theorem drift_integrable_bounded {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : Measurable f) (C : ℝ) (hb : ∀ z, |f z| ≤ C) : Integrable f (γ d) := by
  apply Integrable.of_bound hf.aestronglyMeasurable C
  exact Filter.Eventually.of_forall (fun z => by simpa [Real.norm_eq_abs] using hb z)

private theorem drift_integrable_weight {d : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : Measurable f) (C : ℝ) (hb : ∀ z, |f z| ≤ C) (hg : Integrable g (γ d)) :
    Integrable (fun z => f z * g z) (γ d) := by
  exact hg.bdd_mul hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by simpa [Real.norm_eq_abs] using hb z))

private theorem drift_sigma_meas {d : ℕ} (theta : Vec d) (c : ℝ) :
    Measurable (fun z : Fin d → ℝ => sigma (∑ j, theta j * z j + c)) :=
  measurable_sigma.comp (drift_measurable_logit theta c)

private theorem drift_sigma_abs (t : ℝ) : |sigma t| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [sigma_pos t, sigma_lt_one t]

private theorem drift_sigmaPrime_integrable {d : ℕ} (theta : Vec d) (c : ℝ) :
    Integrable (fun z : Fin d → ℝ => sigmaPrime (∑ j, theta j * z j + c)) (γ d) := by
  apply drift_integrable_bounded _ 1 (fun z => sigmaPrime_abs_le_one _)
  unfold sigmaPrime
  exact (drift_sigma_meas theta c).mul (measurable_const.sub (drift_sigma_meas theta c))

private theorem drift_gaussianVec_integrable (d : ℕ) : Integrable (@Z d) (γ d) := by
  apply Integrable.of_eval_piLp
  intro i
  exact (SparseSGD.Probability.LeastSquares.gaussian_coord_memLp i 2 (by norm_num)).integrable (by norm_num)

private theorem drift_logit_eq {d : ℕ} (theta : Vec d) (c : ℝ) (z : Fin d → ℝ) :
    inner ℝ theta (Z z) + c = ∑ j, theta j * z j + c := by
  simp [SparseSGD.Probability.LeastSquares.euclidean_inner_eq_sum, Z]

/-- The Gaussian part of the actual class-zero gradient has its Stein mean.
All integrability requirements of the external theorem are discharged. -/
theorem gaussian_logistic_gradient_mean {d : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (theta : Vec d) (c : ℝ) :
    (∫ z, sigma (inner ℝ theta (Z z) + c) • Z z ∂γ d) =
      (∫ z, sigmaPrime (inner ℝ theta (Z z) + c) ∂γ d) • theta := by
  classical
  simp_rw [drift_logit_eq]
  have hg : Integrable (fun z : Fin d → ℝ => sigma (∑ j, theta j * z j + c) • Z z) (γ d) :=
    (drift_gaussianVec_integrable d).bdd_smul 1 (drift_sigma_meas theta c).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by simpa [Real.norm_eq_abs] using drift_sigma_abs _))
  ext i
  rw [eval_integral_piLp (fun j => hg.eval_piLp j)]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [logistic_first_order H (fun j => theta j) c i
    (drift_integrable_weight (drift_sigma_meas theta c) 1 (fun z => drift_sigma_abs _)
      ((SparseSGD.Probability.LeastSquares.gaussian_coord_memLp i 2 (by norm_num)).integrable (by norm_num)))
    (drift_sigmaPrime_integrable theta c)]
  ring

theorem gaussian_positive_gradient_mean {d : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (theta mu : Vec d) (c : ℝ) :
    (∫ z, (sigma (inner ℝ theta (Z z) + c) - 1) • (mu + Z z) ∂γ d) =
      (∫ z, sigmaPrime (inner ℝ theta (Z z) + c) ∂γ d) • theta +
        ((∫ z, sigma (inner ℝ theta (Z z) + c) ∂γ d) - 1) • mu := by
  classical
  simp_rw [drift_logit_eq]
  have hm : Measurable (fun z : Fin d → ℝ => sigma (∑ j, theta j * z j + c) - 1) :=
    (drift_sigma_meas theta c).sub measurable_const
  have hb : ∀ z : Fin d → ℝ, |sigma (∑ j, theta j * z j + c) - 1| ≤ 1 :=
    fun z => by simpa [labelReal] using logistic_residual_abs_le_one (∑ j, theta j * z j + c) true
  have hf := drift_integrable_bounded hm 1 hb
  have hg : Integrable (fun z : Fin d → ℝ => (sigma (∑ j, theta j * z j + c) - 1) • Z z) (γ d) :=
    (drift_gaussianVec_integrable d).bdd_smul 1 hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by simpa [Real.norm_eq_abs] using hb z))
  simp_rw [smul_add]
  rw [integral_add (hf.smul_const mu) hg, integral_smul_const,
    integral_sub (drift_integrable_bounded (drift_sigma_meas theta c) 1 (fun z => drift_sigma_abs _))
      (integrable_const 1)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hz : (∫ z, (sigma (∑ j, theta j * z j + c) - 1) • Z z ∂γ d) =
      (∫ z, sigmaPrime (∑ j, theta j * z j + c) ∂γ d) • theta := by
    ext i
    rw [eval_integral_piLp (fun j => hg.eval_piLp j)]
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [logistic_positive_class_first_order H (fun j => theta j) c i
      (drift_integrable_weight hm 1 hb
        ((SparseSGD.Probability.LeastSquares.gaussian_coord_memLp i 2 (by norm_num)).integrable (by norm_num)))
      (drift_sigmaPrime_integrable theta c)]
    ring
  rw [hz, add_comm]

/-- Actual class-mixed vector mean of a single logistic sample. -/
theorem gradient_integral {d : ℕ} (H : SparseSGD.External.GaussianSteinCertificate d)
    (p : unitInterval) (mu theta : Vec d) :
    (∫ a, gradient p mu theta a ∂sampleLaw d p) =
      coefA p mu theta • theta + coefB p mu theta • mu := by
  have hg := (gradient_memLp_two d p mu theta).integrable (by norm_num)
  rw [sampleLaw, integral_prod _ hg, integral_bernoulliMeasure]
  have h0 := gaussian_logistic_gradient_mean H theta (bias p mu)
  have h1 := gaussian_positive_gradient_mean H theta mu (inner ℝ theta mu + bias p mu)
  have e0 : (fun z : Fin d → ℝ => gradient p mu theta (false, z)) =
      (fun z => sigma (inner ℝ theta (Z z) + bias p mu) • Z z) := by
    funext z; simp [gradient, feature, labelReal, Z]
  have e1 : (fun z : Fin d → ℝ => gradient p mu theta (true, z)) =
      (fun z => (sigma (inner ℝ theta (Z z) + (inner ℝ theta mu + bias p mu)) - 1) • (mu + Z z)) := by
    funext z
    simp only [gradient, feature, labelReal, ↓reduceIte, inner_add_right]
    congr 2
    congr 1
    ring
  rw [e0, e1, h0, h1]
  simp only [classLogit0, classLogit1, coefA, coefB]
  simp only [← add_assoc]
  module

def bulkLinear {d : ℕ} (mu : Vec d) : Vec d →L[ℝ] Vec d :=
  ContinuousLinearMap.id ℝ (Vec d) - (r mu ^ 2)⁻¹ • (innerSL ℝ mu).smulRight mu

theorem bulkLinear_apply {d : ℕ} (mu x : Vec d) : bulkLinear mu x = bulkPart mu x := by
  simp only [bulkLinear, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    bulkPart, signalCoord, smul_smul, div_eq_mul_inv, inv_pow, real_inner_comm mu x]
  module

theorem bulkPart_add {d : ℕ} (mu x y : Vec d) :
    bulkPart mu (x + y) = bulkPart mu x + bulkPart mu y := by
  simp only [← bulkLinear_apply, map_add]

theorem bulkPart_sub {d : ℕ} (mu x y : Vec d) :
    bulkPart mu (x - y) = bulkPart mu x - bulkPart mu y := by
  simp only [← bulkLinear_apply, map_sub]

theorem bulkPart_smul {d : ℕ} (mu x : Vec d) (a : ℝ) :
    bulkPart mu (a • x) = a • bulkPart mu x := by
  simp only [← bulkLinear_apply, map_smul]

theorem bulkPart_self {d : ℕ} (mu : Vec d) : bulkPart mu mu = 0 := by
  by_cases hm : mu = 0
  · simp [hm, bulkPart, signalCoord, r]
  · have hr : r mu ≠ 0 := by simpa [r] using norm_ne_zero_iff.mpr hm
    rw [← bulkLinear_apply]
    simp only [bulkLinear, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      real_inner_self_eq_norm_sq, r]
    simp only [r] at hr
    rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hr), one_smul, sub_self]

theorem bulkPart_norm_sq {d : ℕ} (mu x : Vec d) (hr : 0 < r mu) :
    ‖bulkPart mu x‖ ^ 2 = ‖x‖ ^ 2 - (inner ℝ x mu) ^ 2 / r mu ^ 2 := by
  rw [bulkPart, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right,
    signalCoord, smul_smul, div_eq_mul_inv, inv_pow, r]
  simp only [r] at hr
  field_simp
  <;> ring

private theorem drift_weighted_coord2 {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : Measurable f) (C : ℝ) (hb : ∀ z, |f z| ≤ C) (i j : Fin d) :
    Integrable (fun z => f z * z i * z j) (γ d) := by
  have hij := (SparseSGD.Probability.LeastSquares.gaussian_coord_memLp i 2 (by norm_num)).integrable_mul
    (SparseSGD.Probability.LeastSquares.gaussian_coord_memLp j 2 (by norm_num))
  convert drift_integrable_weight hf C hb hij using 1
  funext z; simp only [Pi.mul_apply]; ring

private theorem drift_weighted_norm_integral {d : ℕ} (theta : Vec d)
    {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) (C : ℝ) (hb : ∀ z, |f z| ≤ C)
    (I0 I2 : ℝ) (hS : ∀ i j : Fin d, (∫ z, f z * z i * z j ∂γ d) =
      (if i = j then I0 else 0) + theta i * theta j * I2) :
    (∫ z, f z * ‖Z z‖ ^ 2 ∂γ d) = d * I0 + ‖theta‖ ^ 2 * I2 := by
  classical
  simp only [SparseSGD.Probability.LeastSquares.euclidean_norm_sq_eq_sum]
  simp_rw [Finset.mul_sum, pow_two, ← mul_assoc]
  rw [integral_finsetSum _ (fun i _ => drift_weighted_coord2 hf C hb i i)]
  simp_rw [hS]
  simp only [ite_true]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.sum_mul]

private theorem drift_weighted_inner_integral {d : ℕ} (theta mu : Vec d)
    {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) (C : ℝ) (hb : ∀ z, |f z| ≤ C)
    (I0 I2 : ℝ) (hS : ∀ i j : Fin d, (∫ z, f z * z i * z j ∂γ d) =
      (if i = j then I0 else 0) + theta i * theta j * I2) :
    (∫ z, f z * (inner ℝ (Z z) mu) ^ 2 ∂γ d) =
      ‖mu‖ ^ 2 * I0 + (inner ℝ theta mu) ^ 2 * I2 := by
  classical
  have he (z : Fin d → ℝ) : f z * (inner ℝ (Z z) mu) ^ 2 =
      ∑ i : Fin d, ∑ j : Fin d, (f z * z i * z j) * (mu i * mu j) := by
    simp only [SparseSGD.Probability.LeastSquares.euclidean_inner_eq_sum, pow_two,
      Z, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (drift_weighted_coord2 hf C hb i j).mul_const (mu i * mu j)))]
  simp_rw [integral_finsetSum _ (fun j _ => (drift_weighted_coord2 hf C hb _ j).mul_const (mu _ * mu j)),
    integral_mul_const, hS, add_mul, Finset.sum_add_distrib]
  have hdiag (i : Fin d) : (∑ j : Fin d, (if i = j then I0 else 0) * (mu i * mu j)) =
      mu i ^ 2 * I0 := by simp [pow_two]; ring
  simp_rw [hdiag]
  simp only [SparseSGD.Probability.LeastSquares.euclidean_norm_sq_eq_sum,
    SparseSGD.Probability.LeastSquares.euclidean_inner_eq_sum, ← Finset.sum_mul]
  congr 1
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem drift_weighted_bulk_integral {d : ℕ} (theta mu : Vec d) (hr : 0 < r mu)
    {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) (C : ℝ) (hb : ∀ z, |f z| ≤ C)
    (I0 I2 : ℝ) (hS : ∀ i j : Fin d, (∫ z, f z * z i * z j ∂γ d) =
      (if i = j then I0 else 0) + theta i * theta j * I2) :
    (∫ z, f z * ‖bulkPart mu (Z z)‖ ^ 2 ∂γ d) =
      (d - 1 : ℝ) * I0 + ‖bulkPart mu theta‖ ^ 2 * I2 := by
  have hn : Integrable (fun z : Fin d → ℝ => f z * ‖Z z‖ ^ 2) (γ d) :=
    drift_integrable_weight hf C hb
      ((SparseSGD.Probability.LeastSquares.gaussian_norm_sq_memLp_two d).integrable (by norm_num))
  have hi : Integrable (fun z : Fin d → ℝ => f z * (inner ℝ (Z z) mu) ^ 2) (γ d) :=
    drift_integrable_weight hf C hb
      ((SparseSGD.Probability.LeastSquares.gaussian_inner_memLp mu 2 (by norm_num)).integrable_sq)
  simp_rw [bulkPart_norm_sq mu _ hr, mul_sub, ← mul_div_assoc]
  rw [integral_sub hn (hi.div_const _), integral_div,
    drift_weighted_norm_integral theta hf C hb I0 I2 hS,
    drift_weighted_inner_integral theta mu hf C hb I0 I2 hS]
  simp only [r] at hr ⊢
  field_simp
  <;> ring

private theorem drift_residual_sq_true (t : ℝ) : (sigma t - 1) ^ 2 = (1 - sigma t) ^ 2 := by ring

private theorem drift_class_bulk_second {d : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (theta mu : Vec d)
    (hr : 0 < r mu) (c : ℝ) (y : Bool) :
    (∫ z : Fin d → ℝ, (sigma (inner ℝ theta (Z z) + c) - labelReal y) ^ 2 *
      ‖bulkPart mu (Z z)‖ ^ 2 ∂γ d) =
      (d - 1 : ℝ) * (∫ z, (sigma (inner ℝ theta (Z z) + c) - labelReal y) ^ 2 ∂γ d) +
      ‖bulkPart mu theta‖ ^ 2 * (∫ z, (if y then oneMinusSigmaSqSecond else sigmaSqSecond)
        (inner ℝ theta (Z z) + c) ∂γ d) := by
  simp_rw [drift_logit_eq]
  have hm : Measurable (fun z : Fin d → ℝ => (sigma (∑ j, theta j * z j + c) - labelReal y) ^ 2) :=
    ((drift_sigma_meas theta c).sub measurable_const).pow_const 2
  have hb : ∀ z : Fin d → ℝ, |(sigma (∑ j, theta j * z j + c) - labelReal y) ^ 2| ≤ 1 := by
    intro z
    rw [abs_pow]
    nlinarith [logistic_residual_abs_le_one (∑ j, theta j * z j + c) y,
      abs_nonneg (sigma (∑ j, theta j * z j + c) - labelReal y)]
  apply drift_weighted_bulk_integral theta mu hr hm 1 hb
  intro i j
  cases y
  · simp only [labelReal, Bool.false_eq_true, ↓reduceIte, sub_zero] at *
    apply logistic_positive_residual_second_order H (fun j => theta j) c i j
      (drift_weighted_coord2 hm 1 hb i j) (drift_integrable_bounded hm 1 hb)
    apply drift_integrable_bounded _ 4 (fun z => sigmaSqSecond_abs_le_four _)
    unfold sigmaSqSecond sigmaSecond sigmaPrime
    have hs := drift_sigma_meas theta c
    fun_prop
  · simp only [labelReal, ↓reduceIte] at *
    simp_rw [drift_residual_sq_true] at hm hb ⊢
    apply logistic_negative_residual_second_order H (fun j => theta j) c i j
      (drift_weighted_coord2 hm 1 hb i j) (drift_integrable_bounded hm 1 hb)
    apply drift_integrable_bounded _ 4 (fun z => oneMinusSigmaSqSecond_abs_le_four _)
    unfold oneMinusSigmaSqSecond sigmaSecond sigmaPrime
    have hs := drift_sigma_meas theta c
    fun_prop

theorem bulkGradient_memLp_two {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    MemLp (fun a => bulkPart mu (gradient p mu theta a)) 2 (sampleLaw d p) := by
  simpa only [Function.comp_def, bulkLinear_apply] using
    (bulkLinear mu).comp_memLp' (gradient_memLp_two d p mu theta)

theorem bulkGradient_integral {d : ℕ} (H : SparseSGD.External.GaussianSteinCertificate d)
    (p : unitInterval) (mu theta : Vec d) :
    (∫ a, bulkPart mu (gradient p mu theta a) ∂sampleLaw d p) =
      coefA p mu theta • bulkPart mu theta := by
  simp only [← bulkLinear_apply]
  rw [(bulkLinear mu).integral_comp_comm ((gradient_memLp_two d p mu theta).integrable (by norm_num)),
    gradient_integral H, map_add, map_smul, map_smul, bulkLinear_apply mu mu,
    bulkPart_self, smul_zero, add_zero]

/-- The actual projected single-sample second moment, including both classes. -/
theorem bulkGradient_norm_sq_integral {d : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d)
    (p : unitInterval) (mu theta : Vec d) (hr : 0 < r mu) :
    (∫ a, ‖bulkPart mu (gradient p mu theta a)‖ ^ 2 ∂sampleLaw d p) =
      (d - 1 : ℝ) * coefD0 p mu theta + ‖bulkPart mu theta‖ ^ 2 * coefDtheta p mu theta := by
  have hg := bulkGradient_memLp_two p mu theta
  have hsq := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  rw [sampleLaw, integral_prod _ hsq, integral_bernoulliMeasure]
  have h0 := drift_class_bulk_second H theta mu hr (bias p mu) false
  have h1 := drift_class_bulk_second H theta mu hr (inner ℝ theta mu + bias p mu) true
  have e0 (z : Fin d → ℝ) : ‖bulkPart mu (gradient p mu theta (false, z))‖ ^ 2 =
      (sigma (inner ℝ theta (Z z) + bias p mu) - labelReal false) ^ 2 * ‖bulkPart mu (Z z)‖ ^ 2 := by
    simp [gradient, feature, labelReal, Z, bulkPart_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have e1 (z : Fin d → ℝ) : ‖bulkPart mu (gradient p mu theta (true, z))‖ ^ 2 =
      (sigma (inner ℝ theta (Z z) + (inner ℝ theta mu + bias p mu)) - labelReal true) ^ 2 *
        ‖bulkPart mu (Z z)‖ ^ 2 := by
    simp only [gradient, feature, labelReal, ↓reduceIte, inner_add_right, bulkPart_smul,
      bulkPart_add, bulkPart_self, zero_add, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    congr 2
    congr 1
    congr 1
    ring
  simp_rw [e0, e1]
  rw [h0, h1]
  simp only [labelReal, Bool.false_eq_true, ↓reduceIte, sub_zero, coefD0, coefDtheta,
    classLogit0, classLogit1, drift_residual_sq_true, ← add_assoc, smul_eq_mul]
  ring

private theorem drift_iid_mean {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {κ : Measure X} [IsProbabilityMeasure κ] {B : ℕ} (hB : 0 < B)
    (f : X → E) (hf : Integrable f κ) :
    (∫ a : Fin B → X, (B : ℝ)⁻¹ • ∑ i, f (a i) ∂Measure.pi (fun _ : Fin B => κ)) =
      ∫ x, f x ∂κ := by
  classical
  have hcomp (i : Fin B) : Integrable (fun a : Fin B → X => f (a i))
      (Measure.pi (fun _ : Fin B => κ)) :=
    (measurePreserving_eval (fun _ : Fin B => κ) i).integrable_comp_of_integrable hf
  rw [integral_smul, integral_finsetSum _ (fun i _ => hcomp i)]
  have hcoord (i : Fin B) : (∫ a : Fin B → X, f (a i) ∂Measure.pi (fun _ : Fin B => κ)) =
      ∫ x, f x ∂κ := integral_comp_eval (μ := fun _ : Fin B => κ) (i := i) hf.aestronglyMeasurable
  simp_rw [hcoord]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hB), one_smul]

theorem batchGradient_integral {d B : ℕ} (H : SparseSGD.External.GaussianSteinCertificate d)
    (hB : 0 < B) (p : unitInterval) (mu theta : Vec d) :
    (∫ a, batchGradient p mu theta a ∂batchLaw d B p) =
      coefA p mu theta • theta + coefB p mu theta • mu := by
  change (∫ a : Batch d B, (B : ℝ)⁻¹ • ∑ i, gradient p mu theta (a i)
    ∂Measure.pi (fun _ : Fin B => sampleLaw d p)) = _
  rw [drift_iid_mean hB _
    ((gradient_memLp_two d p mu theta).integrable (by norm_num)), gradient_integral H]

theorem bulkBatchGradient_memLp_two {d B : ℕ} (p : unitInterval) (mu theta : Vec d) :
    MemLp (fun a : Batch d B => bulkPart mu (batchGradient p mu theta a)) 2 (batchLaw d B p) := by
  simpa only [Function.comp_def, bulkLinear_apply, batchLaw] using
    (bulkLinear mu).comp_memLp' (batchGradient_memLp_two d B p mu theta)

theorem bulkBatchGradient_integral {d B : ℕ} (H : SparseSGD.External.GaussianSteinCertificate d)
    (hB : 0 < B) (p : unitInterval) (mu theta : Vec d) :
    (∫ a : Batch d B, bulkPart mu (batchGradient p mu theta a) ∂batchLaw d B p) =
      coefA p mu theta • bulkPart mu theta := by
  simp only [← bulkLinear_apply]
  have hg : Integrable (fun a : Batch d B => batchGradient p mu theta a) (batchLaw d B p) :=
    (batchGradient_memLp_two d B p mu theta).integrable (by norm_num)
  rw [(bulkLinear mu).integral_comp_comm
    hg,
    batchGradient_integral H hB, map_add, map_smul, map_smul, bulkLinear_apply mu mu,
    bulkPart_self, smul_zero, add_zero]

def bulkResidual {d B : ℕ} (p : unitInterval) (mu theta : Vec d) (a : Batch d B) : Vec d :=
  bulkPart mu (batchGradient p mu theta a) - coefA p mu theta • bulkPart mu theta

theorem bulkResidual_memLp_two {d B : ℕ} (p : unitInterval) (mu theta : Vec d) :
    MemLp (bulkResidual (B := B) p mu theta) 2 (batchLaw d B p) :=
  (bulkBatchGradient_memLp_two p mu theta).sub (memLp_const _)

theorem bulkResidual_integral {d B : ℕ} (H : SparseSGD.External.GaussianSteinCertificate d)
    (hB : 0 < B) (p : unitInterval) (mu theta : Vec d) :
    (∫ a, bulkResidual (B := B) p mu theta a ∂batchLaw d B p) = 0 := by
  change (∫ a : Batch d B, bulkPart mu (batchGradient p mu theta a) -
    coefA p mu theta • bulkPart mu theta ∂batchLaw d B p) = 0
  rw [integral_sub
    ((bulkBatchGradient_memLp_two p mu theta).integrable (by norm_num)) (integrable_const _),
    bulkBatchGradient_integral H hB]
  simp

/-- Exact variance of the actual projected iid minibatch residual. -/
theorem bulkResidual_norm_sq_integral {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (p : unitInterval) (mu theta : Vec d) (hr : 0 < r mu) :
    (∫ a, ‖bulkResidual (B := B) p mu theta a‖ ^ 2 ∂batchLaw d B p) =
      (coefDtheta p mu theta - coefA p mu theta ^ 2) / B * ‖bulkPart mu theta‖ ^ 2 +
        (d - 1 : ℝ) * coefD0 p mu theta / B := by
  classical
  let f : Sample d → Vec d := fun a => bulkPart mu (gradient p mu theta a) -
    coefA p mu theta • bulkPart mu theta
  have hf : MemLp f 2 (sampleLaw d p) := (bulkGradient_memLp_two p mu theta).sub (memLp_const _)
  have hmean : ∫ a, f a ∂sampleLaw d p = 0 := by
    rw [integral_sub ((bulkGradient_memLp_two p mu theta).integrable (by norm_num))
      (integrable_const _), bulkGradient_integral H]
    simp
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have he (a : Batch d B) : (B : ℝ)⁻¹ • ∑ i, f (a i) = bulkResidual p mu theta a := by
    simp only [f, bulkResidual, batchGradient, ← bulkLinear_apply, map_smul, map_sum,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul]
    rw [← mul_assoc, inv_mul_cancel₀ hb, one_mul]
  have hvar := SparseSGD.Probability.LeastSquares.iid_batch_average_variance hB f hf hmean
  simp_rw [he] at hvar
  rw [SparseSGD.Probability.LeastSquares.integral_norm_sq_sub_mean
    _ (bulkGradient_memLp_two p mu theta) _ (bulkGradient_integral H p mu theta),
    bulkGradient_norm_sq_integral H p mu theta hr] at hvar
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hvar
  rw [show (batchLaw d B p) = Measure.pi (fun _ : Fin B => sampleLaw d p) from rfl, hvar]
  ring

theorem bulkBatchGradient_norm_sq_integral {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (p : unitInterval) (mu theta : Vec d) (hr : 0 < r mu) :
    (∫ a : Batch d B, ‖bulkPart mu (batchGradient p mu theta a)‖ ^ 2 ∂batchLaw d B p) =
      ((d - 1 : ℝ) * coefD0 p mu theta + ‖bulkPart mu theta‖ ^ 2 * coefDtheta p mu theta) / B +
        ((B : ℝ) - 1) / B * coefA p mu theta ^ 2 * ‖bulkPart mu theta‖ ^ 2 := by
  have hcenter := SparseSGD.Probability.LeastSquares.integral_norm_sq_sub_mean
    _ (bulkBatchGradient_memLp_two (B := B) p mu theta) _ (bulkBatchGradient_integral H hB p mu theta)
  change (∫ a, ‖bulkResidual p mu theta a‖ ^ 2 ∂batchLaw d B p) = _ at hcenter
  rw [bulkResidual_norm_sq_integral H hB p mu theta hr] at hcenter
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hcenter
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hsol := (sub_eq_iff_eq_add).mp hcenter.symm
  rw [hsol]
  field_simp
  <;> ring

private theorem drift_signal_integral {X : Type*} [MeasurableSpace X] {κ : Measure X}
    {d : ℕ} (mu : Vec d) (f : X → Vec d) (hf : Integrable f κ) :
    (∫ a, signalCoord mu (f a) ∂κ) = signalCoord mu (∫ a, f a ∂κ) := by
  simp only [signalCoord]
  simp_rw [real_inner_comm]
  rw [integral_div, integral_inner hf]

theorem update_momentum_memLp_two {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) :
    MemLp (fun a : Batch d B => (update eta beta p mu s a).2) 2 (batchLaw d B p) := by
  exact (memLp_const (beta • s.2)).add
    ((batchGradient_memLp_two d B p mu s.1).const_smul (1 - beta))

theorem update_parameter_memLp_two {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) :
    MemLp (fun a : Batch d B => (update eta beta p mu s a).1) 2 (batchLaw d B p) :=
  (memLp_const s.1).sub ((update_momentum_memLp_two eta beta p mu s).const_smul eta)

theorem update_momentum_integral {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d) :
    (∫ a : Batch d B, (update eta beta p mu s a).2 ∂batchLaw d B p) =
      beta • s.2 + (1 - beta) • (coefA p mu s.1 • s.1 + coefB p mu s.1 • mu) := by
  have hg : Integrable (fun a : Batch d B => batchGradient p mu s.1 a) (batchLaw d B p) :=
    (batchGradient_memLp_two d B p mu s.1).integrable (by norm_num)
  change (∫ a : Batch d B, beta • s.2 + (1 - beta) • batchGradient p mu s.1 a ∂batchLaw d B p) = _
  rw [integral_add (f := fun _ : Batch d B => beta • s.2)
    (g := fun a : Batch d B => (1 - beta) • batchGradient p mu s.1 a)
    (integrable_const _) (hg.smul (1 - beta))]
  simp only [integral_const, probReal_univ, one_smul]
  rw [integral_smul, batchGradient_integral H hB]

theorem update_parameter_integral {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d) :
    (∫ a : Batch d B, (update eta beta p mu s a).1 ∂batchLaw d B p) =
      s.1 - eta • (beta • s.2 + (1 - beta) • (coefA p mu s.1 • s.1 + coefB p mu s.1 • mu)) := by
  change (∫ a : Batch d B, s.1 - eta • (update eta beta p mu s a).2 ∂batchLaw d B p) = _
  rw [integral_sub (f := fun _ : Batch d B => s.1)
    (g := fun a : Batch d B => eta • (update eta beta p mu s a).2) (integrable_const _)
    (((update_momentum_memLp_two (B := B) eta beta p mu s).integrable (by norm_num)).smul eta),
    integral_smul, update_momentum_integral H hB]
  simp

private theorem drift_signal_self {d : ℕ} (mu : Vec d) (hr : 0 < r mu) :
    signalCoord mu mu = r mu := by
  simp only [signalCoord, real_inner_self_eq_norm_sq, r] at hr ⊢
  field_simp

/-- Exact one-step mean signal momentum under the actual fresh batch law. -/
theorem update_signal_momentum_integral {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d) (hr : 0 < r mu) :
    (∫ a : Batch d B, signalCoord mu (update eta beta p mu s a).2 ∂batchLaw d B p) =
      beta * signalCoord mu s.2 + (1 - beta) *
        (coefA p mu s.1 * signalCoord mu s.1 + coefB p mu s.1 * r mu) := by
  rw [drift_signal_integral mu _
    ((update_momentum_memLp_two eta beta p mu s).integrable (by norm_num)),
    update_momentum_integral H hB]
  have hs := drift_signal_self mu hr
  simp only [signalCoord, inner_add_left, real_inner_smul_left] at hs ⊢
  field_simp [ne_of_gt hr] at hs ⊢
  rw [hs] <;> ring

/-- Exact one-step mean signal parameter under the actual fresh batch law. -/
theorem update_signal_parameter_integral {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d) (hr : 0 < r mu) :
    (∫ a : Batch d B, signalCoord mu (update eta beta p mu s a).1 ∂batchLaw d B p) =
      signalCoord mu s.1 - eta * (beta * signalCoord mu s.2 + (1 - beta) *
        (coefA p mu s.1 * signalCoord mu s.1 + coefB p mu s.1 * r mu)) := by
  rw [drift_signal_integral mu _
    ((update_parameter_memLp_two eta beta p mu s).integrable (by norm_num)),
    update_parameter_integral H hB]
  have hs := drift_signal_self mu hr
  simp only [signalCoord, inner_sub_left, inner_add_left, real_inner_smul_left] at hs ⊢
  field_simp [ne_of_gt hr] at hs ⊢
  rw [hs] <;> ring

def integratedGram {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (κ : Measure X) (f g : X → E) : SparseSGD.Moments :=
  ⟨∫ a, ‖f a‖ ^ 2 ∂κ, ∫ a, ‖g a‖ ^ 2 ∂κ, ∫ a, inner ℝ (f a) (g a) ∂κ⟩

private theorem drift_toLp_gram {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {κ : Measure X}
    (f g : X → E) (hf : MemLp f 2 κ) (hg : MemLp g 2 κ) :
    SparseSGD.gramMoments (hf.toLp f) (hg.toLp g) = integratedGram κ f g := by
  apply SparseSGD.Moments.ext
  · change ‖hf.toLp f‖ ^ 2 = ∫ a, ‖f a‖ ^ 2 ∂κ
    rw [SparseSGD.l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with a ha
    rw [ha]
  · change ‖hg.toLp g‖ ^ 2 = ∫ a, ‖g a‖ ^ 2 ∂κ
    rw [SparseSGD.l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with a ha
    rw [ha]
  · change inner ℝ (hf.toLp f) (hg.toLp g) = ∫ a, inner ℝ (f a) (g a) ∂κ
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with a ha hb
    rw [ha, hb]

private theorem drift_integrated_gram_step {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {κ : Measure X} [IsProbabilityMeasure κ] (P : SparseSGD.Params)
    (e q : E) (ξ : X → E) (hξ : MemLp ξ 2 κ) (hmean : ∫ a, ξ a ∂κ = 0)
    (c : ℝ) (hscale : c ^ 2 * (∫ a, ‖ξ a‖ ^ 2 ∂κ) =
      2 * P.w * P.eps * (P.noise * ‖e‖ ^ 2 + P.additive)) :
    integratedGram κ (fun a => (1 - P.w) • e - P.beta • q - c • ξ a)
      (fun a => P.w • e + P.beta • q + c • ξ a) = P.step (SparseSGD.gramMoments e q) := by
  let he : MemLp (fun _ : X => e) 2 κ := memLp_const e
  let hq : MemLp (fun _ : X => q) 2 κ := memLp_const q
  let eL := he.toLp (fun _ => e)
  let qL := hq.toLp (fun _ => q)
  let ξL := hξ.toLp ξ
  have hconst : SparseSGD.gramMoments eL qL = SparseSGD.gramMoments e q := by
    rw [drift_toLp_gram _ _ he hq]
    simp [integratedGram, SparseSGD.gramMoments]
  have hξnorm : ‖ξL‖ ^ 2 = ∫ a, ‖ξ a‖ ^ 2 ∂κ := by
    rw [SparseSGD.l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [hξ.coeFn_toLp] with a ha
    rw [ha]
  have horth (v : E) (hv : MemLp (fun _ : X => v) 2 κ) :
      inner ℝ (hv.toLp (fun _ => v)) ξL = 0 := by
    rw [L2.inner_def]
    calc
      _ = ∫ a, inner ℝ v (ξ a) ∂κ := by
        apply integral_congr_ae
        filter_upwards [hv.coeFn_toLp, hξ.coeFn_toLp] with a ha hb
        rw [ha, hb]
      _ = 0 := by rw [integral_inner (hξ.integrable (by norm_num)), hmean]; simp
  have hstep := SparseSGD.gramMoments_step P eL qL ξL c (horth e he) (horth q hq)
    (by
      have heNorm := congrArg SparseSGD.Moments.R hconst
      change ‖eL‖ ^ 2 = ‖e‖ ^ 2 at heNorm
      rw [hξnorm, heNorm]
      exact hscale)
  have hf := ((he.const_smul (1 - P.w)).sub (hq.const_smul P.beta)).sub (hξ.const_smul c)
  have hg := ((he.const_smul P.w).add (hq.const_smul P.beta)).add (hξ.const_smul c)
  have hfe : hf.toLp (fun a => (1 - P.w) • e - P.beta • q - c • ξ a) =
      (1 - P.w) • eL - P.beta • qL - c • ξL := rfl
  have hge : hg.toLp (fun a => P.w • e + P.beta • q + c • ξ a) =
      P.w • eL + P.beta • qL + c • ξL := rfl
  rw [← hfe, ← hge, hconst] at hstep
  exact (drift_toLp_gram (fun a => (1 - P.w) • e - P.beta • q - c • ξ a)
    (fun a => P.w • e + P.beta • q + c • ξ a) hf hg).symm.trans hstep

def driftParams {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu theta : Vec d) : SparseSGD.Params :=
  SparseSGD.oracleParams beta eta (coefA p mu theta)
    ((coefDtheta p mu theta - coefA p mu theta ^ 2) / B)
    ((d - 1 : ℝ) * coefD0 p mu theta / B)

/-- The one-step bulk drift is precisely the manuscript's moment recursion,
with parameters computed from the actual logistic sample distribution. The
momentum coordinate is scaled by `eta`, as in the manuscript's covariance. -/
theorem update_bulk_integratedGram {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d)
    (hr : 0 < r mu) (hA : coefA p mu s.1 ≠ 0) :
    integratedGram (batchLaw d B p)
      (fun a => bulkPart mu (update eta beta p mu s a).1)
      (fun a => eta • bulkPart mu (update eta beta p mu s a).2) =
    (driftParams (B := B) eta beta p mu s.1).step
      (SparseSGD.gramMoments (bulkPart mu s.1) (eta • bulkPart mu s.2)) := by
  let P := driftParams (B := B) eta beta p mu s.1
  have hscale : (eta * (1 - beta)) ^ 2 *
      (∫ a, ‖bulkResidual (B := B) p mu s.1 a‖ ^ 2 ∂batchLaw d B p) =
      2 * P.w * P.eps * (P.noise * ‖bulkPart mu s.1‖ ^ 2 + P.additive) := by
    rw [bulkResidual_norm_sq_integral H hB p mu s.1 hr]
    exact SparseSGD.oracleParams_scale beta eta (coefA p mu s.1) _ _ _ hA
  have hstep := drift_integrated_gram_step P (bulkPart mu s.1) (eta • bulkPart mu s.2)
    (bulkResidual p mu s.1) (bulkResidual_memLp_two p mu s.1)
    (bulkResidual_integral H hB p mu s.1) (eta * (1 - beta)) hscale
  have he (a : Batch d B) : bulkPart mu (update eta beta p mu s a).1 =
      (1 - P.w) • bulkPart mu s.1 - P.beta • (eta • bulkPart mu s.2) -
        (eta * (1 - beta)) • bulkResidual p mu s.1 a := by
    simp only [update, bulkPart_sub, bulkPart_add, bulkPart_smul, bulkResidual, P,
      driftParams, SparseSGD.oracleParams]
    module
  have hq (a : Batch d B) : eta • bulkPart mu (update eta beta p mu s a).2 =
      P.w • bulkPart mu s.1 + P.beta • (eta • bulkPart mu s.2) +
        (eta * (1 - beta)) • bulkResidual p mu s.1 a := by
    simp only [update, bulkPart_sub, bulkPart_add, bulkPart_smul, bulkResidual, P,
      driftParams, SparseSGD.oracleParams]
    module
  simp_rw [he, hq]
  exact hstep

theorem driftParams_explicit {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu theta : Vec d) :
    driftParams (B := B) eta beta p mu theta =
      ⟨beta, eta * (1 - beta) * coefA p mu theta,
        eta * (coefDtheta p mu theta - coefA p mu theta ^ 2) /
          (2 * (B : ℝ) * coefA p mu theta),
        eta * (d - 1 : ℝ) * coefD0 p mu theta /
          (2 * (B : ℝ) * coefA p mu theta)⟩ := by
  simp only [driftParams, SparseSGD.oracleParams]
  congr 1 <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring

theorem update_bulk_parameter_memLp_two {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) :
    MemLp (fun a : Batch d B => bulkPart mu (update eta beta p mu s a).1) 2 (batchLaw d B p) := by
  simpa only [Function.comp_def, bulkLinear_apply] using
    (bulkLinear mu).comp_memLp' (update_parameter_memLp_two eta beta p mu s)

theorem update_bulk_momentum_memLp_two {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) :
    MemLp (fun a : Batch d B => bulkPart mu (update eta beta p mu s a).2) 2 (batchLaw d B p) := by
  simpa only [Function.comp_def, bulkLinear_apply] using
    (bulkLinear mu).comp_memLp' (update_momentum_memLp_two eta beta p mu s)

/-- The bulk drift in the paper's `(R, eta² V, eta C)` coordinates.
The nonzero curvature required by normalization follows from `0 < p < 1`. -/
theorem update_bulk_moment_drift {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d)
    (hr : 0 < r mu) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (⟨∫ a : Batch d B, ‖bulkPart mu (update eta beta p mu s a).1‖ ^ 2 ∂batchLaw d B p,
      eta ^ 2 * ∫ a : Batch d B, ‖bulkPart mu (update eta beta p mu s a).2‖ ^ 2 ∂batchLaw d B p,
      eta * ∫ a : Batch d B, inner ℝ (bulkPart mu (update eta beta p mu s a).1)
        (bulkPart mu (update eta beta p mu s a).2) ∂batchLaw d B p⟩ : SparseSGD.Moments) =
    (driftParams (B := B) eta beta p mu s.1).step
      ⟨‖bulkPart mu s.1‖ ^ 2, eta ^ 2 * ‖bulkPart mu s.2‖ ^ 2,
        eta * inner ℝ (bulkPart mu s.1) (bulkPart mu s.2)⟩ := by
  have h := update_bulk_integratedGram H hB eta beta p mu s hr
    (ne_of_gt (coefA_pos p mu s.1 hp0 hp1))
  simpa only [integratedGram, SparseSGD.gramMoments, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_right, integral_const_mul] using h

/-- Exact fresh-batch transition drift in all five source coordinates.
This is a distribution-specific statement; no gradient moment formula is
assumed. Gaussian Stein is the only cited external certificate. -/
theorem one_step_drift {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d)
    (hr : 0 < r mu) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (∫ a : Batch d B, signalCoord mu (update eta beta p mu s a).2 ∂batchLaw d B p) =
      beta * signalCoord mu s.2 + (1 - beta) *
        (coefA p mu s.1 * signalCoord mu s.1 + coefB p mu s.1 * r mu) ∧
    (∫ a : Batch d B, signalCoord mu (update eta beta p mu s a).1 ∂batchLaw d B p) =
      signalCoord mu s.1 - eta * (beta * signalCoord mu s.2 + (1 - beta) *
        (coefA p mu s.1 * signalCoord mu s.1 + coefB p mu s.1 * r mu)) ∧
    integratedGram (batchLaw d B p)
      (fun a => bulkPart mu (update eta beta p mu s a).1)
      (fun a => eta • bulkPart mu (update eta beta p mu s a).2) =
      (driftParams (B := B) eta beta p mu s.1).step
        (SparseSGD.gramMoments (bulkPart mu s.1) (eta • bulkPart mu s.2)) := by
  exact ⟨update_signal_momentum_integral H hB eta beta p mu s hr,
    update_signal_parameter_integral H hB eta beta p mu s hr,
    update_bulk_integratedGram H hB eta beta p mu s hr (ne_of_gt (coefA_pos p mu s.1 hp0 hp1))⟩

end
end SparseSGD.Logistic
