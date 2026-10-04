import SparseSGD.Logistic.IncrementLinearMGF

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false

def sampleResidualSquare {d : ℕ} (p : unitInterval) (mu theta : Vec d) (a : Sample d) : ℝ :=
  (sigma (inner ℝ theta (feature mu a)+bias p mu)-labelReal a.1)^2

theorem sampleResidualSquare_nonneg {d : ℕ} (p : unitInterval) (mu theta : Vec d) (a : Sample d) :
    0 ≤ sampleResidualSquare p mu theta a := sq_nonneg _

theorem sampleResidualSquare_le_one {d : ℕ} (p : unitInterval) (mu theta : Vec d) (a : Sample d) :
    sampleResidualSquare p mu theta a ≤ 1 := by
  have hh := logistic_residual_abs_le_one (inner ℝ theta (feature mu a)+bias p mu) a.1
  unfold sampleResidualSquare
  nlinarith [sq_abs (sigma (inner ℝ theta (feature mu a)+bias p mu)-labelReal a.1),
    abs_nonneg (sigma (inner ℝ theta (feature mu a)+bias p mu)-labelReal a.1)]

theorem measurable_sampleResidualSquare {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    Measurable (sampleResidualSquare p mu theta) := by
  have hf := measurable_feature d mu
  have hs : Measurable (fun a : Sample d => sigma (inner ℝ theta (feature mu a)+bias p mu)) :=
    measurable_sigma.comp ((measurable_const.inner hf).add measurable_const)
  exact (hs.sub (measurable_labelReal.comp measurable_fst)).pow_const 2

theorem sampleResidualSquare_memLp_two {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    MemLp (sampleResidualSquare p mu theta) 2 (sampleLaw d p) := by
  apply MemLp.of_bound (measurable_sampleResidualSquare p mu theta).aestronglyMeasurable 1
  filter_upwards with a
  rw [Real.norm_eq_abs, abs_of_nonneg (sampleResidualSquare_nonneg p mu theta a)]
  exact sampleResidualSquare_le_one p mu theta a

theorem sampleResidualSquare_integral {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    (∫ a, sampleResidualSquare p mu theta a ∂sampleLaw d p) = coefD0 p mu theta := by
  rw [sampleLaw, integral_prod _ ((sampleResidualSquare_memLp_two p mu theta).integrable (by norm_num)),
    integral_bernoulliMeasure]
  simp only [sampleResidualSquare, feature, labelReal, ↓reduceIte, Bool.false_eq_true,
    zero_add, sub_zero, coefD0, classLogit0, classLogit1, inner_add_right, smul_eq_mul]
  have he (z : Fin d → ℝ) :
      (sigma (inner ℝ theta mu+inner ℝ theta (WithLp.toLp 2 z)+bias p mu)-1)^2 =
      (1-sigma (inner ℝ theta (WithLp.toLp 2 z)+inner ℝ theta mu+bias p mu))^2 := by
    rw [add_comm (inner ℝ theta mu)]
    ring
  simp_rw [he]
  ring

theorem residualSquare_mean_nonneg {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    0 ≤ coefD0 p mu theta := by
  rw [← sampleResidualSquare_integral]
  exact integral_nonneg (sampleResidualSquare_nonneg p mu theta)

theorem residualSquare_second_moment_le_mean {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    (∫ a, (sampleResidualSquare p mu theta a)^2 ∂sampleLaw d p) ≤ coefD0 p mu theta := by
  rw [← sampleResidualSquare_integral]
  apply integral_mono (sampleResidualSquare_memLp_two p mu theta).integrable_sq
    ((sampleResidualSquare_memLp_two p mu theta).integrable (by norm_num))
  intro a
  have h0 := sampleResidualSquare_nonneg p mu theta a
  have h1 := sampleResidualSquare_le_one p mu theta a
  nlinarith

/-- The rare mean bound needed for the Gaussian complement, with a numerical
constant. It follows directly from the class-zero exponential majorant. -/
theorem tame_residualSquare_mean_le {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2) :
    coefD0 p mu theta ≤ 2*(p : ℝ) := by
  have h0 := gaussian_sigma_sq_integral_bound theta (bias p mu)
  have h1 : (∫ z : Fin d → ℝ, (1-sigma (classLogit1 p mu theta z))^2
      ∂SparseSGD.Probability.standardGaussianProduct d) ≤ 1 := by
    have hm : Measurable (fun z : Fin d → ℝ => (1-sigma (classLogit1 p mu theta z))^2) := by
      unfold classLogit1
      exact (measurable_const.sub (measurable_sigma.comp (by fun_prop))).pow_const 2
    have hb (z : Fin d → ℝ) : (1-sigma (classLogit1 p mu theta z))^2 ≤ 1 := by
      nlinarith [sigma_pos (classLogit1 p mu theta z), sigma_lt_one (classLogit1 p mu theta z)]
    have hi : Integrable (fun z : Fin d → ℝ => (1-sigma (classLogit1 p mu theta z))^2)
        (SparseSGD.Probability.standardGaussianProduct d) := by
      apply Integrable.of_bound hm.aestronglyMeasurable 1
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb z
    have hh := integral_mono hi (integrable_const (1 : ℝ)) hb
    simpa using hh
  have ht := (tame_exponential_controls p mu theta hp htame).1
  have h0' := mul_le_mul_of_nonneg_left ((le_abs_self _).trans h0.2) (sub_nonneg.mpr p.property.2)
  have h1' := mul_le_mul_of_nonneg_left h1 hp.le
  unfold coefD0 classLogit0
  nlinarith

/-- The conditional variance of the Gaussian complement is this residual
energy, rather than the residual count divided by `B`. -/
def batchResidualEnergy {d B : ℕ} (p : unitInterval) (mu theta : Vec d) (a : Batch d B) : ℝ :=
  ((B : ℝ)^2)⁻¹ * ∑ i, sampleResidualSquare p mu theta (a i)

theorem batchResidualEnergy_nonneg {d B : ℕ} (p : unitInterval) (mu theta : Vec d) (a : Batch d B) :
    0 ≤ batchResidualEnergy p mu theta a := by
  unfold batchResidualEnergy
  exact mul_nonneg (inv_nonneg.mpr (sq_nonneg (B : ℝ)))
    (Finset.sum_nonneg (fun i _ => sampleResidualSquare_nonneg p mu theta (a i)))

theorem batchResidualEnergy_le {d B : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hB : 0 < B) (a : Batch d B) : batchResidualEnergy p mu theta a ≤ (B : ℝ)⁻¹ := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hs : (∑ i : Fin B, sampleResidualSquare p mu theta (a i)) ≤ B := by
    simpa using Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => sampleResidualSquare_le_one p mu theta (a i))
  unfold batchResidualEnergy
  have hh := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (sq_nonneg (B : ℝ)))
  convert hh using 1 <;> field_simp <;> ring

theorem batchResidualEnergy_memLp_two {d B : ℕ} (p : unitInterval) (mu theta : Vec d) :
    MemLp (batchResidualEnergy (B := B) p mu theta) 2 (batchLaw d B p) := by
  have hi (i : Fin B) : MemLp (fun a : Batch d B => sampleResidualSquare p mu theta (a i)) 2
      (batchLaw d B p) := (sampleResidualSquare_memLp_two p mu theta).comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin B => sampleLaw d p) i)
  have hs := memLp_finsetSum (Finset.univ : Finset (Fin B)) (fun i _ => hi i)
  exact hs.const_mul ((B : ℝ)^2)⁻¹

theorem batchResidualEnergy_integral {d B : ℕ} (p : unitInterval) (mu theta : Vec d) (hB : 0 < B) :
    (∫ a : Batch d B, batchResidualEnergy p mu theta a ∂batchLaw d B p) = coefD0 p mu theta/B := by
  have hg := (sampleResidualSquare_memLp_two p mu theta).integrable (by norm_num)
  have hi (i : Fin B) : Integrable (fun a : Batch d B => sampleResidualSquare p mu theta (a i))
      (batchLaw d B p) :=
    (measurePreserving_eval (fun _ : Fin B => sampleLaw d p) i).integrable_comp_of_integrable hg
  simp only [batchResidualEnergy]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
  have he (i : Fin B) : (∫ a : Batch d B, sampleResidualSquare p mu theta (a i) ∂batchLaw d B p) =
      coefD0 p mu theta := by
    rw [show batchLaw d B p = Measure.pi (fun _ : Fin B => sampleLaw d p) from rfl,
      integral_comp_eval (μ := fun _ : Fin B => sampleLaw d p) (i := i) hg.aestronglyMeasurable,
      sampleResidualSquare_integral]
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  field_simp

/-- Exact iid residual-energy variance. This is the count fluctuation term
that produces the `d² p/B³` contribution after multiplying by dimension. -/
theorem batchResidualEnergy_variance {d B : ℕ} (p : unitInterval) (mu theta : Vec d) (hB : 0 < B) :
    (∫ a : Batch d B, (batchResidualEnergy p mu theta a - coefD0 p mu theta/B)^2 ∂batchLaw d B p) =
      ((∫ a, (sampleResidualSquare p mu theta a)^2 ∂sampleLaw d p) - coefD0 p mu theta^2)/(B : ℝ)^3 := by
  let f : Sample d → ℝ := fun a => sampleResidualSquare p mu theta a - coefD0 p mu theta
  have hf : MemLp f 2 (sampleLaw d p) := (sampleResidualSquare_memLp_two p mu theta).sub (memLp_const _)
  have hm : ∫ a, f a ∂sampleLaw d p = 0 := by
    rw [integral_sub ((sampleResidualSquare_memLp_two p mu theta).integrable (by norm_num)) (integrable_const _),
      sampleResidualSquare_integral]
    simp
  have hv := SparseSGD.Probability.LeastSquares.iid_batch_average_variance hB f hf hm
  have hn := SparseSGD.Probability.LeastSquares.integral_norm_sq_sub_mean
    (sampleResidualSquare p mu theta) (sampleResidualSquare_memLp_two p mu theta)
    (coefD0 p mu theta) (sampleResidualSquare_integral p mu theta)
  simp only [Real.norm_eq_abs, sq_abs, smul_eq_mul] at hv hn
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have he (a : Batch d B) : batchResidualEnergy p mu theta a - coefD0 p mu theta/B =
      (B : ℝ)⁻¹*((B : ℝ)⁻¹*∑ i, f (a i)) := by
    simp only [batchResidualEnergy, f, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    <;> ring
  have hep (a : Batch d B) : (batchResidualEnergy p mu theta a - coefD0 p mu theta/B)^2 =
      (B : ℝ)⁻¹^2 * ((B : ℝ)⁻¹*∑ i, f (a i))^2 := by
    rw [he]
    exact mul_pow _ _ 2
  simp_rw [hep]
  rw [integral_const_mul]
  change (B : ℝ)⁻¹^2 * (∫ a : Batch d B, ((B : ℝ)⁻¹*∑ i, f (a i))^2 ∂Measure.pi (fun _ : Fin B => sampleLaw d p)) = _
  rw [hv]
  change (B : ℝ)⁻¹^2 * ((∫ a, (sampleResidualSquare p mu theta a-coefD0 p mu theta)^2 ∂sampleLaw d p)/B) = _
  rw [hn]
  field_simp

theorem batchResidualEnergy_variance_le {d B : ℕ} (p : unitInterval) (mu theta : Vec d) (hB : 0 < B) :
    (∫ a : Batch d B, (batchResidualEnergy p mu theta a - coefD0 p mu theta/B)^2 ∂batchLaw d B p) ≤
      coefD0 p mu theta/(B : ℝ)^3 := by
  rw [batchResidualEnergy_variance p mu theta hB]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [residualSquare_second_moment_le_mean p mu theta, sq_nonneg (coefD0 p mu theta)]

theorem batchResidualEnergy_second_moment_le {d B : ℕ} (p : unitInterval) (mu theta : Vec d) (hB : 0 < B) :
    (∫ a : Batch d B, (batchResidualEnergy p mu theta a)^2 ∂batchLaw d B p) ≤
      (coefD0 p mu theta/B)^2 + coefD0 p mu theta/(B : ℝ)^3 := by
  have hh := SparseSGD.Probability.LeastSquares.integral_norm_sq_sub_mean
    (batchResidualEnergy (B := B) p mu theta) (batchResidualEnergy_memLp_two p mu theta)
    (coefD0 p mu theta/B) (batchResidualEnergy_integral p mu theta hB)
  simp only [Real.norm_eq_abs, sq_abs] at hh
  linarith [batchResidualEnergy_variance_le p mu theta hB]

theorem residualSquare_moments {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (n : ℕ) (hn : 2 ≤ n) :
    Integrable (fun a => |sampleResidualSquare p mu theta a|^n) (sampleLaw d p) ∧
    (∫ a, |sampleResidualSquare p mu theta a|^n ∂sampleLaw d p) ≤ coefD0 p mu theta := by
  have hb (a : Sample d) : |sampleResidualSquare p mu theta a|^n ≤ sampleResidualSquare p mu theta a := by
    rw [abs_of_nonneg (sampleResidualSquare_nonneg p mu theta a)]
    simpa only [pow_one] using pow_le_pow_of_le_one
      (sampleResidualSquare_nonneg p mu theta a) (sampleResidualSquare_le_one p mu theta a)
        (show 1 ≤ n by omega)
  have hi : Integrable (fun a => |sampleResidualSquare p mu theta a|^n) (sampleLaw d p) := by
    apply ((sampleResidualSquare_memLp_two p mu theta).integrable (by norm_num)).mono'
      ((measurable_sampleResidualSquare p mu theta).abs.pow_const n).aestronglyMeasurable
    filter_upwards with a
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hb a
  refine ⟨hi, ?_⟩
  rw [← sampleResidualSquare_integral]
  exact integral_mono hi ((sampleResidualSquare_memLp_two p mu theta).integrable (by norm_num)) hb

theorem tame_residualSquare_mgf {d : ℕ}
    (H : SparseSGD.External.BernsteinMomentsCertificate (Sample d))
    (p : unitInterval) (mu theta : Vec d) (t : ℝ)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2) (ht : |t| * 2 < 1) :
    Integrable (fun a => Real.exp (t*(sampleResidualSquare p mu theta a-coefD0 p mu theta))) (sampleLaw d p) ∧
    (∫ a, Real.exp (t*(sampleResidualSquare p mu theta a-coefD0 p mu theta)) ∂sampleLaw d p) ≤
      Real.exp (t^2*(16*(p : ℝ))/(2*(1-|t| * 2))) := by
  have hraw (n : ℕ) (hn : 2 ≤ n) :
      (∫ a, |sampleResidualSquare p mu theta a|^n ∂sampleLaw d p) ≤ (n.factorial : ℝ)*(2*(p : ℝ))*1^n := by
    have hfac : (1 : ℝ) ≤ n.factorial := by exact_mod_cast n.factorial_pos
    have hh := (residualSquare_moments p mu theta n hn).2.trans (tame_residualSquare_mean_le p mu theta hp htame)
    simp only [one_pow, mul_one]
    nlinarith
  have hh := H.centered_mgf (sampleLaw d p) (sampleResidualSquare p mu theta) (2*(p : ℝ)) 1 t
    (measurable_sampleResidualSquare p mu theta)
    ((sampleResidualSquare_memLp_two p mu theta).integrable (by norm_num))
    (by positivity) (by norm_num)
    (fun n hn => (residualSquare_moments p mu theta n hn).1) hraw (by simpa using ht)
  simpa only [sampleResidualSquare_integral, one_pow, mul_one, show 8*(2*(p : ℝ)) = 16*(p : ℝ) by ring] using hh

/-- Actual residual-energy count fluctuations are sub-gamma with rare
variance `16p/B³` and scale `2/B²`. -/
theorem tame_batchResidualEnergy_mgf {d B : ℕ}
    (H : SparseSGD.External.BernsteinMomentsCertificate (Sample d))
    (p : unitInterval) (mu theta : Vec d) (t : ℝ) (hB : 0 < B)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (ht : |t| * (2/(B : ℝ)^2) < 1) :
    Integrable (fun a : Batch d B => Real.exp (t*(batchResidualEnergy p mu theta a-coefD0 p mu theta/B)))
      (batchLaw d B p) ∧
    (∫ a : Batch d B, Real.exp (t*(batchResidualEnergy p mu theta a-coefD0 p mu theta/B)) ∂batchLaw d B p) ≤
      Real.exp (t^2*(16*(p : ℝ)/(B : ℝ)^3)/(2*(1-|t| * (2/(B : ℝ)^2)))) := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hs : |t/(B : ℝ)| * (2/(B : ℝ)) < 1 := by
    rw [abs_div, abs_of_pos hb]
    convert ht using 1 <;> field_simp <;> ring
  have hh := SparseSGD.External.iid_average_mgf (sampleLaw d p)
    (fun a => sampleResidualSquare p mu theta a-coefD0 p mu theta)
    B hB (16*(p : ℝ)) 2 (t/B) (by norm_num) hs
    (fun s hs => tame_residualSquare_mgf H p mu theta s hp htame hs)
  have he (a : Batch d B) : t*(batchResidualEnergy p mu theta a-coefD0 p mu theta/B) =
      (t/B)*((B : ℝ)⁻¹*∑ i, (sampleResidualSquare p mu theta (a i)-coefD0 p mu theta)) := by
    simp only [batchResidualEnergy, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    <;> ring
  simp_rw [he]
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  congr 1
  rw [abs_div, abs_of_pos hb]
  field_simp
  <;> ring

end
end SparseSGD.Logistic
