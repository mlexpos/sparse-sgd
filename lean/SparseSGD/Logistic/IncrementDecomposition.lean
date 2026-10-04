import SparseSGD.Logistic.ConditionalDrift

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

/-- The manuscript's five matched coordinates, in its stated order. -/
def matchedSummary {d : ℕ} (eta beta : ℝ) (mu : Vec d) (s : State d) : Fin 5 → ℝ :=
  ![signalCoord mu s.1, eta / (1-beta) * signalCoord mu s.2,
    ‖bulkPart mu s.1‖^2, eta / (1-beta) * inner ℝ (bulkPart mu s.1) (bulkPart mu s.2),
    (eta / (1-beta))^2 * ‖bulkPart mu s.2‖^2]

def meanBatchGradient {d B : ℕ} (p : unitInterval) (mu theta : Vec d) : Vec d :=
  ∫ a : Batch d B, batchGradient p mu theta a ∂batchLaw d B p

def centeredBatchGradient {d B : ℕ} (p : unitInterval) (mu theta : Vec d)
    (a : Batch d B) : Vec d := batchGradient p mu theta a - meanBatchGradient (B := B) p mu theta

def meanUpdate {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d) : State d :=
  let m := beta • s.2 + (1-beta) • meanBatchGradient (B := B) p mu s.1
  (s.1 - eta • m, m)

def centeredBulkSquare {d B : ℕ} (p : unitInterval) (mu theta : Vec d)
    (a : Batch d B) : ℝ :=
  ‖bulkPart mu (centeredBatchGradient p mu theta a)‖^2 -
    ∫ b : Batch d B, ‖bulkPart mu (centeredBatchGradient p mu theta b)‖^2 ∂batchLaw d B p

def matchedDrift {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (s : State d) : Fin 5 → ℝ := fun i =>
  ∫ a : Batch d B, matchedSummary eta beta mu (update eta beta p mu s a) i ∂batchLaw d B p

def matchedIncrement {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (s : State d) (a : Batch d B) : Fin 5 → ℝ :=
  matchedSummary eta beta mu (update eta beta p mu s a) - matchedDrift (B := B) eta beta p mu s

theorem centeredBatchGradient_memLp_two {d B : ℕ} (p : unitInterval) (mu theta : Vec d) :
    MemLp (centeredBatchGradient (B := B) p mu theta) 2 (batchLaw d B p) :=
  (batchGradient_memLp_two d B p mu theta).sub (memLp_const _)

theorem centeredBatchGradient_integral {d B : ℕ} (p : unitInterval) (mu theta : Vec d) :
    (∫ a : Batch d B, centeredBatchGradient p mu theta a ∂batchLaw d B p) = 0 := by
  simp only [centeredBatchGradient]
  have hg : Integrable (fun a : Batch d B => batchGradient p mu theta a) (batchLaw d B p) :=
    (batchGradient_memLp_two d B p mu theta).integrable (by norm_num)
  rw [integral_sub
    hg (integrable_const _)]
  simp [meanBatchGradient]

theorem centeredBulk_memLp_two {d B : ℕ} (p : unitInterval) (mu theta : Vec d) :
    MemLp (fun a : Batch d B => bulkPart mu (centeredBatchGradient p mu theta a)) 2
      (batchLaw d B p) :=
  by
    simpa only [Function.comp_def, bulkLinear_apply] using
      (bulkLinear mu).comp_memLp' (centeredBatchGradient_memLp_two (B := B) p mu theta)

theorem centeredBulk_integral {d B : ℕ} (p : unitInterval) (mu theta : Vec d) :
    (∫ a : Batch d B, bulkPart mu (centeredBatchGradient p mu theta a) ∂batchLaw d B p) = 0 := by
  simp_rw [← bulkLinear_apply]
  rw [(bulkLinear mu).integral_comp_comm
    ((centeredBatchGradient_memLp_two p mu theta).integrable (by norm_num)),
    centeredBatchGradient_integral, map_zero]

theorem centeredBulkSquare_integrable {d B : ℕ} (p : unitInterval) (mu theta : Vec d) :
    Integrable (centeredBulkSquare (B := B) p mu theta) (batchLaw d B p) :=
  ((memLp_two_iff_integrable_sq_norm
    (centeredBulk_memLp_two (B := B) p mu theta).aestronglyMeasurable).mp
      (centeredBulk_memLp_two p mu theta)).sub (integrable_const _)

theorem centeredBulkSquare_integral {d B : ℕ} (p : unitInterval) (mu theta : Vec d) :
    (∫ a : Batch d B, centeredBulkSquare p mu theta a ∂batchLaw d B p) = 0 := by
  simp only [centeredBulkSquare]
  rw [integral_sub
    ((memLp_two_iff_integrable_sq_norm
      (centeredBulk_memLp_two (B := B) p mu theta).aestronglyMeasurable).mp
        (centeredBulk_memLp_two p mu theta)) (integrable_const _)]
  simp

/-- Centering an affine squared norm exposes both the linear cross term and
the centered squared norm. The cross term must not be dropped. -/
theorem affine_norm_square_centered {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {κ : Measure X} [IsProbabilityMeasure κ] (z : X → E) (hz : MemLp z 2 κ)
    (hzero : ∫ a, z a ∂κ = 0) (u : E) (c : ℝ) (a : X) :
    ‖u + c • z a‖^2 - (∫ b, ‖u + c • z b‖^2 ∂κ) =
      2*c*inner ℝ u (z a) + c^2*(‖z a‖^2 - ∫ b, ‖z b‖^2 ∂κ) := by
  have hi := (hz.integrable (by norm_num)).const_inner (𝕜 := ℝ) u
  have hn := (memLp_two_iff_integrable_sq_norm hz.aestronglyMeasurable).mp hz
  simp_rw [norm_add_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_add (f := fun b => ‖u‖^2 + 2*(c*inner ℝ u (z b)))
      (g := fun b => c^2 * ‖z b‖^2)
      ((integrable_const _).add ((hi.const_mul c).const_mul 2))
      (hn.const_mul (c^2)),
    integral_add (f := fun _ => ‖u‖^2) (g := fun b => 2*(c*inner ℝ u (z b)))
      (integrable_const _) ((hi.const_mul c).const_mul 2)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, integral_const_mul]
  rw [integral_inner (hz.integrable (by norm_num)), hzero]
  simp only [inner_zero_right, mul_zero, add_zero]
  ring

theorem update_centered_parameter {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) (a : Batch d B) :
    (update eta beta p mu s a).1 = (meanUpdate (B := B) eta beta p mu s).1 +
      (-eta*(1-beta)) • centeredBatchGradient p mu s.1 a := by
  simp only [update, meanUpdate, centeredBatchGradient, smul_sub, smul_add, smul_smul]
  module

theorem update_centered_momentum {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) (a : Batch d B) :
    (update eta beta p mu s a).2 = (meanUpdate (B := B) eta beta p mu s).2 +
      (1-beta) • centeredBatchGradient p mu s.1 a := by
  simp only [update, meanUpdate, centeredBatchGradient, smul_sub]
  module

theorem matchedIncrement_bulk_parameter {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) (a : Batch d B) :
    matchedIncrement eta beta p mu s a 2 =
      -2*eta*(1-beta)*inner ℝ (bulkPart mu (meanUpdate (B := B) eta beta p mu s).1)
        (bulkPart mu (centeredBatchGradient p mu s.1 a)) +
      eta^2*(1-beta)^2*centeredBulkSquare p mu s.1 a := by
  change ‖bulkPart mu (update eta beta p mu s a).1‖^2 -
    (∫ b : Batch d B, ‖bulkPart mu (update eta beta p mu s b).1‖^2 ∂batchLaw d B p) = _
  simp only [update_centered_parameter, bulkPart_add, bulkPart_smul]
  rw [affine_norm_square_centered _ (centeredBulk_memLp_two p mu s.1)
    (centeredBulk_integral p mu s.1)]
  simp only [centeredBulkSquare]
  ring

theorem affine_inner_centered {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {κ : Measure X} [IsProbabilityMeasure κ] (z : X → E) (hz : MemLp z 2 κ)
    (hzero : ∫ a, z a ∂κ = 0) (u w : E) (c e : ℝ) (a : X) :
    inner ℝ (u + c • z a) (w + e • z a) -
      (∫ b, inner ℝ (u + c • z b) (w + e • z b) ∂κ) =
    e*inner ℝ u (z a) + c*inner ℝ w (z a) +
      c*e*(‖z a‖^2 - ∫ b, ‖z b‖^2 ∂κ) := by
  have hi := (hz.integrable (by norm_num)).const_inner (𝕜 := ℝ) u
  have hj := (hz.integrable (by norm_num)).const_inner (𝕜 := ℝ) w
  have hn := (memLp_two_iff_integrable_sq_norm hz.aestronglyMeasurable).mp hz
  simp_rw [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  have he (b : X) : inner ℝ (z b) w = inner ℝ w (z b) := real_inner_comm _ _
  simp_rw [he, ← mul_add]
  rw [integral_add (f := fun b => inner ℝ u w + e*inner ℝ u (z b))
    (g := fun b => c*(inner ℝ w (z b) + e*‖z b‖^2))
    ((integrable_const _).add (hi.const_mul e))
    ((hj.add (hn.const_mul e)).const_mul c),
    integral_add (f := fun _ => inner ℝ u w) (g := fun b => e*inner ℝ u (z b))
      (integrable_const _) (hi.const_mul e), integral_const_mul c,
    integral_add hj (hn.const_mul e)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, integral_const_mul]
  rw [integral_inner (hz.integrable (by norm_num)),
    integral_inner (hz.integrable (by norm_num)), hzero]
  simp only [inner_zero_right, mul_zero, add_zero, zero_add]
  ring

theorem matchedIncrement_bulk_momentum {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) (a : Batch d B) (hb : beta ≠ 1) :
    matchedIncrement eta beta p mu s a 4 =
      2*eta^2/(1-beta)*inner ℝ (bulkPart mu (meanUpdate (B := B) eta beta p mu s).2)
        (bulkPart mu (centeredBatchGradient p mu s.1 a)) +
      eta^2*centeredBulkSquare p mu s.1 a := by
  change (eta/(1-beta))^2 * ‖bulkPart mu (update eta beta p mu s a).2‖^2 -
    (∫ b : Batch d B, (eta/(1-beta))^2 * ‖bulkPart mu (update eta beta p mu s b).2‖^2
      ∂batchLaw d B p) = _
  rw [integral_const_mul, ← mul_sub]
  simp only [update_centered_momentum, bulkPart_add, bulkPart_smul]
  rw [affine_norm_square_centered _ (centeredBulk_memLp_two p mu s.1)
    (centeredBulk_integral p mu s.1)]
  simp only [centeredBulkSquare]
  field_simp [sub_ne_zero.mpr (Ne.symm hb)]
  <;> ring

theorem matchedIncrement_bulk_covariance {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) (a : Batch d B) (hb : beta ≠ 1) :
    matchedIncrement eta beta p mu s a 3 =
      eta*inner ℝ (bulkPart mu (meanUpdate (B := B) eta beta p mu s).1)
        (bulkPart mu (centeredBatchGradient p mu s.1 a)) -
      eta^2*inner ℝ (bulkPart mu (meanUpdate (B := B) eta beta p mu s).2)
        (bulkPart mu (centeredBatchGradient p mu s.1 a)) -
      eta^2*(1-beta)*centeredBulkSquare p mu s.1 a := by
  change eta/(1-beta) * inner ℝ (bulkPart mu (update eta beta p mu s a).1)
      (bulkPart mu (update eta beta p mu s a).2) -
    (∫ b : Batch d B, eta/(1-beta) * inner ℝ (bulkPart mu (update eta beta p mu s b).1)
      (bulkPart mu (update eta beta p mu s b).2) ∂batchLaw d B p) = _
  rw [integral_const_mul, ← mul_sub]
  simp only [update_centered_parameter, update_centered_momentum, bulkPart_add, bulkPart_smul]
  rw [affine_inner_centered _ (centeredBulk_memLp_two p mu s.1)
    (centeredBulk_integral p mu s.1)]
  simp only [centeredBulkSquare]
  field_simp [sub_ne_zero.mpr (Ne.symm hb)]
  <;> ring

theorem affine_signal_centered {X : Type*} [MeasurableSpace X]
    {κ : Measure X} [IsProbabilityMeasure κ] {d : ℕ} (z : X → Vec d)
    (hz : Integrable z κ) (hzero : ∫ a, z a ∂κ = 0) (mu u : Vec d) (c : ℝ) (a : X) :
    signalCoord mu (u + c • z a) - (∫ b, signalCoord mu (u + c • z b) ∂κ) =
      c*signalCoord mu (z a) := by
  simp only [signalCoord, inner_add_left, real_inner_smul_left, add_div, mul_div_assoc]
  rw [integral_add (integrable_const _) ((hz.inner_const mu).div_const (r mu) |>.const_mul c)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, integral_const_mul, integral_div]
  have he (b : X) : inner ℝ (z b) mu = inner ℝ mu (z b) := real_inner_comm _ _
  simp_rw [he]
  rw [integral_inner hz, hzero]
  simp

theorem matchedIncrement_signal_parameter {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) (a : Batch d B) :
    matchedIncrement eta beta p mu s a 0 =
      -eta*(1-beta)*signalCoord mu (centeredBatchGradient p mu s.1 a) := by
  change signalCoord mu (update eta beta p mu s a).1 -
    (∫ b : Batch d B, signalCoord mu (update eta beta p mu s b).1 ∂batchLaw d B p) = _
  simp only [update_centered_parameter]
  exact affine_signal_centered _ ((centeredBatchGradient_memLp_two p mu s.1).integrable (by norm_num))
    (centeredBatchGradient_integral p mu s.1) mu _ _ a

theorem matchedIncrement_signal_momentum {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) (a : Batch d B) (hb : beta ≠ 1) :
    matchedIncrement eta beta p mu s a 1 =
      eta*signalCoord mu (centeredBatchGradient p mu s.1 a) := by
  change eta/(1-beta) * signalCoord mu (update eta beta p mu s a).2 -
    (∫ b : Batch d B, eta/(1-beta) * signalCoord mu (update eta beta p mu s b).2 ∂batchLaw d B p) = _
  rw [integral_const_mul, ← mul_sub]
  simp only [update_centered_momentum]
  rw [affine_signal_centered _ ((centeredBatchGradient_memLp_two p mu s.1).integrable (by norm_num))
    (centeredBatchGradient_integral p mu s.1)]
  field_simp [sub_ne_zero.mpr (Ne.symm hb)]

end
end SparseSGD.Logistic
