import SparseSGD.Probability.LeastSquares.Measurability
import SparseSGD.Probability.LeastSquares.GaussianVector

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SparseSGD.Probability.LeastSquares
noncomputable section
set_option maxHeartbeats 800000
local instance : ENNReal.HolderTriple 4 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]⟩

/-- The gradient on the active branch of the single shared Bernoulli switch. -/
private def fullGradient {d : ℕ} (e : Vec d) (a : (Fin d → ℝ) × ℝ) : Vec d :=
  (inner ℝ (WithLp.toLp 2 a.1 : Vec d) e - a.2) • WithLp.toLp 2 a.1

private theorem measurable_fullGradient {d : ℕ} (e : Vec d) :
    Measurable (fullGradient e) := by
  unfold fullGradient
  have hx : Measurable (fun a : (Fin d → ℝ) × ℝ => (WithLp.toLp 2 a.1 : Vec d)) := (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp measurable_fst
  exact (hx.inner measurable_const |>.sub measurable_snd).smul hx

private theorem memLp_mul_prod_two {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {f : α → ℝ} {g : β → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun a : α × β => f a.1 * g a.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq ((hf.aestronglyMeasurable.comp_fst).mul
    (hg.aestronglyMeasurable.comp_snd))).2
  convert hf.integrable_sq.mul_prod hg.integrable_sq using 1
  funext a
  simp only [Pi.mul_apply, mul_pow]

private theorem fullGradient_memLp {d : ℕ} (e : Vec d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hz : MemLp id 2 ν) :
    MemLp (fullGradient e) 2 ((standardGaussianProduct d).prod ν) := by
  apply MemLp.of_eval_piLp
  intro i
  have ha : MemLp (fun x : Fin d → ℝ =>
      inner ℝ (WithLp.toLp 2 x : Vec d) e * x i) 2 (standardGaussianProduct d) :=
    (gaussian_inner_memLp e 4 (by norm_num)).mul (gaussian_coord_memLp i 4 (by norm_num))
  have hb := memLp_mul_prod_two (gaussian_coord_memLp i 2 (by norm_num)) hz
  convert (ha.comp_fst ν).sub hb using 1
  funext a
  simp only [fullGradient, PiLp.smul_apply, Pi.sub_apply, id_eq]
  ring

private theorem fullGradient_integral {d : ℕ} (e : Vec d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0) :
    ∫ a, fullGradient e a ∂((standardGaussianProduct d).prod ν) = e := by
  classical
  have hg := (fullGradient_memLp e ν hz).integrable (by norm_num)
  ext i
  rw [eval_integral_piLp (fun j => hg.eval_piLp j)]
  have ha : Integrable (fun x : Fin d → ℝ =>
      inner ℝ (WithLp.toLp 2 x : Vec d) e * x i) (standardGaussianProduct d) :=
    (gaussian_inner_memLp e 2 (by norm_num)).integrable_mul (gaussian_coord_memLp i 2 (by norm_num))
  have hb := (gaussian_coord_memLp i 2 (by norm_num)).integrable (by norm_num)
  have hz' : Integrable (fun z : ℝ => z) ν := hz.integrable (by norm_num)
  have heq : (fun a : (Fin d → ℝ) × ℝ => fullGradient e a i) =
      fun a => (inner ℝ (WithLp.toLp 2 a.1 : Vec d) e * a.1 i) - a.1 i * a.2 := by
    funext a
    simp only [fullGradient, PiLp.smul_apply]
    ring
  rw [heq, integral_sub (ha.comp_fst ν) (hb.mul_prod hz'), integral_prod_mul (fun x : Fin d → ℝ => x i) (fun z : ℝ => z)]
  simp only [hmean, mul_zero, sub_zero]
  rw [integral_prod _ (ha.comp_fst ν)]
  simp only [integral_const, probReal_univ, one_smul]
  simp only [euclidean_inner_eq_sum, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ]
  · simp_rw [show ∀ j : Fin d, (fun x : Fin d → ℝ => x j * e j * x i) =
        (fun x => (x j * x i) * e j) by intro j; funext x; ring,
      integral_mul_const, standardGaussianProduct_covariance]
    simp
  · intro j hj
    convert ((gaussian_coord_memLp j 2 (by norm_num)).integrable_mul
      (gaussian_coord_memLp i 2 (by norm_num))).mul_const (e j) using 1
    funext x
    simp only [Pi.mul_apply]
    ring

private theorem fullGradient_norm_sq_integral {d : ℕ} (e : Vec d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0) :
    ∫ a, ‖fullGradient e a‖ ^ 2 ∂((standardGaussianProduct d).prod ν) =
      (d + 2) * ‖e‖ ^ 2 + labelVariance ν * d := by
  let A := fun x : Fin d → ℝ => ‖WithLp.toLp 2 x‖ ^ 2
  let C := fun x : Fin d → ℝ => inner ℝ (WithLp.toLp 2 x : Vec d) e
  have hA : MemLp A 2 (standardGaussianProduct d) := gaussian_norm_sq_memLp_two d
  have hC : MemLp C 2 (standardGaussianProduct d) := gaussian_inner_memLp e 2 (by norm_num)
  have hC2 : MemLp (fun x => C x ^ 2) 2 (standardGaussianProduct d) := by
    convert
      ((gaussian_inner_memLp e 4 (by norm_num)).mul
        (gaussian_inner_memLp e 4 (by norm_num)) : MemLp _ 2 _) using 1
    funext x
    simp only [Pi.mul_apply, C, pow_two]
  have hAC2 : Integrable (fun x => A x * C x ^ 2) (standardGaussianProduct d) :=
    hA.integrable_mul hC2
  have hAC : Integrable (fun x => A x * C x) (standardGaussianProduct d) := hA.integrable_mul hC
  have hAi := hA.integrable (by norm_num)
  have hzi : Integrable (fun z : ℝ => z) ν := hz.integrable (by norm_num)
  have ht1 := hAC2.comp_fst ν
  have ht2 := (hAC.mul_prod hzi).const_mul (2 : ℝ)
  have hzsq : Integrable (fun z : ℝ => z ^ 2) ν := hz.integrable_sq
  have ht3 := hAi.mul_prod hzsq
  have heq : (fun a : (Fin d → ℝ) × ℝ => ‖fullGradient e a‖ ^ 2) =
      fun a => A a.1 * C a.1 ^ 2 - 2 * (A a.1 * C a.1 * a.2) + A a.1 * a.2 ^ 2 := by
    funext a
    simp only [fullGradient, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    dsimp [A, C]
    ring
  have ht12 : Integrable (fun a : (Fin d → ℝ) × ℝ =>
      A a.1 * C a.1 ^ 2 - 2 * (A a.1 * C a.1 * a.2))
      ((standardGaussianProduct d).prod ν) := ht1.sub ht2
  rw [heq, integral_add ht12 ht3, integral_sub ht1 ht2,
    integral_const_mul,
    integral_prod_mul (fun x => A x * C x) (fun z : ℝ => z),
    integral_prod_mul A (fun z : ℝ => z ^ 2)]
  simp only [hmean, mul_zero, sub_zero]
  rw [integral_prod _ ht1]
  simp only [integral_const, probReal_univ, one_smul]
  change (∫ x, A x * C x ^ 2 ∂standardGaussianProduct d) +
    (∫ x, A x ∂standardGaussianProduct d) * labelVariance ν = _
  rw [show (∫ x, A x * C x ^ 2 ∂standardGaussianProduct d) =
    (d + 2) * ‖e‖ ^ 2 from standardGaussianProduct_euclidean_norm_inner_sq e,
    show (∫ x, A x ∂standardGaussianProduct d) = d from gaussian_norm_sq_integral d]
  ring

private theorem gradient_eq_gate {d : ℕ} (e : Vec d) (a : Sample d) :
    gradient e a = (if a.1 then (1 : ℝ) else 0) • fullGradient e a.2 := by
  rcases a with ⟨s, x, z⟩
  cases s <;> simp [gradient, feature, fullGradient]

private theorem gate_integrable (p : unitInterval) :
    Integrable (fun s : Bool => if s then (1 : ℝ) else 0) (bernoulliMeasure true false p) :=
  integrable_bernoulliMeasure true false p _

private theorem gate_integral (p : unitInterval) :
    ∫ s : Bool, (if s then (1 : ℝ) else 0) ∂bernoulliMeasure true false p = p := by
  rw [integral_bernoulliMeasure]
  simp

/-- A finite label second moment is sufficient for the actual sample gradient to be in L². -/
theorem gradient_memLp {d : ℕ} (e : Vec d) (p : unitInterval) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hz : MemLp id 2 ν) :
    MemLp (gradient e) 2 (sampleLaw d p ν) := by
  apply (memLp_two_iff_integrable_sq_norm
    (((measurable_gradient d).comp (f := fun a : Sample d => (e, a))
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).2
  have hg := (memLp_two_iff_integrable_sq_norm
    (fullGradient_memLp e ν hz).aestronglyMeasurable).1 (fullGradient_memLp e ν hz)
  convert (gate_integrable p).mul_prod hg using 1
  · funext a
    change ‖gradient e a‖ ^ 2 = _
    rw [gradient_eq_gate]
    cases a.1 <;> simp
  · rfl

/-- The true least-squares sample gradient has mean `p • e`. -/
theorem gradient_integral {d : ℕ} (e : Vec d) (p : unitInterval) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0) :
    ∫ a, gradient e a ∂sampleLaw d p ν = (p : ℝ) • e := by
  simp_rw [gradient_eq_gate]
  rw [sampleLaw, integral_prod_smul (fun s : Bool => if s then (1 : ℝ) else 0) (fullGradient e), gate_integral, fullGradient_integral e ν hz hmean]

/-- The uncentered second moment, including independent additive label noise. -/
theorem gradient_norm_sq_integral {d : ℕ} (e : Vec d) (p : unitInterval) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0) :
    ∫ a, ‖gradient e a‖ ^ 2 ∂sampleLaw d p ν =
      (p : ℝ) * (d + 2) * ‖e‖ ^ 2 + labelVariance ν * (p : ℝ) * d := by
  have heq : (fun a : Sample d => ‖gradient e a‖ ^ 2) =
      fun a => (if a.1 then (1 : ℝ) else 0) * ‖fullGradient e a.2‖ ^ 2 := by
    funext a
    rw [gradient_eq_gate]
    cases a.1 <;> simp
  rw [heq, sampleLaw, integral_prod_mul (fun s : Bool => if s then (1 : ℝ) else 0)
    (fun a => ‖fullGradient e a‖ ^ 2), gate_integral,
    fullGradient_norm_sq_integral e ν hz hmean]
  ring


theorem gradient_centered_memLp {d : ℕ} (e : Vec d) (p : unitInterval) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hz : MemLp id 2 ν) :
    MemLp (fun a => gradient e a - (p : ℝ) • e) 2 (sampleLaw d p ν) :=
  (gradient_memLp e p ν hz).sub (memLp_const ((p : ℝ) • e))

theorem gradient_centered_integral {d : ℕ} (e : Vec d) (p : unitInterval) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0) :
    ∫ a, (gradient e a - (p : ℝ) • e) ∂sampleLaw d p ν = 0 := by
  rw [integral_sub ((gradient_memLp e p ν hz).integrable (by norm_num))
    (integrable_const _), gradient_integral e p ν hz hmean]
  simp

/-- The exact single-sample centered second moment for the shared-switch feature model. -/
theorem gradient_centered_norm_sq_integral {d : ℕ} (e : Vec d) (p : unitInterval)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hz : MemLp id 2 ν)
    (hmean : ∫ z, z ∂ν = 0) :
    ∫ a, ‖gradient e a - (p : ℝ) • e‖ ^ 2 ∂sampleLaw d p ν =
      (p : ℝ) * (d + 2 - p) * ‖e‖ ^ 2 + labelVariance ν * (p : ℝ) * d := by
  have hg := gradient_memLp e p ν hz
  have hgsq := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  have hgi := hg.integrable (by norm_num)
  have hin : Integrable (fun a => inner ℝ (gradient e a) ((p : ℝ) • e))
      (sampleLaw d p ν) := hgi.inner_const _
  have hin2 := hin.const_mul (2 : ℝ)
  have hsub : Integrable (fun a => ‖gradient e a‖ ^ 2 -
      2 * inner ℝ (gradient e a) ((p : ℝ) • e)) (sampleLaw d p ν) := hgsq.sub hin2
  have hint := integral_inner (𝕜 := ℝ) hgi ((p : ℝ) • e)
  rw [gradient_integral e p ν hz hmean, real_inner_self_eq_norm_sq] at hint
  have hint' : (∫ a, inner ℝ (gradient e a) ((p : ℝ) • e) ∂sampleLaw d p ν) =
      ‖(p : ℝ) • e‖ ^ 2 := by simpa only [real_inner_comm] using hint
  simp_rw [norm_sub_sq_real]
  rw [integral_add hsub (integrable_const _), integral_sub hgsq hin2,
    integral_const_mul, hint', gradient_norm_sq_integral e p ν hz hmean]
  simp only [integral_const, probReal_univ, one_smul,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

end
end SparseSGD.Probability.LeastSquares
