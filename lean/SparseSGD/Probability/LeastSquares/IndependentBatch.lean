import SparseSGD.Probability.Batch
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Probability.LeastSquares
noncomputable section

/-- Distinct coordinates of a finite product are orthogonal in expectation when they
are obtained by applying the same centered square-integrable Hilbert-valued function.
The orthogonality follows from independence of the coordinate projections. -/
theorem integral_inner_iid_centered {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {κ : Measure X} [IsProbabilityMeasure κ] {B : ℕ}
    (f : X → E) (hf : Integrable f κ) (hmean : ∫ x, f x ∂κ = 0)
    (i j : Fin B) (hij : i ≠ j) :
    ∫ ω : Fin B → X, ((innerSL ℝ) (f (ω i))) (f (ω j)) ∂(Measure.pi fun _ : Fin B => κ) = 0 := by
  classical
  let μ : Measure (Fin B → X) := Measure.pi fun _ : Fin B => κ
  have hiid := iIndepFun_pi (μ := fun _ : Fin B => κ) (X := fun _ : Fin B => (id : X → X))
    (fun _ => aemeasurable_id)
  have hindep : (fun ω : Fin B → X => ω i) ⟂ᵢ[μ] (fun ω : Fin B → X => ω j) := by
    exact hiid.indep hij
  have hXi : AEMeasurable (fun ω : Fin B → X => ω i) μ := measurable_pi_apply i |>.aemeasurable
  have hXj : AEMeasurable (fun ω : Fin B → X => ω j) μ := measurable_pi_apply j |>.aemeasurable
  have hfi : Integrable f (μ.map (fun ω : Fin B → X => ω i)) := by
    simpa [μ, Measure.pi_map_eval, measure_univ] using hf
  have hfj : Integrable f (μ.map (fun ω : Fin B → X => ω j)) := by
    simpa [μ, Measure.pi_map_eval, measure_univ] using hf
  have heq := hindep.integral_bilin_comp_comp hXi hXj hfi hfj (innerSL ℝ)
  have hIi : (∫ ω : Fin B → X, f (ω i) ∂μ) = 0 := by
    calc
      _ = ∫ x, f x ∂κ := integral_comp_eval (i := i) hf.aestronglyMeasurable
      _ = 0 := hmean
  have hIj : (∫ ω : Fin B → X, f (ω j) ∂μ) = 0 := by
    calc
      _ = ∫ x, f x ∂κ := integral_comp_eval (i := j) hf.aestronglyMeasurable
      _ = 0 := hmean
  rw [innerSL_apply_apply] at heq
  rw [hIi, hIj] at heq
  convert heq using 1; simp


/-- The centered average of an iid finite batch remains square-integrable. -/
theorem iid_batch_average_memLp {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {κ : Measure X} [IsProbabilityMeasure κ] {B : ℕ}
    (f : X → E) (hf : MemLp f 2 κ) :
    MemLp (fun ω : Fin B → X => (B : ℝ)⁻¹ • ∑ i, f (ω i)) 2
      (Measure.pi fun _ : Fin B => κ) := by
  classical
  have hcomp (i : Fin B) : MemLp (fun ω : Fin B → X => f (ω i)) 2
      (Measure.pi fun _ : Fin B => κ) := by
    exact hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin B => κ) i)
  have hsum : MemLp (fun ω : Fin B → X => ∑ i, f (ω i)) 2
      (Measure.pi fun _ : Fin B => κ) := by
    simpa using memLp_finsetSum (Finset.univ : Finset (Fin B))
      (fun i _ => hcomp i)
  change MemLp ((B : ℝ)⁻¹ • (fun ω : Fin B → X => ∑ i, f (ω i))) 2 _
  exact hsum.const_smul ((B : ℝ)⁻¹)


/-- The average of centered iid samples has zero Bochner mean. -/
theorem iid_batch_average_mean {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {κ : Measure X} [IsProbabilityMeasure κ] {B : ℕ}
    (f : X → E) (hf : MemLp f 2 κ) (hmean : ∫ x, f x ∂κ = 0) :
    ∫ ω : Fin B → X, (B : ℝ)⁻¹ • ∑ i, f (ω i) ∂(Measure.pi fun _ : Fin B => κ) = 0 := by
  classical
  let μ : Measure (Fin B → X) := Measure.pi fun _ : Fin B => κ
  have hcomp (i : Fin B) : MemLp (fun ω : Fin B → X => f (ω i)) 2 μ := by
    exact hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin B => κ) i)
  have hsum := integral_finsetSum (μ := μ) (Finset.univ : Finset (Fin B))
    (f := fun i ω => f (ω i)) (fun i _ => (hcomp i).integrable (by norm_num))
  have hi (i : Fin B) : (∫ ω : Fin B → X, f (ω i) ∂μ) = 0 := by
    calc
      _ = ∫ x, f x ∂κ := integral_comp_eval (i := i) hf.aestronglyMeasurable
      _ = 0 := hmean
  rw [integral_smul]
  have hsum' : (∫ ω : Fin B → X, ∑ i, f (ω i) ∂μ) = 0 := by
    rw [hsum]
    simp [hi]
  rw [hsum']
  simp

/-- A centered iid Hilbert-valued average has exactly the single-sample second
moment divided by the batch size. Independence supplies the vanishing cross terms. -/
theorem iid_batch_average_variance {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {κ : Measure X} [IsProbabilityMeasure κ] {B : ℕ}
    (hB : 0 < B) (f : X → E) (hf : MemLp f 2 κ)
    (hmean : ∫ x, f x ∂κ = 0) :
    (∫ ω : Fin B → X, ‖(B : ℝ)⁻¹ • ∑ i, f (ω i)‖ ^ 2
      ∂(Measure.pi fun _ : Fin B => κ)) = (∫ x, ‖f x‖ ^ 2 ∂κ) / B := by
  classical
  let μ : Measure (Fin B → X) := Measure.pi fun _ : Fin B => κ
  have hcomp (i : Fin B) : MemLp (fun ω : Fin B → X => f (ω i)) 2 μ :=
    hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin B => κ) i)
  have hinner (i j : Fin B) :
      Integrable (fun ω : Fin B → X => inner ℝ (f (ω i)) (f (ω j))) μ := by
    have h := L2.integrable_inner (𝕜 := ℝ)
      ((hcomp i).toLp (fun ω : Fin B → X => f (ω i)))
      ((hcomp j).toLp (fun ω : Fin B → X => f (ω j)))
    apply h.congr
    filter_upwards [MemLp.coeFn_toLp (hcomp i), MemLp.coeFn_toLp (hcomp j)] with ω hi hj
    rw [hi, hj]
  have hdiag (i : Fin B) :
      (∫ ω : Fin B → X, inner ℝ (f (ω i)) (f (ω i)) ∂μ) = ∫ x, ‖f x‖ ^ 2 ∂κ := by
    simp_rw [real_inner_self_eq_norm_sq]
    exact integral_comp_eval (μ := fun _ : Fin B => κ) (i := i)
      (f := fun x => ‖f x‖ ^ 2) (hf.aestronglyMeasurable.norm.pow 2)
  have hsum : (∫ ω : Fin B → X, ‖∑ i, f (ω i)‖ ^ 2 ∂μ) =
      (B : ℝ) * ∫ x, ‖f x‖ ^ 2 ∂κ := by
    have hexpand (ω : Fin B → X) : ‖∑ i, f (ω i)‖ ^ 2 =
        ∑ i : Fin B, ∑ j : Fin B, inner ℝ (f (ω i)) (f (ω j)) := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [sum_inner, inner_sum]
      exact Finset.sum_comm
    simp_rw [hexpand]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hinner i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hinner _ j)]
    have hrow (i : Fin B) :
        (∑ j : Fin B, ∫ ω : Fin B → X, inner ℝ (f (ω i)) (f (ω j)) ∂μ) =
        ∫ x, ‖f x‖ ^ 2 ∂κ := by
      rw [Finset.sum_eq_single i]
      · exact hdiag i
      · intro j _ hji
        exact integral_inner_iid_centered f (hf.integrable (by norm_num)) hmean i j hji.symm
      · simp
    simp_rw [hrow]
    simp
  simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [integral_const_mul, hsum]
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  field_simp

/-- Centering subtracts the squared norm of the mean from the second moment. -/
theorem integral_norm_sq_sub_mean {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {κ : Measure X} [IsProbabilityMeasure κ] (f : X → E) (hf : MemLp f 2 κ)
    (m : E) (hmean : ∫ x, f x ∂κ = m) :
    (∫ x, ‖f x - m‖ ^ 2 ∂κ) = (∫ x, ‖f x‖ ^ 2 ∂κ) - ‖m‖ ^ 2 := by
  have hi := hf.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hn := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hip := hi.inner_const (𝕜 := ℝ) m
  have heq : (∫ x, inner ℝ (f x) m ∂κ) = ‖m‖ ^ 2 := by
    calc
      _ = ∫ x, inner ℝ m (f x) ∂κ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => real_inner_comm _ _)
      _ = ‖m‖ ^ 2 := by rw [integral_inner hi, hmean, real_inner_self_eq_norm_sq]
  simp_rw [norm_sub_sq_real]
  rw [integral_add (f := fun x => ‖f x‖ ^ 2 - 2 * inner ℝ (f x) m)
      (g := fun _ => ‖m‖ ^ 2) (hn.sub (hip.const_mul 2)) (integrable_const _),
    integral_sub (f := fun x => ‖f x‖ ^ 2) (g := fun x => 2 * inner ℝ (f x) m)
      hn (hip.const_mul 2), integral_const_mul, heq]
  simp
  ring



end
end SparseSGD.Probability.LeastSquares
