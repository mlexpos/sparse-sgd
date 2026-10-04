import SparseSGD.Logistic.FluidBootstrap

/-! Stopped finite-horizon fluid recurrences.

This file records the algebraic stopping/unrolling interface.  The random
weights are required to be predictable in the later probabilistic layer; in
particular this module makes no claim that a product evaluated along a random
trajectory is deterministic.
-/
namespace SparseSGD.Logistic

noncomputable section

/-- Stopping preserves martingales. Mathlib exposes the corresponding result
for submartingales; the martingale statement follows by applying it also to
the negated process. -/
theorem martingale_stoppedProcess {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtration ℕ m0}
    {f : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ}
    [MeasureTheory.SigmaFiniteFiltration μ ℱ]
    (hf : MeasureTheory.Martingale f ℱ μ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) :
    MeasureTheory.Martingale (MeasureTheory.stoppedProcess f τ) ℱ μ := by
  rw [MeasureTheory.martingale_iff]
  refine ⟨?_, hf.submartingale.stoppedProcess hτ⟩
  have hneg := (hf.neg.submartingale.stoppedProcess hτ).neg
  simpa [MeasureTheory.stoppedProcess] using hneg

/-- A stopped increment is zero once the predictable stop has been reached.
`alive k` is the event that the increment at time `k` is still included. -/
def stoppedIncrement (alive : ℕ → Prop) [DecidablePred alive]
    (noise remainder : ℕ → ℝ) (k : ℕ) : ℝ :=
  if alive k then noise k + remainder k else 0

/-- Exact solution to the scalar inhomogeneous linear recurrence.  `response`
contains the (possibly time-varying) deterministic propagation coefficients. -/
def propagatedSum (response : ℕ → ℕ → ℝ) (forcing : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, response k j * forcing j

/-- Finite-horizon variation of constants, exposed as a recurrence contract.
The first condition says each new forcing term has unit response at its own
step; the second transports every earlier response by the next Jacobian. -/
theorem propagatedSum_succ {response : ℕ → ℕ → ℝ} {forcing : ℕ → ℝ} {k : ℕ}
    (hnew : response (k + 1) k = 1)
    (J : ℝ) (hold : ∀ j < k, response (k + 1) j = J * response k j) :
    propagatedSum response forcing (k + 1) =
      J * propagatedSum response forcing k + forcing k := by
  simp only [propagatedSum, Finset.sum_range_succ]
  rw [hnew]
  have hs : (∑ j ∈ Finset.range k, response (k + 1) j * forcing j) =
      J * ∑ j ∈ Finset.range k, response k j * forcing j := by
    calc
      (∑ j ∈ Finset.range k, response (k + 1) j * forcing j) =
          ∑ j ∈ Finset.range k, (J * response k j) * forcing j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hold j (Finset.mem_range.mp hj)]
      _ = ∑ j ∈ Finset.range k, J * (response k j * forcing j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = J * ∑ j ∈ Finset.range k, response k j * forcing j := by
            rw [Finset.mul_sum]
  rw [hs]
  ring

/-- If an error obeys the one-step affine recurrence with the response
coefficients above, it is exactly the propagated sum of its forcings. -/
theorem recurrence_eq_propagatedSum {J forcing e : ℕ → ℝ}
    (he0 : e 0 = 0)
    (hrec : ∀ k, e (k + 1) = J k * e k + forcing k)
    (response : ℕ → ℕ → ℝ)
    (hnew : ∀ k, response (k + 1) k = 1)
    (hold : ∀ k j, j < k → response (k + 1) j = J k * response k j) :
    ∀ k, e k = propagatedSum response forcing k := by
  intro k
  induction k with
  | zero => simp [propagatedSum, he0]
  | succ k ih =>
      rw [hrec k, ih, propagatedSum_succ (hnew k) (J k) (hold k)]

/-- Arithmetic simplification of a stopped increment when its inclusion
predicate is false. This lemma makes no claim about filtration measurability. -/
theorem stoppedIncrement_eq_of_not_alive {alive : ℕ → Prop} [DecidablePred alive]
    (noise remainder : ℕ → ℝ) (k : ℕ) (h : ¬ alive k) :
    stoppedIncrement alive noise remainder k = 0 := by
  simp [stoppedIncrement, h]

/-- Deterministic products of Jacobians, transporting the forcing at time `j`
to the error at time `k`. No random state enters these products. -/
def jacobianResponse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : ℕ → E →L[ℝ] E) : ℕ → ℕ → E →L[ℝ] E
  | 0, _ => ContinuousLinearMap.id ℝ E
  | k+1, j => if j = k then ContinuousLinearMap.id ℝ E else (J k).comp (jacobianResponse J k j)

theorem jacobianResponse_new {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : ℕ → E →L[ℝ] E) (k : ℕ) :
    jacobianResponse J (k+1) k = ContinuousLinearMap.id ℝ E := by simp [jacobianResponse]

theorem jacobianResponse_old {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : ℕ → E →L[ℝ] E) {j k : ℕ} (hjk : j < k) :
    jacobianResponse J (k+1) j = (J k).comp (jacobianResponse J k j) := by
  simp [jacobianResponse, Nat.ne_of_lt hjk]

theorem vector_recurrence_unroll {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : ℕ → E →L[ℝ] E) (f e : ℕ → E) (he0 : e 0 = 0)
    (hrec : ∀ k, e (k+1) = J k (e k) + f k) :
    ∀ k, e k = ∑ j ∈ Finset.range k, jacobianResponse J k j (f j) := by
  intro k
  induction k with
  | zero => simp [he0]
  | succ k ih =>
    rw [hrec, ih, Finset.sum_range_succ, jacobianResponse_new]
    simp only [ContinuousLinearMap.id_apply, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [jacobianResponse_old J (Finset.mem_range.mp hj)]
    rfl

end
end SparseSGD.Logistic
