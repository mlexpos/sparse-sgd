import SparseSGD.Logistic.Model

open Filter
namespace SparseSGD.Examples
noncomputable section

/-- A teacher family with the prescribed norm in every positive dimension.
Dimension zero is represented by its unique vector. -/
def logisticTeacher (teacherNorm : ℝ) (d : ℕ) : Logistic.Vec d :=
  if hd : 0 < d then EuclideanSpace.single ⟨0, hd⟩ teacherNorm else 0

theorem logisticTeacher_norm (teacherNorm : ℝ) (d : ℕ)
    (hr : 0 ≤ teacherNorm) (hd : 0 < d) :
    Logistic.r (logisticTeacher teacherNorm d) = teacherNorm := by
  simp [Logistic.r, logisticTeacher, hd, Real.norm_eq_abs, abs_of_nonneg hr]

/-- The fixed positive norm assumption used by the actual asymptotic fluid
corollaries is inhabited; it must be eventual because dimension zero is trivial. -/
theorem logisticTeacher_norm_eventually (teacherNorm : ℝ) (hr : 0 ≤ teacherNorm) :
    ∀ᶠ d : ℕ in atTop, Logistic.r (logisticTeacher teacherNorm d) = teacherNorm :=
  (eventually_gt_atTop 0).mono fun d hd => logisticTeacher_norm teacherNorm d hr hd

end
end SparseSGD.Examples
