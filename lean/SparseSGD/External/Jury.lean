import SparseSGD.Discrete.Algebra

open Filter
open scoped Topology

namespace SparseSGD.External

/-- Two-dimensional Jury stability criterion, in the equivalent linear-dynamics
form (powers of the transition matrix converge to zero).

Source: Elaydi, An Introduction to Difference Equations, 3rd ed. (2005),
Theorem 2.37, as cited in manuscript Lemma L2. This is an explicit hypothesis,
not a global axiom. Applications must prove all three scalar inequalities. -/
def JuryStability : Prop :=
  ∀ F : Matrix (Fin 2) (Fin 2) ℝ,
    F.det < 1 → 0 < 1 - F.trace + F.det → 0 < 1 + F.trace + F.det →
      Tendsto (fun n : ℕ => F ^ n) atTop (𝓝 0)

theorem mean_powers_tendsto_zero (jury : JuryStability) (p : Params)
    (hb : p.beta < 1) (hw : 0 < p.w) (hceiling : p.w < 2*(1+p.beta)) :
    Tendsto (fun n : ℕ => p.meanMatrix ^ n) atTop (𝓝 0) := by
  apply jury p.meanMatrix
  · rwa [p.det_meanMatrix]
  · rw [p.det_meanMatrix]
    simp only [Params.meanMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linarith
  · rw [p.det_meanMatrix]
    simp only [Params.meanMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linarith

end SparseSGD.External
