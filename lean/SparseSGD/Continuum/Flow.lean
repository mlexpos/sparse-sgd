import SparseSGD.Continuum.Differential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

open scoped Matrix.Norms.Operator
open NormedSpace

namespace SparseSGD

noncomputable section

def homogeneousGenerator (delta u phi : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, -2 * delta, 0;
     2 * u / delta, -2, 2, 2 * phi / delta;
     1, -delta, -1, 0;
     0, 0, 0, 0]

def homogeneousInitial (s : Moments) : Fin 4 → ℝ := ![s.R, s.V, s.C, 1]

def homogeneousFlowVector (delta u phi : ℝ) (s : Moments) (t : ℝ) : Fin 4 → ℝ :=
  (NormedSpace.exp (t • homogeneousGenerator delta u phi)).mulVec (homogeneousInitial s)

def continuumFlow (delta u phi : ℝ) (s : Moments) (t : ℝ) : Moments :=
  let x := homogeneousFlowVector delta u phi s t
  ⟨x 0, x 1, x 2⟩

theorem continuumFlow_initial (delta u phi : ℝ) (s : Moments) :
    continuumFlow delta u phi s 0 = s := by
  simp [continuumFlow, homogeneousFlowVector, NormedSpace.exp_zero, homogeneousInitial]

/-- The matrix-exponential orbit satisfies the homogeneous linear equation coordinatewise. -/
theorem homogeneousFlowVector_hasDerivAt (delta u phi : ℝ) (s : Moments)
    (t : ℝ) (i : Fin 4) :
    HasDerivAt (fun t => homogeneousFlowVector delta u phi s t i)
      ((homogeneousGenerator delta u phi).mulVec
        (homogeneousFlowVector delta u phi s t) i) t := by
  let L : Matrix (Fin 4) (Fin 4) ℝ →ₗ[ℝ] ℝ :=
    (LinearMap.proj i).comp ((Matrix.mulVecBilin ℝ ℝ).flip (homogeneousInitial s))
  let A := homogeneousGenerator delta u phi
  have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' A t)
  change HasDerivAt (fun t => (NormedSpace.exp (t • A)).mulVec (homogeneousInitial s) i)
    ((A * NormedSpace.exp (t • A)).mulVec (homogeneousInitial s) i) t at h
  simpa only [A, homogeneousFlowVector, ← Matrix.mulVec_mulVec] using h

/-- The extra homogeneous coordinate stays equal to one for every real time. -/
theorem homogeneousFlowVector_fourth (delta u phi : ℝ) (s : Moments) (t : ℝ) :
    homogeneousFlowVector delta u phi s t 3 = 1 := by
  have h (t : ℝ) : HasDerivAt (fun t => homogeneousFlowVector delta u phi s t 3) 0 t := by
    simpa [homogeneousGenerator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using
      homogeneousFlowVector_hasDerivAt delta u phi s t 3
  have hc := is_const_of_deriv_eq_zero (fun t => (h t).differentiableAt)
    (fun t => (h t).deriv) t 0
  simpa [homogeneousFlowVector, homogeneousInitial, NormedSpace.exp_zero] using hc

/-- The explicit flow satisfies the affine moment equations at every real time. -/
theorem continuumFlow_hasDerivAt (delta u phi : ℝ) (s : Moments) (t : ℝ) :
    HasDerivAt (fun t => (continuumFlow delta u phi s t).R)
      (continuumField delta u phi (continuumFlow delta u phi s t)).R t ∧
    HasDerivAt (fun t => (continuumFlow delta u phi s t).V)
      (continuumField delta u phi (continuumFlow delta u phi s t)).V t ∧
    HasDerivAt (fun t => (continuumFlow delta u phi s t).C)
      (continuumField delta u phi (continuumFlow delta u phi s t)).C t := by
  have hR := homogeneousFlowVector_hasDerivAt delta u phi s t 0
  have hV := homogeneousFlowVector_hasDerivAt delta u phi s t 1
  have hC := homogeneousFlowVector_hasDerivAt delta u phi s t 2
  refine ⟨?_, ?_, ?_⟩
  · convert hR using 1 <;>
      simp [continuumFlow, continuumField, homogeneousGenerator, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
  · convert hV using 1 <;>
      (simp [continuumFlow, continuumField, homogeneousGenerator, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, homogeneousFlowVector_fourth]; try ring)
  · convert hC using 1 <;>
      (simp [continuumFlow, continuumField, homogeneousGenerator, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]; try ring)

theorem continuumFlow_isMomentSolution (delta u phi : ℝ) (s : Moments) :
    IsMomentSolution delta u phi (continuumFlow delta u phi s) := by
  intro t _
  exact continuumFlow_hasDerivAt delta u phi s t

theorem continuum_solution_exists (delta u phi : ℝ) (s : Moments) :
    ∃ f : ℝ → Moments, f 0 = s ∧ IsMomentSolution delta u phi f :=
  ⟨continuumFlow delta u phi s, continuumFlow_initial delta u phi s,
    continuumFlow_isMomentSolution delta u phi s⟩

end
end SparseSGD
