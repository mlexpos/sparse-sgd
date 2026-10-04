import SparseSGD.Continuum.Flow

namespace SparseSGD

noncomputable section

/-- At the initial time, any solution with the prescribed initial value agrees with the explicit flow. -/
theorem continuum_solution_unique_at_initial (delta u phi : ℝ) (s : Moments)
    (f : ℝ → Moments) (hf0 : f 0 = s) :
    f 0 = continuumFlow delta u phi s 0 := by
  rw [hf0, continuumFlow_initial]

/-- Lift a classical moment solution to the homogeneous four-coordinate equation. -/
theorem momentSolution_homogeneous_hasDerivAt {delta u phi : ℝ} {f : ℝ → Moments}
    (hf : IsMomentSolution delta u phi f) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t => homogeneousInitial (f t))
      ((homogeneousGenerator delta u phi).mulVec (homogeneousInitial (f t))) t := by
  obtain ⟨hR, hV, hC⟩ := hf t ht
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [homogeneousInitial, homogeneousGenerator, continuumField, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] using hR
  · convert hV using 1 <;>
      (simp [homogeneousInitial, homogeneousGenerator, continuumField, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]; try ring)
  · convert hC using 1 <;>
      (simp [homogeneousInitial, homogeneousGenerator, continuumField, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]; try ring)
  · simpa [homogeneousInitial, homogeneousGenerator, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] using (hasDerivAt_const t (1 : ℝ))

/-- Classical moment solutions with the same initial moments agree at every nonnegative time. -/
theorem momentSolution_unique {delta u phi : ℝ} {f g : ℝ → Moments}
    (hf : IsMomentSolution delta u phi f) (hg : IsMomentSolution delta u phi g)
    (h0 : f 0 = g 0) {t : ℝ} (ht : 0 ≤ t) : f t = g t := by
  let L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
    (Matrix.mulVecBilin ℝ ℝ) (homogeneousGenerator delta u phi)
  let A := L.toContinuousLinearMap
  have hf' (x : ℝ) (hx : 0 ≤ x) := momentSolution_homogeneous_hasDerivAt hf hx
  have hg' (x : ℝ) (hx : 0 ≤ x) := momentSolution_homogeneous_hasDerivAt hg hx
  have heq : Set.EqOn (fun x => homogeneousInitial (f x))
      (fun x => homogeneousInitial (g x)) (Set.Icc 0 t) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ x => A x) (s := fun _ => Set.univ) (K := ‖A‖₊)
    · intro x _
      exact A.lipschitzWith.lipschitzOnWith
    · exact fun x hx => (hf' x hx.1).continuousAt.continuousWithinAt
    · intro x hx
      exact (hf' x hx.1).hasDerivWithinAt
    · simp
    · exact fun x hx => (hg' x hx.1).continuousAt.continuousWithinAt
    · intro x hx
      exact (hg' x hx.1).hasDerivWithinAt
    · simp
    · rw [h0]
  have h := heq ⟨ht, le_rfl⟩
  apply Moments.ext
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 2

/-- The explicit matrix-exponential flow is the unique classical solution on nonnegative time. -/
theorem continuum_solution_unique (delta u phi : ℝ) (s : Moments)
    (f : ℝ → Moments) (hf0 : f 0 = s) (hf : IsMomentSolution delta u phi f)
    (t : ℝ) (ht : 0 ≤ t) : f t = continuumFlow delta u phi s t := by
  exact momentSolution_unique hf (continuumFlow_isMomentSolution delta u phi s)
    (hf0.trans (continuumFlow_initial delta u phi s).symm) ht

/-- Equality of a classical solution and the concrete flow on the full nonnegative time domain. -/
theorem continuum_solution_eqOn (delta u phi : ℝ) (s : Moments)
    (f : ℝ → Moments) (hf0 : f 0 = s) (hf : IsMomentSolution delta u phi f) :
    Set.EqOn f (continuumFlow delta u phi s) (Set.Ici 0) := by
  intro t ht
  exact continuum_solution_unique delta u phi s f hf0 hf t ht

end
end SparseSGD
