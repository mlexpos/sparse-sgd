import SparseSGD.Logistic.FluidDeterministicCoefficients
import SparseSGD.Logistic.VarianceTaylor
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

/-- Actual A, B, D0, Dtheta jets, with the two scalar differentiation orders. -/
def matchedScalarJet (i : Fin 4) (a b : ℕ) (p : unitInterval) (r t q : ℝ) : ℝ :=
  ![scalarCoefAJet a b p r t q,scalarCoefBJet a b p r t q,
    scalarCoefD0Jet a b p r t q,scalarCoefDthetaJet a b p r t q] i

theorem matchedScalarJet_signal (i : Fin 4) (a b : ℕ)
    (p : unitInterval) (r t q : ℝ) :
    HasDerivAt (fun t =>matchedScalarJet i a b p r t q)
      (matchedScalarJet i (a+1) b p r t q) t := by
  fin_cases i
  · simpa [matchedScalarJet] using scalarCoefAJet_signal a b p r t q
  · simpa [matchedScalarJet] using scalarCoefBJet_signal a b p r t q
  · simpa [matchedScalarJet] using scalarCoefD0Jet_signal a b p r t q
  · simpa [matchedScalarJet] using scalarCoefDthetaJet_signal a b p r t q

theorem matchedScalarJet_variance (S : SparseSGD.External.GaussianSteinCertificate 1)
    (i : Fin 4) (a b : ℕ) (p : unitInterval) (r t q : ℝ) (hq : 0≤q) :
    HasDerivWithinAt (fun q =>matchedScalarJet i a b p r t q)
      (matchedScalarJet i a (b+1) p r t q) (Set.Ici 0) q := by
  fin_cases i
  · simpa [matchedScalarJet] using scalarCoefAJet_variance S a b p r t q hq
  · simpa [matchedScalarJet] using scalarCoefBJet_variance S a b p r t q hq
  · simpa [matchedScalarJet] using scalarCoefD0Jet_variance S a b p r t q hq
  · simpa [matchedScalarJet] using scalarCoefDthetaJet_variance S a b p r t q hq

theorem matchedScalarJet_compact_bound (i : Fin 4) (a b : ℕ) (r Q : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (p : unitInterval) (t q : ℝ),
      0<(p:ℝ) → (p:ℝ)≤1/2 → 0≤q → q≤Q →
      |matchedScalarJet i a b p r t q|≤C*(p:ℝ) := by
  fin_cases i
  · simpa [matchedScalarJet] using scalarCoefAJet_compact_bound a b r Q
  · obtain ⟨C,hC,h⟩ := scalarCoefBJet_compact_bound a b r
    exact ⟨C,hC,fun p t q _ _ hq _ =>by simpa [matchedScalarJet] using h p t q hq⟩
  · simpa [matchedScalarJet,scalarCoefD0Jet] using scalarSquareJet_compact_bound 0 a b r Q
  · simpa [matchedScalarJet,scalarCoefDthetaJet] using scalarSquareJet_compact_bound 2 a b r Q

/-- A single compact-variance constant controls all four coefficient jets up
to order two in either variable, uniformly in probability and signal. -/
theorem matchedScalarJet_uniform_bound (r Q : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (i : Fin 4) (a b : Fin 3) (p : unitInterval) (t q : ℝ),
      0<(p:ℝ) → (p:ℝ)≤1/2 → 0≤q → q≤Q →
      |matchedScalarJet i a b p r t q|≤C*(p:ℝ) := by
  classical
  have hex (i : Fin 4) (a b : Fin 3) := matchedScalarJet_compact_bound i a b r Q
  choose C hC h using hex
  let D := ∑ i : Fin 4, ∑ a : Fin 3, ∑ b : Fin 3, C i a b
  have hD : 0≤D := Finset.sum_nonneg (fun _ _ =>Finset.sum_nonneg (fun _ _ =>Finset.sum_nonneg (fun _ _ =>hC _ _ _)))
  refine ⟨D,hD,?_⟩
  intro i a b p t q hp hh hq hQ
  apply (h i a b p t q hp hh hq hQ).trans
  apply mul_le_mul_of_nonneg_right _ p.property.1
  calc
    C i a b ≤ ∑ b : Fin 3, C i a b := Finset.single_le_sum (fun b _ =>hC i a b) (Finset.mem_univ _)
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, C i a b :=
      Finset.single_le_sum (fun a _ =>Finset.sum_nonneg (fun b _ =>hC i a b)) (Finset.mem_univ _)
    _ ≤ D := Finset.single_le_sum (fun i _ =>Finset.sum_nonneg (fun a _ =>Finset.sum_nonneg (fun b _ =>hC i a b))) (Finset.mem_univ _)

/-- Genuine two-variable coefficient Taylor estimates on closed nonnegative
variance rectangles, including the degenerate cold endpoint. -/
theorem matchedScalarJet_rectangle_taylor
    (S : SparseSGD.External.GaussianSteinCertificate 1) (r Q : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (i : Fin 4) (p : unitInterval) (t0 t1 q0 q1 : ℝ),
      0<(p:ℝ) → (p:ℝ)≤1/2 → 0≤q0 → 0≤q1 → q0≤Q → q1≤Q →
      |matchedScalarJet i 0 0 p r t1 q1-matchedScalarJet i 0 0 p r t0 q0-
        matchedScalarJet i 1 0 p r t0 q0*(t1-t0)-
        matchedScalarJet i 0 1 p r t0 q0*(q1-q0)|≤
        C*(p:ℝ)*(|t1-t0|+|q1-q0|)^2 := by
  obtain ⟨C,hC,h⟩ := matchedScalarJet_uniform_bound r Q
  refine ⟨C,hC,?_⟩
  intro i p t0 t1 q0 q1 hp hh hq0 hq1 hQ0 hQ1
  have hrect (q : ℝ) (hq : q∈Set.uIcc q0 q1) : 0≤q ∧ q≤Q := by
    rcases Set.mem_uIcc.mp hq with hq|hq <;> constructor <;> linarith
  have hsub : Set.uIcc q0 q1 ⊆ Set.Ici 0 := fun q hq =>(hrect q hq).1
  apply rectangle_taylor_bound (matchedScalarJet i 0 0 p r) (matchedScalarJet i 1 0 p r)
    (matchedScalarJet i 0 1 p r) (matchedScalarJet i 2 0 p r)
    (matchedScalarJet i 1 1 p r) (matchedScalarJet i 0 2 p r)
    t0 t1 q0 q1 (C*(p:ℝ)) (mul_nonneg hC p.property.1)
  · intro t ht q hq; exact (matchedScalarJet_signal i 0 0 p r t q).hasDerivWithinAt
  · intro q hq; exact (matchedScalarJet_variance S i 0 0 p r t0 q (hrect q hq).1).mono hsub
  · intro t ht q hq; exact (matchedScalarJet_signal i 1 0 p r t q).hasDerivWithinAt
  · intro q hq; exact (matchedScalarJet_variance S i 1 0 p r t0 q (hrect q hq).1).mono hsub
  · intro q hq; exact (matchedScalarJet_variance S i 0 1 p r t0 q (hrect q hq).1).mono hsub
  · intro t ht q hq; exact h i 2 0 p t q hp hh (hrect q hq).1 (hrect q hq).2
  · intro q hq; exact h i 1 1 p t0 q hp hh (hrect q hq).1 (hrect q hq).2
  · intro q hq; exact h i 0 2 p t0 q hp hh (hrect q hq).1 (hrect q hq).2
end
end SparseSGD.Logistic
