import SparseSGD.Continuum.Differential

namespace SparseSGD

/-- The free second-moment energy has a nonpositive derivative whenever V is
nonnegative. Positivity of a given flow is kept as a visible prerequisite. -/
theorem free_moment_energy_antitone (delta : ℝ) (s : ℝ → Moments)
    (hd : 0 ≤ delta) (hs : IsMomentSolution delta 0 0 s)
    (hV : ∀ t, 0 ≤ t → 0 ≤ (s t).V) :
    AntitoneOn (fun t => (s t).R + delta * (s t).V) (Set.Ici 0) := by
  have hder (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt (fun t => (s t).R + delta * (s t).V)
        (-2 * delta * (s t).V) t := by
    obtain ⟨hR, hV, _⟩ := hs t ht
    have h := hR.add (hV.const_mul delta)
    rwa [freeEnergy_dissipation] at h
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
  · exact fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hder t (interior_subset ht)).deriv]
    have := hV t (interior_subset ht)
    nlinarith [mul_nonneg hd this]

theorem free_moment_risk_le_initial_energy (delta : ℝ) (s : ℝ → Moments)
    (hd : 0 ≤ delta) (hs : IsMomentSolution delta 0 0 s)
    (hV : ∀ t, 0 ≤ t → 0 ≤ (s t).V) (t : ℝ) (ht : 0 ≤ t) :
    (s t).R ≤ (s 0).R + delta * (s 0).V := by
  have h := free_moment_energy_antitone delta s hd hs hV (by simp) ht ht
  have hn := mul_nonneg hd (hV t ht)
  linarith

/-- Pathwise energy bound for the free two-coordinate oscillator. -/
theorem free_oscillator_energy_bound (delta : ℝ) (x y : ℝ → ℝ)
    (hd : 0 ≤ delta)
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (-delta * y t) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (x t - y t) t)
    (t : ℝ) (ht : 0 ≤ t) :
    x t ^ 2 + delta * y t ^ 2 ≤ x 0 ^ 2 + delta * y 0 ^ 2 := by
  have hder (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt (fun t => x t ^ 2 + delta * y t ^ 2)
        (-2 * delta * y t ^ 2) t := by
    convert ((hx t ht).pow 2).add (((hy t ht).pow 2).const_mul delta) using 1 <;> ring
  have hanti : AntitoneOn (fun t => x t ^ 2 + delta * y t ^ 2) (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hder t (interior_subset ht)).deriv]
      nlinarith [mul_nonneg hd (sq_nonneg (y t))]
  exact hanti (by simp) ht ht

end SparseSGD
