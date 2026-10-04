import SparseSGD.Logistic.EquilibriumAnalysis
import Mathlib.Analysis.Calculus.MeanValue

/-! The dynamic-curvature field of Proposition LR34. Coordinates are
`(theta, Y, R, V, C)`, including the two normalized momentum moments. -/
namespace SparseSGD.Logistic
noncomputable section

abbrev DynamicState := Fin 5 → ℝ

def dynamicAlpha (r : ℝ) (y : DynamicState) : ℝ :=
  Real.exp ((y 0 ^ 2 + y 2 - r ^ 2) / 2)

def dynamicField (r delta Phi : ℝ) (y : DynamicState) : DynamicState :=
  ![-delta * y 1, -y 1 + dynamicAlpha r y * y 0 - r,
    -2 * delta * y 4, -2 * y 3 + 2 * dynamicAlpha r y * y 4 + 2 * Phi / delta,
    -y 4 + dynamicAlpha r y * y 2 - delta * y 3]

def dynamicDeterminant (y : DynamicState) : ℝ := y 2 * y 3 - y 4 ^ 2

theorem contDiff_dynamicField (r delta Phi : ℝ) :
    ContDiff ℝ ⊤ (dynamicField r delta Phi) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [dynamicField, dynamicAlpha] <;> fun_prop

theorem dynamic_determinant_identity (r delta Phi : ℝ) (y : DynamicState) :
    dynamicField r delta Phi y 2 * y 3 + y 2 * dynamicField r delta Phi y 3 -
      2 * y 4 * dynamicField r delta Phi y 4 =
        -2 * dynamicDeterminant y + (2 * Phi / delta) * y 2 := by
  simp [dynamicField, dynamicDeterminant]
  ring

/-- The determinant identity is the actual derivative along any solution. -/
theorem hasDerivAt_dynamicDeterminant (r delta Phi : ℝ)
    (y : ℝ → DynamicState) (t : ℝ)
    (hy : HasDerivAt y (dynamicField r delta Phi (y t)) t) :
    HasDerivAt (fun s => dynamicDeterminant (y s))
      (-2 * dynamicDeterminant (y t) + (2 * Phi / delta) * y t 2) t := by
  have hc := hasDerivAt_pi.mp hy
  convert ((hc 2).mul (hc 3)).sub ((hc 4).pow 2) using 1
  · rfl
  · rw [← dynamic_determinant_identity r delta Phi (y t)]
    ring

/-- Multiplying the noise-free determinant by its integrating factor gives a
constant, on any closed time interval where the field equation holds. -/
theorem dynamicDeterminant_evolution (r delta a b : ℝ)
    (y : ℝ → DynamicState)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (dynamicField r delta 0 (y t)) t) :
    ∀ t ∈ Set.Icc a b,
      dynamicDeterminant (y t) = Real.exp (-2 * (t-a)) * dynamicDeterminant (y a) := by
  let f := fun t => Real.exp (2*t) * dynamicDeterminant (y t)
  have hf : ∀ t ∈ Set.Icc a b, HasDerivAt f 0 t := by
    intro t ht
    have hq := hasDerivAt_dynamicDeterminant r delta 0 y t (hy t ht)
    have he : HasDerivAt (fun t : ℝ => Real.exp (2*t)) (Real.exp (2*t)*2) t :=
      by simpa using ((hasDerivAt_id t).const_mul 2).exp
    convert he.mul hq using 1 <;> simp [f] <;> ring
  have hc := constant_of_derivWithin_zero
    (fun t ht => (hf t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hf t (Set.mem_Icc_of_Ico ht)).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc (show a < b by linarith [ht.1, ht.2])) t
        (Set.mem_Icc_of_Ico ht)))
  intro t ht
  have h := hc t ht
  change Real.exp (2*t) * dynamicDeterminant (y t) =
    Real.exp (2*a) * dynamicDeterminant (y a) at h
  have he : Real.exp (2*t) * Real.exp (-2*(t-a)) = Real.exp (2*a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (mul_left_cancel₀ (ne_of_gt (Real.exp_pos (2*t))))
  rw [h, ← mul_assoc, he]

theorem dynamic_rank_one_preserved (r delta a b : ℝ) (y : ℝ → DynamicState)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (dynamicField r delta 0 (y t)) t)
    (hzero : dynamicDeterminant (y a) = 0) :
    ∀ t ∈ Set.Icc a b, dynamicDeterminant (y t) = 0 := by
  intro t ht
  rw [dynamicDeterminant_evolution r delta a b y hy t ht, hzero, mul_zero]

abbrev DynamicOscillatorState := Fin 4 → ℝ

def dynamicRankOneLift (z : DynamicOscillatorState) : DynamicState :=
  ![z 0, z 1, z 2 ^ 2, z 3 ^ 2, z 2 * z 3]

def dynamicOscillatorField (r delta : ℝ) (z : DynamicOscillatorState) :
    DynamicOscillatorState :=
  let alpha := dynamicAlpha r (dynamicRankOneLift z)
  ![-delta*z 1, -z 1+alpha*z 0-r, -delta*z 3, -z 3+alpha*z 2]

theorem dynamicRankOneLift_determinant (z : DynamicOscillatorState) :
    dynamicDeterminant (dynamicRankOneLift z) = 0 := by
  simp [dynamicDeterminant, dynamicRankOneLift]
  ring

/-- An actual solution of the four-coordinate oscillator lifts to an actual
solution of the five-coordinate noise-free field. -/
theorem hasDerivAt_dynamicRankOneLift (r delta : ℝ)
    (z : ℝ → DynamicOscillatorState) (t : ℝ)
    (hz : HasDerivAt z (dynamicOscillatorField r delta (z t)) t) :
    HasDerivAt (fun s => dynamicRankOneLift (z s))
      (dynamicField r delta 0 (dynamicRankOneLift (z t))) t := by
  have hc := hasDerivAt_pi.mp hz
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [dynamicRankOneLift, dynamicOscillatorField, dynamicField] using hc 0
  · simpa [dynamicRankOneLift, dynamicOscillatorField, dynamicField] using hc 1
  · convert (hc 2).pow 2 using 1
    · rfl
    · simp [dynamicRankOneLift, dynamicOscillatorField, dynamicField]
      ring
  · convert (hc 3).pow 2 using 1
    · rfl
    · simp [dynamicRankOneLift, dynamicOscillatorField, dynamicField]
      ring
  · convert (hc 2).mul (hc 3) using 1
    · rfl
    · simp [dynamicRankOneLift, dynamicOscillatorField, dynamicField]
      ring

end
end SparseSGD.Logistic
