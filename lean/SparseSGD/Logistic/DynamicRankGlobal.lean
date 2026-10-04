import SparseSGD.Logistic.DynamicLinearBulk
import SparseSGD.Logistic.DynamicFrozen
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000

/-- Full-interval oscillator existence for the actual dynamic-alpha solution.
The bulk oscillator is first solved with the reference curvature as a linear
coefficient. Uniqueness of the resulting second-moment equations then proves
that its lift is exactly the given solution on the entire interval. -/
theorem dynamic_rank_one_full_interval_oscillator (r delta a b : ℝ)
    (y : ℝ → DynamicState) (hab : a ≤ b)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (dynamicField r delta 0 (y t)) t)
    (hR : 0 ≤ y a 2) (hV : 0 ≤ y a 3) (hQ : dynamicDeterminant (y a)=0) :
    ∃ z : ℝ → DynamicOscillatorState,
      (∀ t ∈ Set.Icc a b, HasDerivAt z (dynamicOscillatorField r delta (z t)) t) ∧
      ∀ t ∈ Set.Icc a b, dynamicRankOneLift (z t)=y t := by
  have cy : ContinuousOn y (Set.Icc a b) := fun t ht => (hy t ht).continuousAt.continuousWithinAt
  have calpha : Continuous (dynamicAlpha r) := by unfold dynamicAlpha; fun_prop
  let clamp := fun t : ℝ => max a (min b t)
  have hclamp : Continuous clamp := by dsimp [clamp]; fun_prop
  have hmem : ∀ t, clamp t ∈ Set.Icc a b := by
    intro t
    exact ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩
  have heq : ∀ t ∈ Set.Icc a b, clamp t=t := by
    intro t ht
    simp [clamp,min_eq_right ht.2,max_eq_right ht.1]
  let curvature := fun t => dynamicAlpha r (y (clamp t))
  have hcurv : Continuous curvature := calpha.comp (cy.comp_continuous hclamp hmem)
  obtain ⟨A0,hA0⟩ := isCompact_Icc.exists_bound_of_continuousOn (calpha.comp_continuousOn cy)
  let A := max A0 0
  have hA : 0 ≤ A := le_max_right _ _
  have hcurvA : ∀ t, |curvature t| ≤ A := by
    intro t
    exact (hA0 (clamp t) (hmem t)).trans (le_max_left _ _)
  have hcurveq : ∀ t ∈ Set.Icc a b, curvature t=dynamicAlpha r (y t) := by
    intro t ht
    dsimp [curvature]
    rw [heq t ht]
  obtain ⟨z0,hz0⟩ := dynamic_rank_one_factorization (y a) hR hV hQ
  let s0 : ℝ × ℝ := (z0 2,z0 3)
  obtain ⟨s,hs0,hs⟩ := dynamic_linear_bulk_exists delta a b A curvature s0 hab hA hcurv hcurvA
  let z := fun t => (![y t 0,y t 1,(s t).1,(s t).2] : DynamicOscillatorState)
  have hz : ∀ t ∈ Set.Icc a b, HasDerivAt z (dynamicFrozenOscillatorField r delta (curvature t) (z t)) t := by
    intro t ht
    have hdy := hasDerivAt_pi.mp (hy t ht)
    have hd1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hs t ht)
    have hd2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hs t ht)
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [z,dynamicFrozenOscillatorField,dynamicField] using hdy 0
    · simpa [z,dynamicFrozenOscillatorField,dynamicField,hcurveq t ht] using hdy 1
    · simpa [z,dynamicFrozenOscillatorField,dynamicLinearBulkField,Function.comp_def] using hd1
    · simpa [z,dynamicFrozenOscillatorField,dynamicLinearBulkField,Function.comp_def] using hd2
  have hza : dynamicRankOneLift (z a)=y a := by
    have h0 := congrFun hz0 0
    have h1 := congrFun hz0 1
    have h2 := congrFun hz0 2
    have h3 := congrFun hz0 3
    have h4 := congrFun hz0 4
    ext i
    fin_cases i <;> simp [z,dynamicRankOneLift,hs0,s0] at h0 h1 h2 h3 h4 ⊢
    · exact h2
    · exact h3
    · exact h4
  have hid : ∀ t ∈ Set.Icc a b, y t=dynamicRankOneLift (z t) := by
    apply dynamic_frozen_solution_unique r delta a b A curvature y (fun t => dynamicRankOneLift (z t))
      (fun t ht => hcurvA t)
      (fun t ht => by rw [hcurveq t ht,dynamicFrozenField_eq_actual]; exact hy t ht)
      (fun t ht => hasDerivAt_dynamicFrozenRankOneLift r delta (curvature t) z t (hz t ht)) hza.symm
  refine ⟨z,?_,fun t ht => (hid t ht).symm⟩
  intro t ht
  have hceq : curvature t=dynamicAlpha r (dynamicRankOneLift (z t)) := by
    rw [← hid t ht]
    exact hcurveq t ht
  convert hz t ht using 1
  ext i
  fin_cases i <;> simp [dynamicFrozenOscillatorField,dynamicOscillatorField,hceq]


/-- The full-interval scalar oscillator coordinates asserted in LR34. -/
theorem dynamic_rank_one_full_interval_coordinates (r delta a b : ℝ)
    (y : ℝ → DynamicState) (hab : a ≤ b)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (dynamicField r delta 0 (y t)) t)
    (hR : 0 ≤ y a 2) (hV : 0 ≤ y a 3) (hQ : dynamicDeterminant (y a)=0) :
    ∃ X P : ℝ → ℝ, ∀ t ∈ Set.Icc a b,
      y t 2=(X t)^2 ∧ y t 3=(P t)^2 ∧ y t 4=X t*P t ∧
      HasDerivAt X (-delta*P t) t ∧ HasDerivAt P (-P t+dynamicAlpha r (y t)*X t) t := by
  obtain ⟨z,hz,hlift⟩ := dynamic_rank_one_full_interval_oscillator r delta a b y hab hy hR hV hQ
  refine ⟨fun t => z t 2,fun t => z t 3,?_⟩
  intro t ht
  have h2 := congrFun (hlift t ht) 2
  have h3 := congrFun (hlift t ht) 3
  have h4 := congrFun (hlift t ht) 4
  have hd := hasDerivAt_pi.mp (hz t ht)
  have hd2 := hd 2
  have hd3 := hd 3
  refine ⟨by simpa [dynamicRankOneLift] using h2.symm,
    by simpa [dynamicRankOneLift] using h3.symm,
    by simpa [dynamicRankOneLift] using h4.symm,?_,?_⟩
  · simpa [dynamicOscillatorField] using hd2
  · simpa [dynamicOscillatorField,hlift t ht] using hd3

end
end SparseSGD.Logistic
