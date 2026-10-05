import SparseSGD.Logistic.DynamicPhysical
import SparseSGD.Logistic.DynamicField

/-! v2 prop:S, step 1: strict positivity of the Gram determinant
`Q = R V - C^2` at positive times when `Phi > 0`.  The proof uses the
integrating factor `exp(2t) Q`, whose derivative is `(2 Phi / delta) exp(2t) R`. -/
namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic Filter Topology
noncomputable section

/-- A function that vanishes on a neighbourhood of `s` has zero derivative at `s`. -/
theorem deriv_zero_of_eventually_zero {g : ℝ → ℝ} {g' s : ℝ}
    (h : HasDerivAt g g' s) (he : g =ᶠ[𝓝 s] fun _ => (0 : ℝ)) : g' = 0 :=
  h.unique ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq he)

/-- v2 prop:S (i), integrating-factor monotonicity: with `delta > 0`, `Phi >= 0`
and a physical start, `exp(2t) Q(y t)` is nondecreasing, since
`(exp(2t) Q)' = (2 Phi / delta) exp(2t) R >= 0`. -/
theorem determinant_integrating_factor_monotone (r delta Phi a b : ℝ)
    (y : ℝ → DynamicState) (hd : 0 < delta) (hPhi : 0 ≤ Phi)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hy0 : dynamicPhysical (y a)) :
    MonotoneOn (fun t => Real.exp (2 * t) * dynamicDeterminant (y t)) (Set.Icc a b) := by
  have hder : ∀ t ∈ Set.Icc a b, HasDerivAt
      (fun t => Real.exp (2 * t) * dynamicDeterminant (y t))
      (Real.exp (2 * t) * ((2 * Phi / delta) * y t 2)) t := by
    intro t ht
    have hq := hasDerivAt_dynamicDeterminant r delta Phi y t (hy t ht)
    have he : HasDerivAt (fun t : ℝ => Real.exp (2 * t)) (Real.exp (2 * t) * 2) t := by
      simpa using ((hasDerivAt_id t).const_mul 2).exp
    convert he.mul hq using 1
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
  · exact fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' := interior_subset ht
    rw [(hder t ht').deriv]
    have hab : a ≤ b := ht'.1.trans ht'.2
    have hR := (dynamicPhysical_preserved r delta Phi a b y hab hd hPhi hy hy0 t ht').1
    positivity

/-- v2 prop:S (i): `Q(y t) >= exp(-2 (t - s)) Q(y s)` for `a <= s <= t <= b`. -/
theorem determinant_lower_bound (r delta Phi a b : ℝ)
    (y : ℝ → DynamicState) (hd : 0 < delta) (hPhi : 0 ≤ Phi)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hy0 : dynamicPhysical (y a)) {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    Real.exp (-2 * (t - s)) * dynamicDeterminant (y s) ≤ dynamicDeterminant (y t) := by
  have hm := determinant_integrating_factor_monotone r delta Phi a b y hd hPhi hy hy0
    ⟨hs, hst.trans htb⟩ ⟨hs.trans hst, htb⟩ hst
  simp only at hm
  have h1 : Real.exp (2 * t) * Real.exp (-2 * (t - s)) = Real.exp (2 * s) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos := Real.exp_pos (2 * t)
  have : Real.exp (2 * t) * (Real.exp (-2 * (t - s)) * dynamicDeterminant (y s)) ≤
      Real.exp (2 * t) * dynamicDeterminant (y t) := by
    rw [← mul_assoc, h1]; exact hm
  exact le_of_mul_le_mul_left this hpos

/-- v2 prop:S (i), first step: if `Phi > 0` and the start is physical, the Gram
determinant is strictly positive at every positive time. -/
theorem determinant_pos_of_pos_time (r delta Phi T : ℝ)
    (y : ℝ → DynamicState) (hd : 0 < delta) (hPhi : 0 < Phi)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hy0 : dynamicPhysical (y 0)) :
    ∀ t ∈ Set.Ioc 0 T, 0 < dynamicDeterminant (y t) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.le.trans ht.2
  have hphys := dynamicPhysical_preserved r delta Phi 0 T y hT hd hPhi.le hy hy0
  have hQnn : ∀ s ∈ Set.Icc 0 T, 0 ≤ dynamicDeterminant (y s) := by
    intro s hs
    have := (hphys s hs).2.2
    unfold dynamicDeterminant; linarith
  by_contra hcon
  have hQt : dynamicDeterminant (y t) = 0 :=
    le_antisymm (not_lt.mp hcon) (hQnn t ⟨ht.1.le, ht.2⟩)
  have hm := determinant_integrating_factor_monotone r delta Phi 0 T y hd hPhi.le hy hy0
  -- Q vanishes on [0,t]
  have hQ0 : ∀ s ∈ Set.Icc 0 t, dynamicDeterminant (y s) = 0 := by
    intro s hs
    have h1 := hm ⟨hs.1, hs.2.trans ht.2⟩ ⟨ht.1.le, ht.2⟩ hs.2
    simp only [hQt, mul_zero] at h1
    have h2 := hQnn s ⟨hs.1, hs.2.trans ht.2⟩
    have h3 : 0 ≤ Real.exp (2 * s) * dynamicDeterminant (y s) :=
      mul_nonneg (Real.exp_pos _).le h2
    have h4 : Real.exp (2 * s) * dynamicDeterminant (y s) = 0 := le_antisymm h1 h3
    rcases mul_eq_zero.mp h4 with h | h
    · exact absurd h (Real.exp_pos _).ne'
    · exact h
  -- pick the midpoint
  set s := t / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith [ht.1]
  have hst : s < t := by linarith [ht.1]
  have hsI : s ∈ Set.Ioo 0 t := ⟨hs0, hst⟩
  have hnhds : Set.Ioo 0 t ∈ 𝓝 s := Ioo_mem_nhds hsI.1 hsI.2
  have hyI : ∀ u ∈ Set.Ioo 0 t, HasDerivAt y (dynamicField r delta Phi (y u)) u :=
    fun u hu => hy u ⟨hu.1.le, hu.2.le.trans ht.2⟩
  -- R = 0 near s
  have hR0 : ∀ u ∈ Set.Ioo 0 t, y u 2 = 0 := by
    intro u hu
    have hnu : Set.Ioo 0 t ∈ 𝓝 u := Ioo_mem_nhds hu.1 hu.2
    have hq := hasDerivAt_dynamicDeterminant r delta Phi y u (hyI u hu)
    have hz := deriv_zero_of_eventually_zero hq (by
      filter_upwards [hnu] with v hv using hQ0 v ⟨hv.1.le, hv.2.le⟩)
    rw [hQ0 u ⟨hu.1.le, hu.2.le⟩] at hz
    have : (2 * Phi / delta) * y u 2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exfalso; have : 2 * Phi / delta ≠ 0 := by positivity
      exact this h
    · exact h
  -- C = 0
  have hC0 : ∀ u ∈ Set.Ioo 0 t, y u 4 = 0 := by
    intro u hu
    have hnu : Set.Ioo 0 t ∈ 𝓝 u := Ioo_mem_nhds hu.1 hu.2
    have hc := (hasDerivAt_pi.mp (hyI u hu)) 2
    have hz := deriv_zero_of_eventually_zero hc (by
      filter_upwards [hnu] with v hv using hR0 v hv)
    simp [dynamicField] at hz
    rcases hz with h | h
    · exact absurd h hd.ne'
    · exact h
  -- V = 0
  have hV0 : ∀ u ∈ Set.Ioo 0 t, y u 3 = 0 := by
    intro u hu
    have hnu : Set.Ioo 0 t ∈ 𝓝 u := Ioo_mem_nhds hu.1 hu.2
    have hc := (hasDerivAt_pi.mp (hyI u hu)) 4
    have hz := deriv_zero_of_eventually_zero hc (by
      filter_upwards [hnu] with v hv using hC0 v hv)
    simp only [dynamicField] at hz
    simp [hR0 u hu, hC0 u hu] at hz
    rcases hz with h | h
    · exact absurd h hd.ne'
    · exact h
  -- contradiction with V' = 2 Phi / delta
  have hc := (hasDerivAt_pi.mp (hyI s hsI)) 3
  have hz := deriv_zero_of_eventually_zero hc (by
    filter_upwards [hnhds] with v hv using hV0 v hv)
  simp only [dynamicField] at hz
  simp [hV0 s hsI, hC0 s hsI] at hz
  have : 0 < 2 * Phi / delta := by positivity
  rcases hz with h | h
  · linarith
  · exact absurd h hd.ne'

/-- v2 prop:S (i): with additionally `Q(y 0) > 0`, the determinant is positive on
all of `[0, T]`. -/
theorem determinant_pos_of_pos_initial (r delta Phi T : ℝ)
    (y : ℝ → DynamicState) (hd : 0 < delta) (hPhi : 0 < Phi)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hy0 : dynamicPhysical (y 0)) (hQ0 : 0 < dynamicDeterminant (y 0)) :
    ∀ t ∈ Set.Icc 0 T, 0 < dynamicDeterminant (y t) := by
  intro t ht
  rcases ht.1.eq_or_lt with h | h
  · rw [← h]; exact hQ0
  · exact determinant_pos_of_pos_time r delta Phi T y hd hPhi hy hy0 t ⟨h, ht.2⟩

end
end SparseSGD.Logistic.V2
