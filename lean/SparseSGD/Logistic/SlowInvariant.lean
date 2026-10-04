import SparseSGD.Logistic.SlowGlobal

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1000000

/-- Constant-barrier comparison, retaining the initial value if it exceeds the barrier. -/
theorem scalar_dissipation_max_bound (x x' : ℝ → ℝ) (c L a b : ℝ)
    (hc : 0 < c) (hab : a ≤ b)
    (hx : ∀ t ∈ Set.Icc a b, HasDerivAt x (x' t) t)
    (hbound : ∀ t ∈ Set.Icc a b, x' t ≤ -c*(x t-L)) :
    x b ≤ max (x a) L := by
  have H := scalar_dissipation_bound (fun t => x t-L) x' c a b
    (fun t ht => (hx t ht).sub_const L) hbound hab
  have he0 := (Real.exp_pos (-c*(b-a))).le
  have he1 : Real.exp (-c*(b-a)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hM0 : 0 ≤ max (x a) L-L := sub_nonneg.mpr (le_max_right _ _)
  have hMa : x a-L ≤ max (x a) L-L := by linarith [le_max_left (x a) L]
  have H1 := mul_le_mul_of_nonneg_left hMa he0
  have H2 := mul_le_mul_of_nonneg_right he1 hM0
  linarith

theorem slow_signal_nonnegative (r Phi a : ℝ) (y : ℝ → ℝ × ℝ)
    (hr : 0 ≤ r) (hy0 : 0 ≤ (y a).1)
    (hy : ∀ t, a ≤ t → HasDerivAt y (slowField r Phi (y t).1 (y t).2) t) :
    ∀ t, a ≤ t → 0 ≤ (y t).1 := by
  intro t ht
  have hq := (extendedSlowCurvature_continuous r Phi a y hy).div_const 2
  have H := scalar_linear_nonneg_pos (fun s => extendedSlowCurvature r a y s/2)
    (fun s => (y s).1) hq a t r ht hr hy0 (by
      intro s hs
      have Hd : HasDerivAt (fun s => (y s).1) (slowField r Phi (y s).1 (y s).2).1 s :=
        (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt s (hy s hs.1)
      convert Hd using 1
      dsimp [extendedSlowCurvature,slowField]
      rw [max_eq_right hs.1]
      ring)
  exact H.1

/-- The source's invariant rectangle, with its exponential constants written
as reciprocals of the positive lower curvature. -/
theorem slow_invariant_rectangle (r Phi a : ℝ) (y : ℝ → ℝ × ℝ)
    (hr : 0 ≤ r) (hPhi : 0 ≤ Phi) (htheta0 : 0 ≤ (y a).1) (hR0 : 0 ≤ (y a).2)
    (hy : ∀ t, a ≤ t → HasDerivAt y (slowField r Phi (y t).1 (y t).2) t) :
    ∀ t, a ≤ t →
      0 ≤ (y t).1 ∧ (y t).1 ≤ max (y a).1 (r/Real.exp (-r^2/2)) ∧
      0 ≤ (y t).2 ∧ (y t).2 ≤ max (y a).2 (Phi/Real.exp (-r^2/2)) := by
  have htheta := slow_signal_nonnegative r Phi a y hr htheta0 hy
  have hR := slow_bulk_nonnegative r Phi a y hPhi hR0 hy
  let c := Real.exp (-r^2/2)
  have hc : 0 < c := Real.exp_pos _
  have halpha (t : ℝ) (ht : a ≤ t) : c ≤ alpha (y t).1 (y t).2 r := by
    apply Real.exp_le_exp.mpr
    nlinarith [(hR t ht).1,sq_nonneg (y t).1]
  intro t ht
  refine ⟨htheta t ht,?_,(hR t ht).1,?_⟩
  · apply scalar_dissipation_max_bound (fun s => (y s).1)
      (fun s => r-alpha (y s).1 (y s).2 r*(y s).1) c (r/c) a t hc ht
    · intro s hs
      exact (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt s (hy s hs.1)
    · intro s hs
      have H := mul_le_mul_of_nonneg_right (halpha s hs.1) (htheta s hs.1)
      have hid : c*(r/c)=r := by field_simp
      nlinarith only [H,hid]
  · apply scalar_dissipation_max_bound (fun s => (y s).2)
      (fun s => 2*(Phi-alpha (y s).1 (y s).2 r*(y s).2)) (2*c) (Phi/c) a t (by positivity) ht
    · intro s hs
      exact (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt s (hy s hs.1)
    · intro s hs
      have H := mul_le_mul_of_nonneg_right (halpha s hs.1) (hR s hs.1).1
      have hid : c*(Phi/c)=Phi := by field_simp
      nlinarith only [H,hid]

end
end SparseSGD.Logistic
