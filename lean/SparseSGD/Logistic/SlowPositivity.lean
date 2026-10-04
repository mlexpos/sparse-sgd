import SparseSGD.Logistic.SlowContraction

namespace SparseSGD.Logistic
noncomputable section
open MeasureTheory
set_option maxHeartbeats 1000000

/-- Integrating factor for a scalar inhomogeneous linear equation. -/
def scalarIntegratingFactor (q : ℝ → ℝ) (a t : ℝ) : ℝ :=
  Real.exp (∫ s in a..t, q s)

theorem scalarIntegratingFactor_pos (q : ℝ → ℝ) (a t : ℝ) :
    0 < scalarIntegratingFactor q a t := Real.exp_pos _

theorem scalarIntegratingFactor_initial (q : ℝ → ℝ) (a : ℝ) :
    scalarIntegratingFactor q a a=1 := by simp [scalarIntegratingFactor]

theorem scalarIntegratingFactor_hasDerivAt (q : ℝ → ℝ) (hq : Continuous q) (a t : ℝ) :
    HasDerivAt (scalarIntegratingFactor q a) (scalarIntegratingFactor q a t*q t) t := by
  exact (intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable a t)
    hq.aestronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt).exp

theorem scalarIntegratingFactor_product_derivative (q x : ℝ → ℝ) (hq : Continuous q)
    (a c t : ℝ) (hx : HasDerivAt x (c-q t*x t) t) :
    HasDerivAt (fun t => scalarIntegratingFactor q a t*x t)
      (c*scalarIntegratingFactor q a t) t := by
  convert (scalarIntegratingFactor_hasDerivAt q hq a t).mul hx using 1
  ring

/-- Positive forcing preserves the nonnegative half-line; positive forcing
makes the solution strictly positive after any positive time. -/
theorem scalar_linear_nonneg_pos (q x : ℝ → ℝ) (hq : Continuous q) (a b c : ℝ)
    (hab : a ≤ b) (hc : 0 ≤ c) (hx0 : 0 ≤ x a)
    (hx : ∀ t ∈ Set.Icc a b, HasDerivAt x (c-q t*x t) t) :
    0 ≤ x b ∧ (0 < c → a < b → 0 < x b) := by
  let f := fun t => scalarIntegratingFactor q a t*x t
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivAt f (c*scalarIntegratingFactor q a t) t :=
    scalarIntegratingFactor_product_derivative q x hq a c t (hx t ht)
  have hcont : ContinuousOn f (Set.Icc a b) := fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hmono : MonotoneOn f (Set.Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hcont
    · intro t ht
      exact (hderiv t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact mul_nonneg hc (scalarIntegratingFactor_pos q a t).le
  have hstart : f a=x a := by simp [f,scalarIntegratingFactor_initial]
  have H := hmono ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  rw [hstart] at H
  have hxb : 0 ≤ x b := by
    have H0 : 0 ≤ scalarIntegratingFactor q a b*x b := hx0.trans H
    exact nonneg_of_mul_nonneg_right H0 (scalarIntegratingFactor_pos q a b)
  refine ⟨hxb,?_⟩
  intro hcpos habpos
  have hstrict : StrictMonoOn f (Set.Icc a b) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b) hcont
    · intro t ht
      exact (hderiv t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact mul_pos hcpos (scalarIntegratingFactor_pos q a t)
  have H := hstrict ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ habpos
  rw [hstart] at H
  have H0 : 0 < scalarIntegratingFactor q a b*x b := hx0.trans_lt H
  exact pos_of_mul_pos_right H0 (scalarIntegratingFactor_pos q a b).le

/-- Continuously extend the along-path logistic curvature to earlier times. -/
def extendedSlowCurvature (r a : ℝ) (y : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  2*alpha (y (max a t)).1 (y (max a t)).2 r

theorem extendedSlowCurvature_continuous (r Phi a : ℝ) (y : ℝ → ℝ × ℝ)
    (hy : ∀ t, a ≤ t → HasDerivAt y (slowField r Phi (y t).1 (y t).2) t) :
    Continuous (extendedSlowCurvature r a y) := by
  have hcy : ContinuousOn y (Set.Ici a) := fun t ht => (hy t ht).continuousAt.continuousWithinAt
  have hcm : Continuous (fun t => y (max a t)) := hcy.comp_continuous
    (continuous_const.max continuous_id) (fun t => le_max_left a t)
  unfold extendedSlowCurvature alpha
  exact continuous_const.mul (Real.continuous_exp.comp
    ((((hcm.fst.pow 2).add hcm.snd).sub continuous_const).div_const 2))

theorem slow_bulk_nonnegative (r Phi a : ℝ) (y : ℝ → ℝ × ℝ)
    (hPhi : 0 ≤ Phi) (hy0 : 0 ≤ (y a).2)
    (hy : ∀ t, a ≤ t → HasDerivAt y (slowField r Phi (y t).1 (y t).2) t) :
    ∀ t, a ≤ t → 0 ≤ (y t).2 ∧ (0 < Phi → a < t → 0 < (y t).2) := by
  intro t ht
  have hq := extendedSlowCurvature_continuous r Phi a y hy
  have H := scalar_linear_nonneg_pos (extendedSlowCurvature r a y) (fun s => (y s).2) hq a t (2*Phi)
    ht (by positivity) hy0 (by
      intro s hs
      have Hd : HasDerivAt (fun s => (y s).2) (slowField r Phi (y s).1 (y s).2).2 s :=
        (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt s (hy s hs.1)
      convert Hd using 1
      dsimp [extendedSlowCurvature,slowField]
      rw [max_eq_right hs.1]
      ring)
  exact ⟨H.1,fun hp hapt => H.2 (by positivity) hapt⟩

end
end SparseSGD.Logistic
