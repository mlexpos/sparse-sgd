import SparseSGD.Logistic.DynamicRank
namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 1600000

def dynamicFrozenField (r delta curvature : ℝ) (y : DynamicState) : DynamicState :=
  ![-delta*y 1,-y 1+curvature*y 0-r,-2*delta*y 4,
    -2*y 3+2*curvature*y 4,-y 4+curvature*y 2-delta*y 3]

def dynamicFrozenOscillatorField (r delta curvature : ℝ) (z : DynamicOscillatorState) : DynamicOscillatorState :=
  ![-delta*z 1,-z 1+curvature*z 0-r,-delta*z 3,-z 3+curvature*z 2]

theorem dynamicFrozenField_eq_actual (r delta : ℝ) (y : DynamicState) :
    dynamicFrozenField r delta (dynamicAlpha r y) y=dynamicField r delta 0 y := by
  ext i
  fin_cases i <;> simp [dynamicFrozenField,dynamicField]

theorem contDiff_dynamicFrozenData (r delta : ℝ) :
    ContDiff ℝ ⊤ (fun q : ℝ × DynamicState => dynamicFrozenField r delta q.1 q.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [dynamicFrozenField] <;> fun_prop

theorem hasDerivAt_dynamicFrozenRankOneLift (r delta curvature : ℝ)
    (z : ℝ → DynamicOscillatorState) (t : ℝ)
    (hz : HasDerivAt z (dynamicFrozenOscillatorField r delta curvature (z t)) t) :
    HasDerivAt (fun s => dynamicRankOneLift (z s))
      (dynamicFrozenField r delta curvature (dynamicRankOneLift (z t))) t := by
  have hc := hasDerivAt_pi.mp hz
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [dynamicRankOneLift,dynamicFrozenOscillatorField,dynamicFrozenField] using hc 0
  · simpa [dynamicRankOneLift,dynamicFrozenOscillatorField,dynamicFrozenField] using hc 1
  · convert (hc 2).pow 2 using 1
    · rfl
    · simp [dynamicRankOneLift,dynamicFrozenOscillatorField,dynamicFrozenField]
      ring
  · convert (hc 3).pow 2 using 1
    · rfl
    · simp [dynamicRankOneLift,dynamicFrozenOscillatorField,dynamicFrozenField]
      ring
  · convert (hc 2).mul (hc 3) using 1
    · rfl
    · simp [dynamicRankOneLift,dynamicFrozenOscillatorField,dynamicFrozenField]
      ring

/-- Uniqueness for the actual linear time-dependent lift field. The uniform
Lipschitz bound is derived from a smooth joint map on a compact data ball. -/
theorem dynamic_frozen_solution_unique (r delta a b A : ℝ) (curvature : ℝ → ℝ)
    (y z : ℝ → DynamicState) (hA : ∀ t ∈ Set.Icc a b, |curvature t| ≤ A)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (dynamicFrozenField r delta (curvature t) (y t)) t)
    (hz : ∀ t ∈ Set.Icc a b, HasDerivAt z (dynamicFrozenField r delta (curvature t) (z t)) t)
    (hi : y a=z a) : ∀ t ∈ Set.Icc a b, y t=z t := by
  have cy : ContinuousOn y (Set.Icc a b) := fun t ht => (hy t ht).continuousAt.continuousWithinAt
  have cz : ContinuousOn z (Set.Icc a b) := fun t ht => (hz t ht).continuousAt.continuousWithinAt
  obtain ⟨My,hMy⟩ := isCompact_Icc.exists_bound_of_continuousOn cy
  obtain ⟨Mz,hMz⟩ := isCompact_Icc.exists_bound_of_continuousOn cz
  let M := max A (max My Mz)
  obtain ⟨L,hL⟩ := (contDiff_dynamicFrozenData r delta).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall (0:ℝ × DynamicState) M) (isCompact_closedBall (0:ℝ × DynamicState) M)
  have hLip : ∀ t ∈ Set.Ico a b, LipschitzOnWith L (dynamicFrozenField r delta (curvature t))
      (Metric.closedBall (0:DynamicState) M) := by
    intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx u hu
    have htA : |curvature t| ≤ M := (hA t (Set.mem_Icc_of_Ico ht)).trans (le_max_left _ _)
    have hxM : ‖x‖ ≤ M := by simpa using hx
    have huM : ‖u‖ ≤ M := by simpa using hu
    have hm := hL.norm_sub_le
      (x:=(curvature t,x)) (y:=(curvature t,u))
      (by simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs] using max_le htA hxM)
      (by simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs] using max_le htA huM)
    simpa [dist_eq_norm,Prod.norm_def] using hm
  have hdist := dist_le_of_trajectories_ODE_of_mem (v:=fun t => dynamicFrozenField r delta (curvature t))
    (s:=fun _ => Metric.closedBall (0:DynamicState) M) (K:=L) hLip cy
    (fun t ht => (hy t (Set.mem_Icc_of_Ico ht)).hasDerivWithinAt)
    (fun t ht => by simpa [M] using ((hMy t (Set.mem_Icc_of_Ico ht)).trans ((le_max_left My Mz).trans (le_max_right A (max My Mz)))))
    cz (fun t ht => (hz t (Set.mem_Icc_of_Ico ht)).hasDerivWithinAt)
    (fun t ht => by simpa [M] using ((hMz t (Set.mem_Icc_of_Ico ht)).trans ((le_max_right My Mz).trans (le_max_right A (max My Mz)))))
    (δ:=0) (by simp [hi])
  intro t ht
  exact dist_eq_zero.mp (le_antisymm (by simpa using hdist t ht) dist_nonneg)

end
end SparseSGD.Logistic
