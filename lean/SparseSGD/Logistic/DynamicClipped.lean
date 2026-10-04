import SparseSGD.Logistic.DynamicEuler
import SparseSGD.Logistic.SlowLimitExistence

namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 1600000

def dynamicBoxClamp (M : ℝ) (y : DynamicState) : DynamicState :=
  fun i => max (-M) (min M (y i))

theorem dynamicBoxClamp_lipschitz (M : ℝ) : LipschitzWith 1 (dynamicBoxClamp M) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x-y))).2
  intro i
  have hc : LipschitzWith 1 (fun t : ℝ => max (-M) (min M t)) :=
    (LipschitzWith.id.const_min M).const_max (-M)
  have h := hc.norm_sub_le (x i) (y i)
  simp only [NNReal.coe_one,one_mul] at h
  exact h.trans (by simpa only [Pi.sub_apply] using norm_le_pi_norm (x-y) i)

theorem dynamicBoxClamp_norm_bound (M : ℝ) (hM : 0 ≤ M) (y : DynamicState) :
    ‖dynamicBoxClamp M y‖ ≤ M := by
  apply (pi_norm_le_iff_of_nonneg hM).2
  intro i
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩

theorem dynamicBoxClamp_eq (M : ℝ) (y : DynamicState) (hy : ‖y‖ ≤ M) :
    dynamicBoxClamp M y=y := by
  ext i
  have hi : |y i| ≤ M := by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y i).trans hy
  simp [dynamicBoxClamp,min_eq_right (abs_le.mp hi).2,max_eq_right (abs_le.mp hi).1]

/-- A bounded extension of the actual dynamic-alpha field has a global
solution. The energy bootstrap later proves this extension is never used
on any prescribed finite physical interval. -/
theorem dynamic_clipped_solution_exists (r delta Phi M : ℝ) (hM : 0 ≤ M) (y0 : DynamicState) :
    ∃ y : ℝ → DynamicState, y 0=y0 ∧ ∀ t,
      HasDerivAt y (dynamicField r delta Phi (dynamicBoxClamp M (y t))) t := by
  obtain ⟨L,F,hF,hLip,hBound⟩ := dynamicField_compact_bounds r delta Phi M
  let f := fun y => dynamicField r delta Phi (dynamicBoxClamp M y)
  have hfLip : LipschitzWith L f := by
    apply LipschitzWith.of_dist_le_mul
    intro x z
    have hm := hLip.norm_sub_le (by simpa using dynamicBoxClamp_norm_bound M hM x)
      (by simpa using dynamicBoxClamp_norm_bound M hM z)
    have hc := (dynamicBoxClamp_lipschitz M).norm_sub_le x z
    simp only [NNReal.coe_one,one_mul] at hc
    have hb := mul_le_mul_of_nonneg_left hc L.coe_nonneg
    simpa only [f,dist_eq_norm] using hm.trans hb
  exact bounded_lipschitz_ode_global (fun _ => f) y0 L F hF
    (fun _ y => hBound _ (dynamicBoxClamp_norm_bound M hM y)) (fun _ => hfLip) (fun _ => continuous_const)

end
end SparseSGD.Logistic
