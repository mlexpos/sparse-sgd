import SparseSGD.Logistic.DynamicCompact
import Mathlib.Analysis.ODE.DiscreteGronwall
namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 1200000

/-- The actual smooth field has a Lipschitz constant and a speed bound on
any state ball. -/
theorem dynamicField_compact_bounds (r delta Phi M : ℝ) :
    ∃ L : ℝ≥0, ∃ F : ℝ, 0 ≤ F ∧
      LipschitzOnWith L (dynamicField r delta Phi) (Metric.closedBall 0 M) ∧
      ∀ y, ‖y‖ ≤ M → ‖dynamicField r delta Phi y‖ ≤ F := by
  obtain ⟨L,hL⟩ := (contDiff_dynamicField r delta Phi).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall 0 M) (isCompact_closedBall 0 M)
  obtain ⟨F,hF⟩ := (isCompact_closedBall (0:DynamicState) M).exists_bound_of_continuousOn
    (contDiff_dynamicField r delta Phi).continuous.continuousOn
  refine ⟨L,max F 0,le_max_right _ _,hL,?_⟩
  intro y hy
  exact (hF y (by simpa using hy)).trans (le_max_left _ _)

/-- The Euler truncation error follows from the actual ODE equation and
bounded speed on the interval; it is not postulated. -/
theorem dynamic_ode_euler_error (r delta Phi M F t h : ℝ) (L : ℝ≥0)
    (y : ℝ → DynamicState) (hh : 0 ≤ h) (hF : 0 ≤ F)
    (hy : ∀ s ∈ Set.Icc t (t+h), HasDerivAt y (dynamicField r delta Phi (y s)) s)
    (hyM : ∀ s ∈ Set.Icc t (t+h), ‖y s‖ ≤ M)
    (hb : ∀ z, ‖z‖ ≤ M → ‖dynamicField r delta Phi z‖ ≤ F)
    (hL : LipschitzOnWith L (dynamicField r delta Phi) (Metric.closedBall 0 M)) :
    ‖y (t+h)-(y t+h • dynamicField r delta Phi (y t))‖ ≤ (L:ℝ)*F*h^2 := by
  have hspeed : ∀ s ∈ Set.Icc t (t+h), ‖y s-y t‖ ≤ F*(s-t) :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs => (hy s hs).hasDerivWithinAt)
      (fun s hs => hb (y s) (hyM s (Set.mem_Icc_of_Ico hs)))
  let z := fun s => y s-(s-t) • dynamicField r delta Phi (y t)
  have hz : ∀ s ∈ Set.Icc t (t+h), HasDerivAt z
      (dynamicField r delta Phi (y s)-dynamicField r delta Phi (y t)) s := by
    intro s hs
    convert (hy s hs).sub (((hasDerivAt_id s).sub_const t).smul_const
      (dynamicField r delta Phi (y t))) using 1
    · rfl
    · simp
  have herr := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s hs => (hz s hs).hasDerivWithinAt) (C:=(L:ℝ)*F*h) (by
      intro s hs
      have hs' := Set.mem_Icc_of_Ico hs
      calc
        _ ≤ (L:ℝ)*‖y s-y t‖ := hL.norm_sub_le
          (by simpa using hyM s hs') (by simpa using hyM t ⟨le_rfl,by linarith⟩)
        _ ≤ (L:ℝ)*(F*(s-t)) := mul_le_mul_of_nonneg_left (hspeed s hs') L.coe_nonneg
        _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (by linarith [hs.2]) (mul_nonneg L.coe_nonneg hF))
    (t+h) ⟨by linarith,le_rfl⟩
  simpa [z,sub_eq_add_neg,mul_pow,pow_two,mul_assoc,add_assoc] using herr

/-- A one-step stability inequality, used for the proved actual drift
residual and the proved ODE truncation residual. -/
theorem dynamic_one_step_error (f : DynamicState → DynamicState) (h E G : ℝ)
    (L : ℝ≥0) (x z xn zn : DynamicState) (hh : 0 ≤ h)
    (hf : ‖f x-f z‖ ≤ (L:ℝ)*‖x-z‖)
    (hx : ‖xn-(x+h • f x)‖ ≤ E) (hz : ‖zn-(z+h • f z)‖ ≤ G) :
    ‖xn-zn‖ ≤ (1+h*(L:ℝ))*‖x-z‖+E+G := by
  have hid : xn-zn = (xn-(x+h • f x))+((x-z)+h • (f x-f z))+
      ((z+h • f z)-zn) := by module
  rw [hid]
  calc
    _ ≤ ‖xn-(x+h • f x)‖+‖(x-z)+h • (f x-f z)‖+‖(z+h • f z)-zn‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ E+(‖x-z‖+h*((L:ℝ)*‖x-z‖))+G := by
      have hn := (norm_add_le (x-z) (h • (f x-f z))).trans
        (add_le_add le_rfl (by simpa [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh] using
          mul_le_mul_of_nonneg_left hf hh))
      have hz' : ‖(z+h • f z)-zn‖ ≤ G := by simpa [norm_sub_rev] using hz
      exact add_le_add (add_le_add hx hn) hz'
    _ = _ := by ring

/-- Finite discrete Gronwall with a constant forcing and an explicit
finite-horizon exponential. -/
theorem dynamic_discrete_gronwall (u : ℕ → ℝ) (N : ℕ) (h J L T : ℝ)
    (hun : ∀ n ≤ N, 0 ≤ u n) (hh : 0 ≤ h) (hJ : 0 ≤ J) (hL : 0 ≤ L)
    (hu : ∀ n < N, u (n+1) ≤ (1+h*L)*u n+h*J)
    (hT : (N:ℝ)*h ≤ T) :
    ∀ n ≤ N, u n ≤ (u 0+T*J)*Real.exp (T*L) := by
  let v := fun n => u (min n N)
  have hv : ∀ n ≥ 0, v (n+1) ≤ (1+h*L)*v n+h*J := by
    intro n _
    by_cases hn : n < N
    · simpa [v,Nat.min_eq_left (Nat.le_of_lt hn),Nat.min_eq_left (Nat.succ_le_of_lt hn)] using hu n hn
    · have hn' : N ≤ n := Nat.le_of_not_gt hn
      have huN : 0 ≤ u N := hun N le_rfl
      simp only [v,Nat.min_eq_right hn',Nat.min_eq_right (hn'.trans (Nat.le_succ n))]
      have hnn := mul_nonneg (mul_nonneg hh hL) huN
      nlinarith
  have hb := discrete_gronwall (u:=v) (b:=fun _ => h*J) (c:=fun _ => h*L)
    (by simpa [v] using hun 0 (Nat.zero_le N)) hv (fun _ _ => mul_nonneg hh hL) (fun _ _ => mul_nonneg hh hJ)
  intro n hn
  have hb' := hb (n:=n) (Nat.zero_le n)
  simp [v,Nat.min_eq_left hn,Finset.sum_const] at hb'
  apply hb'.trans
  have hnt : (n:ℝ)*h ≤ T := (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hh).trans hT
  have hu0 : 0 ≤ u 0 := hun 0 (Nat.zero_le N)
  have hT0 : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) hh).trans hT
  rw [← mul_assoc,← mul_assoc] at hb'
  exact mul_le_mul (add_le_add le_rfl (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hnt hJ))
    (Real.exp_le_exp.mpr (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hnt hL))
    (Real.exp_pos _).le (add_nonneg hu0 (mul_nonneg hT0 hJ))

end
end SparseSGD.Logistic
