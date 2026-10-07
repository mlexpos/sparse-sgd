import SparseSGD.Logistic.V2.ActualDecomposition
import SparseSGD.Logistic.V2.RecursionTame

/-!
# Physical invariance, tracking and consistency for the actual drift map

* `AP.Model` records the model relation `rho = 1 - w p / h`, which `AP.Adm` does not;
  `AP.ofModel_model` shows that `AP.ofModel` satisfies it.
* `AP_map_physical` / `AP_iterate_physical`: the actual one-step map preserves the physical
  covariance cone `dynamicPhysical`.  The new quadratic form equals
  `Qo(α + h a γ, (1-h) γ) + h N γ²` with `γ = β - δ h α` and
  `N = κ d0 + ν y2 - h a² (1-ρ) y2`, and `N ≥ 0` by `scalar_bulk_variance_nonneg`.
* `AP_tracking_of_bound`, `AP_consistency_of_bound`: copies of the tame finite-horizon
  tracking and one-step consistency, with the residual from `AP_decomposition_phys` at
  physical orbit points.
-/

namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

/-- The model relation `rho = 1 - w p / h` (and `0 < h`) between the parameters of an `AP`. -/
def AP.Model (a : AP) : Prop := 0 < a.h ∧ a.rho = 1 - a.w * (a.p : ℝ) / a.h

/-- The parameters of the actual model satisfy the model relation. -/
theorem AP.ofModel_model (d B : ℕ) (eta beta : ℝ) (p : unitInterval)
    (hB : 0 < B) (hp : 0 < (p : ℝ)) (hbeta : 0 < 1 - beta) :
    (AP.ofModel d B eta beta p).Model := by
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  refine ⟨by simpa [AP.ofModel] using hbeta, ?_⟩
  simp only [AP.ofModel]
  field_simp

/-- Abstract one-step physical invariance: if `N = κ d0 + ν y2 - h a² (1-ρ) y2 ≥ 0`
then `y + h • increment` is physical. -/
theorem physical_step_aux (r : ℝ) (y : DynamicState) (h δ κ a b d0 ν ρ : ℝ)
    (hy : dynamicPhysical y) (hh : 0 ≤ h)
    (hN : 0 ≤ κ * d0 + ν * y 2 - h * a ^ 2 * (1 - ρ) * y 2) :
    dynamicPhysical (y + h • dynamicIncrement r (dynamicIncrementData y h δ κ a b d0 ν ρ)) := by
  have hQ := (dynamicPhysical_iff_quadratic y).1 hy
  rw [dynamicPhysical_iff_quadratic]
  intro α β
  have key := hQ (α + h * a * (β - δ * h * α)) ((1 - h) * (β - δ * h * α))
  have h2 := mul_nonneg (mul_nonneg hh hN) (sq_nonneg (β - δ * h * α))
  simp [dynamicIncrement, dynamicIncrementData]
  nlinarith [key, h2]

/-- Physical invariance of the actual one-step map (for model parameters). -/
theorem AP_map_physical (S2 : SparseSGD.External.GaussianSteinCertificate 2)
    (r deltaS PhiS : ℝ) (hr : 0 < r) (a : AP) (ha : a.Adm deltaS PhiS) (hm : a.Model)
    (y : DynamicState) (hy : dynamicPhysical y) : dynamicPhysical (a.map r y) := by
  obtain ⟨-, -, -, hw0, hwk, hp0, -, -⟩ := ha
  obtain ⟨hh, hrho⟩ := hm
  have hV := scalar_bulk_variance_nonneg S2 a.p r (y 0) (y 2) hr hy.1
  have hD := scalarCoefD0_nonneg a.p r (y 0) (y 0 ^ 2 + y 2)
  have hy2 := hy.1
  have hρ : a.h * (1 - a.rho) = a.w * (a.p : ℝ) := by
    rw [hrho]; field_simp; ring
  have hN : 0 ≤ a.kappa * actD0 a.p r y + a.w * actDt a.p r y * y 2 -
      a.h * (actA a.p r y) ^ 2 * (1 - a.rho) * y 2 := by
    have e : a.kappa * actD0 a.p r y + a.w * actDt a.p r y * y 2 -
        a.h * (actA a.p r y) ^ 2 * (1 - a.rho) * y 2 =
        (a.kappa - a.w) * actD0 a.p r y + (a.w / (a.p : ℝ)) *
          (scalarCoefD0 a.p r (y 0) (y 0 ^ 2 + y 2) + y 2 *
            (scalarCoefDtheta a.p r (y 0) (y 0 ^ 2 + y 2) -
              (scalarCoefA a.p r (y 0) (y 0 ^ 2 + y 2)) ^ 2)) := by
      have e1 : a.h * (actA a.p r y) ^ 2 * (1 - a.rho) * y 2 =
          (actA a.p r y) ^ 2 * (a.w * (a.p : ℝ)) * y 2 := by
        rw [← hρ]; ring
      rw [e1]
      simp only [actA, actD0, actDt]
      field_simp
      ring
    rw [e]
    have hd0 : 0 ≤ actD0 a.p r y := div_nonneg hD hp0.le
    exact add_nonneg (mul_nonneg (by linarith) hd0)
      (mul_nonneg (div_nonneg hw0 hp0.le) hV)
  exact physical_step_aux r y a.h a.delta a.kappa (actA a.p r y) (actB a.p r y)
    (actD0 a.p r y) (a.w * actDt a.p r y) a.rho hy hh.le (by linarith [hN])

/-- Orbits of the actual map from a physical start stay physical. -/
theorem AP_iterate_physical (S2 : SparseSGD.External.GaussianSteinCertificate 2)
    (r deltaS PhiS : ℝ) (hr : 0 < r) (a : AP) (ha : a.Adm deltaS PhiS) (hm : a.Model)
    (y : DynamicState) (hy : dynamicPhysical y) :
    ∀ k : ℕ, dynamicPhysical ((a.map r)^[k] y) := by
  intro k
  induction k with
  | zero => simpa using hy
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact AP_map_physical S2 r deltaS PhiS hr a ha hm _ ih

/-- `h ≤ varrho` for `h ≥ 0`. -/
theorem AP.h_le_varrho (deltaS PhiS : ℝ) (a : AP) (hh : 0 ≤ a.h) :
    a.h ≤ a.varrho deltaS PhiS := by
  unfold AP.varrho
  have := abs_nonneg (a.delta - deltaS); have := abs_nonneg (a.Phi - PhiS)
  have := a.p.property.1
  rw [abs_of_nonneg hh]; linarith

/-- The residual of one actual step against the Euler step is `h • err`. -/
theorem AP_step_residual (r deltaS PhiS : ℝ) (a : AP) (x : DynamicState) :
    a.map r x - (x + a.h • dynamicField r deltaS PhiS x) = a.h • a.err r deltaS PhiS x := by
  rw [AP.map_eq r deltaS PhiS a x, smul_add]; abel

/-- Finite-horizon tracking for the actual map: orbits from a physical start stay within
`CT varrho` of the ODE solution at the grid times, uniformly over admissible model parameters
with `varrho ≤ vT`. -/
theorem AP_tracking_of_bound (S2 : SparseSGD.External.GaussianSteinCertificate 2)
    (r deltaS PhiS : ℝ) (hr : 0 < r) (hd : 0 < deltaS) (hP : 0 ≤ PhiS)
    (T M0 : ℝ) (hT : 0 ≤ T) :
    ∃ CT vT : ℝ, 0 < CT ∧ 0 < vT ∧ ∀ a : AP, a.Adm deltaS PhiS → a.Model →
      a.varrho deltaS PhiS ≤ vT → ∀ (y0 : DynamicState) (y : ℝ → DynamicState),
      dynamicPhysical y0 →
      IsODESol (dynamicField r deltaS PhiS) y0 y → (∀ t ∈ Set.Icc 0 T, ‖y t‖ ≤ M0) →
      ∀ k : ℕ, (k : ℝ) * a.h ≤ T →
        ‖(a.map r)^[k] y0 - y ((k : ℝ) * a.h)‖ ≤ CT * a.varrho deltaS PhiS ∧
        ‖(a.map r)^[k] y0 - y ((k : ℝ) * a.h)‖ ≤ 1 := by
  obtain ⟨K, p0, hK0, hp0, hK⟩ := AP_decomposition_phys r deltaS PhiS hr hd hP (M0 + 1)
  obtain ⟨L, F, hF0, hLip, hFb⟩ := dynamicField_compact_bounds r deltaS PhiS (M0 + 1)
  set A : ℝ := T * (K + L * F) * Real.exp (T * L) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A + 1, min p0 (1 / (A + 1)), by linarith, lt_min hp0 (by positivity), ?_⟩
  intro a ha hm hv y0 y hy0 hy hyb k hk
  have hh : 0 ≤ a.h := hm.1.le
  have hvn := AP.varrho_nonneg deltaS PhiS a
  have hhv := AP.h_le_varrho deltaS PhiS a hh
  have hpv := AP.p_le_varrho deltaS PhiS a
  have hpp0 : (a.p : ℝ) ≤ p0 := hpv.trans (hv.trans (min_le_left _ _))
  have hv2 : a.varrho deltaS PhiS ≤ 1 / (A + 1) := hv.trans (min_le_right _ _)
  have hAv : A * a.varrho deltaS PhiS ≤ 1 := by
    have : a.varrho deltaS PhiS * (A + 1) ≤ 1 := by
      rw [le_div_iff₀ (by linarith)] at hv2; exact hv2
    nlinarith
  have hsmall : (‖(a.map r)^[0] y0 - y 0‖ + T * (K * a.varrho deltaS PhiS + (L : ℝ) * F * a.h)) *
      Real.exp (T * L) ≤ 1 := by
    have h0 : (a.map r)^[0] y0 - y 0 = 0 := by simp [hy.1]
    rw [h0, norm_zero, zero_add]
    calc T * (K * a.varrho deltaS PhiS + (L : ℝ) * F * a.h) * Real.exp (T * L)
        ≤ T * (K * a.varrho deltaS PhiS + (L : ℝ) * F * a.varrho deltaS PhiS) *
            Real.exp (T * L) := by gcongr
      _ = A * a.varrho deltaS PhiS := by rw [hA]; ring
      _ ≤ 1 := hAv
  have hphys := AP_iterate_physical S2 r deltaS PhiS hr a ha hm y0 hy0
  have hgrid := dynamic_grid_error_of_local_residual r deltaS PhiS (M0 + 1) F a.h
    (K * a.varrho deltaS PhiS) T L k (fun n => (a.map r)^[n] y0) y hh (by positivity) hF0 hk
    (fun t ht => hy.2 t ht.1)
    (fun t ht => by linarith [hyb t ht]) hLip hFb
    (fun n _ hxn => by
      have hres := AP_step_residual r deltaS PhiS a ((a.map r)^[n] y0)
      have hn : (a.map r)^[n + 1] y0 = a.map r ((a.map r)^[n] y0) :=
        Function.iterate_succ_apply' _ _ _
      show ‖(a.map r)^[n + 1] y0 -
        ((a.map r)^[n] y0 + a.h • dynamicField r deltaS PhiS ((a.map r)^[n] y0))‖ ≤ _
      rw [hn, hres, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
      exact mul_le_mul_of_nonneg_left (hK a ha hpp0 _ hxn (add_nonneg (sq_nonneg _) (hphys n).1)) hh |>.trans
        (le_of_eq (by ring)))
    (by simpa [hy.1] using hsmall)
  have := hgrid k le_rfl
  have h0 : (a.map r)^[0] y0 - y 0 = 0 := by simp [hy.1]
  have hbd : ‖(a.map r)^[k] y0 - y ((k : ℝ) * a.h)‖ ≤ A * a.varrho deltaS PhiS := by
    refine this.trans ?_
    simp only [h0, norm_zero, zero_add]
    calc T * (K * a.varrho deltaS PhiS + (L : ℝ) * F * a.h) * Real.exp (T * L)
        ≤ T * (K * a.varrho deltaS PhiS + (L : ℝ) * F * a.varrho deltaS PhiS) *
            Real.exp (T * L) := by gcongr
      _ = A * a.varrho deltaS PhiS := by rw [hA]; ring
  refine ⟨hbd.trans ?_, hbd.trans hAv⟩
  exact mul_le_mul_of_nonneg_right (by linarith) hvn

/-- One-step consistency of the actual map along physical ODE solutions (physicality of the
solution follows from `dynamicPhysical_preserved` and `hy0 : dynamicPhysical (y 0)`):
`‖y((k+1)h) - Ψ(y(kh))‖ ≤ C1 h varrho`, for `p ≤ p0`. -/
theorem AP_consistency_of_bound (r deltaS PhiS : ℝ) (hr : 0 < r) (hd : 0 < deltaS)
    (hP : 0 ≤ PhiS) (M0 : ℝ) :
    ∃ C1 p0 : ℝ, 0 ≤ C1 ∧ 0 < p0 ∧ ∀ a : AP, a.Adm deltaS PhiS → a.Model →
      (a.p : ℝ) ≤ p0 → ∀ (y : ℝ → DynamicState),
      dynamicPhysical (y 0) →
      (∀ t : ℝ, 0 ≤ t → HasDerivAt y (dynamicField r deltaS PhiS (y t)) t) →
      (∀ t : ℝ, 0 ≤ t → ‖y t‖ ≤ M0) → ∀ k : ℕ,
        ‖y (((k + 1 : ℕ) : ℝ) * a.h) - a.map r (y ((k : ℝ) * a.h))‖ ≤
          C1 * a.h * a.varrho deltaS PhiS := by
  obtain ⟨K, p0, hK0, hp0, hK⟩ := AP_decomposition_phys r deltaS PhiS hr hd hP M0
  obtain ⟨L, F, hF0, hLip, hFb⟩ := dynamicField_compact_bounds r deltaS PhiS M0
  refine ⟨L * F + K, p0, by positivity, hp0, ?_⟩
  intro a ha hm hpp0 y hy0 hy hyb k
  have hh : 0 ≤ a.h := hm.1.le
  have hvn := AP.varrho_nonneg deltaS PhiS a
  have hhv := AP.h_le_varrho deltaS PhiS a hh
  have hk0 : 0 ≤ (k : ℝ) * a.h := by positivity
  have hphys : dynamicPhysical (y ((k : ℝ) * a.h)) :=
    dynamicPhysical_preserved r deltaS PhiS 0 ((k : ℝ) * a.h) y hk0 hd hP
      (fun t ht => hy t ht.1) hy0 _ ⟨hk0, le_rfl⟩
  have heul := dynamic_ode_euler_error r deltaS PhiS M0 F ((k : ℝ) * a.h) a.h L y hh hF0
    (fun s hs => hy s (hk0.trans hs.1)) (fun s hs => hyb s (hk0.trans hs.1)) hFb hLip
  have hres := AP_step_residual r deltaS PhiS a (y ((k : ℝ) * a.h))
  have hid : y (((k + 1 : ℕ) : ℝ) * a.h) - a.map r (y ((k : ℝ) * a.h)) =
      (y ((k : ℝ) * a.h + a.h) - (y ((k : ℝ) * a.h) +
        a.h • dynamicField r deltaS PhiS (y ((k : ℝ) * a.h)))) -
        a.h • a.err r deltaS PhiS (y ((k : ℝ) * a.h)) := by
    have e1 : ((k + 1 : ℕ) : ℝ) * a.h = (k : ℝ) * a.h + a.h := by push_cast; ring
    rw [e1, ← hres]; abel
  rw [hid]
  have hb1 := hK a ha hpp0 (y ((k : ℝ) * a.h)) (hyb _ hk0) (add_nonneg (sq_nonneg _) hphys.1)
  calc _ ≤ ‖y ((k : ℝ) * a.h + a.h) - (y ((k : ℝ) * a.h) +
          a.h • dynamicField r deltaS PhiS (y ((k : ℝ) * a.h)))‖ +
        ‖a.h • a.err r deltaS PhiS (y ((k : ℝ) * a.h))‖ := norm_sub_le _ _
    _ ≤ (L : ℝ) * F * a.h ^ 2 + a.h * (K * a.varrho deltaS PhiS) := by
        refine add_le_add heul ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
        exact mul_le_mul_of_nonneg_left hb1 hh
    _ ≤ (L * F + K) * a.h * a.varrho deltaS PhiS := by
        have : (L : ℝ) * F * a.h ^ 2 ≤ (L : ℝ) * F * a.h * a.varrho deltaS PhiS := by
          rw [pow_two, ← mul_assoc]
          exact mul_le_mul_of_nonneg_left hhv (by positivity)
        nlinarith

end
end SparseSGD.Logistic.V2
