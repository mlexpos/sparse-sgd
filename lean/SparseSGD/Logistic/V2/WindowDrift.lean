import SparseSGD.Logistic.V2.WindowMapAlgebra
import SparseSGD.Logistic.V2.RecursionTame

/-! # v2 `prop:W2` (iii): the drift recursion in window coordinates

Write `h = eta eps p` (fixed) and let `eps -> 0`.  The tame drift recursion
`tameDriftMap r eps (h / eps^2) Phi 0 1` (step `eps`, `delta = h / eps^2`, coordinates
`y = (theta, m/p, R, V/p^2, C/p)`) is conjugated by the scaling
`windowScale (h / eps) y = (y0, s y1, y2, s^2 y3, s y4)`, `s = h / eps`, to the map
`windowDriftMap r h eps Phi` below, with `alpha` evaluated at the old state.
At `eps = 0` this is exactly the undamped `windowMap r h`.

Contents: the map, the scaling and its fidelity lemma `windowDriftMap_conj`, the fixed-point
identities, and convergence of fixed points as `eps -> 0` to
`windowFixedPoint theta R (h a)`, `a = exp ((theta^2 + R - r^2)/2)`.
-/
namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic Filter Topology
noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-- The tame drift recursion in window coordinates (`h = eta eps p`, damping `eps`, temperature
`Phi`); `alpha` is evaluated at the old state.  Equals `windowMap r h` at `eps = 0`. -/
def windowDriftMap (r h eps Phi : ℝ) (x : DynamicState) : DynamicState :=
  ![x 0 - ((1 - eps) * x 1 + h * (dynamicAlpha r x * x 0 - r)),
    (1 - eps) * x 1 + h * (dynamicAlpha r x * x 0 - r),
    x 2 - 2 * ((1 - eps) * x 4 + h * dynamicAlpha r x * x 2)
      + ((1 - eps) ^ 2 * x 3 + 2 * (1 - eps) * h * dynamicAlpha r x * x 4
        + h ^ 2 * dynamicAlpha r x ^ 2 * x 2 + 2 * eps * h * Phi),
    (1 - eps) ^ 2 * x 3 + 2 * (1 - eps) * h * dynamicAlpha r x * x 4
        + h ^ 2 * dynamicAlpha r x ^ 2 * x 2 + 2 * eps * h * Phi,
    (1 - eps) * x 4 + h * dynamicAlpha r x * x 2
      - ((1 - eps) ^ 2 * x 3 + 2 * (1 - eps) * h * dynamicAlpha r x * x 4
        + h ^ 2 * dynamicAlpha r x ^ 2 * x 2 + 2 * eps * h * Phi)]

/-- The window scaling `(y0, s y1, y2, s^2 y3, s y4)`. -/
def windowScale (s : ℝ) (y : DynamicState) : DynamicState :=
  ![y 0, s * y 1, y 2, s ^ 2 * y 3, s * y 4]

/-- `dynamicAlpha` only sees coordinates `0` and `2`, which the scaling fixes. -/
theorem dynamicAlpha_windowScale (r s : ℝ) (y : DynamicState) :
    dynamicAlpha r (windowScale s y) = dynamicAlpha r y := by
  simp [dynamicAlpha, windowScale]

/-- Fidelity: `windowDriftMap` is the tame drift recursion in window coordinates. -/
theorem windowDriftMap_conj (r h eps Phi : ℝ) (heps : eps ≠ 0) (y : DynamicState) :
    windowDriftMap r h eps Phi (windowScale (h / eps) y) =
      windowScale (h / eps) (tameDriftMap r eps (h / eps ^ 2) Phi 0 1 y) := by
  have hα := dynamicAlpha_windowScale r (h / eps) y
  unfold windowDriftMap
  rw [hα]
  by_cases hh : h = 0
  · subst hh
    ext i
    fin_cases i <;>
      simp [windowScale, tameDriftMap, dynamicIncrement, dynamicIncrementData]
  · ext i
    fin_cases i <;>
      simp [windowScale, tameDriftMap, dynamicIncrement, dynamicIncrementData] <;>
      field_simp <;> ring

/-- At `eps = 0` the drift map is the undamped window map. -/
theorem windowDriftMap_zero (r h Phi : ℝ) : windowDriftMap r h 0 Phi = windowMap r h := by
  funext x
  simp [windowDriftMap, windowMap]

/-- Fixed points of the drift window map: `m = 0`, `alpha theta = r`, and the `c`, `v` values. -/
theorem windowDriftMap_fixed (r h eps Phi : ℝ) (x : DynamicState) (hh : h ≠ 0) (heps : eps ≠ 2)
    (hfix : windowDriftMap r h eps Phi x = x) :
    x 1 = 0 ∧ dynamicAlpha r x * x 0 = r ∧
      x 4 = -(h * dynamicAlpha r x * x 2) / (2 - eps) ∧
      x 3 = 2 * h * dynamicAlpha r x * x 2 / (2 - eps) := by
  have h0 := congrFun hfix 0
  have h1 := congrFun hfix 1
  have h2 := congrFun hfix 2
  have h3 := congrFun hfix 3
  have h4 := congrFun hfix 4
  simp only [windowDriftMap, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2 h3 h4
  have h2e : (2 - eps) ≠ 0 := sub_ne_zero.2 (Ne.symm heps)
  have hx1 : x 1 = 0 := by linarith
  have hsig : h * (dynamicAlpha r x * x 0 - r) = 0 := by rw [hx1] at h0; linarith
  have hsig' : dynamicAlpha r x * x 0 = r := by
    rcases mul_eq_zero.1 hsig with h' | h'
    · exact absurd h' hh
    · linarith
  have hV : (1 - eps) ^ 2 * x 3 + 2 * (1 - eps) * h * dynamicAlpha r x * x 4
        + h ^ 2 * dynamicAlpha r x ^ 2 * x 2 + 2 * eps * h * Phi = x 3 := h3
  have h4' : (2 - eps) * x 4 = -(h * dynamicAlpha r x * x 2) := by
    rw [h3] at h4
    nlinarith [h2, h4, h3]
  have hx4 : x 4 = -(h * dynamicAlpha r x * x 2) / (2 - eps) := by
    field_simp; linarith
  refine ⟨hx1, hsig', hx4, ?_⟩
  -- x3 = V' = 2((1-eps) x4 + h alpha x2) from x2' = x2
  have hv2 : x 3 = 2 * ((1 - eps) * x 4 + h * dynamicAlpha r x * x 2) := by
    rw [← h3] at h2; linarith
  rw [hv2, hx4]
  field_simp
  ring

/-- `dynamicAlpha` at the window fixed point is `exp ((theta^2 + R - r^2)/2)`. -/
theorem dynamicAlpha_windowFixedPoint (r theta R w : ℝ) :
    dynamicAlpha r (windowFixedPoint theta R w) = Real.exp ((theta ^ 2 + R - r ^ 2) / 2) := by
  simp [dynamicAlpha, windowFixedPoint]

/-- Fixed points of the drift window map converge to `windowFixedPoint theta R (h a)` as
`eps -> 0`, once `theta` and `R` converge. -/
theorem windowDrift_fixedPoint_tendsto (r h theta R : ℝ) (l : Filter ℝ) (hl : l ≤ 𝓝 0)
    (Phi : ℝ → ℝ) (x : ℝ → DynamicState) (hh : h ≠ 0)
    (hfix : ∀ᶠ eps in l, windowDriftMap r h eps (Phi eps) (x eps) = x eps)
    (h0 : Tendsto (fun eps => x eps 0) l (𝓝 theta))
    (h2 : Tendsto (fun eps => x eps 2) l (𝓝 R)) :
    Tendsto x l (𝓝 (windowFixedPoint theta R
      (h * Real.exp ((theta ^ 2 + R - r ^ 2) / 2)))) := by
  set a := Real.exp ((theta ^ 2 + R - r ^ 2) / 2) with ha
  have hne : ∀ᶠ eps in l, eps ≠ 2 :=
    hl (isOpen_ne.mem_nhds (by norm_num : (0:ℝ) ≠ 2))
  have hal : Tendsto (fun eps => dynamicAlpha r (x eps)) l (𝓝 a) := by
    simp only [dynamicAlpha]
    exact (((h0.pow 2).add h2).sub_const (r ^ 2)).div_const 2 |>.rexp
  have hev := hfix.and hne
  rw [tendsto_pi_nhds]
  intro i
  fin_cases i
  · simpa [windowFixedPoint] using h0
  · have : (fun eps => x eps 1) =ᶠ[l] fun _ => (0:ℝ) := by
      filter_upwards [hev] with eps he
      exact (windowDriftMap_fixed r h eps (Phi eps) (x eps) hh he.2 he.1).1
    simpa [windowFixedPoint] using tendsto_const_nhds.congr' this.symm
  · simpa [windowFixedPoint] using h2
  · have hT : Tendsto (fun eps => 2 * h * dynamicAlpha r (x eps) * x eps 2 / (2 - eps)) l
        (𝓝 (2 * h * a * R / (2 - 0))) := by
      exact ((hal.const_mul (2 * h)).mul h2).div
        (tendsto_const_nhds.sub (tendsto_id'.2 hl)) (by norm_num)
    have : (fun eps => 2 * h * dynamicAlpha r (x eps) * x eps 2 / (2 - eps)) =ᶠ[l]
        fun eps => x eps 3 := by
      filter_upwards [hev] with eps he
      exact (windowDriftMap_fixed r h eps (Phi eps) (x eps) hh he.2 he.1).2.2.2.symm
    have := hT.congr' this
    simpa [windowFixedPoint, mul_assoc, mul_comm, mul_left_comm] using
      (by convert this using 2; ring : Tendsto (fun eps => x eps 3) l (𝓝 (h * a * R)))
  · have hT : Tendsto (fun eps => -(h * dynamicAlpha r (x eps) * x eps 2) / (2 - eps)) l
        (𝓝 (-(h * a * R) / (2 - 0))) := by
      exact ((hal.const_mul h).mul h2).neg.div
        (tendsto_const_nhds.sub (tendsto_id'.2 hl)) (by norm_num)
    have : (fun eps => -(h * dynamicAlpha r (x eps) * x eps 2) / (2 - eps)) =ᶠ[l]
        fun eps => x eps 4 := by
      filter_upwards [hev] with eps he
      exact (windowDriftMap_fixed r h eps (Phi eps) (x eps) hh he.2 he.1).2.2.1.symm
    have := hT.congr' this
    simpa [windowFixedPoint] using
      (by convert this using 2; ring : Tendsto (fun eps => x eps 4) l (𝓝 (-(h * a * R) / 2)))

/-- The limit of fixed points satisfies the signal equation `a theta = r`. -/
theorem windowDrift_fixedPoint_signal (r h theta R : ℝ) (l : Filter ℝ) [l.NeBot] (hl : l ≤ 𝓝 0)
    (Phi : ℝ → ℝ) (x : ℝ → DynamicState) (hh : h ≠ 0)
    (hfix : ∀ᶠ eps in l, windowDriftMap r h eps (Phi eps) (x eps) = x eps)
    (h0 : Tendsto (fun eps => x eps 0) l (𝓝 theta))
    (h2 : Tendsto (fun eps => x eps 2) l (𝓝 R)) :
    Real.exp ((theta ^ 2 + R - r ^ 2) / 2) * theta = r := by
  have hne : ∀ᶠ eps in l, eps ≠ 2 :=
    hl (isOpen_ne.mem_nhds (by norm_num : (0:ℝ) ≠ 2))
  have hal : Tendsto (fun eps => dynamicAlpha r (x eps)) l
      (𝓝 (Real.exp ((theta ^ 2 + R - r ^ 2) / 2))) := by
    simp only [dynamicAlpha]
    exact (((h0.pow 2).add h2).sub_const (r ^ 2)).div_const 2 |>.rexp
  have hT := hal.mul h0
  have : (fun eps => dynamicAlpha r (x eps) * x eps 0) =ᶠ[l] fun _ => r := by
    filter_upwards [hfix.and hne] with eps he
    exact (windowDriftMap_fixed r h eps (Phi eps) (x eps) hh he.2 he.1).2.1
  exact tendsto_nhds_unique (hT.congr' this) tendsto_const_nhds

end
end SparseSGD.Logistic.V2
