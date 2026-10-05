import Mathlib
import SparseSGD.Scaling.Helps.StepSpectrum
import SparseSGD.Scaling.Helps.SmallDeltaSlowRoot
import SparseSGD.Scaling.Helps.SmallDeltaFactor
import SparseSGD.Scaling.Helps.Limits

/-!
# `lem:small_delta`: the per-step rate for small `ε, Δ` (v2)

Formalizes `lem:small_delta` of `paper/appendix/momentum_helps.tex`: for `ε, Δ ≤ 1/50`,
`Λ = 2 η p (1-u)(1+ϑ)` with `|ϑ| ≤ 25(ε+Δ)`, where `η p = ε Δ`.

Proof structure (as in the tex):

* the step cubic `q` of `lem:step_spectrum` has coefficients `a2 = 3 + ε b₂`, `a1 = 2 + 4Δ + ε b₁`,
  `a0 = 2Δ(2-ε)(1-u)` in the ranges required by the slow-root bracket (`smallA*`,
  `small_coeff_bounds`);
* the slow root `z_s` of `q` gives the spectral radius `1 + ε z_s` of the step map
  (`small_delta_root`), and `z_s = -(a0/a1)(1+ϑ₁)` with `|ϑ₁| ≤ 4 a0 ≤ 16 Δ`;
* `Λ = -log(1 + ε z_s) = ε |z_s| (1+ϑ₂)` with `0 ≤ ϑ₂ ≤ ε` (`small_delta_theta2`);
* `a0/a1 = 2Δ(1-u)(1+ϑ₃)` with `|ϑ₃| ≤ 3(ε+Δ)` (`small_delta_ratio`);
* the three factors multiply to `1+ϑ` with `|ϑ| ≤ 25(ε+Δ)` (`small_delta_prod_bound`).

The least-squares form is `lsRate_small_delta`.
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD SparseSGD.Probability.LeastSquares MeasureTheory

noncomputable section

/-- The `z²` coefficient `a2 = 3 + ε b₂` of the step cubic `q`. -/
def smallA2 (eps Delta u : ℝ) : ℝ := 3 + eps * spectrumB2 eps Delta u

/-- The `z` coefficient `a1 = 2 + 4Δ + ε b₁` of the step cubic `q`. -/
def smallA1 (eps Delta u : ℝ) : ℝ := 2 + 4 * Delta + eps * spectrumB1 eps Delta u

/-- The constant coefficient `a0 = 2Δ(2-ε)(1-u)` of the step cubic `q`. -/
def smallA0 (eps Delta u : ℝ) : ℝ := 2 * Delta * (2 - eps) * (1 - u)

theorem spectrumQ_eq_small (eps Delta u : ℝ) (z : ℂ) :
    spectrumQ eps Delta u z = z ^ 3 + (smallA2 eps Delta u : ℂ) * z ^ 2
      + (smallA1 eps Delta u : ℂ) * z + (smallA0 eps Delta u : ℂ) := rfl

/-- v2 `lem:small_delta` (coefficient ranges): for `0 < ε, Δ ≤ 1/50` and `0 ≤ u < 1`,
`|a2 - 3| ≤ 0.024`, `a1 ∈ [1.97, 2.11]`, `0 < a0 ≤ 4Δ ≤ 0.08`. -/
theorem small_coeff_bounds {eps Delta u : ℝ} (he0 : 0 < eps) (he : eps ≤ 1 / 50)
    (hD0 : 0 < Delta) (hD : Delta ≤ 1 / 50) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    |smallA2 eps Delta u - 3| ≤ 0.024 ∧ 1.97 ≤ smallA1 eps Delta u ∧
      smallA1 eps Delta u ≤ 2.11 ∧ 0 < smallA0 eps Delta u ∧
      smallA0 eps Delta u ≤ 4 * Delta ∧ smallA0 eps Delta u ≤ 0.08 := by
  obtain ⟨h1, h2⟩ := abs_spectrumB_le_small he0 he hD0.le hD hu0 hu1.le
  obtain ⟨h1l, h1u⟩ := abs_le.1 h1
  obtain ⟨h2l, h2u⟩ := abs_le.1 h2
  have e1u : eps * spectrumB1 eps Delta u ≤ eps * 1.17 := mul_le_mul_of_nonneg_left h1u he0.le
  have e1l : eps * (-1.17) ≤ eps * spectrumB1 eps Delta u := mul_le_mul_of_nonneg_left h1l he0.le
  have e2u : eps * spectrumB2 eps Delta u ≤ eps * 1.17 := mul_le_mul_of_nonneg_left h2u he0.le
  have e2l : eps * (-1.17) ≤ eps * spectrumB2 eps Delta u := mul_le_mul_of_nonneg_left h2l he0.le
  have hk : (2 - eps) * (1 - u) ≤ 2 := by nlinarith
  have hpos : 0 < (2 - eps) * (1 - u) := mul_pos (by linarith) (by linarith)
  have hA0 : smallA0 eps Delta u = 2 * Delta * ((2 - eps) * (1 - u)) := by
    unfold smallA0; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold smallA2
    rw [abs_le]
    constructor <;> nlinarith
  · unfold smallA1; nlinarith
  · unfold smallA1; nlinarith
  · rw [hA0]; positivity
  · rw [hA0]; nlinarith
  · rw [hA0]; nlinarith

/-- v2 `lem:small_delta` (slow root and spectral radius): for `0 < ε, Δ ≤ 1/50`, `0 ≤ u_n`,
`u = u_n + ε²Δ/(2(2-ε)) < 1` and arbitrary additive part `a`, the slow root `z_s ∈ (-0.06, 0)`
of `spectrumQ ε Δ u` is the maximiser of `‖1 + ε z‖`: `stepRadius ⟨1-ε, ε²Δ, u_n, a⟩ = 1 + ε z_s`,
and `z_s = -(a0/a1)(1+ϑ₁)` with `|ϑ₁| ≤ 4 a0`. -/
theorem small_delta_root {eps Delta un a u : ℝ} (he0 : 0 < eps) (he : eps ≤ 1 / 50)
    (hD0 : 0 < Delta) (hD : Delta ≤ 1 / 50) (hun : 0 ≤ un)
    (hu : u = un + eps ^ 2 * Delta / (2 * (2 - eps))) (hu1 : u < 1) :
    ∃ zs : ℝ, spectrumQ eps Delta u (zs : ℂ) = 0 ∧ -0.06 < zs ∧ zs < 0 ∧
      stepRadius (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params) = 1 + eps * zs ∧
      ∃ ϑ1 : ℝ, zs = -(smallA0 eps Delta u / smallA1 eps Delta u) * (1 + ϑ1) ∧
        |ϑ1| ≤ 4 * smallA0 eps Delta u := by
  have hfrac : 0 ≤ eps ^ 2 * Delta / (2 * (2 - eps)) :=
    div_nonneg (by positivity) (by linarith)
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  obtain ⟨h2, h1l, h1u, h0, h0t, h0u⟩ := small_coeff_bounds he0 he hD0 hD hu0 hu1
  obtain ⟨zs, hroot, hz1, hz2, ϑ1, hzϑ, hϑ⟩ :=
    exists_slowRoot_full (a2 := smallA2 eps Delta u) (a1 := smallA1 eps Delta u)
      (a0 := smallA0 eps Delta u) h2 h1l h1u h0 h0u
  have hzsC : (zs : ℂ) ^ 3 + (smallA2 eps Delta u : ℂ) * (zs : ℂ) ^ 2
      + (smallA1 eps Delta u : ℂ) * (zs : ℂ) + (smallA0 eps Delta u : ℂ) = 0 := hroot
  have hzs : zs ^ 3 + smallA2 eps Delta u * zs ^ 2 + smallA1 eps Delta u * zs
      + smallA0 eps Delta u = 0 := by exact_mod_cast hzsC
  have hq0 : spectrumQ eps Delta u (zs : ℂ) = 0 := by rw [spectrumQ_eq_small]; exact hzsC
  obtain ⟨_, ⟨hpos, _⟩, hmax⟩ := eigenvalue_max (smallA2 eps Delta u) (smallA1 eps Delta u)
    (smallA0 eps Delta u) zs h2 h1l h1u h0 h0u hzs hz1.le hz2.le eps he0 he
  have he2 : eps ≠ 2 := by intro h; linarith
  have hrad : stepRadius (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params) = 1 + eps * zs := by
    apply le_antisymm
    · obtain ⟨z, hz, hn⟩ := stepRadius_attained (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params)
      obtain ⟨mu, hmu, rfl⟩ := (mem_stepRoots_iff_spectrumQ eps Delta un a u he0.ne' he2 hu z).1 hz
      rw [← hn]
      refine hmax mu ?_
      show mu ^ 3 + (smallA2 eps Delta u : ℂ) * mu ^ 2 + (smallA1 eps Delta u : ℂ) * mu
        + (smallA0 eps Delta u : ℂ) = 0
      rw [← spectrumQ_eq_small]; exact hmu
    · have hmem : (((1 + eps * zs : ℝ)) : ℂ) ∈
          stepRoots (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params) := by
        refine (mem_stepRoots_iff_spectrumQ eps Delta un a u he0.ne' he2 hu _).2
          ⟨(zs : ℂ), hq0, ?_⟩
        push_cast; ring
      have := norm_le_stepRadius (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params) hmem
      rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at this
  exact ⟨zs, hq0, hz1, hz2, hrad, ϑ1, hzϑ, hϑ⟩

/-- v2 `lem:small_delta` (logarithm step): if the spectral radius is `1 + ε z_s` with
`z_s ∈ (-0.06, 0)` and `0 < ε ≤ 1/50`, then `Λ = ε |z_s| (1+ϑ₂)` with `0 ≤ ϑ₂ ≤ ε`. -/
theorem small_delta_theta2 {eps zs : ℝ} {P : Params} (he0 : 0 < eps) (he : eps ≤ 1 / 50)
    (hz1 : -0.06 < zs) (hz2 : zs < 0) (hP : stepRadius P = 1 + eps * zs) :
    ∃ ϑ2 : ℝ, 0 ≤ ϑ2 ∧ ϑ2 ≤ eps ∧ perStepRate P = eps * |zs| * (1 + ϑ2) := by
  set x : ℝ := -(eps * zs) with hx
  have hxpos : 0 < x := by rw [hx]; nlinarith
  have hxle : x ≤ 0.06 * eps := by rw [hx]; nlinarith
  have hx1 : x < 1 := by nlinarith
  have habs : eps * |zs| = x := by rw [abs_of_neg hz2, hx]; ring
  have hL : perStepRate P = -Real.log (1 - x) := by
    unfold perStepRate; rw [hP]
    congr 2; rw [hx]; ring
  have hge := neg_log_one_sub_ge hx1
  have hle := neg_log_one_sub_le hx1
  have h1x : 0 < 1 - x := by linarith
  refine ⟨perStepRate P / x - 1, ?_, ?_, ?_⟩
  · rw [hL]
    have : 1 ≤ -Real.log (1 - x) / x := by rw [le_div_iff₀ hxpos]; linarith
    linarith
  · rw [hL]
    have h3 : x / (1 - x) ≤ x * (1 + eps) := by
      rw [div_le_iff₀ h1x]
      have h4 : 1 ≤ (1 + eps) * (1 - x) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h4 hxpos.le]
    have : -Real.log (1 - x) / x ≤ 1 + eps := by
      rw [div_le_iff₀ hxpos]; linarith
    linarith
  · rw [habs]
    field_simp
    ring

/-- v2 `lem:small_delta` (ratio step): `a0/a1 = 2Δ(1-u)(1+ϑ₃)` with `|ϑ₃| ≤ 3(ε+Δ)`. -/
theorem small_delta_ratio {eps Delta u : ℝ} (he0 : 0 < eps) (he : eps ≤ 1 / 50)
    (hD0 : 0 < Delta) (hD : Delta ≤ 1 / 50) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ ϑ3 : ℝ, smallA0 eps Delta u / smallA1 eps Delta u = 2 * Delta * (1 - u) * (1 + ϑ3) ∧
      |ϑ3| ≤ 3 * (eps + Delta) := by
  obtain ⟨_, h1l, h1u, _⟩ := small_coeff_bounds he0 he hD0 hD hu0 hu1
  obtain ⟨h1, _⟩ := abs_spectrumB_le_small he0 he hD0.le hD hu0 hu1.le
  obtain ⟨h1l', h1u'⟩ := abs_le.1 h1
  have e1u : eps * spectrumB1 eps Delta u ≤ eps * 1.17 := mul_le_mul_of_nonneg_left h1u' he0.le
  have e1l : eps * (-1.17) ≤ eps * spectrumB1 eps Delta u := mul_le_mul_of_nonneg_left h1l' he0.le
  have ha1 : 0 < smallA1 eps Delta u := by linarith
  refine ⟨(2 - eps) / smallA1 eps Delta u - 1, ?_, ?_⟩
  · unfold smallA0
    field_simp
    ring
  · have hnum : 2 - eps - smallA1 eps Delta u = -eps - 4 * Delta - eps * spectrumB1 eps Delta u := by
      unfold smallA1; ring
    have heq : (2 - eps) / smallA1 eps Delta u - 1
        = (2 - eps - smallA1 eps Delta u) / smallA1 eps Delta u := by
      field_simp
    rw [heq, abs_div, abs_of_pos ha1, div_le_iff₀ ha1, hnum, abs_le]
    constructor <;> nlinarith

/-- Elementary product bound: constants for `(1+ϑ₁)(1+ϑ₂)(1+ϑ₃) - 1` in `lem:small_delta`. -/
theorem small_delta_prod_bound {e D t1 t2 t3 : ℝ} (he0 : 0 < e) (he : e ≤ 1 / 50)
    (hD0 : 0 < D) (hD : D ≤ 1 / 50) (h1 : |t1| ≤ 16 * D) (h2l : 0 ≤ t2) (h2u : t2 ≤ e)
    (h3 : |t3| ≤ 3 * (e + D)) :
    |(1 + t1) * (1 + t2) * (1 + t3) - 1| ≤ 25 * (e + D) := by
  obtain ⟨h1l, h1u⟩ := abs_le.1 h1
  obtain ⟨h3l, h3u⟩ := abs_le.1 h3
  have p1 : 0 ≤ 1 + t1 := by linarith
  have p2 : 0 ≤ 1 + t2 := by linarith
  have p3 : 0 ≤ 1 + t3 := by linarith
  rw [abs_le]
  constructor
  · -- lower bound
    have a1 : (1 - 16 * D) * 1 ≤ (1 + t1) * (1 + t2) :=
      mul_le_mul (by linarith) (by linarith) zero_le_one p1
    have a2 : (1 - 16 * D) * 1 * (1 - 3 * (e + D)) ≤ (1 + t1) * (1 + t2) * (1 + t3) :=
      mul_le_mul a1 (by linarith) (by linarith) (mul_nonneg p1 p2)
    nlinarith
  · -- upper bound
    have a1 : (1 + t1) * (1 + t2) ≤ (1 + 16 * D) * (1 + e) :=
      mul_le_mul (by linarith) (by linarith) p2 (by linarith)
    have a2 : (1 + t1) * (1 + t2) * (1 + t3) ≤ (1 + 16 * D) * (1 + e) * (1 + 3 * (e + D)) :=
      mul_le_mul a1 (by linarith) p3 (by positivity)
    nlinarith [mul_pos he0 hD0]

/-- v2 `lem:small_delta` (D1): for `0 < ε, Δ ≤ 1/50`, `0 ≤ u_n`, `u = u_n + ε²Δ/(2(2-ε)) < 1`
and arbitrary additive part `a`, with `p = ⟨1-ε, ε²Δ, u_n, a⟩`:
`0 < ρ < 1`, `ρ = 1 + ε z_s` for the slow root `z_s` of `spectrumQ ε Δ u`, and
`Λ = 2εΔ(1-u)(1+ϑ)` with `|ϑ| ≤ 25(ε+Δ)`.  Here `2εΔ = 2ηp`. -/
theorem lem_small_delta {eps Delta un a u : ℝ} (he0 : 0 < eps) (he : eps ≤ 1 / 50)
    (hD0 : 0 < Delta) (hD : Delta ≤ 1 / 50) (hun : 0 ≤ un)
    (hu : u = un + eps ^ 2 * Delta / (2 * (2 - eps))) (hu1 : u < 1) :
    0 < stepRadius (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params) ∧
      stepRadius (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params) < 1 ∧
      (∃ zs : ℝ, spectrumQ eps Delta u (zs : ℂ) = 0 ∧ -0.06 < zs ∧ zs < 0 ∧
        stepRadius (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params) = 1 + eps * zs) ∧
      |perStepRate (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params) - 2 * eps * Delta * (1 - u)|
        ≤ 25 * (eps + Delta) * (2 * eps * Delta * (1 - u)) ∧
      ∃ ϑ : ℝ, |ϑ| ≤ 25 * (eps + Delta) ∧
        perStepRate (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params)
          = 2 * eps * Delta * (1 - u) * (1 + ϑ) := by
  have hfrac : 0 ≤ eps ^ 2 * Delta / (2 * (2 - eps)) :=
    div_nonneg (by positivity) (by linarith)
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  obtain ⟨zs, hq0, hz1, hz2, hrad, ϑ1, hzϑ, hϑ1⟩ :=
    small_delta_root (a := a) he0 he hD0 hD hun hu hu1
  obtain ⟨_, _, _, h0, h0t, _⟩ := small_coeff_bounds he0 he hD0 hD hu0 hu1
  obtain ⟨ϑ2, h2l, h2u, hΛ⟩ := small_delta_theta2 he0 he hz1 hz2 hrad
  obtain ⟨ϑ3, hr3, hϑ3⟩ := small_delta_ratio he0 he hD0 hD hu0 hu1
  have hprod := small_delta_prod_bound he0 he hD0 hD (t1 := ϑ1) (t2 := ϑ2) (t3 := ϑ3)
    (by linarith) h2l h2u hϑ3
  have hc : 0 < 2 * eps * Delta * (1 - u) := by
    have : 0 < 1 - u := by linarith
    positivity
  have hΛeq : perStepRate (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params)
      = 2 * eps * Delta * (1 - u) * ((1 + ϑ1) * (1 + ϑ2) * (1 + ϑ3)) := by
    rw [hΛ, abs_of_neg hz2, hzϑ]
    have : -(-(smallA0 eps Delta u / smallA1 eps Delta u) * (1 + ϑ1))
        = smallA0 eps Delta u / smallA1 eps Delta u * (1 + ϑ1) := by ring
    rw [this, hr3]
    ring
  have hlin : (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params) = ⟨1 - eps, eps ^ 2 * Delta, un, a⟩ := rfl
  refine ⟨?_, ?_, ⟨zs, hq0, hz1, hz2, hrad⟩, ?_, ?_⟩
  · rw [hrad]; nlinarith
  · rw [hrad]; nlinarith
  · rw [hΛeq]
    have : 2 * eps * Delta * (1 - u) * ((1 + ϑ1) * (1 + ϑ2) * (1 + ϑ3)) - 2 * eps * Delta * (1 - u)
        = 2 * eps * Delta * (1 - u) * ((1 + ϑ1) * (1 + ϑ2) * (1 + ϑ3) - 1) := by ring
    rw [this, abs_mul, abs_of_pos hc, mul_comm (25 * (eps + Delta))]
    exact mul_le_mul_of_nonneg_left hprod hc.le
  · exact ⟨(1 + ϑ1) * (1 + ϑ2) * (1 + ϑ3) - 1, hprod, by rw [hΛeq]; ring⟩

/-- v2 `lem:small_delta` (D2, rate form): `Λ = ε |z_s| (1+ϑ₂)` with `0 ≤ ϑ₂ ≤ ε`, where `z_s` is the
slow root of `spectrumQ ε Δ u`. -/
theorem lem_small_delta_theta2 {eps Delta un a u : ℝ} (he0 : 0 < eps) (he : eps ≤ 1 / 50)
    (hD0 : 0 < Delta) (hD : Delta ≤ 1 / 50) (hun : 0 ≤ un)
    (hu : u = un + eps ^ 2 * Delta / (2 * (2 - eps))) (hu1 : u < 1) :
    ∃ zs : ℝ, spectrumQ eps Delta u (zs : ℂ) = 0 ∧ -0.06 < zs ∧ zs < 0 ∧
      ∃ ϑ2 : ℝ, 0 ≤ ϑ2 ∧ ϑ2 ≤ eps ∧
        perStepRate (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params) = eps * |zs| * (1 + ϑ2) := by
  obtain ⟨zs, hq0, hz1, hz2, hrad, _⟩ := small_delta_root (a := a) he0 he hD0 hD hun hu hu1
  exact ⟨zs, hq0, hz1, hz2, small_delta_theta2 he0 he hz1 hz2 hrad⟩

/-- v2 `lem:small_delta` (D2, ratio form): `a0/a1 = 2Δ(1-u)(1+ϑ₃)` with `|ϑ₃| ≤ 3(ε+Δ)`, where
`a0 = 2Δ(2-ε)(1-u)` and `a1 = 2 + 4Δ + ε b₁`. -/
theorem lem_small_delta_ratio {eps Delta u : ℝ} (he0 : 0 < eps) (he : eps ≤ 1 / 50)
    (hD0 : 0 < Delta) (hD : Delta ≤ 1 / 50) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ ϑ3 : ℝ, |ϑ3| ≤ 3 * (eps + Delta) ∧
      (2 * Delta * (2 - eps) * (1 - u)) / (2 + 4 * Delta + eps * spectrumB1 eps Delta u)
        = 2 * Delta * (1 - u) * (1 + ϑ3) := by
  obtain ⟨ϑ3, h, hb⟩ := small_delta_ratio he0 he hD0 hD hu0 hu1
  exact ⟨ϑ3, hb, h⟩

/-- v2 `lem:small_delta` (D3, LS form): for `B > 0`, `p > 0`, `ε = 1-β ∈ (0, 1/50]`, `η > 0`,
`Δ = η p/ε ≤ 1/50` and `u = η/η₊ < 1`,
`|Λ - 2ηp(1-u)| ≤ 25(ε+Δ)·2ηp(1-u)`. -/
theorem lsRate_small_delta {d B : ℕ} {p : unitInterval} {beta : ℝ} (ν : Measure ℝ)
    (hB : 0 < B) (hp : 0 < (p : ℝ)) {eps Delta u eta : ℝ} (heps : eps = 1 - beta)
    (he0 : 0 < eps) (he : eps ≤ 1 / 50) (heta : 0 < eta)
    (hDelta : Delta = eta * p / eps) (hD : Delta ≤ 1 / 50)
    (hu : u = eta / criticalRate d B p beta) (hu1 : u < 1) :
    |lsRate d B p ν beta eta - 2 * eta * p * (1 - u)|
      ≤ 25 * (eps + Delta) * (2 * eta * p * (1 - u)) := by
  have hb : beta = 1 - eps := by linarith
  subst hb
  have hD0 : 0 < Delta := by rw [hDelta]; positivity
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hp1 := p.2.2
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hun : 0 ≤ eta * (((d : ℝ) + 2 - p) / (2 * B)) :=
    mul_nonneg heta.le (div_nonneg (by linarith) (by positivity))
  have e1 : 1 - (1 - eps) = eps := by ring
  have hw : (params d B p ν (1 - eps) eta).w = eps ^ 2 * Delta := by
    have := params_w_eq (d := d) (B := B) (p := p) (beta := 1 - eps) hp ν (by linarith) eta
    rw [e1] at this
    rw [this, hDelta]
  have hn : (params d B p ν (1 - eps) eta).noise = eta * (((d : ℝ) + 2 - p) / (2 * B)) :=
    params_noise_eq hB hp ν eta
  have hbeta : (params d B p ν (1 - eps) eta).beta = 1 - eps := rfl
  have hQ : lsRate d B p ν (1 - eps) eta
      = perStepRate (⟨1 - eps, eps ^ 2 * Delta, eta * (((d : ℝ) + 2 - p) / (2 * B)), 0⟩ : Params) := by
    unfold lsRate
    exact perStepRate_congr hbeta hw hn
  have hu' : u = eta * (((d : ℝ) + 2 - p) / (2 * B)) + eps ^ 2 * Delta / (2 * (2 - eps)) := by
    have h1 := params_totalLoad d B p hp.ne' ν (1 - eps) eta
    have h2 : (params d B p ν (1 - eps) eta).totalLoad
        = eta * (((d : ℝ) + 2 - p) / (2 * B)) + eps ^ 2 * Delta / (2 * (2 - eps)) := by
      unfold Params.totalLoad Params.curvature
      rw [hw, hn, hbeta]
      have : 1 + (1 - eps) = 2 - eps := by ring
      rw [this]
    have h3 : u = eta * inverseCriticalRate d B p (1 - eps) := by
      rw [hu]; unfold criticalRate; rw [div_inv_eq_mul]
    rw [h3, ← h1, h2]
  have hmain := (lem_small_delta he0 he hD0 hD hun hu' hu1 (a := 0)).2.2.2.1
  have hc : 2 * eps * Delta * (1 - u) = 2 * eta * p * (1 - u) := by
    rw [hDelta]; field_simp
  rw [hQ]
  rw [hc] at hmain
  exact hmain

end

end SparseSGD.Scaling.Helps
