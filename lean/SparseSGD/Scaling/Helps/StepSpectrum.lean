import Mathlib
import SparseSGD.Scaling.Helps.Transfer

/-!
# Explicit step-spectrum cubic (v2 `lem:step_spectrum`)

Formalizes `lem:step_spectrum` of `paper/appendix/momentum_helps.tex`.
For `β = 1 - ε`, `w = ε² Δ`, noise load `u_n` and total load `u = u_n + u_c` with
`u_c = ε²Δ/(2(2-ε))` (the curvature of `⟨1-ε, ε²Δ, u_n, a⟩`), the eigenvalues of the step map
are `1 + ε μ` with `μ` a root of the explicit monic cubic
`q(z) = z³ + (3 + ε b₂) z² + (2 + 4Δ + ε b₁) z + 2Δ(2-ε)(1-u)`.
The coefficients `b₁, b₂` are `transferR1, transferR2` rewritten in terms of the total load `u`,
and satisfy `|b_i| ≤ 1 + (16/3)Δ + εΔ²` for `ε ≤ 1/2`.

Complex-variable versions (`spectrumQ`) are used for the eigenvalue statements, and real-variable
versions (`spectrumQR`) are provided as well.

**Hypotheses added relative to the tex.**  The identities (S1), (S2) need `ε ≠ 2`
(i.e. `β ≠ -1`), because `u_c = ε²Δ/(2(2-ε))` is a division by `2 - ε`; in the paper `β ∈ [0,1)`,
so `ε ∈ (0,1]` and this is automatic.
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD

noncomputable section

/-- The coefficient `b₁` of `lem:step_spectrum` (total-load form). -/
def spectrumB1 (eps Delta u : ℝ) : ℝ :=
  (-(2 - eps) - Delta * (12 * u - 4 + eps * (6 - 10 * u) + eps ^ 2 * (2 * u - 2))
    - 2 * eps * (1 - eps) * Delta ^ 2) / (2 - eps)

/-- The coefficient `b₂` of `lem:step_spectrum` (total-load form). -/
def spectrumB2 (eps Delta u : ℝ) : ℝ :=
  (-(2 - eps) + Delta * (8 - eps * (8 + 4 * u) + eps ^ 2 * (2 + 2 * u))
    - 2 * eps ^ 2 * (1 - eps) * Delta ^ 2) / (2 - eps)

/-- The explicit cubic `q` of `lem:step_spectrum`, over `ℂ`. -/
def spectrumQ (eps Delta u : ℝ) (z : ℂ) : ℂ :=
  z ^ 3 + ((3 + eps * spectrumB2 eps Delta u : ℝ) : ℂ) * z ^ 2
    + ((2 + 4 * Delta + eps * spectrumB1 eps Delta u : ℝ) : ℂ) * z
    + ((2 * Delta * (2 - eps) * (1 - u) : ℝ) : ℂ)

/-- The explicit cubic `q` of `lem:step_spectrum`, over `ℝ`. -/
def spectrumQR (eps Delta u z : ℝ) : ℝ :=
  z ^ 3 + (3 + eps * spectrumB2 eps Delta u) * z ^ 2
    + (2 + 4 * Delta + eps * spectrumB1 eps Delta u) * z + 2 * Delta * (2 - eps) * (1 - u)

theorem spectrumQ_ofReal (eps Delta u z : ℝ) :
    spectrumQ eps Delta u (z : ℂ) = ((spectrumQR eps Delta u z : ℝ) : ℂ) := by
  simp only [spectrumQ, spectrumQR]; push_cast; ring

/-! ### (S1) the coefficients -/

/-- v2 `lem:step_spectrum`: `b₂ = r₂` after substituting `u = u_n + u_c`. -/
theorem spectrumB2_eq (eps Delta un : ℝ) (he : eps ≠ 2) :
    spectrumB2 eps Delta (un + eps ^ 2 * Delta / (2 * (2 - eps))) = transferR2 eps Delta un := by
  have h : (2 - eps) ≠ 0 := sub_ne_zero.2 (Ne.symm he)
  unfold spectrumB2 transferR2
  field_simp
  ring

/-- v2 `lem:step_spectrum`: `b₁ = r₁` after substituting `u = u_n + u_c`. -/
theorem spectrumB1_eq (eps Delta un : ℝ) (he : eps ≠ 2) :
    spectrumB1 eps Delta (un + eps ^ 2 * Delta / (2 * (2 - eps))) = transferR1 eps Delta un := by
  have h : (2 - eps) ≠ 0 := sub_ne_zero.2 (Ne.symm he)
  unfold spectrumB1 transferR1
  field_simp
  ring

/-- v2 `lem:step_spectrum`: the constant coefficient `2Δ(2-ε)(1-u)` equals `transferQ0`. -/
theorem spectrumQ0_eq (eps Delta un : ℝ) (he : eps ≠ 2) :
    2 * Delta * (2 - eps) * (1 - (un + eps ^ 2 * Delta / (2 * (2 - eps))))
      = transferQ0 eps Delta un := by
  have h : (2 - eps) ≠ 0 := sub_ne_zero.2 (Ne.symm he)
  unfold transferQ0 transferR0
  field_simp
  ring

/-- v2 `lem:step_spectrum` (S1), in terms of `Params.totalLoad`. -/
theorem spectrumQ0_eq_totalLoad (eps Delta un a : ℝ) (he : eps ≠ 2) :
    2 * Delta * (2 - eps) * (1 - (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params).totalLoad)
      = transferQ0 eps Delta un := by
  have h : (2 - eps) ≠ 0 := sub_ne_zero.2 (Ne.symm he)
  have : (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params).totalLoad
      = un + eps ^ 2 * Delta / (2 * (2 - eps)) := by
    simp only [Params.totalLoad, Params.curvature]
    congr 2; ring
  rw [this]
  exact spectrumQ0_eq eps Delta un he

/-! ### (S2) the eigenvalues -/

/-- v2 `lem:step_spectrum` (S2): for `ε ≠ 0`, `ε ≠ 2`, `z` is an eigenvalue of the step map of
`⟨1-ε, ε²Δ, u_n, a⟩` (any additive part `a`) iff `z = 1 + ε μ` with `q(μ) = 0`,
where `q` is built from the total load `u = u_n + u_c`. -/
theorem mem_stepRoots_iff_spectrumQ (eps Delta un a u : ℝ) (he : eps ≠ 0) (he2 : eps ≠ 2)
    (hu : u = un + eps ^ 2 * Delta / (2 * (2 - eps))) (z : ℂ) :
    z ∈ stepRoots (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params) ↔
      ∃ mu : ℂ, spectrumQ eps Delta u mu = 0 ∧ z = 1 + (eps : ℂ) * mu := by
  have key : z ∈ stepRoots (⟨1 - eps, eps ^ 2 * Delta, un, a⟩ : Params) ↔
      z ∈ stepRoots (transferParams eps Delta un) := Iff.rfl
  rw [key, mem_stepRoots_transfer_iff eps Delta un he z]
  have hq : ∀ mu : ℂ, spectrumQ eps Delta u mu =
      mu ^ 3 + (transferQ2 eps Delta un : ℂ) * mu ^ 2
        + (transferQ1 eps Delta un : ℂ) * mu + (transferQ0 eps Delta un : ℂ) := by
    intro mu
    have h2 := spectrumB2_eq eps Delta un he2
    have h1 := spectrumB1_eq eps Delta un he2
    have h0 := spectrumQ0_eq eps Delta un he2
    rw [← hu] at h2 h1 h0
    simp only [spectrumQ, transferQ2, transferQ1, ← h2, ← h1, ← h0]
  constructor
  · rintro ⟨mu, hmu, hz⟩
    refine ⟨mu, ?_, hz⟩
    rw [hq]; exact hmu
  · rintro ⟨mu, hmu, hz⟩
    refine ⟨mu, ?_, hz⟩
    rw [hq] at hmu; exact hmu

/-! ### (S3) bounds on the coefficients -/

private theorem X1_bounds {eps u : ℝ} (he0 : 0 < eps) (he : eps ≤ 1 / 2) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) :
    -4 ≤ 12 * u - 4 + eps * (6 - 10 * u) + eps ^ 2 * (2 * u - 2) ∧
      12 * u - 4 + eps * (6 - 10 * u) + eps ^ 2 * (2 * u - 2) ≤ 8 := by
  constructor <;> nlinarith [mul_nonneg hu0 he0.le, mul_nonneg hu0 (sq_nonneg eps),
    mul_nonneg (sub_nonneg.2 hu1) he0.le, mul_nonneg (sub_nonneg.2 hu1) (sq_nonneg eps),
    mul_nonneg (sub_nonneg.2 he) he0.le, mul_nonneg (mul_nonneg hu0 he0.le) (sub_nonneg.2 he),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hu1) he0.le) (sub_nonneg.2 he)]

private theorem X2_bounds {eps u : ℝ} (he0 : 0 < eps) (he : eps ≤ 1 / 2) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) :
    3 ≤ 8 - eps * (8 + 4 * u) + eps ^ 2 * (2 + 2 * u) ∧
      8 - eps * (8 + 4 * u) + eps ^ 2 * (2 + 2 * u) ≤ 8 := by
  constructor <;> nlinarith [mul_nonneg hu0 he0.le, mul_nonneg hu0 (sq_nonneg eps),
    mul_nonneg (sub_nonneg.2 hu1) he0.le, mul_nonneg (sub_nonneg.2 hu1) (sq_nonneg eps),
    mul_nonneg (sub_nonneg.2 he) he0.le, mul_nonneg (mul_nonneg hu0 he0.le) (sub_nonneg.2 he),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hu1) he0.le) (sub_nonneg.2 he)]

/-- v2 `lem:step_spectrum` (S3): `|b₁| ≤ 1 + (16/3)Δ + εΔ²` for `0 < ε ≤ 1/2`, `Δ ≥ 0`,
`u ∈ [0,1]`. -/
theorem abs_spectrumB1_le {eps Delta u : ℝ} (he0 : 0 < eps) (he : eps ≤ 1 / 2)
    (hD : 0 ≤ Delta) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |spectrumB1 eps Delta u| ≤ 1 + 16 / 3 * Delta + eps * Delta ^ 2 := by
  obtain ⟨hx1, hx2⟩ := X1_bounds he0 he hu0 hu1
  have hd : 0 < 2 - eps := by linarith
  have hM : 0 ≤ 1 + 16 / 3 * Delta + eps * Delta ^ 2 := by positivity
  unfold spectrumB1
  rw [abs_div, abs_of_pos hd, div_le_iff₀ hd, abs_le]
  have e1 : 0 ≤ Delta * eps * Delta := by positivity
  have e2 : 0 ≤ Delta * (1 / 2 - eps) := mul_nonneg hD (by linarith)
  have e3 : 0 ≤ Delta ^ 2 * eps * (1 / 2 - eps) := by
    have := sub_nonneg.2 he
    positivity
  have e4 : 0 ≤ Delta ^ 2 * eps * (1 / 2 - eps) := e3
  have f1 : 0 ≤ Delta * (12 * u - 4 + eps * (6 - 10 * u) + eps ^ 2 * (2 * u - 2) + 4) :=
    mul_nonneg hD (by linarith)
  have f2 : 0 ≤ Delta * (8 - (12 * u - 4 + eps * (6 - 10 * u) + eps ^ 2 * (2 * u - 2))) :=
    mul_nonneg hD (by linarith)
  constructor <;> nlinarith [mul_nonneg hD (sub_nonneg.2 he), mul_nonneg hD hd.le,
    mul_nonneg (mul_nonneg hD hD) he0.le, mul_nonneg (mul_nonneg hD hD) (mul_nonneg he0.le (sub_nonneg.2 he))]

/-- v2 `lem:step_spectrum` (S3): `|b₂| ≤ 1 + (16/3)Δ + εΔ²` for `0 < ε ≤ 1/2`, `Δ ≥ 0`,
`u ∈ [0,1]`. -/
theorem abs_spectrumB2_le {eps Delta u : ℝ} (he0 : 0 < eps) (he : eps ≤ 1 / 2)
    (hD : 0 ≤ Delta) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |spectrumB2 eps Delta u| ≤ 1 + 16 / 3 * Delta + eps * Delta ^ 2 := by
  obtain ⟨hx1, hx2⟩ := X2_bounds he0 he hu0 hu1
  have hd : 0 < 2 - eps := by linarith
  have hM : 0 ≤ 1 + 16 / 3 * Delta + eps * Delta ^ 2 := by positivity
  unfold spectrumB2
  rw [abs_div, abs_of_pos hd, div_le_iff₀ hd, abs_le]
  have f1 : 0 ≤ Delta * (8 - eps * (8 + 4 * u) + eps ^ 2 * (2 + 2 * u) - 3) :=
    mul_nonneg hD (by linarith)
  have f2 : 0 ≤ Delta * (8 - (8 - eps * (8 + 4 * u) + eps ^ 2 * (2 + 2 * u))) :=
    mul_nonneg hD (by linarith)
  constructor <;> nlinarith [mul_nonneg hD (sub_nonneg.2 he), mul_nonneg hD hd.le,
    mul_nonneg (mul_nonneg hD hD) he0.le,
    mul_nonneg (mul_nonneg hD hD) (mul_nonneg he0.le (sub_nonneg.2 he)),
    mul_nonneg (mul_nonneg (mul_nonneg hD hD) he0.le) (mul_nonneg he0.le (sub_nonneg.2 he))]

/-- v2 `lem:step_spectrum` (S3): both `|b₁|` and `|b₂|` are at most `1 + (16/3)Δ + εΔ²`. -/
theorem abs_spectrumB_le {eps Delta u : ℝ} (he0 : 0 < eps) (he : eps ≤ 1 / 2)
    (hD : 0 ≤ Delta) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |spectrumB1 eps Delta u| ≤ 1 + 16 / 3 * Delta + eps * Delta ^ 2 ∧
      |spectrumB2 eps Delta u| ≤ 1 + 16 / 3 * Delta + eps * Delta ^ 2 :=
  ⟨abs_spectrumB1_le he0 he hD hu0 hu1, abs_spectrumB2_le he0 he hD hu0 hu1⟩

/-- v2 `lem:step_spectrum` (S3), small-parameter form: for `ε, Δ ≤ 1/50`, `|b_i| ≤ 1.17`. -/
theorem abs_spectrumB_le_small {eps Delta u : ℝ} (he0 : 0 < eps) (he : eps ≤ 1 / 50)
    (hD : 0 ≤ Delta) (hD1 : Delta ≤ 1 / 50) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |spectrumB1 eps Delta u| ≤ 1.17 ∧ |spectrumB2 eps Delta u| ≤ 1.17 := by
  have he' : eps ≤ 1 / 2 := by linarith
  obtain ⟨h1, h2⟩ := abs_spectrumB_le he0 he' hD hu0 hu1
  have hb : 1 + 16 / 3 * Delta + eps * Delta ^ 2 ≤ 1.17 := by
    have : eps * Delta ^ 2 ≤ 1 / 50 * (1 / 50) ^ 2 := by
      apply mul_le_mul he (pow_le_pow_left₀ hD hD1 2) (by positivity) (by norm_num)
    nlinarith
  exact ⟨h1.trans hb, h2.trans hb⟩

/-! ### (S4) the chi-plus-remainder identity -/

/-- v2 `lem:step_spectrum` (S4), over `ℂ`:
`q(z) - χ(z;Δ,u) = ε (b₂ z² + b₁ z - 2Δ(1-u))`. -/
theorem spectrumQ_sub_chi (eps Delta u : ℝ) (z : ℂ) :
    spectrumQ eps Delta u z - chiC z (Delta : ℂ) (u : ℂ) =
      (eps : ℂ) * ((spectrumB2 eps Delta u : ℝ) * z ^ 2 + (spectrumB1 eps Delta u : ℝ) * z
        - 2 * (Delta : ℂ) * (1 - (u : ℂ))) := by
  simp only [spectrumQ, chiC]
  push_cast
  ring

/-- v2 `lem:step_spectrum` (S4), over `ℝ`. -/
theorem spectrumQR_sub_chi (eps Delta u z : ℝ) :
    spectrumQR eps Delta u z - chiC z Delta u =
      eps * (spectrumB2 eps Delta u * z ^ 2 + spectrumB1 eps Delta u * z
        - 2 * Delta * (1 - u)) := by
  simp only [spectrumQR, chiC]
  ring

end
end SparseSGD.Scaling.Helps
