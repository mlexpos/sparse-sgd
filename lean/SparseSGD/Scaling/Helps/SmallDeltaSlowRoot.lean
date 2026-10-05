import Mathlib
import SparseSGD.Scaling.Helps.RootPerturbation

/-!
# Slow-root bracketing for an abstract monic real cubic (v2 `lem:small_delta`, part 1)

Formalizes the paragraph "The slow root" in the proof of `lem:small_delta` of
`paper/appendix/momentum_helps.tex`.  Setting: `f(x) = x^3 + a2 x^2 + a1 x + a0` with real
coefficients satisfying `|a2 - 3| ≤ 0.024`, `1.97 ≤ a1 ≤ 2.11`, `0 < a0 ≤ 0.08`; put
`t± := (a0/a1)(1 ± 4 a0)`.  Then `f(-t+) < 0 < f(-t-)`, so `f` has a real root in
`(-t+, -t-)`.  The statements are uniform in the coefficients (no `ε` or `Δ` appears), so they
can be applied to the coefficients of the step cubic and of `χ`.
-/

namespace SparseSGD.Scaling.Helps

open Set

noncomputable section

/-- The real monic cubic. -/
def slowCubic (a2 a1 a0 x : ℝ) : ℝ := x ^ 3 + a2 * x ^ 2 + a1 * x + a0

/-- Lower endpoint `t- = (a0/a1)(1 - 4 a0)`. -/
def slowTm (a1 a0 : ℝ) : ℝ := a0 / a1 * (1 - 4 * a0)

/-- Upper endpoint `t+ = (a0/a1)(1 + 4 a0)`. -/
def slowTp (a1 a0 : ℝ) : ℝ := a0 / a1 * (1 + 4 * a0)

/-- v2 `lem:small_delta`, slow root, bracketing (B1):
`0 ≤ t- < t+ ≤ 0.06` and `f(-t+) < 0 < f(-t-)`. -/
theorem slowRoot_bracket {a2 a1 a0 : ℝ} (h2 : |a2 - 3| ≤ 0.024) (h1l : 1.97 ≤ a1)
    (h1u : a1 ≤ 2.11) (h0 : 0 < a0) (h0u : a0 ≤ 0.08) :
    0 ≤ slowTm a1 a0 ∧ slowTm a1 a0 < slowTp a1 a0 ∧ slowTp a1 a0 ≤ 0.06 ∧
      slowCubic a2 a1 a0 (-slowTp a1 a0) < 0 ∧ 0 < slowCubic a2 a1 a0 (-slowTm a1 a0) := by
  obtain ⟨h2l, h2u⟩ := abs_le.mp h2
  have ha1 : 0 < a1 := by linarith
  have hr0 : 0 < a0 / a1 := div_pos h0 ha1
  have hrle : a0 / a1 ≤ a0 / 1.97 :=
    div_le_div_of_nonneg_left h0.le (by norm_num) h1l
  have hrmul : a0 / a1 * a1 = a0 := div_mul_cancel₀ _ ha1.ne'
  have hm0 : 0 < 1 - 4 * a0 := by linarith
  have hp1 : 0 < 1 + 4 * a0 := by linarith
  have htm_nonneg : 0 ≤ slowTm a1 a0 := by
    unfold slowTm; exact (mul_pos hr0 hm0).le
  have htp_pos : 0 < slowTp a1 a0 := by
    unfold slowTp; exact mul_pos hr0 hp1
  have hlt : slowTm a1 a0 < slowTp a1 a0 := by
    unfold slowTm slowTp
    nlinarith [mul_pos hr0 h0]
  -- bound t+ ≤ 0.68 a0
  have htp_le : slowTp a1 a0 ≤ 0.68 * a0 := by
    unfold slowTp
    have h1 : a0 / a1 * (1 + 4 * a0) ≤ a0 / 1.97 * 1.32 :=
      mul_le_mul hrle (by linarith) hp1.le (by positivity)
    have h2' : a0 / 1.97 * 1.32 ≤ 0.68 * a0 := by
      have : a0 / 1.97 * 1.32 = a0 * (1.32 / 1.97) := by ring
      rw [this]
      nlinarith [(by norm_num : (1.32 : ℝ) / 1.97 ≤ 0.68)]
    linarith
  have htp_06 : slowTp a1 a0 ≤ 0.06 := by linarith
  have eqp : a1 * slowTp a1 a0 = a0 * (1 + 4 * a0) := by
    unfold slowTp
    have : a1 * (a0 / a1 * (1 + 4 * a0)) = (a0 / a1 * a1) * (1 + 4 * a0) := by ring
    rw [this, hrmul]
  have eqm : a1 * slowTm a1 a0 = a0 * (1 - 4 * a0) := by
    unfold slowTm
    have : a1 * (a0 / a1 * (1 - 4 * a0)) = (a0 / a1 * a1) * (1 - 4 * a0) := by ring
    rw [this, hrmul]
  refine ⟨htm_nonneg, hlt, htp_06, ?_, ?_⟩
  · -- f(-t+) = -4 a0^2 + t+^2 (a2 - t+) < 0
    have e : slowCubic a2 a1 a0 (-slowTp a1 a0) =
        -4 * a0 ^ 2 + slowTp a1 a0 ^ 2 * (a2 - slowTp a1 a0) := by
      unfold slowCubic
      linear_combination (-1 : ℝ) * eqp
    rw [e]
    have hsq : slowTp a1 a0 ^ 2 ≤ (0.68 * a0) ^ 2 := by
      apply pow_le_pow_left₀ htp_pos.le htp_le
    have hfac : a2 - slowTp a1 a0 ≤ 3.024 := by linarith
    have hfac0 : 0 ≤ slowTp a1 a0 ^ 2 := by positivity
    have hprod : slowTp a1 a0 ^ 2 * (a2 - slowTp a1 a0) ≤ (0.68 * a0) ^ 2 * 3.024 := by
      calc slowTp a1 a0 ^ 2 * (a2 - slowTp a1 a0)
          ≤ slowTp a1 a0 ^ 2 * 3.024 := mul_le_mul_of_nonneg_left hfac hfac0
        _ ≤ (0.68 * a0) ^ 2 * 3.024 := by nlinarith
    nlinarith [sq_pos_of_pos h0]
  · -- f(-t-) = 4 a0^2 + t-^2 (a2 - t-) > 0
    have e : slowCubic a2 a1 a0 (-slowTm a1 a0) =
        4 * a0 ^ 2 + slowTm a1 a0 ^ 2 * (a2 - slowTm a1 a0) := by
      unfold slowCubic
      linear_combination (-1 : ℝ) * eqm
    rw [e]
    have : 0 ≤ slowTm a1 a0 ^ 2 * (a2 - slowTm a1 a0) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [sq_pos_of_pos h0]

/-- v2 `lem:small_delta`, slow root, existence (B2): a real root of `f` strictly between
`-t+` and `-t-`. -/
theorem exists_slowRoot {a2 a1 a0 : ℝ} (h2 : |a2 - 3| ≤ 0.024) (h1l : 1.97 ≤ a1)
    (h1u : a1 ≤ 2.11) (h0 : 0 < a0) (h0u : a0 ≤ 0.08) :
    ∃ x : ℝ, -slowTp a1 a0 < x ∧ x < -slowTm a1 a0 ∧ x ^ 3 + a2 * x ^ 2 + a1 * x + a0 = 0 := by
  obtain ⟨hm0, hlt, hp, hneg, hpos⟩ := slowRoot_bracket h2 h1l h1u h0 h0u
  have hcont : ContinuousOn (slowCubic a2 a1 a0) (Icc (-slowTp a1 a0) (-slowTm a1 a0)) := by
    unfold slowCubic; fun_prop
  have hab : -slowTp a1 a0 ≤ -slowTm a1 a0 := by linarith
  have := intermediate_value_Ioo hab hcont (show (0:ℝ) ∈ Ioo _ _ from ⟨hneg, hpos⟩)
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := this
  exact ⟨x, hx1, hx2, hx⟩

/-- v2 `lem:small_delta`, slow root, consequences of (B2): the root is a complex root of the
cubic, lies in `(-0.06, 0)`, and has the form `-(a0/a1)(1+ϑ1)` with `|ϑ1| ≤ 4 a0`. -/
theorem exists_slowRoot_full {a2 a1 a0 : ℝ} (h2 : |a2 - 3| ≤ 0.024) (h1l : 1.97 ≤ a1)
    (h1u : a1 ≤ 2.11) (h0 : 0 < a0) (h0u : a0 ≤ 0.08) :
    ∃ x : ℝ, ((x : ℂ) ∈ cubicRoots (a2 : ℂ) (a1 : ℂ) (a0 : ℂ)) ∧ -0.06 < x ∧ x < 0 ∧
      ∃ ϑ : ℝ, x = -(a0 / a1) * (1 + ϑ) ∧ |ϑ| ≤ 4 * a0 := by
  obtain ⟨hm0, hlt, hp, hneg, hpos⟩ := slowRoot_bracket h2 h1l h1u h0 h0u
  obtain ⟨x, hx1, hx2, hx⟩ := exists_slowRoot h2 h1l h1u h0 h0u
  have ha1 : 0 < a1 := by linarith
  have hr0 : 0 < a0 / a1 := div_pos h0 ha1
  refine ⟨x, ?_, by linarith, by linarith, -x / (a0 / a1) - 1, ?_, ?_⟩
  · show (x : ℂ) ^ 3 + (a2 : ℂ) * (x : ℂ) ^ 2 + (a1 : ℂ) * (x : ℂ) + (a0 : ℂ) = 0
    exact_mod_cast hx
  · field_simp
    ring
  · have hxa : -(a0 / a1 * (1 + 4 * a0)) < x := by unfold slowTp at hx1; linarith
    have hxb : x < -(a0 / a1 * (1 - 4 * a0)) := by unfold slowTm at hx2; linarith
    rw [abs_le]
    constructor
    · have : (1 - 4 * a0) * (a0 / a1) < -x := by linarith
      have h' : (1 - 4 * a0) < -x / (a0 / a1) := by
        rw [lt_div_iff₀ hr0]; exact this
      linarith
    · have : -x < (1 + 4 * a0) * (a0 / a1) := by linarith
      have h' : -x / (a0 / a1) < (1 + 4 * a0) := by
        rw [div_lt_iff₀ hr0]; exact this
      linarith

end

end SparseSGD.Scaling.Helps
