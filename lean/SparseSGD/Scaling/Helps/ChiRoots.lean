import SparseSGD.Scaling.Helps.CubicRoots

/-!
# Roots of the continuum characteristic cubic (`v2 lem:chi_roots`)

With `r_c(Δ,u) = continuumPerronRate Δ u` and `χ = spectrumPolynomial`, this file proves all five
parts (a)-(e) of `v2 lem:chi_roots` for `Δ > 0`, `u ∈ [0,1)`, including the endpoint `u = 0`
(which the pre-merge statements `continuumPerronRate_lt_one_sub_load`,
`continuumPerronRate_quarter_cube`, `speedupRatio_lt_two` exclude).

* (a) `chi_roots_a`, `chi_roots_a_eq_iff`;
* (b) `chi_roots_b_le`, `chi_roots_b_ge`;
* (c) `chi_roots_c`;
* (d) `chi_roots_d_bracket` (the bracket `-t₊ < x < -t₋`, `r_c = -x`) and `chi_roots_d`, uniform in
  `u ∈ [0,1)` and `Δ ∈ (0,1/50]` with the explicit constant `18`:
  `|r_c - 2Δ(1-u)| ≤ 18 Δ (2Δ(1-u))`;
* (e) `chi_roots_e`, `chi_roots_e_zero_le`, `chi_roots_e_zero_eq_iff`.

The bundle is `lem_chi_roots`.
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD

noncomputable section

/-! ### (a) and (b) -/

/-- `v2 lem:chi_roots (b)`, `Δ ≤ 1/4`: `r_c(Δ,0) = 1 - √(1-4Δ)`. -/
theorem chi_roots_b_le {Delta : ℝ} (hD : 0 < Delta) (h : Delta ≤ 1/4) :
    continuumPerronRate Delta 0 = 1 - Real.sqrt (1 - 4*Delta) := by
  rw [continuumPerronRate_zero_load hD, max_eq_right (by linarith)]

/-- `v2 lem:chi_roots (b)`, `Δ ≥ 1/4`: `r_c(Δ,0) = 1`. -/
theorem chi_roots_b_ge {Delta : ℝ} (hD : 0 < Delta) (h : 1/4 ≤ Delta) :
    continuumPerronRate Delta 0 = 1 := by
  rw [continuumPerronRate_zero_load hD, max_eq_left (by linarith), Real.sqrt_zero]; ring

/-- `v2 lem:chi_roots (a)`: `r_c ≤ 1 - u`. -/
theorem chi_roots_a {Delta u : ℝ} (hD : 0 < Delta) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    continuumPerronRate Delta u ≤ 1 - u := by
  rcases eq_or_lt_of_le hu0 with h | h
  · subst h
    rw [continuumPerronRate_zero_load hD]
    have := Real.sqrt_nonneg (max 0 (1 - 4*Delta))
    linarith
  · exact (continuumPerronRate_lt_one_sub_load Delta u hD h hu1).le

/-- `v2 lem:chi_roots (a)`: equality `r_c = 1 - u` holds only if `u = 0` and `Δ ≥ 1/4`. -/
theorem chi_roots_a_eq_iff {Delta u : ℝ} (hD : 0 < Delta) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    continuumPerronRate Delta u = 1 - u ↔ (u = 0 ∧ 1/4 ≤ Delta) := by
  constructor
  · intro h
    rcases eq_or_lt_of_le hu0 with h0 | h0
    · subst h0
      refine ⟨rfl, ?_⟩
      rw [continuumPerronRate_zero_load hD] at h
      have hs : Real.sqrt (max 0 (1 - 4*Delta)) = 0 := by linarith
      have hm : max 0 (1 - 4*Delta) = 0 := (Real.sqrt_eq_zero (le_max_left _ _)).1 hs
      have := le_max_right 0 (1 - 4*Delta)
      rw [hm] at this
      linarith
    · exact absurd h (continuumPerronRate_lt_one_sub_load Delta u hD h0 hu1).ne
  · rintro ⟨rfl, h⟩
    rw [chi_roots_b_ge hD h]; ring

/-! ### (c) -/

/-- `v2 lem:chi_roots (c)`: `r_c(1/4,u) = 1 - u^(1/3)` for every `u ∈ [0,1)`, including `u = 0`. -/
theorem chi_roots_c {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    continuumPerronRate (1/4) u = 1 - u^((1:ℝ)/3) := by
  rcases eq_or_lt_of_le hu0 with h | h
  · subst h
    rw [continuumPerronRate_zero_load (by norm_num), Real.zero_rpow (by norm_num)]
    norm_num
  · have hcube : (u^((1:ℝ)/3))^3 = u := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h.le]; norm_num
    have ha0 : 0 < u^((1:ℝ)/3) := Real.rpow_pos_of_pos h _
    have ha1 : u^((1:ℝ)/3) < 1 := Real.rpow_lt_one h.le hu1 (by norm_num)
    have := continuumPerronRate_quarter_cube ha0 ha1
    rwa [hcube] at this

/-! ### (e) -/

/-- `v2 lem:chi_roots (e)`, `u ∈ (0,1)`: `r_c < 4Δ(1-u)`. -/
theorem chi_roots_e {Delta u : ℝ} (hD : 0 < Delta) (hu0 : 0 < u) (hu1 : u < 1) :
    continuumPerronRate Delta u < 4*Delta*(1-u) := by
  have h := speedupRatio_lt_two hD hu0 hu1
  unfold speedupRatio at h
  have hden : 0 < 2*Delta*(1-u) := by
    have : 0 < 1 - u := by linarith
    positivity
  rw [div_lt_iff₀ hden] at h
  linarith

/-- `v2 lem:chi_roots (e)`, `u = 0`: `r_c(Δ,0) ≤ 4Δ`. -/
theorem chi_roots_e_zero_le {Delta : ℝ} (hD : 0 < Delta) :
    continuumPerronRate Delta 0 ≤ 4*Delta := by
  rcases le_or_gt Delta (1/4) with h | h
  · rw [chi_roots_b_le hD h]
    set s := Real.sqrt (1 - 4*Delta) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s^2 = 1 - 4*Delta := Real.sq_sqrt (by linarith)
    have hs1 : s ≤ 1 := by nlinarith
    nlinarith
  · rw [chi_roots_b_ge hD h.le]; linarith

/-- `v2 lem:chi_roots (e)`, `u = 0`: `r_c(Δ,0) = 4Δ` only if `Δ = 1/4`. -/
theorem chi_roots_e_zero_eq_iff {Delta : ℝ} (hD : 0 < Delta) :
    continuumPerronRate Delta 0 = 4*Delta ↔ Delta = 1/4 := by
  constructor
  · intro heq
    rcases le_or_gt Delta (1/4) with h | h
    · rw [chi_roots_b_le hD h] at heq
      set s := Real.sqrt (1 - 4*Delta) with hs
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have hs2 : s^2 = 1 - 4*Delta := Real.sq_sqrt (by linarith)
      have hfac : s * (s - 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 hfac with h0 | h1
      · rw [h0] at hs2; linarith
      · have : s = 1 := by linarith
        rw [this] at hs2; linarith
    · rw [chi_roots_b_ge hD h.le] at heq
      linarith
  · rintro rfl
    rw [chi_roots_b_ge hD le_rfl]; norm_num

/-! ### (d) -/

/-- Bracket constant `a₀ = 4Δ(1-u) = χ(0)`. -/
def chiA0 (Delta u : ℝ) : ℝ := 4*Delta*(1-u)

/-- Bracket constant `a₁ = 2+4Δ` (the linear coefficient of `χ`). -/
def chiA1 (Delta : ℝ) : ℝ := 2+4*Delta

/-- `t₊ = (a₀/a₁)(1+4a₀)`. -/
def chiTplus (Delta u : ℝ) : ℝ := chiA0 Delta u / chiA1 Delta * (1 + 4*chiA0 Delta u)

/-- `t₋ = (a₀/a₁)(1-4a₀)`. -/
def chiTminus (Delta u : ℝ) : ℝ := chiA0 Delta u / chiA1 Delta * (1 - 4*chiA0 Delta u)

private theorem chi_aux_plus {a0 a1 t : ℝ} (_h0 : 0 < a0)
    (hat : a1 * t = a0 * (1 + 4*a0)) (ht0 : 0 < t) (htle : t ≤ 66/100*a0) :
    (-t)^3 + 3*(-t)^2 + a1*(-t) + a0 < 0 := by
  have h2 : t^2 ≤ (66/100*a0)^2 := pow_le_pow_left₀ ht0.le htle 2
  nlinarith [pow_pos ht0 3, sq_pos_of_pos _h0]

private theorem chi_aux_minus {a0 a1 t : ℝ} (_h0 : 0 < a0)
    (hat : a1 * t = a0 * (1 - 4*a0)) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 < (-t)^3 + 3*(-t)^2 + a1*(-t) + a0 := by
  nlinarith [mul_pos (pow_pos ht0 2) (by linarith : 0 < 3 - t), sq_pos_of_pos _h0]

/-- `v2 lem:chi_roots (d)`, bracket: for `Δ ∈ (0,1/50]`, `u ∈ [0,1)`, with `a₀ = 4Δ(1-u)`,
`a₁ = 2+4Δ`, `t± = (a₀/a₁)(1 ± 4a₀)`, `χ` has a real root `x ∈ (-t₊, -t₋)` and `r_c = -x`. -/
theorem chi_roots_d_bracket {Delta u : ℝ} (hD : 0 < Delta) (hD1 : Delta ≤ 1/50)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ x : ℝ, -chiTplus Delta u < x ∧ x < -chiTminus Delta u ∧
      spectrumPolynomial Delta u x = 0 ∧ continuumPerronRate Delta u = -x := by
  have h1u : 0 < 1 - u := by linarith
  have ha0 : 0 < chiA0 Delta u := by unfold chiA0; positivity
  have ha0' : chiA0 Delta u ≤ 2/25 := by
    unfold chiA0; nlinarith [mul_nonneg hD.le hu0]
  have ha1 : 2 ≤ chiA1 Delta := by unfold chiA1; linarith
  have ha1ne : chiA1 Delta ≠ 0 := by linarith
  have hpoly : ∀ x, spectrumPolynomial Delta u x =
      x^3 + 3*x^2 + chiA1 Delta * x + chiA0 Delta u := by
    intro x; unfold spectrumPolynomial chiA0 chiA1; ring
  have hs : chiA0 Delta u / chiA1 Delta * chiA1 Delta = chiA0 Delta u :=
    div_mul_cancel₀ _ ha1ne
  have hs0 : 0 < chiA0 Delta u / chiA1 Delta := div_pos ha0 (by linarith)
  have hs2 : chiA0 Delta u / chiA1 Delta ≤ chiA0 Delta u / 2 := by nlinarith
  have hat_p : chiA1 Delta * chiTplus Delta u = chiA0 Delta u * (1 + 4*chiA0 Delta u) := by
    unfold chiTplus; field_simp
  have hat_m : chiA1 Delta * chiTminus Delta u = chiA0 Delta u * (1 - 4*chiA0 Delta u) := by
    unfold chiTminus; field_simp
  have hp_def : chiTplus Delta u = chiA0 Delta u / chiA1 Delta * (1 + 4*chiA0 Delta u) := rfl
  have hm_def : chiTminus Delta u = chiA0 Delta u / chiA1 Delta * (1 - 4*chiA0 Delta u) := rfl
  have hp0 : 0 < chiTplus Delta u := by
    rw [hp_def]; exact mul_pos hs0 (by linarith)
  have hm0 : 0 < chiTminus Delta u := by
    rw [hm_def]; exact mul_pos hs0 (by linarith)
  have hp_le : chiTplus Delta u ≤ 66/100 * chiA0 Delta u := by
    rw [hp_def]
    have := mul_le_mul hs2 (show 1 + 4*chiA0 Delta u ≤ 132/100 by linarith)
      (by linarith) (by linarith)
    linarith
  have hm_le : chiTminus Delta u ≤ 1 := by
    rw [hm_def]
    have := mul_le_mul hs2 (show 1 - 4*chiA0 Delta u ≤ 1 by linarith)
      (by linarith) (by linarith)
    linarith
  have hmp : chiTminus Delta u < chiTplus Delta u := by
    rw [hp_def, hm_def]; nlinarith [mul_pos hs0 ha0]
  have hneg : spectrumPolynomial Delta u (-chiTplus Delta u) < 0 := by
    rw [hpoly]; exact chi_aux_plus ha0 hat_p hp0 hp_le
  have hpos : 0 < spectrumPolynomial Delta u (-chiTminus Delta u) := by
    rw [hpoly]; exact chi_aux_minus ha0 hat_m hm0 hm_le
  have hcont : ContinuousOn (spectrumPolynomial Delta u)
      (Set.Icc (-chiTplus Delta u) (-chiTminus Delta u)) := by
    unfold spectrumPolynomial; fun_prop
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (by linarith) hcont
    (show (0 : ℝ) ∈ Set.Ioo (spectrumPolynomial Delta u (-chiTplus Delta u))
      (spectrumPolynomial Delta u (-chiTminus Delta u)) from ⟨hneg, hpos⟩)
  refine ⟨x, hx.1, hx.2, hfx, ?_⟩
  have hxl : -1/10 < x := by nlinarith [hx.1]
  have hxu : x < 0 := by linarith [hx.2]
  have := continuumPerronRate_eq_of_rightmost hfx (by linarith)
    (by nlinarith [sq_nonneg x, hD])
  exact this

/-- `v2 lem:chi_roots (d)`: uniformly in `u ∈ [0,1)` and `Δ ∈ (0,1/50]`,
`|r_c(Δ,u) - 2Δ(1-u)| ≤ 18 Δ (2Δ(1-u))`. The explicit constant is `18`. -/
theorem chi_roots_d {Delta u : ℝ} (hD : 0 < Delta) (hD1 : Delta ≤ 1/50)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    |continuumPerronRate Delta u - 2*Delta*(1-u)| ≤ 18*Delta*(2*Delta*(1-u)) := by
  obtain ⟨x, hx1, hx2, -, hr⟩ := chi_roots_d_bracket hD hD1 hu0 hu1
  have h1u : 0 < 1 - u := by linarith
  have ha0 : 0 < chiA0 Delta u := by unfold chiA0; positivity
  have ha1ne : chiA1 Delta ≠ 0 := by unfold chiA1; linarith
  have hs0 : 0 < chiA0 Delta u / chiA1 Delta :=
    div_pos ha0 (by unfold chiA1; linarith)
  obtain ⟨s, hsdef⟩ : ∃ s, s = chiA0 Delta u / chiA1 Delta := ⟨_, rfl⟩
  rw [← hsdef] at hs0
  have hsa : s * (2 + 4*Delta) = 4*Delta*(1-u) := by
    rw [hsdef]; unfold chiA1 chiA0; unfold chiA1 at ha1ne; field_simp
  have hq0 : 0 < 2*Delta*(1-u) := by positivity
  obtain ⟨q, hq⟩ : ∃ q, q = 2*Delta*(1-u) := ⟨_, rfl⟩
  rw [← hq] at hq0 ⊢
  have hsq : s + 2*Delta*s = q := by rw [hq]; linarith
  have hsle : s ≤ q := by nlinarith [mul_pos hD hs0]
  have hA0 : chiA0 Delta u = 2*q := by rw [hq]; unfold chiA0; ring
  have ha0le : chiA0 Delta u ≤ 4*Delta := by
    unfold chiA0; nlinarith [mul_nonneg hD.le hu0]
  have htp : chiTplus Delta u = s + 4*chiA0 Delta u * s := by
    unfold chiTplus; rw [← hsdef]; ring
  have htm : chiTminus Delta u = s - 4*chiA0 Delta u * s := by
    unfold chiTminus; rw [← hsdef]; ring
  have hk : 4*chiA0 Delta u * s ≤ 16*Delta*q := by
    have h1 : 4*chiA0 Delta u * s ≤ 4*chiA0 Delta u * q :=
      mul_le_mul_of_nonneg_left hsle (by linarith)
    have h2 : 4*chiA0 Delta u * q ≤ 4*(4*Delta) * q :=
      mul_le_mul_of_nonneg_right (by linarith) hq0.le
    linarith
  have hk2 : 2*Delta*s ≤ 2*Delta*q := mul_le_mul_of_nonneg_left hsle (by linarith)
  have hDq : 0 ≤ Delta * q := mul_nonneg hD.le hq0.le
  rw [abs_le]
  rw [htp] at hx1
  rw [htm] at hx2
  constructor <;> nlinarith

/-! ### Bundle -/

/-- `v2 lem:chi_roots`, parts (a)-(e), for `Δ > 0` and `u ∈ [0,1)`; (d) is uniform in
`u ∈ [0,1)` with constant `18` for `Δ ∈ (0,1/50]`. -/
theorem lem_chi_roots :
    (∀ Delta u : ℝ, 0 < Delta → 0 ≤ u → u < 1 →
      continuumPerronRate Delta u ≤ 1 - u ∧
        (continuumPerronRate Delta u = 1 - u ↔ (u = 0 ∧ 1/4 ≤ Delta))) ∧
    (∀ Delta : ℝ, 0 < Delta →
      (Delta ≤ 1/4 → continuumPerronRate Delta 0 = 1 - Real.sqrt (1 - 4*Delta)) ∧
      (1/4 ≤ Delta → continuumPerronRate Delta 0 = 1)) ∧
    (∀ u : ℝ, 0 ≤ u → u < 1 → continuumPerronRate (1/4) u = 1 - u^((1:ℝ)/3)) ∧
    (∀ Delta u : ℝ, 0 < Delta → Delta ≤ 1/50 → 0 ≤ u → u < 1 →
      |continuumPerronRate Delta u - 2*Delta*(1-u)| ≤ 18*Delta*(2*Delta*(1-u))) ∧
    (∀ Delta u : ℝ, 0 < Delta → 0 ≤ u → u < 1 →
      (0 < u → continuumPerronRate Delta u < 4*Delta*(1-u)) ∧
      (u = 0 → continuumPerronRate Delta u ≤ 4*Delta ∧
        (continuumPerronRate Delta u = 4*Delta ↔ Delta = 1/4))) := by
  refine ⟨fun D u hD hu0 hu1 => ⟨chi_roots_a hD hu0 hu1, chi_roots_a_eq_iff hD hu0 hu1⟩,
    fun D hD => ⟨chi_roots_b_le hD, chi_roots_b_ge hD⟩,
    fun u hu0 hu1 => chi_roots_c hu0 hu1,
    fun D u hD hD1 hu0 hu1 => chi_roots_d hD hD1 hu0 hu1,
    fun D u hD hu0 hu1 => ⟨fun h => chi_roots_e hD h hu1, ?_⟩⟩
  rintro rfl
  exact ⟨chi_roots_e_zero_le hD, chi_roots_e_zero_eq_iff hD⟩

end
end SparseSGD.Scaling.Helps
