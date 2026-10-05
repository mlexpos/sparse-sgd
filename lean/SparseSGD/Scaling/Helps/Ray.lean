import SparseSGD.Scaling.Helps.CubicRoots

/-!
# Fastest relaxation along a ray (momentum-helps appendix)

Formalizes `v2 lem:ray` (the fastest relaxation along the ray `u = ν Δ / 2` is
`rayRate ν`, attained uniquely at `Δ = rayDelta ν`) together with the hyperbola
algebra of `v2 cor:samplecost` (Steps 3-5).

All statements assume `ν > 0`.
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD

noncomputable section

/-- `v2 lem:ray`: the optimal step along the ray, `Δ*(ν) = 1/(1+√(1+ν²))`. -/
def rayDelta (nu : ℝ) : ℝ := 1 / (1 + Real.sqrt (1 + nu ^ 2))

/-- `v2 lem:ray`: the optimal rate along the ray, `1 - ν Δ*(ν)`. -/
def rayRate (nu : ℝ) : ℝ := 1 - nu * rayDelta nu

/-- Basic facts about `s = √(1+ν²)`. -/
private theorem sqrt_facts {nu : ℝ} (hnu : 0 < nu) :
    Real.sqrt (1 + nu ^ 2) ^ 2 = 1 + nu ^ 2 ∧ 1 < Real.sqrt (1 + nu ^ 2) ∧
      Real.sqrt (1 + nu ^ 2) < 1 + nu := by
  have hs2 : Real.sqrt (1 + nu ^ 2) ^ 2 = 1 + nu ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (1 + nu ^ 2) := Real.sqrt_nonneg _
  refine ⟨hs2, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- `v2 lem:ray` (R1): bracket identity. -/
theorem spectrumPolynomial_ray (Delta nu mu : ℝ) :
    spectrumPolynomial Delta (nu * Delta / 2) (-mu) =
      -mu * (1 - mu) * (2 - mu) + 4 * (1 - mu) * Delta - 2 * nu * Delta ^ 2 := by
  unfold spectrumPolynomial; ring

/-- `v2 lem:ray` (R2): vertex form of the bracket; concave in `Δ` with maximum
`(1-μ)h(μ)/ν` at `Δ = (1-μ)/ν`. -/
theorem spectrumPolynomial_ray_vertex {nu : ℝ} (hnu : 0 < nu) (Delta mu : ℝ) :
    spectrumPolynomial Delta (nu * Delta / 2) (-mu) =
      (1 - mu) / nu * (nu * mu ^ 2 - 2 * (1 + nu) * mu + 2)
        - 2 * nu * (Delta - (1 - mu) / nu) ^ 2 := by
  rw [spectrumPolynomial_ray]
  field_simp
  ring

/-- `v2 lem:ray` (R2): the maximum of the bracket over `Δ`. -/
theorem spectrumPolynomial_ray_le {nu : ℝ} (hnu : 0 < nu) (Delta mu : ℝ) :
    spectrumPolynomial Delta (nu * Delta / 2) (-mu) ≤
      (1 - mu) / nu * (nu * mu ^ 2 - 2 * (1 + nu) * mu + 2) := by
  rw [spectrumPolynomial_ray_vertex hnu]
  have : 0 ≤ 2 * nu * (Delta - (1 - mu) / nu) ^ 2 := by positivity
  linarith

/-- `v2 lem:ray` (R3): `rayRate ν = (1+ν-√(1+ν²))/ν`. -/
theorem rayRate_eq {nu : ℝ} (hnu : 0 < nu) :
    rayRate nu = (1 + nu - Real.sqrt (1 + nu ^ 2)) / nu := by
  obtain ⟨hs2, hs1, _⟩ := sqrt_facts hnu
  unfold rayRate rayDelta
  have : 0 < 1 + Real.sqrt (1 + nu ^ 2) := by linarith
  field_simp
  nlinarith

/-- `v2 lem:ray` (R3): roots of `h(μ) = ν μ² - 2(1+ν)μ + 2`. -/
theorem ray_quadratic_factor {nu : ℝ} (hnu : 0 < nu) (mu : ℝ) :
    nu * mu ^ 2 - 2 * (1 + nu) * mu + 2 =
      nu * (mu - rayRate nu) * (mu - (1 + nu + Real.sqrt (1 + nu ^ 2)) / nu) := by
  obtain ⟨hs2, hs1, _⟩ := sqrt_facts hnu
  rw [rayRate_eq hnu]
  field_simp
  nlinarith [hs2]

/-- `v2 lem:ray` (R4): `0 < rayDelta ν`. -/
theorem rayDelta_pos {nu : ℝ} (hnu : 0 < nu) : 0 < rayDelta nu := by
  obtain ⟨_, hs1, _⟩ := sqrt_facts hnu
  unfold rayDelta
  have : 0 < 1 + Real.sqrt (1 + nu ^ 2) := by linarith
  positivity

/-- `v2 lem:ray` (R4): `ν Δ* < 1`. -/
theorem nu_mul_rayDelta_lt_one {nu : ℝ} (hnu : 0 < nu) : nu * rayDelta nu < 1 := by
  obtain ⟨_, hs1, hs3⟩ := sqrt_facts hnu
  unfold rayDelta
  have : 0 < 1 + Real.sqrt (1 + nu ^ 2) := by linarith
  rw [mul_one_div, div_lt_one this]
  have hs0 : 0 ≤ Real.sqrt (1 + nu ^ 2) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (1 + nu ^ 2) ^ 2 = 1 + nu ^ 2 := Real.sq_sqrt (by positivity)
  nlinarith

/-- `v2 lem:ray` (R4): `Δ* < 2/ν`. -/
theorem rayDelta_lt_two_div {nu : ℝ} (hnu : 0 < nu) : rayDelta nu < 2 / nu := by
  have h := nu_mul_rayDelta_lt_one hnu
  rw [lt_div_iff₀ hnu]
  linarith

/-- `v2 lem:ray` (R4): `0 < rayRate ν`. -/
theorem rayRate_pos {nu : ℝ} (hnu : 0 < nu) : 0 < rayRate nu := by
  unfold rayRate
  linarith [nu_mul_rayDelta_lt_one hnu]

/-- `v2 lem:ray` (R4): `rayRate ν < 1`. -/
theorem rayRate_lt_one {nu : ℝ} (hnu : 0 < nu) : rayRate nu < 1 := by
  unfold rayRate
  have := mul_pos hnu (rayDelta_pos hnu)
  linarith

/-- `v2 lem:ray` (R4): `Δ* = (1 - rayRate ν)/ν`. -/
theorem rayDelta_eq {nu : ℝ} (hnu : 0 < nu) : rayDelta nu = (1 - rayRate nu) / nu := by
  unfold rayRate
  field_simp
  ring

/-- `v2 lem:ray` (R4): `1 - 2Δ* = (νΔ*)²`. -/
theorem one_sub_two_rayDelta {nu : ℝ} (hnu : 0 < nu) :
    1 - 2 * rayDelta nu = (nu * rayDelta nu) ^ 2 := by
  obtain ⟨hs2, hs1, _⟩ := sqrt_facts hnu
  unfold rayDelta
  have : 0 < 1 + Real.sqrt (1 + nu ^ 2) := by linarith
  field_simp
  nlinarith [hs2]

/-- `v2 lem:ray` (R5): the cubic at `x = -r*` is `-2ν(Δ-Δ*)² ≤ 0`. -/
theorem spectrumPolynomial_ray_at_rayRate {nu : ℝ} (hnu : 0 < nu) (Delta : ℝ) :
    spectrumPolynomial Delta (nu * Delta / 2) (-rayRate nu) =
      -2 * nu * (Delta - rayDelta nu) ^ 2 := by
  rw [spectrumPolynomial_ray_vertex hnu, ← rayDelta_eq hnu]
  have h := ray_quadratic_factor hnu (rayRate nu)
  have h0 : nu * rayRate nu ^ 2 - 2 * (1 + nu) * rayRate nu + 2 = 0 := by
    rw [h]; ring
  rw [h0]; ring

/-- `v2 lem:ray` (R5): nonpositivity. -/
theorem spectrumPolynomial_ray_at_rayRate_le {nu : ℝ} (hnu : 0 < nu) (Delta : ℝ) :
    spectrumPolynomial Delta (nu * Delta / 2) (-rayRate nu) ≤ 0 := by
  rw [spectrumPolynomial_ray_at_rayRate hnu]
  have : 0 ≤ 2 * nu * (Delta - rayDelta nu) ^ 2 := by positivity
  linarith

/-- `v2 lem:ray` (R5): equality iff `Δ = Δ*`. -/
theorem spectrumPolynomial_ray_at_rayRate_eq_zero_iff {nu : ℝ} (hnu : 0 < nu) (Delta : ℝ) :
    spectrumPolynomial Delta (nu * Delta / 2) (-rayRate nu) = 0 ↔ Delta = rayDelta nu := by
  rw [spectrumPolynomial_ray_at_rayRate hnu]
  constructor
  · intro h
    have h2 : (Delta - rayDelta nu) ^ 2 = 0 := by
      have : -2 * nu ≠ 0 := by linarith
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h this
      · exact h
    have := pow_eq_zero_iff (two_ne_zero) |>.1 h2
    linarith
  · intro h; rw [h]; ring

/-- `v2 lem:ray` (R6): `χ'(-r*) = 3r*² - 6r* + 2 + 4Δ* = 2 - 2Δ* > 0`. -/
theorem ray_deriv_at_rayRate {nu : ℝ} (hnu : 0 < nu) :
    3 * (rayRate nu) ^ 2 - 6 * rayRate nu + 2 + 4 * rayDelta nu = 2 - 2 * rayDelta nu := by
  have h := one_sub_two_rayDelta hnu
  unfold rayRate
  nlinarith [h]

/-- `v2 lem:ray` (R6): positivity of `χ'` at the touching point. -/
theorem ray_deriv_at_rayRate_pos {nu : ℝ} (hnu : 0 < nu) :
    0 < 3 * (-rayRate nu) ^ 2 + 6 * (-rayRate nu) + 2 + 4 * rayDelta nu := by
  have h := ray_deriv_at_rayRate hnu
  have h2 := one_sub_two_rayDelta hnu
  have : 0 < (nu * rayDelta nu) ^ 2 := by
    have := mul_pos hnu (rayDelta_pos hnu); positivity
  nlinarith

/-- `v2 lem:ray` (R7): along the ray, `r_c(Δ, νΔ/2) ≤ r*`. -/
theorem continuumPerronRate_ray_le {nu : ℝ} (hnu : 0 < nu) (Delta : ℝ) :
    continuumPerronRate Delta (nu * Delta / 2) ≤ rayRate nu := by
  have := continuumPerronRate_le_of_nonpos (spectrumPolynomial_ray_at_rayRate_le hnu Delta)
  linarith

/-- `v2 lem:ray` (R7): strict inequality for `Δ ≠ Δ*`. -/
theorem continuumPerronRate_ray_lt {nu : ℝ} (hnu : 0 < nu) {Delta : ℝ}
    (hD : Delta ≠ rayDelta nu) :
    continuumPerronRate Delta (nu * Delta / 2) < rayRate nu := by
  have hlt : spectrumPolynomial Delta (nu * Delta / 2) (-rayRate nu) < 0 := by
    rw [spectrumPolynomial_ray_at_rayRate hnu]
    have : 0 < (Delta - rayDelta nu) ^ 2 := by
      have : Delta - rayDelta nu ≠ 0 := sub_ne_zero.2 hD
      positivity
    nlinarith
  have := continuumPerronRate_lt_of_neg hlt
  linarith

/-- `v2 lem:ray` (R8): the rate is attained at `Δ = Δ*`. -/
theorem continuumPerronRate_ray_at_rayDelta {nu : ℝ} (hnu : 0 < nu) :
    continuumPerronRate (rayDelta nu) (nu * rayDelta nu / 2) = rayRate nu := by
  have hroot : spectrumPolynomial (rayDelta nu) (nu * rayDelta nu / 2) (-rayRate nu) = 0 :=
    (spectrumPolynomial_ray_at_rayRate_eq_zero_iff hnu _).2 rfl
  have hr1 := rayRate_lt_one hnu
  have := continuumPerronRate_eq_of_rightmost hroot (by linarith) (ray_deriv_at_rayRate_pos hnu)
  linarith

/-- `v2 lem:ray` (R9): `rayRate ν` is the greatest value of `r_c(Δ, νΔ/2)` over
`Δ ∈ (0, 2/ν)`. -/
theorem lem_ray {nu : ℝ} (hnu : 0 < nu) :
    IsGreatest ((fun D => continuumPerronRate D (nu * D / 2)) '' Set.Ioo 0 (2 / nu))
      (rayRate nu) := by
  refine ⟨⟨rayDelta nu, ⟨rayDelta_pos hnu, rayDelta_lt_two_div hnu⟩, ?_⟩, ?_⟩
  · exact continuumPerronRate_ray_at_rayDelta hnu
  · rintro _ ⟨D, _, rfl⟩
    exact continuumPerronRate_ray_le hnu D

/-- `v2 lem:ray` (R9): the maximizer is unique. -/
theorem lem_ray_unique {nu : ℝ} (hnu : 0 < nu) {D : ℝ} (_hD : D ∈ Set.Ioo 0 (2 / nu))
    (hmax : continuumPerronRate D (nu * D / 2) = rayRate nu) : D = rayDelta nu := by
  by_contra h
  have := continuumPerronRate_ray_lt hnu h
  linarith

/-- `v2 lem:ray` (R9): supremum form. -/
theorem lem_ray_sSup {nu : ℝ} (hnu : 0 < nu) :
    sSup ((fun D => continuumPerronRate D (nu * D / 2)) '' Set.Ioo 0 (2 / nu)) =
      rayRate nu :=
  (lem_ray hnu).csSup_eq

/-- `v2 cor:samplecost` (R10): `1/r* = (1+ν+√(1+ν²))/2`. -/
theorem inv_rayRate {nu : ℝ} (hnu : 0 < nu) :
    1 / rayRate nu = (1 + nu + Real.sqrt (1 + nu ^ 2)) / 2 := by
  obtain ⟨hs2, hs1, _⟩ := sqrt_facts hnu
  have hr := rayRate_pos hnu
  rw [rayRate_eq hnu] at hr ⊢
  have hnum : 0 < 1 + nu - Real.sqrt (1 + nu ^ 2) := by
    have := div_pos_iff.1 hr
    rcases this with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · linarith
  field_simp
  nlinarith [hs2]

/-- `v2 cor:samplecost` (R11): the hyperbola constant. -/
def hyperbolaN (a b : ℝ) : ℝ := (a + b + Real.sqrt (a ^ 2 + b ^ 2)) / 2

/-- `v2 cor:samplecost` (R11): `b / r*(a/b) = N`. -/
theorem hyperbola_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    b / rayRate (a / b) = hyperbolaN a b := by
  have hnu : 0 < a / b := div_pos ha hb
  have h1 := inv_rayRate hnu
  have hsq : Real.sqrt (1 + (a / b) ^ 2) = Real.sqrt (a ^ 2 + b ^ 2) / b := by
    have : 1 + (a / b) ^ 2 = (a ^ 2 + b ^ 2) / b ^ 2 := by field_simp; ring
    rw [this, Real.sqrt_div (by positivity), Real.sqrt_sq hb.le]
  rw [hsq] at h1
  rw [div_eq_mul_one_div, h1]
  unfold hyperbolaN
  field_simp
  ring

/-- `v2 cor:samplecost` (R11): `(N/a - 1)(N/b - 1) = 1/2`. -/
theorem hyperbola_relation {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (hyperbolaN a b / a - 1) * (hyperbolaN a b / b - 1) = 1 / 2 := by
  have hs2 : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  unfold hyperbolaN
  field_simp
  nlinarith [hs2]

/-- `v2 cor:samplecost` (R11): `N ≥ max a b`. -/
theorem hyperbola_ge_max {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    max a b ≤ hyperbolaN a b := by
  have hs2 : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_nonneg _
  have hga : a ≤ Real.sqrt (a ^ 2 + b ^ 2) := by nlinarith
  have hgb : b ≤ Real.sqrt (a ^ 2 + b ^ 2) := by nlinarith
  unfold hyperbolaN
  apply max_le <;> linarith

end
end SparseSGD.Scaling.Helps
