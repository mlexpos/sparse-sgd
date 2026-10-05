import SparseSGD.Logistic.DynamicEnergy
import SparseSGD.Logistic.DynamicPhysical

/-! # v2: the free-energy Lyapunov function of `prop:S`

For the five-moment field `dynamicField r delta Phi` (paper `eq:LR5`) put
`b = Phi/delta` and `Q = R*V - C^2`.  The free energy is
`L = (alpha - r*theta)/delta + Y^2/2 + V/2 - (b/2) log Q`, and its derivative along
solutions is minus the dissipation `Y^2 + (V-b)^2/V + b^2 C^2/(Q V)`. -/
namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000

/-- v2 `eq:LR5-lyap`: the free-energy Lyapunov function
`U/Delta + Y^2/2 + V/2 - (b/2) log Q`, `b = Phi/Delta`.  One definition covers
`Phi = 0` (coefficient of the log vanishes) and `Phi > 0`. -/
def lyapunov (r delta Phi : ℝ) (y : DynamicState) : ℝ :=
  dynamicEnergy r delta y / delta - Phi / (2 * delta) * Real.log (dynamicDeterminant y)

/-- v2 `eq:LR5-dissipation`: the dissipation `Y^2 + (V-b)^2/V + b^2 C^2/(Q V)`. -/
def dissipation (delta Phi : ℝ) (y : DynamicState) : ℝ :=
  (y 1) ^ 2 + (y 3 - Phi / delta) ^ 2 / y 3 +
    (Phi / delta) ^ 2 * (y 4) ^ 2 / (dynamicDeterminant y * y 3)

/-- v2 `eq:LR5-lyap`: expanded form `(alpha - r theta)/delta + Y^2/2 + V/2 - (b/2) log Q`. -/
theorem lyapunov_eq (r delta Phi : ℝ) (y : DynamicState) (hdelta : delta ≠ 0) :
    lyapunov r delta Phi y =
      (dynamicAlpha r y - r * y 0) / delta + (y 1) ^ 2 / 2 + y 3 / 2 -
        (Phi / delta) / 2 * Real.log (dynamicDeterminant y) := by
  unfold lyapunov dynamicEnergy
  field_simp
  ring

/-- v2 prop:S proof step 1, `eq:LR5-dissipation`: along a solution with `Q > 0`
and `V > 0`, `L' = -(Y^2 + (V-b)^2/V + b^2 C^2/(Q V))`. -/
theorem hasDerivAt_lyapunov (r delta Phi : ℝ) (y : ℝ → DynamicState) (t : ℝ)
    (hdelta : 0 < delta)
    (hy : HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hQ : 0 < dynamicDeterminant (y t)) (hV : 0 < y t 3) :
    HasDerivAt (fun s => lyapunov r delta Phi (y s))
      (-dissipation delta Phi (y t)) t := by
  have hE := (hasDerivAt_dynamicEnergy r delta Phi y t hdelta.ne' hy).div_const delta
  have hQd := hasDerivAt_dynamicDeterminant r delta Phi y t hy
  have hL := (hQd.log hQ.ne').const_mul (Phi / (2 * delta))
  refine (hE.sub hL).congr_deriv ?_
  have hQ0 := hQ.ne'
  have hV0 := hV.ne'
  have hd0 := hdelta.ne'
  unfold dissipation
  have hQdef : y t 2 * y t 3 = dynamicDeterminant (y t) + y t 4 ^ 2 := by
    unfold dynamicDeterminant; ring
  generalize dynamicDeterminant (y t) = Q at *
  field_simp
  linear_combination (-Phi ^ 2) * hQdef

/-- v2 prop:S (zero load), `eq:LR5-dissipation` at `Phi = 0`: `L' = -(Y^2 + V)`
with no positivity hypotheses. -/
theorem hasDerivAt_lyapunov_zero_load (r delta : ℝ) (y : ℝ → DynamicState) (t : ℝ)
    (hdelta : 0 < delta)
    (hy : HasDerivAt y (dynamicField r delta 0 (y t)) t) :
    HasDerivAt (fun s => lyapunov r delta 0 (y s)) (-((y t 1) ^ 2 + y t 3)) t := by
  have hE := (hasDerivAt_dynamicEnergy r delta 0 y t hdelta.ne' hy).div_const delta
  have : (fun s => lyapunov r delta 0 (y s)) =
      fun s => dynamicEnergy r delta (y s) / delta := by
    funext s; simp [lyapunov]
  rw [this]
  convert hE using 1
  field_simp
  ring

/-- v2 `eq:LR5-dissipation` at `Phi = 0`: the dissipation is `Y^2 + V`, for all
states (Lean's `0/0 = 0` handles `V = 0`). -/
theorem dissipation_zero_load (delta : ℝ) (y : DynamicState) :
    dissipation delta 0 y = (y 1) ^ 2 + y 3 := by
  unfold dissipation
  by_cases hV : y 3 = 0
  · simp [hV]
  · simp
    field_simp

/-- v2 prop:S proof step 1: `Q' = -2Q + 2 b R`, restating
`hasDerivAt_dynamicDeterminant` (`2 Phi/delta = 2 b`). -/
theorem v2_determinant_derivative (r delta Phi : ℝ) (y : ℝ → DynamicState) (t : ℝ)
    (hy : HasDerivAt y (dynamicField r delta Phi (y t)) t) :
    HasDerivAt (fun s => dynamicDeterminant (y s))
      (-2 * dynamicDeterminant (y t) + 2 * (Phi / delta) * y t 2) t := by
  have h := hasDerivAt_dynamicDeterminant r delta Phi y t hy
  convert h using 1
  ring

/-- v2 prop:S (dissipation sign): `dissipation >= 0` when `V > 0`, `Q > 0`. -/
theorem dissipation_nonneg (delta Phi : ℝ) (y : DynamicState)
    (hV : 0 < y 3) (hQ : 0 < dynamicDeterminant y) : 0 ≤ dissipation delta Phi y := by
  unfold dissipation
  have : 0 ≤ (Phi / delta) ^ 2 * (y 4) ^ 2 / (dynamicDeterminant y * y 3) :=
    div_nonneg (by positivity) (mul_nonneg hQ.le hV.le)
  have h2 : 0 ≤ (y 3 - Phi / delta) ^ 2 / y 3 := div_nonneg (sq_nonneg _) hV.le
  have := sq_nonneg (y 1)
  linarith

/-- v2 prop:S (LaSalle step): for `Phi, delta > 0`, `V > 0`, `Q > 0`, the dissipation
vanishes iff `Y = 0`, `V = b` and `C = 0`. -/
theorem dissipation_eq_zero_iff (delta Phi : ℝ) (y : DynamicState)
    (hPhi : 0 < Phi) (hdelta : 0 < delta) (hV : 0 < y 3)
    (hQ : 0 < dynamicDeterminant y) :
    dissipation delta Phi y = 0 ↔ y 1 = 0 ∧ y 3 = Phi / delta ∧ y 4 = 0 := by
  have hb : 0 < Phi / delta := div_pos hPhi hdelta
  unfold dissipation
  have h1 : 0 ≤ (y 1) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (y 3 - Phi / delta) ^ 2 / y 3 := div_nonneg (sq_nonneg _) hV.le
  have h3 : 0 ≤ (Phi / delta) ^ 2 * (y 4) ^ 2 / (dynamicDeterminant y * y 3) :=
    div_nonneg (by positivity) (mul_nonneg hQ.le hV.le)
  have hden : 0 < dynamicDeterminant y * y 3 := mul_pos hQ hV
  constructor
  · intro h
    have e1 : (y 1) ^ 2 = 0 := by linarith
    have e2 : (y 3 - Phi / delta) ^ 2 / y 3 = 0 := by linarith
    have e3 : (Phi / delta) ^ 2 * (y 4) ^ 2 / (dynamicDeterminant y * y 3) = 0 := by linarith
    refine ⟨pow_eq_zero_iff (two_ne_zero) |>.1 e1, ?_, ?_⟩
    · have := (div_eq_zero_iff.1 e2).resolve_right hV.ne'
      have := pow_eq_zero_iff (two_ne_zero) |>.1 this
      linarith
    · have := (div_eq_zero_iff.1 e3).resolve_right hden.ne'
      have h4 : (y 4) ^ 2 = 0 := by
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (by positivity)
        · exact h
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h4
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    simp

/-- v2 prop:S (observability determinant): the Hessian of the potential
`exp((theta^2+R-r^2)/2) - r theta` in `(theta, R)` has determinant `alpha^2/4`;
here `alpha(1+theta^2)`, `alpha theta/2`, `alpha/4` are the entries
`U_{theta theta}`, `U_{theta R}`, `U_{R R}` divided by the common factor. -/
theorem potential_hessian_det (alpha theta : ℝ) :
    (alpha * (1 + theta ^ 2)) * (alpha / 4) - (alpha * theta / 2) ^ 2 = alpha ^ 2 / 4 := by
  ring

/-- Elementary: `log x <= x/k + log k - 1` for `x, k > 0`. -/
theorem log_le_div_add_log (x k : ℝ) (hx : 0 < x) (hk : 0 < k) :
    Real.log x ≤ x / k + Real.log k - 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hk)
  rw [Real.log_div hx.ne' hk.ne'] at h
  linarith

/-- On a physical state with `Q > 0`, both `R` and `V` are positive. -/
theorem pos_of_physical_det_pos (y : DynamicState) (hy : dynamicPhysical y)
    (hQ : 0 < dynamicDeterminant y) : 0 < y 2 ∧ 0 < y 3 := by
  obtain ⟨hR, hV, _⟩ := hy
  unfold dynamicDeterminant at hQ
  refine ⟨?_, ?_⟩
  · rcases hR.lt_or_eq with h | h
    · exact h
    · rw [← h] at hQ; nlinarith [sq_nonneg (y 4)]
  · rcases hV.lt_or_eq with h | h
    · exact h
    · rw [← h] at hQ; nlinarith [sq_nonneg (y 4)]

/-- v2 prop:S (coercivity, step 3): for physical `y` with `Q > 0`, `delta > 0`,
`Phi >= 0`, `L >= (1 + theta^2/4 + R/4 - 3 r^2/2)/delta + Y^2/2 + V/4
 - (b/2)(log(2 Phi) + log(2 b) - 2)`, `b = Phi/delta`.  At `Phi = 0` the last
term is `0` (`b = 0`), i.e. it is omitted, as in the paper. -/
theorem lyapunov_lower_bound (r delta Phi : ℝ) (y : DynamicState)
    (hy : dynamicPhysical y) (hQ : 0 < dynamicDeterminant y)
    (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) :
    (1 + (y 0) ^ 2 / 4 + y 2 / 4 - 3 * r ^ 2 / 2) / delta + (y 1) ^ 2 / 2 + y 3 / 4 -
        (Phi / delta) / 2 * (Real.log (2 * Phi) + Real.log (2 * (Phi / delta)) - 2) ≤
      lyapunov r delta Phi y := by
  have hco := dynamicEnergy_coercive r delta y
  have hE : (1 + (y 0) ^ 2 / 4 + y 2 / 2 - 3 * r ^ 2 / 2) / delta + (y 1) ^ 2 / 2 + y 3 / 2 ≤
      dynamicEnergy r delta y / delta := by
    have h0 : (1 + (y 0) ^ 2 / 4 + y 2 / 2 - 3 * r ^ 2 / 2 + delta / 2 * ((y 1) ^ 2 + y 3)) / delta ≤
        dynamicEnergy r delta y / delta :=
      div_le_div_of_nonneg_right (by linarith) hdelta.le
    have h1 : (1 + (y 0) ^ 2 / 4 + y 2 / 2 - 3 * r ^ 2 / 2 + delta / 2 * ((y 1) ^ 2 + y 3)) / delta =
        (1 + (y 0) ^ 2 / 4 + y 2 / 2 - 3 * r ^ 2 / 2) / delta + (y 1) ^ 2 / 2 + y 3 / 2 := by
      field_simp
      ring
    linarith
  have e5 : (1 + (y 0) ^ 2 / 4 + y 2 / 4 - 3 * r ^ 2 / 2) / delta =
      (1 + (y 0) ^ 2 / 4 + y 2 / 2 - 3 * r ^ 2 / 2) / delta - y 2 / (4 * delta) := by
    field_simp; ring
  rcases hPhi.lt_or_eq with hP | hP
  · obtain ⟨hR, hV⟩ := pos_of_physical_det_pos y hy hQ
    have hb : 0 < Phi / delta := div_pos hP hdelta
    have hQle : Real.log (dynamicDeterminant y) ≤ Real.log (y 2) + Real.log (y 3) := by
      rw [← Real.log_mul hR.ne' hV.ne']
      exact Real.log_le_log hQ (by unfold dynamicDeterminant; nlinarith [sq_nonneg (y 4)])
    have h1 := log_le_div_add_log (y 2) (2 * Phi) hR (by linarith)
    have h2 := log_le_div_add_log (y 3) (2 * (Phi / delta)) hV (by linarith)
    have hkey : Phi / (2 * delta) * Real.log (dynamicDeterminant y) ≤
        Phi / (2 * delta) * (Real.log (y 2) + Real.log (y 3)) :=
      mul_le_mul_of_nonneg_left hQle (by positivity)
    have e1 : Phi / (2 * delta) * (y 2 / (2 * Phi)) = y 2 / (4 * delta) := by
      field_simp; ring
    have e2 : Phi / (2 * delta) * (y 3 / (2 * (Phi / delta))) = y 3 / 4 := by
      field_simp; norm_num
    have hmul := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
      (show 0 ≤ Phi / (2 * delta) by positivity)
    have e3 : Phi / (2 * delta) = (Phi / delta) / 2 := by field_simp
    have e4 : (y 2 / (2 * Phi) + Real.log (2 * Phi) - 1 +
        (y 3 / (2 * (Phi / delta)) + Real.log (2 * (Phi / delta)) - 1)) =
        y 2 / (2 * Phi) + y 3 / (2 * (Phi / delta)) +
          (Real.log (2 * Phi) + Real.log (2 * (Phi / delta)) - 2) := by ring
    have hexp : Phi / (2 * delta) * (y 2 / (2 * Phi) + y 3 / (2 * (Phi / delta)) +
        (Real.log (2 * Phi) + Real.log (2 * (Phi / delta)) - 2)) =
        Phi / (2 * delta) * (y 2 / (2 * Phi)) + Phi / (2 * delta) * (y 3 / (2 * (Phi / delta))) +
        Phi / (2 * delta) * (Real.log (2 * Phi) + Real.log (2 * (Phi / delta)) - 2) := by ring
    rw [e4, hexp, e1, e2] at hmul
    unfold lyapunov
    rw [← e3]
    linarith
  · subst hP
    have hR : 0 ≤ y 2 := hy.1
    have hq : 0 ≤ y 2 / 4 / delta := by positivity
    have e : (1 + (y 0) ^ 2 / 4 + y 2 / 4 - 3 * r ^ 2 / 2) / delta + y 2 / 4 / delta =
        (1 + (y 0) ^ 2 / 4 + y 2 / 2 - 3 * r ^ 2 / 2) / delta := by field_simp; ring
    have hV : 0 ≤ y 3 := hy.2.1
    simp only [lyapunov, zero_div, zero_mul, sub_zero, mul_zero]
    linarith

/-- Explicit bound `B(E, r, delta, Phi)` for the norm on Lyapunov sublevel sets:
`1 + 4 (delta+1) (|E| + (b/2)|log(2 Phi) + log(2 b) - 2| + 3 r^2/(2 delta))`,
`b = Phi/delta`. -/
def lyapunovBound (r delta Phi E : ℝ) : ℝ :=
  1 + 4 * (delta + 1) * (|E| +
    (Phi / delta) / 2 * |Real.log (2 * Phi) + Real.log (2 * (Phi / delta)) - 2| +
    3 * r ^ 2 / (2 * delta))

/-- v2 prop:S (sublevel sets are bounded): for physical `y` with `Q > 0`,
`L(y) <= E` implies `‖y‖ <= lyapunovBound r delta Phi E`. -/
theorem lyapunov_sublevel_norm_le (r delta Phi E : ℝ) (y : DynamicState)
    (hy : dynamicPhysical y) (hQ : 0 < dynamicDeterminant y)
    (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) (hE : lyapunov r delta Phi y ≤ E) :
    ‖y‖ ≤ lyapunovBound r delta Phi E := by
  have hlow := lyapunov_lower_bound r delta Phi y hy hQ hdelta hPhi
  obtain ⟨hR, hV, hC⟩ := hy
  set b := Phi / delta with hbdef
  have hb : 0 ≤ b := div_nonneg hPhi hdelta.le
  set L := Real.log (2 * Phi) + Real.log (2 * b) - 2 with hL
  set W := |E| + b / 2 * |L| + 3 * r ^ 2 / (2 * delta) with hW
  have hbL : b / 2 * L ≤ b / 2 * |L| := mul_le_mul_of_nonneg_left (le_abs_self L) (by positivity)
  have hr : 3 * r ^ 2 / 2 / delta = 3 * r ^ 2 / (2 * delta) := by field_simp
  have hS : (1 + (y 0) ^ 2 / 4 + y 2 / 4) / delta + (y 1) ^ 2 / 2 + y 3 / 4 ≤ W := by
    have e : (1 + (y 0) ^ 2 / 4 + y 2 / 4 - 3 * r ^ 2 / 2) / delta =
        (1 + (y 0) ^ 2 / 4 + y 2 / 4) / delta - 3 * r ^ 2 / (2 * delta) := by
      rw [sub_div, hr]
    rw [e] at hlow
    have := le_abs_self E
    linarith
  have hmain : 1 + (y 0) ^ 2 / 4 + y 2 / 4 + delta * ((y 1) ^ 2 / 2 + y 3 / 4) ≤ delta * W := by
    have h1 := mul_le_mul_of_nonneg_left hS hdelta.le
    have h0 : (1 + (y 0) ^ 2 / 4 + y 2 / 4) / delta * delta = 1 + (y 0) ^ 2 / 4 + y 2 / 4 :=
      div_mul_cancel₀ _ hdelta.ne'
    nlinarith
  have hk : 0 ≤ delta * ((y 1) ^ 2 / 2 + y 3 / 4) := by positivity
  have hth : (y 0) ^ 2 ≤ 4 * (delta * W) := by nlinarith [sq_nonneg (y 0)]
  have hR' : y 2 ≤ 4 * (delta * W) := by nlinarith [sq_nonneg (y 0)]
  have hY : (y 1) ^ 2 ≤ 2 * W := by
    have : delta * (y 1 ^ 2) ≤ delta * (2 * W) := by nlinarith [sq_nonneg (y 0), mul_nonneg hdelta.le hV]
    exact le_of_mul_le_mul_left this hdelta
  have hV' : y 3 ≤ 4 * W := by
    have : delta * (y 3) ≤ delta * (4 * W) := by nlinarith [sq_nonneg (y 0), mul_nonneg hdelta.le (sq_nonneg (y 1))]
    exact le_of_mul_le_mul_left this hdelta
  have hdW : 0 < delta * W := by nlinarith [sq_nonneg (y 0)]
  have hW0 : 0 < W := by
    by_contra h
    have h' := not_lt.mp h
    nlinarith
  have hB : lyapunovBound r delta Phi E = 1 + 4 * (delta + 1) * W := rfl
  rw [hB]
  have hB0 : 0 ≤ 1 + 4 * (delta + 1) * W := by positivity
  have hdW' : 4 * (delta + 1) * W = 4 * (delta * W) + 4 * W := by ring
  apply (pi_norm_le_iff_of_nonneg hB0).2
  intro i
  fin_cases i
  · change |y 0| ≤ _
    nlinarith [sq_abs (y 0), sq_nonneg (|y 0| - 1 / 2)]
  · change |y 1| ≤ _
    nlinarith [sq_abs (y 1), sq_nonneg (|y 1| - 1 / 2)]
  · change |y 2| ≤ _
    rw [abs_of_nonneg hR]
    linarith
  · change |y 3| ≤ _
    rw [abs_of_nonneg hV]
    linarith
  · change |y 4| ≤ _
    have hab : |y 4| ≤ y 2 + y 3 := by
      nlinarith [sq_abs (y 4), sq_nonneg (y 2 - y 3), abs_nonneg (y 4)]
    linarith

/-- v2 prop:S (determinant stays away from `0` on sublevel sets, `Phi > 0`):
`L(y) <= E` implies `exp(-2 delta (E + 3 r^2/(2 delta))/Phi) <= Q`. -/
theorem lyapunov_sublevel_det_lower (r delta Phi E : ℝ) (y : DynamicState)
    (hy : dynamicPhysical y) (hQ : 0 < dynamicDeterminant y)
    (hdelta : 0 < delta) (hPhi : 0 < Phi) (hE : lyapunov r delta Phi y ≤ E) :
    Real.exp (-2 * delta * (E + 3 * r ^ 2 / (2 * delta)) / Phi) ≤ dynamicDeterminant y := by
  have hco := dynamicEnergy_coercive r delta y
  obtain ⟨hR, hV, _⟩ := hy
  have hen : -(3 * r ^ 2 / 2) ≤ dynamicEnergy r delta y := by
    have : 0 ≤ delta / 2 * ((y 1) ^ 2 + y 3) := by positivity
    nlinarith [sq_nonneg (y 0)]
  have hen' : -(3 * r ^ 2 / 2) / delta ≤ dynamicEnergy r delta y / delta :=
    div_le_div_of_nonneg_right hen hdelta.le
  unfold lyapunov at hE
  have h1 : -(3 * r ^ 2 / 2) / delta - E ≤ Phi / (2 * delta) * Real.log (dynamicDeterminant y) := by
    linarith
  have h2 : -2 * delta * (E + 3 * r ^ 2 / (2 * delta)) ≤
      Real.log (dynamicDeterminant y) * Phi := by
    have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * delta by positivity)
    have e1 : 2 * delta * (-(3 * r ^ 2 / 2) / delta - E) = -2 * delta * (E + 3 * r ^ 2 / (2 * delta)) := by
      field_simp; ring
    have e2 : 2 * delta * (Phi / (2 * delta) * Real.log (dynamicDeterminant y)) =
        Real.log (dynamicDeterminant y) * Phi := by
      field_simp
    rw [e1, e2] at h3
    exact h3
  have h4 : -2 * delta * (E + 3 * r ^ 2 / (2 * delta)) / Phi ≤ Real.log (dynamicDeterminant y) :=
    (div_le_iff₀ hPhi).2 h2
  exact (Real.le_log_iff_exp_le hQ).1 h4

/-- v2 prop:S (`V` stays away from `0` on sublevel sets, `Phi > 0`):
`V >= exp(-2 delta (E + 3 r^2/(2 delta))/Phi) / B`. -/
theorem lyapunov_sublevel_V_lower (r delta Phi E : ℝ) (y : DynamicState)
    (hy : dynamicPhysical y) (hQ : 0 < dynamicDeterminant y)
    (hdelta : 0 < delta) (hPhi : 0 < Phi) (hE : lyapunov r delta Phi y ≤ E) :
    Real.exp (-2 * delta * (E + 3 * r ^ 2 / (2 * delta)) / Phi) / lyapunovBound r delta Phi E ≤
      y 3 := by
  have hdet := lyapunov_sublevel_det_lower r delta Phi E y hy hQ hdelta hPhi hE
  have hnorm := lyapunov_sublevel_norm_le r delta Phi E y hy hQ hdelta hPhi.le hE
  have hBpos : 0 < lyapunovBound r delta Phi E := by
    unfold lyapunovBound
    have : 0 ≤ 4 * (delta + 1) * (|E| +
      (Phi / delta) / 2 * |Real.log (2 * Phi) + Real.log (2 * (Phi / delta)) - 2| +
      3 * r ^ 2 / (2 * delta)) := by positivity
    linarith
  have hR : y 2 ≤ lyapunovBound r delta Phi E :=
    (le_abs_self (y 2)).trans ((norm_le_pi_norm y 2).trans hnorm)
  apply (div_le_iff₀ hBpos).2
  have hQle : dynamicDeterminant y ≤ y 2 * y 3 := by
    unfold dynamicDeterminant; nlinarith [sq_nonneg (y 4)]
  calc _ ≤ dynamicDeterminant y := hdet
    _ ≤ y 2 * y 3 := hQle
    _ ≤ lyapunovBound r delta Phi E * y 3 := mul_le_mul_of_nonneg_right hR hy.2.1
    _ = y 3 * lyapunovBound r delta Phi E := mul_comm _ _

/-- v2 prop:S (sublevel bounds), combined statement: norm bound, and for `Phi > 0` the
lower bounds on `Q` and `V`. -/
theorem lyapunov_sublevel_bounds (r delta Phi E : ℝ) (y : DynamicState)
    (hy : dynamicPhysical y) (hQ : 0 < dynamicDeterminant y)
    (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) (hE : lyapunov r delta Phi y ≤ E) :
    ‖y‖ ≤ lyapunovBound r delta Phi E ∧
      (0 < Phi →
        Real.exp (-2 * delta * (E + 3 * r ^ 2 / (2 * delta)) / Phi) ≤ dynamicDeterminant y ∧
        Real.exp (-2 * delta * (E + 3 * r ^ 2 / (2 * delta)) / Phi) /
          lyapunovBound r delta Phi E ≤ y 3) :=
  ⟨lyapunov_sublevel_norm_le r delta Phi E y hy hQ hdelta hPhi hE,
    fun hP => ⟨lyapunov_sublevel_det_lower r delta Phi E y hy hQ hdelta hP hE,
      lyapunov_sublevel_V_lower r delta Phi E y hy hQ hdelta hP hE⟩⟩

/-- Sum-of-squares form of the log-determinant Hessian numerator
(`beta^2 - 2 gamma Q` for the line `Q + beta t + gamma t^2`). -/
theorem logdet_hessian_sos (R V C d2 d3 d4 : ℝ) (hR : R ≠ 0) :
    (d2 * V + R * d3 - 2 * C * d4) ^ 2 - 2 * (d2 * d3 - d4 ^ 2) * (R * V - C ^ 2) =
      (R * V - C ^ 2) ^ 2 * d2 ^ 2 / R ^ 2 + (R * d3 - 2 * C * d4 + C ^ 2 * d2 / R) ^ 2 +
        2 * (R * V - C ^ 2) * (d4 - C * d2 / R) ^ 2 := by
  field_simp
  ring

/-- Pointwise positivity of the second derivative of `L` along a line (nonzero
direction `d`), at a state with `R > 0`, `Q > 0`. -/
theorem lyapunov_hessian_pos (δ Φ e θ R V C d0 d1 d2 d3 d4 : ℝ) (hδ : 0 < δ) (hΦ : 0 < Φ)
    (he : 0 < e) (hR : 0 < R) (hQ : 0 < R * V - C ^ 2)
    (hd : ¬(d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ d3 = 0 ∧ d4 = 0)) :
    0 < (e * ((θ * d0 + d2 / 2) ^ 2 + d0 ^ 2) + δ / 2 * (2 * d1 ^ 2)) / δ -
      Φ / (2 * δ) * ((2 * (d2 * d3 - d4 ^ 2) * (R * V - C ^ 2) -
        (d2 * V + R * d3 - 2 * C * d4) ^ 2) / (R * V - C ^ 2) ^ 2) := by
  have hsos := logdet_hessian_sos R V C d2 d3 d4 hR.ne'
  generalize hS : (d2 * V + R * d3 - 2 * C * d4) ^ 2 - 2 * (d2 * d3 - d4 ^ 2) * (R * V - C ^ 2) = S at hsos
  generalize hQd : R * V - C ^ 2 = Q at *
  have hQ2 : 0 < Q ^ 2 := by positivity
  have hexpr : (e * ((θ * d0 + d2 / 2) ^ 2 + d0 ^ 2) + δ / 2 * (2 * d1 ^ 2)) / δ -
      Φ / (2 * δ) * ((2 * (d2 * d3 - d4 ^ 2) * Q - (d2 * V + R * d3 - 2 * C * d4) ^ 2) / Q ^ 2) =
      e * ((θ * d0 + d2 / 2) ^ 2 + d0 ^ 2) / δ + d1 ^ 2 + Φ / (2 * δ) * (S / Q ^ 2) := by
    rw [← hS]
    field_simp
    ring
  rw [hexpr]
  have hS0 : 0 ≤ S := by
    rw [hsos]; positivity
  have hT1 : 0 ≤ e * ((θ * d0 + d2 / 2) ^ 2 + d0 ^ 2) / δ := by positivity
  have hT3 : 0 ≤ Φ / (2 * δ) * (S / Q ^ 2) := by positivity
  have hT2 := sq_nonneg d1
  by_contra hle
  have hle := not_lt.mp hle
  have h1 : e * ((θ * d0 + d2 / 2) ^ 2 + d0 ^ 2) / δ = 0 := by linarith
  have h2 : d1 ^ 2 = 0 := by linarith
  have h3 : Φ / (2 * δ) * (S / Q ^ 2) = 0 := by linarith
  have hd1 : d1 = 0 := pow_eq_zero_iff two_ne_zero |>.1 h2
  have h1' : (θ * d0 + d2 / 2) ^ 2 + d0 ^ 2 = 0 := by
    rcases div_eq_zero_iff.1 h1 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h he.ne'
      · exact h
    · exact absurd h hδ.ne'
  have hd0 : d0 = 0 := by nlinarith [sq_nonneg (θ * d0 + d2 / 2), sq_nonneg d0]
  have hd2 : d2 = 0 := by
    have : (θ * d0 + d2 / 2) ^ 2 = 0 := by nlinarith [sq_nonneg (θ * d0 + d2 / 2), sq_nonneg d0]
    have := pow_eq_zero_iff two_ne_zero |>.1 this
    rw [hd0] at this
    linarith
  have hS' : S = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h (by positivity)
    · rcases div_eq_zero_iff.1 h with h | h
      · exact h
      · exact absurd h hQ2.ne'
  rw [hS', hd2] at hsos
  simp at hsos
  have hA : 0 ≤ (R * d3 - 2 * C * d4) ^ 2 := sq_nonneg _
  have hB : 0 ≤ 2 * Q * d4 ^ 2 := by positivity
  have hd4 : d4 = 0 := by
    have : 2 * Q * d4 ^ 2 = 0 := by nlinarith
    have h4 : d4 ^ 2 = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (by positivity)
      · exact h
    exact pow_eq_zero_iff two_ne_zero |>.1 h4
  have hd3 : d3 = 0 := by
    subst hd4
    have : (R * d3) ^ 2 = 0 := by nlinarith
    have := pow_eq_zero_iff two_ne_zero |>.1 this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hR.ne'
    · exact h
  exact hd ⟨hd0, hd1, hd2, hd3, hd4⟩

/-- The Lyapunov function restricted to the line `t ↦ p + t d`. -/
def lineLyap (r δ Φ : ℝ) (p d : DynamicState) (t : ℝ) : ℝ :=
  lyapunov r δ Φ (fun i => p i + t * d i)

def lineQ (p d : DynamicState) (t : ℝ) : ℝ :=
  (p 2 + t * d 2) * (p 3 + t * d 3) - (p 4 + t * d 4) ^ 2

def lineQ' (p d : DynamicState) (t : ℝ) : ℝ :=
  d 2 * (p 3 + t * d 3) + (p 2 + t * d 2) * d 3 - 2 * (p 4 + t * d 4) * d 4

def lineG (r : ℝ) (p d : DynamicState) (t : ℝ) : ℝ :=
  ((p 0 + t * d 0) ^ 2 + (p 2 + t * d 2) - r ^ 2) / 2

def lineF (r δ Φ : ℝ) (p d : DynamicState) (t : ℝ) : ℝ :=
  (Real.exp (lineG r p d t) * ((p 0 + t * d 0) * d 0 + d 2 / 2) - r * d 0 +
      δ / 2 * (2 * (p 1 + t * d 1) * d 1 + d 3)) / δ -
    Φ / (2 * δ) * (lineQ' p d t / lineQ p d t)

def lineF2 (r δ Φ : ℝ) (p d : DynamicState) (t : ℝ) : ℝ :=
  (Real.exp (lineG r p d t) * (((p 0 + t * d 0) * d 0 + d 2 / 2) ^ 2 + d 0 ^ 2) +
      δ / 2 * (2 * d 1 ^ 2)) / δ -
    Φ / (2 * δ) * ((2 * (d 2 * d 3 - d 4 ^ 2) * lineQ p d t - lineQ' p d t ^ 2) /
      lineQ p d t ^ 2)

theorem lineLyap_eq (r δ Φ : ℝ) (p d : DynamicState) :
    lineLyap r δ Φ p d = fun t =>
      (Real.exp (lineG r p d t) - r * (p 0 + t * d 0) +
        δ / 2 * ((p 1 + t * d 1) ^ 2 + (p 3 + t * d 3))) / δ -
        Φ / (2 * δ) * Real.log (lineQ p d t) := rfl

theorem hasDerivAt_aff (p d : DynamicState) (i : Fin 5) (t : ℝ) :
    HasDerivAt (fun t : ℝ => p i + t * d i) (d i) t := by
  simpa using ((hasDerivAt_id t).mul_const (d i)).const_add (p i)

theorem hasDerivAt_lineG (r : ℝ) (p d : DynamicState) (t : ℝ) :
    HasDerivAt (lineG r p d) ((p 0 + t * d 0) * d 0 + d 2 / 2) t := by
  have h := ((((hasDerivAt_aff p d 0 t).pow 2).add (hasDerivAt_aff p d 2 t)).sub_const
    (r ^ 2)).div_const 2
  exact h.congr_deriv (by simp; ring)

theorem hasDerivAt_lineQ (p d : DynamicState) (t : ℝ) :
    HasDerivAt (lineQ p d) (lineQ' p d t) t := by
  have h := ((hasDerivAt_aff p d 2 t).mul (hasDerivAt_aff p d 3 t)).sub
    ((hasDerivAt_aff p d 4 t).pow 2)
  exact h.congr_deriv (by simp [lineQ'])

theorem hasDerivAt_lineQ' (p d : DynamicState) (t : ℝ) :
    HasDerivAt (lineQ' p d) (2 * (d 2 * d 3 - d 4 ^ 2)) t := by
  have h := (((hasDerivAt_aff p d 3 t).const_mul (d 2)).add
    ((hasDerivAt_aff p d 2 t).mul_const (d 3))).sub
    (((hasDerivAt_aff p d 4 t).const_mul 2).mul_const (d 4))
  exact h.congr_deriv (by ring)

theorem hasDerivAt_lineLyap (r δ Φ : ℝ) (p d : DynamicState) (t : ℝ)
    (hq : lineQ p d t ≠ 0) :
    HasDerivAt (lineLyap r δ Φ p d) (lineF r δ Φ p d t) t := by
  rw [lineLyap_eq]
  have hg := (hasDerivAt_lineG r p d t).exp
  have hE := ((hg.sub ((hasDerivAt_aff p d 0 t).const_mul r)).add
    ((((hasDerivAt_aff p d 1 t).pow 2).add (hasDerivAt_aff p d 3 t)).const_mul (δ / 2)))
  have hL := ((hasDerivAt_lineQ p d t).log hq).const_mul (Φ / (2 * δ))
  exact ((hE.div_const δ).sub hL).congr_deriv (by simp [lineF])

theorem hasDerivAt_lineF (r δ Φ : ℝ) (p d : DynamicState) (t : ℝ)
    (hq : lineQ p d t ≠ 0) :
    HasDerivAt (lineF r δ Φ p d) (lineF2 r δ Φ p d t) t := by
  have hg := (hasDerivAt_lineG r p d t).exp
  have hθ := (hasDerivAt_aff p d 0 t).mul_const (d 0)
  have h1 := (hg.mul (hθ.add_const (d 2 / 2)))
  have h2 := ((hasDerivAt_aff p d 1 t).const_mul 2).mul_const (d 1)
  have h3 := ((h1.sub_const (r * d 0)).add ((h2.add_const (d 3)).const_mul (δ / 2))).div_const δ
  have h4 := ((hasDerivAt_lineQ' p d t).div (hasDerivAt_lineQ p d t) hq).const_mul (Φ / (2 * δ))
  exact (h3.sub h4).congr_deriv (by simp [lineF2]; ring)

/-- The open convex cone of positive definite covariance blocks. -/
def lyapunovDomain : Set DynamicState :=
  {y | 0 < y 2 ∧ 0 < y 3 ∧ (y 4) ^ 2 < y 2 * y 3}

theorem pos_comb (a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hu : 0 < u) (hv : 0 < v) : 0 < a * u + b * v := by
  rcases ha.lt_or_eq with h | h
  · nlinarith [mul_pos h hu, mul_nonneg hb hv.le]
  · subst h
    have : b = 1 := by linarith
    subst this
    simpa using hv

theorem cross_pos (Rx Vx Cx Ry Vy Cy : ℝ) (hRx : 0 < Rx) (hVx : 0 < Vx) (hRy : 0 < Ry)
    (hVy : 0 < Vy) (hx : Cx ^ 2 < Rx * Vx) (hy : Cy ^ 2 < Ry * Vy) :
    2 * Cx * Cy < Rx * Vy + Ry * Vx := by
  have h1 : (2 * Cx * Cy) ^ 2 < (Rx * Vy + Ry * Vx) ^ 2 := by
    have h2 : Cx ^ 2 * Cy ^ 2 < (Rx * Vx) * (Ry * Vy) :=
      mul_lt_mul'' hx hy (sq_nonneg _) (sq_nonneg _)
    nlinarith [sq_nonneg (Rx * Vy - Ry * Vx)]
  have := abs_lt_of_sq_lt_sq h1 (by positivity)
  exact (abs_lt.1 this).2

theorem convex_lyapunovDomain : Convex ℝ lyapunovDomain := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hRx, hVx, hQx⟩ := hx
  obtain ⟨hRy, hVy, hQy⟩ := hy
  simp only [lyapunovDomain, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hc := cross_pos _ _ _ _ _ _ hRx hVx hRy hVy hQx hQy
  refine ⟨pos_comb a b _ _ ha hb hab hRx hRy, pos_comb a b _ _ ha hb hab hVx hVy, ?_⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hQx' : 0 < x 2 * x 3 - x 4 ^ 2 := by linarith
  have hQy' : 0 < y 2 * y 3 - y 4 ^ 2 := by linarith
  have hab' : 0 ≤ a * (1 - a) := mul_nonneg ha hb
  have hid : (a * x 2 + (1 - a) * y 2) * (a * x 3 + (1 - a) * y 3) -
      (a * x 4 + (1 - a) * y 4) ^ 2 =
      a ^ 2 * (x 2 * x 3 - x 4 ^ 2) + (1 - a) ^ 2 * (y 2 * y 3 - y 4 ^ 2) +
        a * (1 - a) * (x 2 * y 3 + y 2 * x 3 - 2 * x 4 * y 4) := by ring
  have hpos : 0 < a ^ 2 * (x 2 * x 3 - x 4 ^ 2) + (1 - a) ^ 2 * (y 2 * y 3 - y 4 ^ 2) := by
    rcases ha.lt_or_eq with h | h
    · have := mul_pos (pow_pos h 2) hQx'
      have := mul_nonneg (sq_nonneg (1 - a)) hQy'.le
      linarith
    · subst h
      simpa using hQy'
  have : 0 ≤ a * (1 - a) * (x 2 * y 3 + y 2 * x 3 - 2 * x 4 * y 4) :=
    mul_nonneg hab' (by linarith)
  nlinarith


/-- On the segment from `x` to `y` in the domain, the point `x + t (y - x)` is in the domain. -/
theorem line_mem (x y : DynamicState) (hx : x ∈ lyapunovDomain) (hy : y ∈ lyapunovDomain)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun i => x i + t * (y - x) i) ∈ lyapunovDomain := by
  have h := convex_lyapunovDomain hx hy (show 0 ≤ 1 - t by linarith [ht.2]) ht.1 (by ring)
  convert h using 1
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  ring

/-- v2 prop:S (strict convexity): for `delta, Phi > 0` the free energy is strictly
convex on the cone `{R > 0, V > 0, C^2 < R V}`. -/
theorem strictConvexOn_lyapunov (r δ Φ : ℝ) (hδ : 0 < δ) (hΦ : 0 < Φ) :
    StrictConvexOn ℝ lyapunovDomain (lyapunov r δ Φ) := by
  refine ⟨convex_lyapunovDomain, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  set d : DynamicState := y - x with hd
  have hdi : ∀ i, d i = y i - x i := fun i => rfl
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < lineQ x d t ∧ 0 < x 2 + t * d 2 := by
    intro t ht
    obtain ⟨hR, hV, hQ⟩ := line_mem x y hx hy t ht
    have hQ' : (x 4 + t * d 4) ^ 2 < (x 2 + t * d 2) * (x 3 + t * d 3) := hQ
    exact ⟨by unfold lineQ; linarith, hR⟩
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (lineLyap r δ Φ x d) (lineF r δ Φ x d t) t :=
    fun t ht => hasDerivAt_lineLyap r δ Φ x d t (hmem t ht).1.ne'
  have hcont : ContinuousOn (lineLyap r δ Φ x d) (Set.Icc 0 1) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hd0 : ¬(d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 0 ∧ d 3 = 0 ∧ d 4 = 0) := by
    rintro ⟨h0, h1, h2, h3, h4⟩
    apply hxy
    have key : ∀ i, d i = 0 → x i = y i := fun i hi => by have := hdi i; linarith
    funext i
    fin_cases i
    · exact key 0 h0
    · exact key 1 h1
    · exact key 2 h2
    · exact key 3 h3
    · exact key 4 h4
  have hconv : StrictConvexOn ℝ (Set.Icc (0 : ℝ) 1) (lineLyap r δ Φ x d) := by
    apply strictConvexOn_of_deriv2_pos (convex_Icc 0 1) hcont
    intro t ht
    rw [interior_Icc] at ht
    have hnb : deriv (lineLyap r δ Φ x d) =ᶠ[nhds t] lineF r δ Φ x d := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact (hderiv s (Set.Ioo_subset_Icc_self hs)).deriv
    obtain ⟨hq, hR⟩ := hmem t (Set.Ioo_subset_Icc_self ht)
    have h2 : deriv^[2] (lineLyap r δ Φ x d) t = lineF2 r δ Φ x d t := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
      rw [hnb.deriv_eq]
      exact (hasDerivAt_lineF r δ Φ x d t hq.ne').deriv
    rw [h2]
    exact lyapunov_hessian_pos δ Φ _ (x 0 + t * d 0) (x 2 + t * d 2) (x 3 + t * d 3)
      (x 4 + t * d 4) (d 0) (d 1) (d 2) (d 3) (d 4) hδ hΦ (Real.exp_pos _) hR hq hd0
  have h := hconv.2 (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp) (by norm_num) ha hb hab
  have e0 : lineLyap r δ Φ x d 0 = lyapunov r δ Φ x := by
    unfold lineLyap; congr 1; funext i; simp
  have e1 : lineLyap r δ Φ x d 1 = lyapunov r δ Φ y := by
    unfold lineLyap; congr 1; funext i; simp [hdi]
  have ha' : a = 1 - b := by linarith
  have eb : lineLyap r δ Φ x d b = lyapunov r δ Φ (a • x + b • y) := by
    unfold lineLyap; congr 1; funext i; simp [hdi, ha']; ring
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one] at h
  rw [eb, e0, e1] at h
  exact h

end
end SparseSGD.Logistic.V2
