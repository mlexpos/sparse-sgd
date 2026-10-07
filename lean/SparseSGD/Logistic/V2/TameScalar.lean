import SparseSGD.Logistic.V2.ActualCoefficients

/-!
# Lemma G.3 in scalar variables without realizability

`tame_coefficients` and `tame_scalarJets_first_second` are stated for vectors `(mu, theta)`,
so they only apply at scalar states `(t, q)` with `q ≥ t²` (Cauchy-Schwarz).  The proofs use the
vectors only through `q = ‖theta‖²`, `⟨theta, mu⟩ = r t`, `‖mu‖ = r`, and one-dimensional
Gaussian averages `gaussianAverage f c q`.  Here the whole chain is restated for scalars
`(p, r, t, q)` with `0 ≤ q` and `t` arbitrary, by direct translation:

* `‖theta‖² ↦ q`, `⟨theta, mu⟩ ↦ r t`, `‖mu‖² ↦ r²`;
* `tameError ↦ tameErrorS`, `gaussianAlpha ↦ exp((q - r²)/2)`, `bias ↦ scalarBias`;
* the vector Gaussian integral bounds are transported to `gaussianAverage` through
  `gaussian_projected_average` in dimension one (only `q ≥ 0` is used there).

No vector-only fact enters: the term `e^{r|t|}` is part of `tameErrorS`, and `r t ≤ r |t|`
needs only `r ≥ 0`.

The final results are `scalar_tame_values_q`, `scalar_tame_jets_q` and
`scalar_tame_matched_jets_q`, the analogues of `scalar_tame_values`, `scalar_tame_jets` and
`scalar_tame_matched_jets` valid at every `t` and every `q ≥ 0`.
-/

namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic SparseSGD.Probability
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

/-- `p ≤ tameErrorS` for `r ≥ 0` (scalar form of `tameError_ge_probability`). -/
theorem tameErrorS_ge_probability (p : unitInterval) (r t q : ℝ) (hr : 0 ≤ r) :
    (p : ℝ) ≤ tameErrorS p r t q := by
  have hp := p.property.1
  have he : 1 ≤ Real.exp (r * |t|) := Real.one_le_exp (mul_nonneg hr (abs_nonneg t))
  have ha := (Real.exp_pos ((q - r ^ 2) / 2)).le
  have hsum : 1 ≤ Real.exp (2 * q - r ^ 2) + Real.exp ((3 * q - r ^ 2) / 2) +
      (1 + Real.exp ((q - r ^ 2) / 2)) * Real.exp (r * |t|) := by
    nlinarith [Real.exp_pos (2 * q - r ^ 2), Real.exp_pos ((3 * q - r ^ 2) / 2)]
  unfold tameErrorS
  calc (p : ℝ) = (p : ℝ) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hp

private theorem exists_theta1 (q : ℝ) (hq : 0 ≤ q) : ∃ θ : Vec 1, ‖θ‖ ^ 2 = q := by
  refine ⟨WithLp.toLp 2 (fun _ => Real.sqrt q), ?_⟩
  rw [EuclideanSpace.norm_eq]
  simp [Real.sq_sqrt hq]

/-! ### Scalar Gaussian-average bounds -/

private theorem sc_sigmaPrime_error (c q : ℝ) (hq : 0 ≤ q) :
    |gaussianAverage sigmaPrime c q - Real.exp (c + q / 2)| ≤ 2 * Real.exp (2 * c + 2 * q) := by
  obtain ⟨θ, hθ⟩ := exists_theta1 q hq
  have H := gaussian_sigmaPrime_error_bound θ c
  rwa [gaussian_projected_average θ c sigmaPrime sigmaPrime_continuous, hθ] at H

private theorem sc_sigmaPrime_bound (c q : ℝ) (hq : 0 ≤ q) :
    |gaussianAverage sigmaPrime c q| ≤ Real.exp (c + q / 2) := by
  obtain ⟨θ, hθ⟩ := exists_theta1 q hq
  have H := (gaussian_sigmaPrime_integral_bound θ c).2
  rwa [gaussian_projected_average θ c sigmaPrime sigmaPrime_continuous, hθ] at H

private theorem sc_sigma_bound (c q : ℝ) (hq : 0 ≤ q) :
    |gaussianAverage sigma c q| ≤ Real.exp (c + q / 2) := by
  obtain ⟨θ, hθ⟩ := exists_theta1 q hq
  have H := (gaussian_sigma_integral_bound θ c).2
  rwa [gaussian_projected_average θ c sigma sigma_continuous, hθ] at H

private theorem sc_sigmaSq_bound (c q : ℝ) (hq : 0 ≤ q) :
    |gaussianAverage (fun x => sigma x ^ 2) c q| ≤ Real.exp (2 * c + 2 * q) := by
  obtain ⟨θ, hθ⟩ := exists_theta1 q hq
  have H := (gaussian_sigma_sq_integral_bound θ c).2
  have hc : Continuous (fun x : ℝ => sigma x ^ 2) := by fun_prop
  rwa [gaussian_projected_average θ c (fun x => sigma x ^ 2) hc, hθ] at H

private theorem sc_oneMinusSigmaSq_error (c q : ℝ) (hq : 0 ≤ q) :
    |gaussianAverage (fun x => (1 - sigma x) ^ 2) c q - 1| ≤ 2 * Real.exp (c + q / 2) := by
  obtain ⟨θ, hθ⟩ := exists_theta1 q hq
  have H := gaussian_oneMinusSigma_sq_error_bound θ c
  have hc : Continuous (fun x : ℝ => (1 - sigma x) ^ 2) := by fun_prop
  rwa [gaussian_projected_average θ c (fun x => (1 - sigma x) ^ 2) hc, hθ] at H

private theorem sc_sigmaSqSecond_bound (c q : ℝ) (hq : 0 ≤ q) :
    |gaussianAverage sigmaSqSecond c q| ≤ 4 * Real.exp (2 * c + 2 * q) := by
  obtain ⟨θ, hθ⟩ := exists_theta1 q hq
  have H := (gaussian_sigmaSqSecond_integral_bound θ c).2
  rwa [gaussian_projected_average θ c sigmaSqSecond sigmaSqSecond_continuous, hθ] at H

private theorem sc_oneMinusSigmaSqSecond_bound (c q : ℝ) (hq : 0 ≤ q) :
    |gaussianAverage oneMinusSigmaSqSecond c q| ≤ 2 * Real.exp (c + q / 2) := by
  obtain ⟨θ, hθ⟩ := exists_theta1 q hq
  have H := (gaussian_oneMinusSigmaSqSecond_integral_bound θ c).2
  rwa [gaussian_projected_average θ c oneMinusSigmaSqSecond oneMinusSigmaSqSecond_continuous,
    hθ] at H

/-! ### Scalar bias identities and exponential controls -/

private theorem sc_bias_first (p : unitInterval) (r q : ℝ)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Real.exp (scalarBias p r + q / 2) =
      (p : ℝ) / (1 - (p : ℝ)) * Real.exp ((q - r ^ 2) / 2) := by
  unfold scalarBias
  rw [show Real.log ((p : ℝ) / (1 - (p : ℝ))) - r ^ 2 / 2 + q / 2 =
    Real.log ((p : ℝ) / (1 - (p : ℝ))) + (q - r ^ 2) / 2 by ring,
    Real.exp_add, Real.exp_log (div_pos hp0 (by linarith))]

private theorem sc_bias_second (p : unitInterval) (r q : ℝ)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Real.exp (2 * scalarBias p r + 2 * q) =
      (p : ℝ) ^ 2 / (1 - (p : ℝ)) ^ 2 * Real.exp (2 * q - r ^ 2) := by
  unfold scalarBias
  rw [show 2 * (Real.log ((p : ℝ) / (1 - (p : ℝ))) - r ^ 2 / 2) + 2 * q =
    (Real.log ((p : ℝ) / (1 - (p : ℝ))) + Real.log ((p : ℝ) / (1 - (p : ℝ)))) +
      (2 * q - r ^ 2) by ring, Real.exp_add, Real.exp_add,
    Real.exp_log (div_pos hp0 (by linarith))]
  field_simp

private theorem sc_exponential_controls (p : unitInterval) (r t q : ℝ)
    (hp0 : 0 < (p : ℝ)) (hr : 0 ≤ r) (htame : tameErrorS p r t q ≤ 1 / 2) :
    (1 - (p : ℝ)) * Real.exp (2 * scalarBias p r + 2 * q) ≤ 2 * (p : ℝ) * tameErrorS p r t q ∧
    (1 - (p : ℝ)) * Real.exp (2 * scalarBias p r + 2 * q) ≤
      2 * (p : ℝ) * Real.exp ((q - r ^ 2) / 2) * tameErrorS p r t q ∧
    (p : ℝ) * Real.exp (r * t + scalarBias p r + q / 2) ≤ 2 * (p : ℝ) * tameErrorS p r t q ∧
    (p : ℝ) * Real.exp (r * t + scalarBias p r + q / 2) ≤
      2 * (p : ℝ) * Real.exp ((q - r ^ 2) / 2) * tameErrorS p r t q := by
  have hphalf : (p : ℝ) ≤ 1 / 2 := (tameErrorS_ge_probability p r t q hr).trans htame
  have hp1 : (p : ℝ) < 1 := by linarith
  have hden : 0 < 1 - (p : ℝ) := by linarith
  let X := Real.exp (2 * q - r ^ 2)
  let Y := Real.exp ((3 * q - r ^ 2) / 2)
  let E := Real.exp (r * |t|)
  let a := Real.exp ((q - r ^ 2) / 2)
  let eps := tameErrorS p r t q
  have hX : 0 < X := Real.exp_pos _
  have hY : 0 < Y := Real.exp_pos _
  have hE : 0 < E := Real.exp_pos _
  have ha : 0 < a := Real.exp_pos _
  have hXY : X = a * Y := by
    dsimp [X, Y, a]
    rw [← Real.exp_add]
    congr 1
    ring
  have heq : eps = (p : ℝ) * (X + Y + (1 + a) * E) := rfl
  have hx : (p : ℝ) * X ≤ eps := by
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ hp0.le
    have H : 0 ≤ (1 + a) * E := by positivity
    linarith
  have hy : (p : ℝ) * Y ≤ eps := by
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ hp0.le
    have H : 0 ≤ (1 + a) * E := by positivity
    linarith
  have he : (p : ℝ) * E ≤ eps := by nlinarith
  have hae : (p : ℝ) * a * E ≤ eps := by nlinarith
  have hratio : (p : ℝ) ^ 2 / (1 - (p : ℝ)) ≤ 2 * (p : ℝ) ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg (p : ℝ)]
  have H0 : (1 - (p : ℝ)) * Real.exp (2 * scalarBias p r + 2 * q) ≤ 2 * (p : ℝ) ^ 2 * X := by
    rw [sc_bias_second p r q hp0 hp1]
    calc
      _ = ((p : ℝ) ^ 2 / (1 - (p : ℝ))) * X := by dsimp [X]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hratio hX.le
  have H1 : (p : ℝ) * Real.exp (r * t + scalarBias p r + q / 2) ≤
      2 * (p : ℝ) ^ 2 * a * E := by
    rw [show r * t + scalarBias p r + q / 2 = (scalarBias p r + q / 2) + r * t by ring,
      Real.exp_add, sc_bias_first p r q hp0 hp1]
    have hm : Real.exp (r * t) ≤ E :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self t) hr)
    calc
      _ = ((p : ℝ) ^ 2 / (1 - (p : ℝ))) * a * Real.exp (r * t) := by dsimp [a]; ring
      _ ≤ (2 * (p : ℝ) ^ 2) * a * E := mul_le_mul
        (mul_le_mul_of_nonneg_right hratio ha.le) hm (Real.exp_pos _).le (by positivity)
  refine ⟨H0.trans ?_, H0.trans ?_, H1.trans ?_, H1.trans ?_⟩
  · have H := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2 * (p : ℝ) by positivity)
    nlinarith
  · rw [hXY]
    have H := mul_le_mul_of_nonneg_left hy (show 0 ≤ 2 * (p : ℝ) * a by positivity)
    change 2 * (p : ℝ) ^ 2 * (a * Y) ≤ 2 * (p : ℝ) * a * eps
    nlinarith
  · have H := mul_le_mul_of_nonneg_left hae (show 0 ≤ 2 * (p : ℝ) by positivity)
    nlinarith
  · have H := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * (p : ℝ) * a by positivity)
    nlinarith

/-! ### Value bounds -/

private theorem sc_coefficients (p : unitInterval) (r t q : ℝ)
    (hp0 : 0 < (p : ℝ)) (hr : 0 ≤ r) (hq : 0 ≤ q) (htame : tameErrorS p r t q ≤ 1 / 2) :
    |scalarCoefA p r t q - (p : ℝ) * Real.exp ((q - r ^ 2) / 2)| ≤
      6 * (p : ℝ) * Real.exp ((q - r ^ 2) / 2) * tameErrorS p r t q ∧
    |scalarCoefB p r t q + (p : ℝ)| ≤ 2 * (p : ℝ) * tameErrorS p r t q ∧
    |scalarCoefD0 p r t q - (p : ℝ)| ≤ 6 * (p : ℝ) * tameErrorS p r t q ∧
    |scalarCoefDtheta p r t q| ≤ 12 * (p : ℝ) * tameErrorS p r t q := by
  obtain ⟨h0, h0a, h1, h1a⟩ := sc_exponential_controls p r t q hp0 hr htame
  have hphalf : (p : ℝ) ≤ 1 / 2 := (tameErrorS_ge_probability p r t q hr).trans htame
  have hp1 : (p : ℝ) < 1 := by linarith
  have hd : 0 ≤ 1 - (p : ℝ) := by linarith
  have hpp := hp0.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · have H0 := sc_sigmaPrime_error (scalarBias p r) q hq
    have H1 := sc_sigmaPrime_bound (r * t + scalarBias p r) q hq
    have hm : (1 - (p : ℝ)) * Real.exp (scalarBias p r + q / 2) =
        (p : ℝ) * Real.exp ((q - r ^ 2) / 2) := by
      rw [sc_bias_first p r q hp0 hp1]
      field_simp [show 1 - (p : ℝ) ≠ 0 by linarith]
    have key : scalarCoefA p r t q - (p : ℝ) * Real.exp ((q - r ^ 2) / 2) =
        (1 - (p : ℝ)) * (gaussianAverage sigmaPrime (scalarBias p r) q -
          Real.exp (scalarBias p r + q / 2)) +
        (p : ℝ) * gaussianAverage sigmaPrime (r * t + scalarBias p r) q := by
      unfold scalarCoefA
      linear_combination hm
    rw [key]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg hd, abs_of_pos hp0]
    have e0 := mul_le_mul_of_nonneg_left H0 hd
    have e1 := mul_le_mul_of_nonneg_left H1 hp0.le
    nlinarith
  · have H := sc_sigma_bound (r * t + scalarBias p r) q hq
    unfold scalarCoefB
    rw [show (p : ℝ) * (gaussianAverage sigma (r * t + scalarBias p r) q - 1) + (p : ℝ) =
      (p : ℝ) * gaussianAverage sigma (r * t + scalarBias p r) q by ring, abs_mul,
      abs_of_pos hp0]
    have := mul_le_mul_of_nonneg_left H hp0.le
    nlinarith
  · have H0 := sc_sigmaSq_bound (scalarBias p r) q hq
    have H1 := sc_oneMinusSigmaSq_error (r * t + scalarBias p r) q hq
    unfold scalarCoefD0
    rw [show (1 - (p : ℝ)) * gaussianAverage (fun x => sigma x ^ 2) (scalarBias p r) q +
        (p : ℝ) * gaussianAverage (fun x => (1 - sigma x) ^ 2) (r * t + scalarBias p r) q -
        (p : ℝ) =
      (1 - (p : ℝ)) * gaussianAverage (fun x => sigma x ^ 2) (scalarBias p r) q +
        (p : ℝ) * (gaussianAverage (fun x => (1 - sigma x) ^ 2) (r * t + scalarBias p r) q -
          1) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg hd, abs_of_pos hp0]
    have e0 := mul_le_mul_of_nonneg_left H0 hd
    have e1 := mul_le_mul_of_nonneg_left H1 hp0.le
    nlinarith
  · have H0 := sc_sigmaSqSecond_bound (scalarBias p r) q hq
    have H1 := sc_oneMinusSigmaSqSecond_bound (r * t + scalarBias p r) q hq
    unfold scalarCoefDtheta
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg hd, abs_of_pos hp0]
    have e0 := mul_le_mul_of_nonneg_left H0 hd
    have e1 := mul_le_mul_of_nonneg_left H1 hp0.le
    nlinarith

/-- Lemma G.3 value bounds for the normalized state coefficients at every state with
`q = y 0 ^ 2 + y 2 ≥ 0` (no realizability `y 2 ≥ 0` needed) and small tame error.
Constants are `6, 2, 6, 12`, as in `tame_coefficients`. -/
theorem scalar_tame_values_q (r : ℝ) (hr : 0 < r) :
    ∀ (p : unitInterval) (y : DynamicState), 0 < (p : ℝ) → 0 ≤ y 0 ^ 2 + y 2 →
      tameErrorS p r (y 0) (y 0 ^ 2 + y 2) ≤ 1 / 2 →
      |actA p r y - dynamicAlpha r y| ≤
          6 * dynamicAlpha r y * tameErrorS p r (y 0) (y 0 ^ 2 + y 2) ∧
      |actB p r y + 1| ≤ 2 * tameErrorS p r (y 0) (y 0 ^ 2 + y 2) ∧
      |actD0 p r y - 1| ≤ 6 * tameErrorS p r (y 0) (y 0 ^ 2 + y 2) ∧
      |actDt p r y| ≤ 12 * tameErrorS p r (y 0) (y 0 ^ 2 + y 2) := by
  intro p y hp hq he
  obtain ⟨hA, hB, hD, hT⟩ := sc_coefficients p r (y 0) (y 0 ^ 2 + y 2) hp hr.le hq he
  have hα : dynamicAlpha r y = Real.exp ((y 0 ^ 2 + y 2 - r ^ 2) / 2) := rfl
  rw [hα]
  have key : ∀ (c x m : ℝ), |c - (p : ℝ) * m| ≤ x * (p : ℝ) →
      |c / (p : ℝ) - m| ≤ x := by
    intro c x m h
    have : c / (p : ℝ) - m = (c - (p : ℝ) * m) / (p : ℝ) := by field_simp
    rw [this, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact key _ _ _ (by linarith [hA])
  · have := key (scalarCoefB p r (y 0) (y 0 ^ 2 + y 2))
      (2 * tameErrorS p r (y 0) (y 0 ^ 2 + y 2)) (-1)
      (by rw [mul_neg_one, sub_neg_eq_add]; linarith)
    simpa [actB, sub_neg_eq_add] using this
  · exact key _ _ _ (by rw [mul_one]; linarith)
  · have := key (scalarCoefDtheta p r (y 0) (y 0 ^ 2 + y 2))
      (12 * tameErrorS p r (y 0) (y 0 ^ 2 + y 2)) 0
      (by rw [mul_zero, sub_zero]; linarith)
    simpa [actDt] using this

/-! ### Derivative bounds -/

private theorem sc_sigma_mixture_derivative (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : unitInterval) (r t q : ℝ), 0 < (p : ℝ) → 0 ≤ r → 0 ≤ q →
      tameErrorS p r t q ≤ 1 / 2 →
      |(1 - (p : ℝ)) * gaussianAverage (sigmaDerivative n) (scalarBias p r) q +
        (p : ℝ) * gaussianAverage (sigmaDerivative n) (r * t + scalarBias p r) q -
        (p : ℝ) * Real.exp ((q - r ^ 2) / 2)| ≤
        C * (p : ℝ) * Real.exp ((q - r ^ 2) / 2) * tameErrorS p r t q := by
  obtain ⟨C, hC, h⟩ := gaussian_sigmaDerivative_bounds n
  refine ⟨4 * C, by linarith, fun p r t q hp hr hq ht => ?_⟩
  have hp1 : (p : ℝ) < 1 := by linarith [tameErrorS_ge_probability p r t q hr]
  have hd : 0 ≤ 1 - (p : ℝ) := by linarith
  have hm : (1 - (p : ℝ)) * Real.exp (scalarBias p r + q / 2) =
      (p : ℝ) * Real.exp ((q - r ^ 2) / 2) := by
    rw [sc_bias_first p r q hp hp1]
    field_simp [show 1 - (p : ℝ) ≠ 0 by linarith]
  have hs := sc_exponential_controls p r t q hp hr ht
  have h0 := (h (scalarBias p r) q hq).2
  have h1 := (h (r * t + scalarBias p r) q hq).1
  rw [← hm]
  rw [show (1 - (p : ℝ)) * gaussianAverage (sigmaDerivative n) (scalarBias p r) q +
      (p : ℝ) * gaussianAverage (sigmaDerivative n) (r * t + scalarBias p r) q -
      (1 - (p : ℝ)) * Real.exp (scalarBias p r + q / 2) =
      (1 - (p : ℝ)) * (gaussianAverage (sigmaDerivative n) (scalarBias p r) q -
        Real.exp (scalarBias p r + q / 2)) +
      (p : ℝ) * gaussianAverage (sigmaDerivative n) (r * t + scalarBias p r) q by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg hd, abs_of_pos hp]
  have H0 := mul_le_mul_of_nonneg_left h0 hd
  have H1 := mul_le_mul_of_nonneg_left h1 hp.le
  have H2 := mul_le_mul_of_nonneg_left hs.2.1 (show 0 ≤ C by linarith)
  have H3 := mul_le_mul_of_nonneg_left hs.2.2.2 (show 0 ≤ C by linarith)
  nlinarith

private theorem sc_sigma_positive_derivative (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : unitInterval) (r t q : ℝ), 0 < (p : ℝ) → 0 ≤ r → 0 ≤ q →
      tameErrorS p r t q ≤ 1 / 2 →
      |(p : ℝ) * gaussianAverage (sigmaDerivative n) (r * t + scalarBias p r) q| ≤
        C * (p : ℝ) * tameErrorS p r t q := by
  obtain ⟨C, hC, h⟩ := gaussian_sigmaDerivative_bounds n
  refine ⟨2 * C, by linarith, fun p r t q hp hr hq ht => ?_⟩
  rw [abs_mul, abs_of_pos hp]
  have h1 := mul_le_mul_of_nonneg_left (h (r * t + scalarBias p r) q hq).1 hp.le
  have hs := mul_le_mul_of_nonneg_left (sc_exponential_controls p r t q hp hr ht).2.2.1
    (show 0 ≤ C by linarith)
  nlinarith

private theorem sc_square_mixture_derivative (n : ℕ) (hn : n ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : unitInterval) (r t q : ℝ), 0 < (p : ℝ) → 0 ≤ r → 0 ≤ q →
      tameErrorS p r t q ≤ 1 / 2 →
      |(1 - (p : ℝ)) * gaussianAverage (sigmaSquareDerivative n) (scalarBias p r) q +
        (p : ℝ) * gaussianAverage (oneMinusSigmaSquareDerivative n) (r * t + scalarBias p r) q| ≤
        C * (p : ℝ) * tameErrorS p r t q := by
  obtain ⟨C, hC, h⟩ := gaussian_sigmaSquareDerivative_bound n
  obtain ⟨D, hD, h'⟩ := gaussian_oneMinusSigmaSquareDerivative_bound n hn
  refine ⟨2 * (C + D), by positivity, fun p r t q hp hr hq ht => ?_⟩
  have hd : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.property.2
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg hd, abs_of_pos hp]
  have h0 := mul_le_mul_of_nonneg_left (h (scalarBias p r) q hq) hd
  have h1 := mul_le_mul_of_nonneg_left (h' (r * t + scalarBias p r) q hq) hp.le
  have hs := sc_exponential_controls p r t q hp hr ht
  have h2 := mul_le_mul_of_nonneg_left hs.1 hC
  have h3 := mul_le_mul_of_nonneg_left hs.2.2.1 hD
  nlinarith

private theorem sc_square_positive_derivative (n : ℕ) (hn : n ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : unitInterval) (r t q : ℝ), 0 < (p : ℝ) → 0 ≤ r → 0 ≤ q →
      tameErrorS p r t q ≤ 1 / 2 →
      |(p : ℝ) * gaussianAverage (oneMinusSigmaSquareDerivative n) (r * t + scalarBias p r) q| ≤
        C * (p : ℝ) * tameErrorS p r t q := by
  obtain ⟨C, hC, h⟩ := gaussian_oneMinusSigmaSquareDerivative_bound n hn
  refine ⟨2 * C, by positivity, fun p r t q hp hr hq ht => ?_⟩
  rw [abs_mul, abs_of_pos hp]
  have h1 := mul_le_mul_of_nonneg_left (h (r * t + scalarBias p r) q hq) hp.le
  have hs := mul_le_mul_of_nonneg_left (sc_exponential_controls p r t q hp hr ht).2.2.1 hC
  nlinarith

/-! ### Jet bounds -/

private theorem sc_factor_abs_bound {f z C u : ℝ} (hf : 0 ≤ f) (h : |u| ≤ C * z) :
    |f * u| ≤ C * f * z := by
  rw [abs_mul, abs_of_nonneg hf]
  calc
    f * |u| ≤ f * (C * z) := mul_le_mul_of_nonneg_left h hf
    _ = _ := by ring

private theorem sc_A_variance_jet (b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : unitInterval) (r t q : ℝ), 0 < (p : ℝ) → 0 ≤ r → 0 ≤ q →
      tameErrorS p r t q ≤ 1 / 2 →
      |scalarCoefAJet 0 b p r t q - (1 / 2 : ℝ) ^ b * (p : ℝ) * Real.exp ((q - r ^ 2) / 2)| ≤
        C * (1 / 2 : ℝ) ^ b * (p : ℝ) * Real.exp ((q - r ^ 2) / 2) * tameErrorS p r t q := by
  obtain ⟨C, hC, h⟩ := sc_sigma_mixture_derivative (1 + 0 + 2 * b)
  refine ⟨C, hC, fun p r t q hp hr hq ht => ?_⟩
  unfold scalarCoefAJet scalarGaussianJet
  simp only [pow_zero, one_mul, ite_true]
  rw [show (1 / 2 : ℝ) ^ b * ((1 - (p : ℝ)) * gaussianAverage (sigmaDerivative (1 + 0 + 2 * b))
      (scalarBias p r) q + (p : ℝ) * gaussianAverage (sigmaDerivative (1 + 0 + 2 * b))
      (r * t + scalarBias p r) q) - (1 / 2 : ℝ) ^ b * (p : ℝ) * Real.exp ((q - r ^ 2) / 2) =
      (1 / 2 : ℝ) ^ b * ((1 - (p : ℝ)) * gaussianAverage (sigmaDerivative (1 + 0 + 2 * b))
      (scalarBias p r) q + (p : ℝ) * gaussianAverage (sigmaDerivative (1 + 0 + 2 * b))
      (r * t + scalarBias p r) q - (p : ℝ) * Real.exp ((q - r ^ 2) / 2)) by ring]
  have hh := sc_factor_abs_bound (by positivity : 0 ≤ (1 / 2 : ℝ) ^ b) (h p r t q hp hr hq ht)
  convert hh using 1 <;> ring

private theorem sc_A_signal_jet (a b : ℕ) (ha : a ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : unitInterval) (r t q : ℝ), 0 < (p : ℝ) → 0 ≤ r → 0 ≤ q →
      tameErrorS p r t q ≤ 1 / 2 →
      |scalarCoefAJet a b p r t q| ≤
        C * (r ^ a * (1 / 2 : ℝ) ^ b) * (p : ℝ) * tameErrorS p r t q := by
  obtain ⟨C, hC, h⟩ := sc_sigma_positive_derivative (1 + a + 2 * b)
  refine ⟨C, hC, fun p r t q hp hr hq ht => ?_⟩
  unfold scalarCoefAJet scalarGaussianJet
  simp only [ha, ite_false, zero_add]
  have hh := sc_factor_abs_bound (by positivity : 0 ≤ r ^ a * (1 / 2 : ℝ) ^ b)
    (h p r t q hp hr hq ht)
  convert hh using 1
  ring

private theorem sc_B_jet (a b : ℕ) (hab : a + b ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : unitInterval) (r t q : ℝ), 0 < (p : ℝ) → 0 ≤ r → 0 ≤ q →
      tameErrorS p r t q ≤ 1 / 2 →
      |scalarCoefBJet a b p r t q| ≤
        C * (r ^ a * (1 / 2 : ℝ) ^ b) * (p : ℝ) * tameErrorS p r t q := by
  obtain ⟨C, hC, h⟩ := sc_sigma_positive_derivative (0 + a + 2 * b)
  refine ⟨C, hC, fun p r t q hp hr hq ht => ?_⟩
  simp only [scalarCoefBJet, hab, ite_false, sub_zero]
  unfold scalarGaussianJet
  simp only [scalar_gaussianAverage_zero, mul_zero, ite_self, zero_add]
  have hh := sc_factor_abs_bound (by positivity : 0 ≤ r ^ a * (1 / 2 : ℝ) ^ b)
    (h p r t q hp hr hq ht)
  rw [zero_add] at hh
  convert hh using 1
  ring

private theorem sc_square_jet (base a b : ℕ) (hn : base + a + 2 * b ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : unitInterval) (r t q : ℝ), 0 < (p : ℝ) → 0 ≤ r → 0 ≤ q →
      tameErrorS p r t q ≤ 1 / 2 →
      |scalarGaussianJet sigmaSquareDerivative oneMinusSigmaSquareDerivative base a b p r t q| ≤
        C * (r ^ a * (1 / 2 : ℝ) ^ b) * (p : ℝ) * tameErrorS p r t q := by
  obtain ⟨C, hC, h⟩ := sc_square_mixture_derivative (base + a + 2 * b) hn
  obtain ⟨D, hD, h'⟩ := sc_square_positive_derivative (base + a + 2 * b) hn
  refine ⟨C + D, by positivity, fun p r t q hp hr hq ht => ?_⟩
  have hf : 0 ≤ r ^ a * (1 / 2 : ℝ) ^ b := by positivity
  have hz : 0 ≤ (r ^ a * (1 / 2 : ℝ) ^ b) * (p : ℝ) * tameErrorS p r t q :=
    mul_nonneg (mul_nonneg hf hp.le) (p.property.1.trans (tameErrorS_ge_probability p r t q hr))
  unfold scalarGaussianJet
  by_cases ha : a = 0
  · simp only [ha, ite_true]
    have hh := sc_factor_abs_bound hf (h p r t q hp hr hq ht)
    simp only [ha] at hh hz ⊢
    nlinarith [mul_nonneg hD hz]
  · simp only [ha, ite_false, zero_add]
    have hh := sc_factor_abs_bound hf (h' p r t q hp hr hq ht)
    nlinarith [mul_nonneg hC hz]

/-- Scalar form of `TameScalarJetBounds`, defined above as `TameScalarJetBoundsS`, is monotone
in the constant. -/
private theorem sc_jetBounds_mono {a b : ℕ} {C D : ℝ} {p : unitInterval} {r t q : ℝ}
    (hr : 0 ≤ r) (hCD : C ≤ D) (h : TameScalarJetBoundsS a b C p r t q) :
    TameScalarJetBoundsS a b D p r t q := by
  have hf : 0 ≤ r ^ a * (1 / 2 : ℝ) ^ b := by positivity
  have hz : 0 ≤ (r ^ a * (1 / 2 : ℝ) ^ b) * (p : ℝ) * tameErrorS p r t q :=
    mul_nonneg (mul_nonneg hf p.property.1) (p.property.1.trans (tameErrorS_ge_probability p r t q hr))
  have halpha : 0 ≤ (if a = 0 then Real.exp ((q - r ^ 2) / 2) else (1 : ℝ)) := by
    split_ifs
    · exact (Real.exp_pos _).le
    · norm_num
  rcases h with ⟨hA, hB, hD0, hDtheta⟩
  refine ⟨hA.trans ?_, hB.trans ?_, hD0.trans ?_, hDtheta.trans ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hCD (mul_nonneg hz halpha)]
  all_goals nlinarith [mul_le_mul_of_nonneg_right hCD hz]

private theorem sc_jets (a b : ℕ) (hab : a + b ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : unitInterval) (r t q : ℝ), 0 < (p : ℝ) → 0 ≤ r → 0 ≤ q →
      tameErrorS p r t q ≤ 1 / 2 → TameScalarJetBoundsS a b C p r t q := by
  have hA : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : unitInterval) (r t q : ℝ), 0 < (p : ℝ) → 0 ≤ r → 0 ≤ q →
      tameErrorS p r t q ≤ 1 / 2 →
      |scalarCoefAJet a b p r t q -
          (if a = 0 then r ^ a * (1 / 2 : ℝ) ^ b * (p : ℝ) * Real.exp ((q - r ^ 2) / 2)
            else 0)| ≤
        C * (r ^ a * (1 / 2 : ℝ) ^ b) * (p : ℝ) * tameErrorS p r t q *
          (if a = 0 then Real.exp ((q - r ^ 2) / 2) else 1) := by
    by_cases ha : a = 0
    · subst a
      obtain ⟨C, hC, h⟩ := sc_A_variance_jet b
      refine ⟨C, hC, fun p r t q hp hr hq ht => ?_⟩
      have := h p r t q hp hr hq ht
      simp only [pow_zero, one_mul, ite_true]
      convert this using 1 <;> ring
    · obtain ⟨C, hC, h⟩ := sc_A_signal_jet a b ha
      refine ⟨C, hC, fun p r t q hp hr hq ht => ?_⟩
      simpa only [ha, ite_false, sub_zero, mul_one] using h p r t q hp hr hq ht
  obtain ⟨A, hA0, HA⟩ := hA
  obtain ⟨B, hB, HB⟩ := sc_B_jet a b hab
  obtain ⟨D, hD, HD⟩ := sc_square_jet 0 a b (by omega)
  obtain ⟨T, hT, HT⟩ := sc_square_jet 2 a b (by omega)
  refine ⟨A + B + D + T, by positivity, fun p r t q hp hr hq ht => ?_⟩
  have hf : 0 ≤ r ^ a * (1 / 2 : ℝ) ^ b := by positivity
  have hz : 0 ≤ (r ^ a * (1 / 2 : ℝ) ^ b) * (p : ℝ) * tameErrorS p r t q :=
    mul_nonneg (mul_nonneg hf hp.le) (p.property.1.trans (tameErrorS_ge_probability p r t q hr))
  have halpha : 0 ≤ (if a = 0 then Real.exp ((q - r ^ 2) / 2) else (1 : ℝ)) := by
    split_ifs
    · exact (Real.exp_pos _).le
    · norm_num
  refine ⟨(HA p r t q hp hr hq ht).trans ?_, (HB p r t q hp hr hq ht).trans ?_,
    ?_, ?_⟩
  · nlinarith [mul_nonneg (by positivity : 0 ≤ B + D + T) (mul_nonneg hz halpha)]
  · nlinarith [mul_nonneg (by positivity : 0 ≤ A + D + T) hz]
  · refine (?_ : _ ≤ D * (r ^ a * (1 / 2 : ℝ) ^ b) * (p : ℝ) * tameErrorS p r t q).trans ?_
    · simpa only [scalarCoefD0Jet] using HD p r t q hp hr hq ht
    · nlinarith [mul_nonneg (by positivity : 0 ≤ A + B + T) hz]
  · refine (?_ : _ ≤ T * (r ^ a * (1 / 2 : ℝ) ^ b) * (p : ℝ) * tameErrorS p r t q).trans ?_
    · simpa only [scalarCoefDthetaJet] using HT p r t q hp hr hq ht
    · nlinarith [mul_nonneg (by positivity : 0 ≤ A + B + D) hz]

/-- Lemma G.3 first and second jet bounds in scalar variables, valid at every `t` and every
`q ≥ 0` with small tame error (no realizability `q ≥ t²`). -/
theorem scalar_tame_jets_q (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℕ, 1 ≤ a + b → a + b ≤ 2 →
      ∀ (p : unitInterval) (t q : ℝ), 0 < (p : ℝ) → 0 ≤ q →
        tameErrorS p r t q ≤ 1 / 2 → TameScalarJetBoundsS a b C p r t q := by
  classical
  have hex (i : Fin 3 × Fin 3) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (p : unitInterval) (t q : ℝ), 0 < (p : ℝ) → 0 ≤ q →
        tameErrorS p r t q ≤ 1 / 2 → i.1.val + i.2.val ≠ 0 →
          TameScalarJetBoundsS i.1.val i.2.val C p r t q := by
    by_cases hi : i.1.val + i.2.val = 0
    · exact ⟨0, le_rfl, fun _ _ _ _ _ _ h => (h hi).elim⟩
    · obtain ⟨C, hC, h⟩ := sc_jets i.1.val i.2.val hi
      exact ⟨C, hC, fun p t q hp hq ht _ => h p r t q hp hr.le hq ht⟩
  choose c hc hbound using hex
  refine ⟨∑ i, c i, Finset.sum_nonneg (fun i _ => hc i), ?_⟩
  intro a b hab hab2 p t q hp hq ht
  let i : Fin 3 × Fin 3 := (⟨a, by omega⟩, ⟨b, by omega⟩)
  have hci : c i ≤ ∑ i, c i := Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)
  exact sc_jetBounds_mono hr.le hci (hbound i p t q hp hq ht (by dsimp [i]; omega))

/-- The jet bounds packaged through `matchedScalarJet i a b`, `i : Fin 4` indexing
`A, B, D0, Dθ`, valid at every `t` and `q ≥ 0`: the main term appears only for `A`
with `a = 0`. -/
theorem scalar_tame_matched_jets_q (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℕ, 1 ≤ a + b → a + b ≤ 2 →
      ∀ (p : unitInterval) (t q : ℝ), 0 < (p : ℝ) → 0 ≤ q →
        tameErrorS p r t q ≤ 1 / 2 → ∀ i : Fin 4,
          |matchedScalarJet i a b p r t q -
              (if i = 0 ∧ a = 0 then
                r ^ a * (1 / 2 : ℝ) ^ b * (p : ℝ) * Real.exp ((q - r ^ 2) / 2)
              else 0)| ≤
            C * (r ^ a * (1 / 2 : ℝ) ^ b) * (p : ℝ) * tameErrorS p r t q *
              (if i = 0 ∧ a = 0 then Real.exp ((q - r ^ 2) / 2) else 1) := by
  obtain ⟨C, hC, h⟩ := scalar_tame_jets_q r hr
  refine ⟨C, hC, fun a b hab hab2 p t q hp hq he i => ?_⟩
  obtain ⟨hA, hB, hD, hT⟩ := h a b hab hab2 p t q hp hq he
  fin_cases i
  · simpa [matchedScalarJet] using hA
  · simpa [matchedScalarJet] using hB
  · simpa [matchedScalarJet] using hD
  · simpa [matchedScalarJet] using hT

end
end SparseSGD.Logistic.V2
