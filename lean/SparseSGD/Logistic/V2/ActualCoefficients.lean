import SparseSGD.Logistic.V2.ActualMap
import SparseSGD.Logistic.TameCoefficientDerivatives
import SparseSGD.Logistic.FluidDeterministicVariance
import SparseSGD.Logistic.FluidDeterministicScalarTaylor

/-!
# Lemma G.3 in scalar state variables

The tame value bounds (`tame_coefficients`) and jet bounds (`tame_scalarJets_first_second`)
are stated for actual vectors `(mu, theta)`.  Here they are restated for scalar arguments
`(r, t, q)` with `q = t^2 + R`, `R ≥ 0`, by realizing `(r, t, R)` with the explicit frame in
`Vec 2`.  This makes them available at every `DynamicState` with `y 2 ≥ 0`.

* `tameErrorS` is the scalar form of `tameError`; `tameErrorS_le_mul` is `ε ≍ p` on compacts.
* `scalar_tame_values` bounds the normalized state coefficients `actA/actB/actD0/actDt`.
* `scalar_tame_jets` is `TameScalarJetBounds` in scalar variables (`TameScalarJetBoundsS`),
  also packaged through `matchedScalarJet`.
-/

namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

/-- Scalar form of `tameError` at `(r, t, q) = (r mu, signalCoord mu theta, ‖theta‖²)`. -/
def tameErrorS (p : unitInterval) (r t q : ℝ) : ℝ :=
  (p : ℝ) * (Real.exp (2 * q - r ^ 2) + Real.exp ((3 * q - r ^ 2) / 2) +
    (1 + Real.exp ((q - r ^ 2) / 2)) * Real.exp (r * |t|))

/-- `tameError` is `tameErrorS` evaluated at the scalar summaries. -/
theorem tameError_eq_tameErrorS {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hr : 0 < r mu) :
    tameError p mu theta = tameErrorS p (r mu) (signalCoord mu theta) (‖theta‖ ^ 2) := by
  rw [tameError_source_formula p mu theta hr]
  rfl

/-- The scalar tame error is at most a constant times `p` on compact sets of `(t, q)`. -/
theorem tameErrorS_le_mul (r M : ℝ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (p : unitInterval) (t q : ℝ), |t| ≤ M → q ≤ M ^ 2 + M →
      tameErrorS p r t q ≤ E * (p : ℝ) := by
  refine ⟨Real.exp (2 * (M ^ 2 + M) - r ^ 2) + Real.exp ((3 * (M ^ 2 + M) - r ^ 2) / 2) +
    (1 + Real.exp ((M ^ 2 + M - r ^ 2) / 2)) * Real.exp (|r| * M), by positivity, ?_⟩
  intro p t q ht hq
  have hp := p.property.1
  have h1 : Real.exp (2 * q - r ^ 2) ≤ Real.exp (2 * (M ^ 2 + M) - r ^ 2) :=
    Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp ((3 * q - r ^ 2) / 2) ≤ Real.exp ((3 * (M ^ 2 + M) - r ^ 2) / 2) :=
    Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp ((q - r ^ 2) / 2) ≤ Real.exp ((M ^ 2 + M - r ^ 2) / 2) :=
    Real.exp_le_exp.2 (by linarith)
  have h4 : Real.exp (r * |t|) ≤ Real.exp (|r| * M) := by
    apply Real.exp_le_exp.2
    calc r * |t| ≤ |r| * |t| := mul_le_mul_of_nonneg_right (le_abs_self r) (abs_nonneg t)
      _ ≤ |r| * M := mul_le_mul_of_nonneg_left ht (abs_nonneg r)
  unfold tameErrorS
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_right _ hp
  have h5 : (1 + Real.exp ((q - r ^ 2) / 2)) * Real.exp (r * |t|) ≤
      (1 + Real.exp ((M ^ 2 + M - r ^ 2) / 2)) * Real.exp (|r| * M) :=
    mul_le_mul (by linarith) h4 (Real.exp_pos _).le (by positivity)
  linarith

/-- A vector realization in `Vec 2` of any scalar geometry `(r, t, R)` with `R ≥ 0`. -/
theorem exists_frame (rr t R : ℝ) (hr : 0 < rr) (hR : 0 ≤ R) :
    ∃ mu theta : Vec 2, r mu = rr ∧ signalCoord mu theta = t ∧ ‖theta‖ ^ 2 = t ^ 2 + R :=
  ⟨scalarFrameMu rr, scalarFrameTheta t R, scalarFrameMu_norm rr hr.le,
    scalarFrameTheta_signal rr t R hr, scalarFrameTheta_norm t R hR⟩

/-- Lemma G.3 value bounds for the normalized state coefficients, at any state with
`y 2 ≥ 0` and small tame error. -/
theorem scalar_tame_values (r : ℝ) (hr : 0 < r) :
    ∀ (p : unitInterval) (y : DynamicState), 0 < (p : ℝ) → 0 ≤ y 2 →
      tameErrorS p r (y 0) (y 0 ^ 2 + y 2) ≤ 1 / 2 →
      |actA p r y - dynamicAlpha r y| ≤
          6 * dynamicAlpha r y * tameErrorS p r (y 0) (y 0 ^ 2 + y 2) ∧
      |actB p r y + 1| ≤ 2 * tameErrorS p r (y 0) (y 0 ^ 2 + y 2) ∧
      |actD0 p r y - 1| ≤ 6 * tameErrorS p r (y 0) (y 0 ^ 2 + y 2) ∧
      |actDt p r y| ≤ 12 * tameErrorS p r (y 0) (y 0 ^ 2 + y 2) := by
  intro p y hp hy2 he
  obtain ⟨mu, theta, hmu, hsig, hth⟩ := exists_frame r (y 0) (y 2) hr hy2
  have hrmu : 0 < SparseSGD.Logistic.r mu := by rw [hmu]; exact hr
  have hE : tameError p mu theta = tameErrorS p r (y 0) (y 0 ^ 2 + y 2) := by
    rw [tameError_eq_tameErrorS p mu theta hrmu, hmu, hsig, hth]
  have hα : gaussianAlpha mu theta = dynamicAlpha r y := by
    have : ‖mu‖ = r := hmu
    simp only [gaussianAlpha, dynamicAlpha, this, hth]
  obtain ⟨hA, hB, hD, hT⟩ := tame_coefficients p mu theta hp (by rw [hE]; exact he)
  rw [hE, hα] at hA
  rw [hE] at hB hD hT
  have hA' : coefA p mu theta / (p : ℝ) = actA p r y := by
    rw [coefA_eq_scalar p mu theta hrmu, hmu, hsig, hth]; rfl
  have hB' : coefB p mu theta / (p : ℝ) = actB p r y := by
    rw [coefB_eq_scalar p mu theta hrmu, hmu, hsig, hth]; rfl
  have hD' : coefD0 p mu theta / (p : ℝ) = actD0 p r y := by
    rw [coefD0_eq_scalar p mu theta hrmu, hmu, hsig, hth]; rfl
  have hT' : coefDtheta p mu theta / (p : ℝ) = actDt p r y := by
    rw [coefDtheta_eq_scalar p mu theta hrmu, hmu, hsig, hth]; rfl
  have key : ∀ (c x : ℝ) (m : ℝ), |c - (p : ℝ) * m| ≤ x * (p : ℝ) →
      |c / (p : ℝ) - m| ≤ x := by
    intro c x m h
    have : c / (p : ℝ) - m = (c - (p : ℝ) * m) / (p : ℝ) := by field_simp
    rw [this, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hA']
    exact key _ _ _ (by linarith [hA])
  · rw [← hB']
    have := key (coefB p mu theta) (2 * tameErrorS p r (y 0) (y 0 ^ 2 + y 2)) (-1)
      (by rw [mul_neg_one, sub_neg_eq_add]; linarith)
    simpa [sub_neg_eq_add] using this
  · rw [← hD']
    exact key _ _ _ (by rw [mul_one]; linarith)
  · rw [← hT']
    have := key (coefDtheta p mu theta) (12 * tameErrorS p r (y 0) (y 0 ^ 2 + y 2)) 0
      (by rw [mul_zero, sub_zero]; linarith)
    simpa using this

/-- Scalar form of `TameScalarJetBounds a b C` at `(r, t, q)`, with `α = exp((q - r²)/2)` and
`e = tameErrorS p r t q`; the jet factor is `r^a (1/2)^b`. -/
def TameScalarJetBoundsS (a b : ℕ) (C : ℝ) (p : unitInterval) (r t q : ℝ) : Prop :=
  |scalarCoefAJet a b p r t q -
      (if a = 0 then r ^ a * (1 / 2 : ℝ) ^ b * (p : ℝ) * Real.exp ((q - r ^ 2) / 2) else 0)| ≤
    C * (r ^ a * (1 / 2 : ℝ) ^ b) * (p : ℝ) * tameErrorS p r t q *
      (if a = 0 then Real.exp ((q - r ^ 2) / 2) else 1) ∧
  |scalarCoefBJet a b p r t q| ≤ C * (r ^ a * (1 / 2 : ℝ) ^ b) * (p : ℝ) * tameErrorS p r t q ∧
  |scalarCoefD0Jet a b p r t q| ≤ C * (r ^ a * (1 / 2 : ℝ) ^ b) * (p : ℝ) * tameErrorS p r t q ∧
  |scalarCoefDthetaJet a b p r t q| ≤
    C * (r ^ a * (1 / 2 : ℝ) ^ b) * (p : ℝ) * tameErrorS p r t q

/-- Lemma G.3 first and second jet bounds in scalar variables: valid at every `(t, R)` with
`R ≥ 0`, `q = t² + R`, and small tame error. -/
theorem scalar_tame_jets (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℕ, 1 ≤ a + b → a + b ≤ 2 →
      ∀ (p : unitInterval) (t R : ℝ), 0 < (p : ℝ) → 0 ≤ R →
        tameErrorS p r t (t ^ 2 + R) ≤ 1 / 2 →
        TameScalarJetBoundsS a b C p r t (t ^ 2 + R) := by
  obtain ⟨C, hC, h⟩ := tame_scalarJets_first_second
  refine ⟨C, hC, fun a b hab hab2 p t R hp hR he => ?_⟩
  obtain ⟨mu, theta, hmu, hsig, hth⟩ := exists_frame r t R hr hR
  have hrmu : 0 < SparseSGD.Logistic.r mu := by rw [hmu]; exact hr
  have hE : tameError p mu theta = tameErrorS p r t (t ^ 2 + R) := by
    rw [tameError_eq_tameErrorS p mu theta hrmu, hmu, hsig, hth]
  have hα : gaussianAlpha mu theta = Real.exp ((t ^ 2 + R - r ^ 2) / 2) := by
    have : ‖mu‖ = r := hmu
    simp only [gaussianAlpha, this, hth]
  have H := h a b hab hab2 p mu theta hrmu hp (by rw [hE]; exact he)
  simp only [TameScalarJetBounds, scalarJetFactor, hE, hα, hmu, hsig, hth] at H
  exact H

/-- The jet bounds packaged through `matchedScalarJet i a b`, `i : Fin 4` indexing
`A, B, D0, Dθ`: the main term appears only for `A` with `a = 0`. -/
theorem scalar_tame_matched_jets (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℕ, 1 ≤ a + b → a + b ≤ 2 →
      ∀ (p : unitInterval) (t R : ℝ), 0 < (p : ℝ) → 0 ≤ R →
        tameErrorS p r t (t ^ 2 + R) ≤ 1 / 2 → ∀ i : Fin 4,
          |matchedScalarJet i a b p r t (t ^ 2 + R) -
              (if i = 0 ∧ a = 0 then
                r ^ a * (1 / 2 : ℝ) ^ b * (p : ℝ) * Real.exp ((t ^ 2 + R - r ^ 2) / 2)
              else 0)| ≤
            C * (r ^ a * (1 / 2 : ℝ) ^ b) * (p : ℝ) * tameErrorS p r t (t ^ 2 + R) *
              (if i = 0 ∧ a = 0 then Real.exp ((t ^ 2 + R - r ^ 2) / 2) else 1) := by
  obtain ⟨C, hC, h⟩ := scalar_tame_jets r hr
  refine ⟨C, hC, fun a b hab hab2 p t R hp hR he i => ?_⟩
  obtain ⟨hA, hB, hD, hT⟩ := h a b hab hab2 p t R hp hR he
  fin_cases i
  · simpa [matchedScalarJet] using hA
  · simpa [matchedScalarJet] using hB
  · simpa [matchedScalarJet] using hD
  · simpa [matchedScalarJet] using hT

end
end SparseSGD.Logistic.V2
