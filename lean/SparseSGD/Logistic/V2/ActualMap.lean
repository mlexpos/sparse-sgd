import SparseSGD.Logistic.DynamicConsistency
import SparseSGD.Logistic.ScalarCoefficients
import SparseSGD.Logistic.SourceAssumptions

/-!
# The actual drift recursion as an autonomous map of `DynamicState`

This is the actual drift recursion of `prop:LR34` / `cor:recursion`.  The Gaussian coefficients
depend on `theta` only through `(r, t, q) = (r mu, signalCoord mu theta, ‖theta‖²)`
(`coef*_eq_scalar`).  Since `‖theta‖² = theta_∥² + R_⊥`, they are evaluated at the state
`(t, q) = (y 0, y 0 ^ 2 + y 2)`, which turns the recursion into an autonomous self-map
`actualDriftMap` of `DynamicState`.

* `actualDriftMap_eq_dynamicDriftMap` links it to `dynamicDriftMap` along any compatible `theta`.
* `AP` is the parameter structure mirroring `TP` of `V2/RecursionTame.lean`, with
  state-dependent coefficients; `AP.ofModel` is the actual model.
-/

namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic
noncomputable section

/-- Normalized coefficient `A/p` evaluated at the state `(t,q) = (y 0, y 0^2 + y 2)`. -/
def actA (p : unitInterval) (r : ℝ) (y : DynamicState) : ℝ :=
  scalarCoefA p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ)

/-- Normalized coefficient `B/p` evaluated at the state. -/
def actB (p : unitInterval) (r : ℝ) (y : DynamicState) : ℝ :=
  scalarCoefB p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ)

/-- Normalized coefficient `D0/p` evaluated at the state. -/
def actD0 (p : unitInterval) (r : ℝ) (y : DynamicState) : ℝ :=
  scalarCoefD0 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ)

/-- Normalized coefficient `Dθ/p` evaluated at the state. -/
def actDt (p : unitInterval) (r : ℝ) (y : DynamicState) : ℝ :=
  scalarCoefDtheta p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ)

/-- The actual drift recursion as an autonomous map of the 5-variable state. -/
def actualDriftMap (d B : ℕ) (eta beta : ℝ) (p : unitInterval) (r : ℝ)
    (y : DynamicState) : DynamicState :=
  dynamicCoefficientStep r (1-beta) (eta*(p:ℝ)/(1-beta))
    (scalarCoefA p r (y 0) (y 0^2+y 2)/(p:ℝ)) (scalarCoefB p r (y 0) (y 0^2+y 2)/(p:ℝ))
    ((((d-1:ℝ)*scalarCoefD0 p r (y 0) (y 0^2+y 2) +
        y 2*scalarCoefDtheta p r (y 0) (y 0^2+y 2))/(B:ℝ)
      + ((B:ℝ)-1)/(B:ℝ)*(scalarCoefA p r (y 0) (y 0^2+y 2))^2*y 2)/(p:ℝ)^2) y

/-- The autonomous map agrees with `dynamicDriftMap` whenever `theta` has the summary geometry
`signalCoord mu theta = y 0`, `‖theta‖² = y 0² + y 2`. -/
theorem actualDriftMap_eq_dynamicDriftMap {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu theta : Vec d) (y : DynamicState) (hr : 0 < r mu)
    (ht : signalCoord mu theta = y 0) (hq : ‖theta‖^2 = y 0^2 + y 2) :
    actualDriftMap d B eta beta p (r mu) y = dynamicDriftMap (B:=B) eta beta p mu theta y := by
  unfold actualDriftMap dynamicDriftMap
  rw [coefA_eq_scalar p mu theta hr, coefB_eq_scalar p mu theta hr,
    coefD0_eq_scalar p mu theta hr, coefDtheta_eq_scalar p mu theta hr, ht, hq]

/-- Orbit corollary: an orbit of `dynamicDriftMap` along parameters `theta k` with matching
summaries is an orbit of the autonomous map. -/
theorem orbit_eq_actualDriftMap {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (theta : ℕ → Vec d) (x : ℕ → DynamicState) (hr : 0 < r mu)
    (ht : ∀ k, signalCoord mu (theta k) = x k 0)
    (hq : ∀ k, ‖theta k‖^2 = x k 0^2 + x k 2)
    (hx : ∀ k, x (k+1) = dynamicDriftMap (B:=B) eta beta p mu (theta k) (x k)) (k : ℕ) :
    x (k+1) = actualDriftMap d B eta beta p (r mu) (x k) := by
  rw [hx k, actualDriftMap_eq_dynamicDriftMap eta beta p mu (theta k) (x k) hr (ht k) (hq k)]

/-- Parameters of the actual recursion: step `h`, `delta`, source load `Phi`, noise weight `w`
(multiplying `Dθ/p`), batch ratio `rho`, and the probability `p`. -/
structure AP where
  h : ℝ
  delta : ℝ
  Phi : ℝ
  w : ℝ
  rho : ℝ
  p : unitInterval

/-- Temperature `kappa = 2 Phi / delta`. -/
def AP.kappa (a : AP) : ℝ := 2 * a.Phi / a.delta

/-- The increment with state-dependent coefficients. -/
def AP.inc (r : ℝ) (a : AP) (y : DynamicState) : DynamicState :=
  dynamicIncrement r (dynamicIncrementData y a.h a.delta a.kappa
    (actA a.p r y) (actB a.p r y) (actD0 a.p r y) (a.w * actDt a.p r y) a.rho)

/-- One-step map `y + h • inc`. -/
def AP.map (r : ℝ) (a : AP) (y : DynamicState) : DynamicState := y + a.h • a.inc r y

/-- The perturbation `inc - f` of the base field. -/
def AP.err (r deltaS PhiS : ℝ) (a : AP) (y : DynamicState) : DynamicState :=
  a.inc r y - dynamicField r deltaS PhiS y

/-- Distance of the parameters from the base point, plus `p`. -/
def AP.varrho (deltaS PhiS : ℝ) (a : AP) : ℝ :=
  |a.h| + |a.delta - deltaS| + |a.Phi - PhiS| + (a.p : ℝ)

/-- Admissible parameter tube. -/
def AP.Adm (deltaS PhiS : ℝ) (a : AP) : Prop :=
  |a.delta - deltaS| ≤ deltaS / 2 ∧ 0 ≤ a.rho ∧ a.rho ≤ 1 ∧ 0 ≤ a.w ∧ a.w ≤ a.kappa ∧
  0 < (a.p : ℝ) ∧ (a.p : ℝ) ≤ 1 / 2 ∧ a.varrho deltaS PhiS ≤ 1

/-- Parameters of the actual model. -/
def AP.ofModel (d B : ℕ) (eta beta : ℝ) (p : unitInterval) : AP :=
  ⟨1 - beta, eta * (p:ℝ) / (1 - beta), dynamicSourceLoad d B eta,
    (1 - beta) / ((B:ℝ) * (p:ℝ)), ((B:ℝ) - 1) / (B:ℝ), p⟩

/-- `map = y + h (f + err)`, exactly. -/
theorem AP.map_eq (r deltaS PhiS : ℝ) (a : AP) (y : DynamicState) :
    a.map r y = y + a.h • (dynamicField r deltaS PhiS y + a.err r deltaS PhiS y) := by
  rw [AP.map, AP.err]; congr 2; abel

/-- The model parameters reproduce `actualDriftMap`. -/
theorem AP.ofModel_map (d B : ℕ) (eta beta : ℝ) (p : unitInterval) (r : ℝ)
    (hB : 0 < B) (heta : eta ≠ 0) (hbeta : 1 - beta ≠ 0) (hp : (p:ℝ) ≠ 0) :
    (AP.ofModel d B eta beta p).map r = actualDriftMap d B eta beta p r := by
  funext y
  have hBr : (B:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hn := dynamicCoefficientStep_eq_increment r (1-beta) (eta*(p:ℝ)/(1-beta))
    (scalarCoefA p r (y 0) (y 0^2+y 2)/(p:ℝ)) (scalarCoefB p r (y 0) (y 0^2+y 2)/(p:ℝ))
    ((((d-1:ℝ)*scalarCoefD0 p r (y 0) (y 0^2+y 2) +
        y 2*scalarCoefDtheta p r (y 0) (y 0^2+y 2))/(B:ℝ)
      + ((B:ℝ)-1)/(B:ℝ)*(scalarCoefA p r (y 0) (y 0^2+y 2))^2*y 2)/(p:ℝ)^2)
    (2 * dynamicSourceLoad d B eta / (eta*(p:ℝ)/(1-beta)))
    (scalarCoefD0 p r (y 0) (y 0^2+y 2)/(p:ℝ))
    ((1 - beta) / ((B:ℝ) * (p:ℝ)) * (scalarCoefDtheta p r (y 0) (y 0^2+y 2)/(p:ℝ)))
    (((B:ℝ) - 1) / (B:ℝ)) y
    (by
      simp only [dynamicSourceLoad]
      field_simp
      ring)
  unfold actualDriftMap
  rw [hn]
  rfl

/-- Admissibility of `w` and `kappa` for the model parameters. -/
theorem AP.ofModel_w_le_kappa (d B : ℕ) (eta beta : ℝ) (p : unitInterval)
    (hd : 2 ≤ d) (hB : 0 < B) (hp : 0 < (p:ℝ)) (hbeta : 0 < 1 - beta) (heta : 0 < eta) :
    0 ≤ (AP.ofModel d B eta beta p).w ∧
      (AP.ofModel d B eta beta p).w ≤ (AP.ofModel d B eta beta p).kappa := by
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hdR : (1:ℝ) ≤ (d:ℝ) - 1 := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hk : (AP.ofModel d B eta beta p).kappa =
      (1 - beta) * ((d:ℝ) - 1) / ((B:ℝ) * (p:ℝ)) := by
    simp only [AP.kappa, AP.ofModel, dynamicSourceLoad]
    field_simp
  refine ⟨by simp only [AP.ofModel]; positivity, ?_⟩
  rw [hk]
  simp only [AP.ofModel]
  have hpos : 0 < (B:ℝ) * (p:ℝ) := by positivity
  rw [div_le_div_iff_of_pos_right hpos]
  nlinarith

/-- `rho = (B-1)/B` lies in `[0,1]`. -/
theorem AP.ofModel_rho (d B : ℕ) (eta beta : ℝ) (p : unitInterval) (hB : 0 < B) :
    0 ≤ (AP.ofModel d B eta beta p).rho ∧ (AP.ofModel d B eta beta p).rho ≤ 1 := by
  have hB1 : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hBr : (0:ℝ) < B := by linarith
  simp only [AP.ofModel]
  constructor
  · exact div_nonneg (by linarith) hBr.le
  · rw [div_le_one hBr]; linarith

/-- The bulk coordinate of the canonical equilibrium is positive. -/
theorem equilibrium_bulk_pos (r deltaS PhiS : ℝ) (hr : 0 < r) (hP : 0 < PhiS)
    (hd : 0 < deltaS) : 0 < (dynamicCanonicalEquilibrium r deltaS PhiS) 2 := by
  have hs := (positiveRoot_spec r PhiS hr hP.le).1
  simp only [dynamicCanonicalEquilibrium, equilibriumBulk]
  simpa using div_pos (mul_pos hP hs) hr

/-- Tame specialization: with the tame coefficients the increment is `tameInc`'s increment,
i.e. `AP.inc` only depends on the state through the coefficients. -/
theorem AP.inc_of_tame (r : ℝ) (a : AP) (y : DynamicState)
    (hA : actA a.p r y = dynamicAlpha r y) (hB : actB a.p r y = -1)
    (hD : actD0 a.p r y = 1) (hT : a.w * actDt a.p r y = 0) :
    a.inc r y = dynamicIncrement r
      (dynamicIncrementData y a.h a.delta a.kappa (dynamicAlpha r y) (-1) 1 0 a.rho) := by
  rw [AP.inc, hA, hB, hD, hT]

end
end SparseSGD.Logistic.V2
