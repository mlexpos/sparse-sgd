import SparseSGD.Logistic.V2.ActualCoefficients
import SparseSGD.Logistic.V2.TameScalar
import SparseSGD.Logistic.FluidDeterministicDerivative

/-!
# Derivatives, Lipschitz bounds and value bounds of the actual coefficients

* `matchedScalarJet_hasFDerivAt_pos`: the joint Fréchet derivative of the zeroth jet in `(t, q)` at
  `q > 0`, obtained from the rectangle Taylor bound.
* `matchedScalarState_hasFDerivAt`: the chain rule through `y ↦ (y 0, y 0^2 + y 2)`.
* `coefErrA/B/D/T`: coefficient errors with explicit derivatives, and `coefErr_deriv_bound`
  (`‖D coefErr‖ ≤ C · tameErrorS`).
* `matchedScalarJet_clip`: the jets only depend on `max q 0`.
* `actCoef_lipschitzOn`, `actCoef_bounded`: Lipschitz and value bounds on balls, valid at all
  states (including `q ≤ 0`), uniformly in `p`.
-/

namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

/-- Joint Fréchet derivative of the zeroth coefficient jet in `(t, q)` at `q > 0`. -/
theorem matchedScalarJet_hasFDerivAt_pos (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (i : Fin 4) (p : unitInterval) (r t q : ℝ) (hp : 0 < (p : ℝ)) (hp2 : (p : ℝ) ≤ 1 / 2)
    (hq : 0 < q) :
    HasFDerivAt (fun x : ℝ × ℝ => matchedScalarJet i 0 0 p r x.1 x.2)
      ((matchedScalarJet i 1 0 p r t q) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (matchedScalarJet i 0 1 p r t q) • ContinuousLinearMap.snd ℝ ℝ ℝ) (t, q) := by
  obtain ⟨C, hC, h⟩ := matchedScalarJet_rectangle_taylor S1 r (q + 1)
  let s : Set (ℝ × ℝ) := {x | 0 ≤ x.2 ∧ x.2 ≤ q + 1}
  have hs : s ∈ nhds (t, q) := by
    have h1 : Set.Icc (0 : ℝ) (q + 1) ∈ nhds ((t, q) : ℝ × ℝ).2 :=
      Icc_mem_nhds hq (by linarith)
    exact continuous_snd.continuousAt.preimage_mem_nhds h1
  have hpC : 0 ≤ 4 * C * (p : ℝ) := by positivity
  refine (hasFDerivWithinAt_of_local_quadratic_bound _ _ s (t, q) (4 * C * (p : ℝ)) 1 hpC
    one_pos ?_).hasFDerivAt hs
  intro y hy _
  have H := h i p t y.1 q y.2 hp hp2 hq.le hy.1 (by linarith) hy.2
  have h1 : |y.1 - t| ≤ ‖y - (t, q)‖ := by
    simpa [Real.norm_eq_abs] using norm_fst_le (y - (t, q))
  have h2 : |y.2 - q| ≤ ‖y - (t, q)‖ := by
    simpa [Real.norm_eq_abs] using norm_snd_le (y - (t, q))
  have h3 : (|y.1 - t| + |y.2 - q|) ^ 2 ≤ (2 * ‖y - (t, q)‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h4 : C * (p : ℝ) * (|y.1 - t| + |y.2 - q|) ^ 2 ≤
      4 * C * (p : ℝ) * ‖y - (t, q)‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left h3 (mul_nonneg hC hp.le)
    nlinarith
  rw [Real.norm_eq_abs]
  refine le_trans (le_of_eq ?_) (H.trans h4)
  congr 1
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul]
  ring

/-- Chain rule: derivative of the state-level jet `matchedScalarState` at states with
`y 0^2 + y 2 > 0`. -/
theorem matchedScalarState_hasFDerivAt (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (i : Fin 4) (p : unitInterval) (r : ℝ) (y : DynamicState) (hp : 0 < (p : ℝ))
    (hp2 : (p : ℝ) ≤ 1 / 2) (hq : 0 < y 0 ^ 2 + y 2) :
    HasFDerivAt (matchedScalarState i p r) (matchedScalarStateDerivative i p r y) y := by
  have h1 := matchedScalarJet_hasFDerivAt_pos S1 i p r (y 0) (y 0 ^ 2 + y 2) hp hp2 hq
  have h0 : HasFDerivAt (fun y : DynamicState => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ) 0) y :=
    hasFDerivAt_apply 0 y
  have h2 : HasFDerivAt (fun y : DynamicState => y 2)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ) 2) y :=
    hasFDerivAt_apply 2 y
  have hsq : HasFDerivAt (fun y : DynamicState => y 0 ^ 2 + y 2)
      ((2 * y 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ) 0 +
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ) 2) y := by
    have := (h0.mul h0).add h2
    convert this using 1
    · funext z; simp [sq]
    · ext z; simp; ring
  have hg := h0.prodMk hsq
  have hc := h1.comp y hg
  refine HasFDerivAt.congr_fderiv hc ?_
  ext z
  simp [matchedScalarStateDerivative]
  ring

/-- Gaussian average with variance clipped at zero. -/
theorem gaussianAverage_clip' (f : ℝ → ℝ) (c q : ℝ) :
    SparseSGD.Probability.gaussianAverage f c q =
      SparseSGD.Probability.gaussianAverage f c (max q 0) := by
  unfold SparseSGD.Probability.gaussianAverage
  rcases le_total q 0 with h | h
  · rw [max_eq_right h, Real.sqrt_zero, Real.sqrt_eq_zero_of_nonpos h]
  · rw [max_eq_left h]

/-- The generic Gaussian jet depends on the variance only through `max q 0`. -/
theorem scalarGaussianJet_clip (f0 f1 : ℕ → ℝ → ℝ) (base a b : ℕ) (p : unitInterval)
    (r t q : ℝ) :
    scalarGaussianJet f0 f1 base a b p r t q =
      scalarGaussianJet f0 f1 base a b p r t (max q 0) := by
  unfold scalarGaussianJet
  rw [gaussianAverage_clip' (f0 _) _ q, gaussianAverage_clip' (f1 _) _ q]

/-- Clipping: all matched jets only depend on `max q 0`. -/
theorem matchedScalarJet_clip (i : Fin 4) (a b : ℕ) (p : unitInterval) (r t q : ℝ) :
    matchedScalarJet i a b p r t q = matchedScalarJet i a b p r t (max q 0) := by
  fin_cases i
  · change scalarCoefAJet a b p r t q = scalarCoefAJet a b p r t (max q 0)
    exact scalarGaussianJet_clip _ _ _ _ _ _ _ _ _
  · change scalarCoefBJet a b p r t q = scalarCoefBJet a b p r t (max q 0)
    unfold scalarCoefBJet
    rw [scalarGaussianJet_clip (fun _ _ => 0) _ _ _ _ _ _ _ q]
  · change scalarCoefD0Jet a b p r t q = scalarCoefD0Jet a b p r t (max q 0)
    exact scalarGaussianJet_clip _ _ _ _ _ _ _ _ _
  · change scalarCoefDthetaJet a b p r t q = scalarCoefDthetaJet a b p r t (max q 0)
    exact scalarGaussianJet_clip _ _ _ _ _ _ _ _ _

/-- Coordinate projection of a `DynamicState`, as a continuous linear functional. -/
def coordFn (k : Fin 5) : DynamicState →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ) k

/-- Coefficient error for `A`: `actA - α`. -/
def coefErrA (p : unitInterval) (r : ℝ) (y : DynamicState) : ℝ := actA p r y - dynamicAlpha r y

/-- Coefficient error for `B`: `actB + 1`. -/
def coefErrB (p : unitInterval) (r : ℝ) (y : DynamicState) : ℝ := actB p r y + 1

/-- Coefficient error for `D0`: `actD0 - 1`. -/
def coefErrD (p : unitInterval) (r : ℝ) (y : DynamicState) : ℝ := actD0 p r y - 1

/-- Coefficient error for `Dθ`: `actDt`. -/
def coefErrT (p : unitInterval) (r : ℝ) (y : DynamicState) : ℝ := actDt p r y

/-- Derivative of `y ↦ matchedScalarState i p r y / p` through `(y 0, y 0^2 + y 2)`. -/
def normJetDeriv (i : Fin 4) (p : unitInterval) (r : ℝ) (y : DynamicState) :
    DynamicState →L[ℝ] ℝ :=
  (matchedScalarJet i 1 0 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ) +
      2 * y 0 * (matchedScalarJet i 0 1 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ))) • coordFn 0 +
    (matchedScalarJet i 0 1 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ)) • coordFn 2

/-- Derivative of `dynamicAlpha r`: `∂₀ α = y₀ α`, `∂₂ α = α / 2`. -/
def dynamicAlphaDeriv (r : ℝ) (y : DynamicState) : DynamicState →L[ℝ] ℝ :=
  (dynamicAlpha r y * y 0) • coordFn 0 + (dynamicAlpha r y / 2) • coordFn 2

/-- Derivative of `coefErrA`:
`∂₀ = J10/p + 2 y₀ (J01/p - α/2)`, `∂₂ = J01/p - α/2`. -/
def coefErrADeriv (p : unitInterval) (r : ℝ) (y : DynamicState) : DynamicState →L[ℝ] ℝ :=
  (matchedScalarJet 0 1 0 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ) +
      2 * y 0 * (matchedScalarJet 0 0 1 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ) -
        dynamicAlpha r y / 2)) • coordFn 0 +
    (matchedScalarJet 0 0 1 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ) - dynamicAlpha r y / 2) •
      coordFn 2

/-- The normalized jet `matchedScalarState i / p` is differentiable at `q > 0`. -/
theorem hasFDerivAt_normJet (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (i : Fin 4) (p : unitInterval) (r : ℝ) (y : DynamicState) (hp : 0 < (p : ℝ))
    (hp2 : (p : ℝ) ≤ 1 / 2) (hq : 0 < y 0 ^ 2 + y 2) :
    HasFDerivAt (fun z => matchedScalarState i p r z / (p : ℝ)) (normJetDeriv i p r y) y := by
  have h := (matchedScalarState_hasFDerivAt S1 i p r y hp hp2 hq).const_mul ((p : ℝ)⁻¹)
  have hf : (fun z => matchedScalarState i p r z / (p : ℝ)) =
      fun z => (p : ℝ)⁻¹ * matchedScalarState i p r z := by
    funext z; ring
  rw [hf]
  refine HasFDerivAt.congr_fderiv h ?_
  ext z
  simp [matchedScalarStateDerivative, normJetDeriv, coordFn]
  field_simp

/-- `dynamicAlpha r` has the derivative `dynamicAlphaDeriv r y`. -/
theorem hasFDerivAt_dynamicAlpha_coord (r : ℝ) (y : DynamicState) :
    HasFDerivAt (dynamicAlpha r) (dynamicAlphaDeriv r y) y := by
  have h0 : HasFDerivAt (fun y : DynamicState => y 0) (coordFn 0) y := hasFDerivAt_apply 0 y
  have h2 : HasFDerivAt (fun y : DynamicState => y 2) (coordFn 2) y := hasFDerivAt_apply 2 y
  have h := ((((h0.mul h0).add h2).sub_const (r ^ 2)).const_mul (1 / 2 : ℝ)).exp
  have hf : dynamicAlpha r =
      fun y : DynamicState => Real.exp (1 / 2 * (y 0 * y 0 + y 2 - r ^ 2)) := by
    funext z; simp only [dynamicAlpha, sq]; congr 1; ring
  rw [hf]
  refine HasFDerivAt.congr_fderiv h ?_
  ext z
  simp [dynamicAlphaDeriv, coordFn, dynamicAlpha, sq]
  ring

/-- `coefErrA` is differentiable at states with `q > 0`. -/
theorem coefErrA_hasFDerivAt (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r : ℝ) (y : DynamicState) (hp : 0 < (p : ℝ)) (hp2 : (p : ℝ) ≤ 1 / 2)
    (hq : 0 < y 0 ^ 2 + y 2) :
    HasFDerivAt (coefErrA p r) (coefErrADeriv p r y) y := by
  have h := (hasFDerivAt_normJet S1 0 p r y hp hp2 hq).sub (hasFDerivAt_dynamicAlpha_coord r y)
  have hf : coefErrA p r = fun z => matchedScalarState 0 p r z / (p : ℝ) - dynamicAlpha r z := by
    funext z; simp [coefErrA, actA, matchedScalarState, matchedScalarJet]
  rw [hf]
  refine HasFDerivAt.congr_fderiv h ?_
  ext z
  simp [normJetDeriv, dynamicAlphaDeriv, coefErrADeriv, coordFn]
  ring

/-- `coefErrB` is differentiable at states with `q > 0`. -/
theorem coefErrB_hasFDerivAt (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r : ℝ) (y : DynamicState) (hp : 0 < (p : ℝ)) (hp2 : (p : ℝ) ≤ 1 / 2)
    (hq : 0 < y 0 ^ 2 + y 2) :
    HasFDerivAt (coefErrB p r) (normJetDeriv 1 p r y) y := by
  have h := (hasFDerivAt_normJet S1 1 p r y hp hp2 hq).add_const 1
  have hf : coefErrB p r = fun z => matchedScalarState 1 p r z / (p : ℝ) + 1 := by
    funext z; simp [coefErrB, actB, matchedScalarState, matchedScalarJet]
  rw [hf]; exact h

/-- `coefErrD` is differentiable at states with `q > 0`. -/
theorem coefErrD_hasFDerivAt (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r : ℝ) (y : DynamicState) (hp : 0 < (p : ℝ)) (hp2 : (p : ℝ) ≤ 1 / 2)
    (hq : 0 < y 0 ^ 2 + y 2) :
    HasFDerivAt (coefErrD p r) (normJetDeriv 2 p r y) y := by
  have h := (hasFDerivAt_normJet S1 2 p r y hp hp2 hq).sub_const 1
  have hf : coefErrD p r = fun z => matchedScalarState 2 p r z / (p : ℝ) - 1 := by
    funext z; simp [coefErrD, actD0, matchedScalarState, matchedScalarJet]
  rw [hf]; exact h

/-- `coefErrT` is differentiable at states with `q > 0`. -/
theorem coefErrT_hasFDerivAt (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r : ℝ) (y : DynamicState) (hp : 0 < (p : ℝ)) (hp2 : (p : ℝ) ≤ 1 / 2)
    (hq : 0 < y 0 ^ 2 + y 2) :
    HasFDerivAt (coefErrT p r) (normJetDeriv 3 p r y) y := by
  have h := hasFDerivAt_normJet S1 3 p r y hp hp2 hq
  have hf : coefErrT p r = fun z => matchedScalarState 3 p r z / (p : ℝ) := by
    funext z; simp [coefErrT, actDt, matchedScalarState, matchedScalarJet]
  rw [hf]; exact h

/-- Coordinate-form functionals have norm at most `|c₀| + |c₂|`. -/
theorem norm_coord_comb_le (c0 c2 : ℝ) :
    ‖c0 • coordFn 0 + c2 • coordFn 2‖ ≤ |c0| + |c2| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv0 : |v 0| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0
  have hv2 : |v 2| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 2
  have : (c0 • coordFn 0 + c2 • coordFn 2) v = c0 * v 0 + c2 * v 2 := by
    simp [coordFn]
  rw [this, Real.norm_eq_abs]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hv0 (abs_nonneg c0),
    mul_le_mul_of_nonneg_left hv2 (abs_nonneg c2)]

/-- Coordinates of a state in a ball. -/
theorem abs_coord_le_of_norm_le (y : DynamicState) (M : ℝ) (hy : ‖y‖ ≤ M) (k : Fin 5) :
    |y k| ≤ M := by
  simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y k).trans hy

/-- The clipped variance of a state in a ball is in `[0, M^2 + M]`. -/
theorem clipq_mem (y : DynamicState) (M : ℝ) (hy : ‖y‖ ≤ M) :
    0 ≤ max (y 0 ^ 2 + y 2) 0 ∧ max (y 0 ^ 2 + y 2) 0 ≤ M ^ 2 + M := by
  have h0 := abs_coord_le_of_norm_le y M hy 0
  have h2 := abs_coord_le_of_norm_le y M hy 2
  refine ⟨le_max_right _ _, max_le ?_ (by nlinarith [abs_nonneg (y 0)])⟩
  nlinarith [abs_nonneg (y 0), sq_abs (y 0), le_abs_self (y 2), abs_nonneg (y 2)]

/-- Division by `p` of a bound of the form `|x| ≤ B p`. -/
theorem abs_div_le_of_le_mul (x p B : ℝ) (hp : 0 < p) (h : |x| ≤ B * p) : |x / p| ≤ B := by
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]; exact h

/-- The derivatives of the coefficient errors are bounded by a constant times the tame error,
on bounded physical states with `q > 0` and small tame error. -/
theorem coefErr_deriv_bound (S1 : SparseSGD.External.GaussianSteinCertificate 1) (r : ℝ)
    (hr : 0 < r) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : unitInterval) (y : DynamicState), 0 < (p : ℝ) → (p : ℝ) ≤ 1 / 2 →
      ‖y‖ ≤ M → 0 < y 0 ^ 2 + y 2 →
      tameErrorS p r (y 0) (y 0 ^ 2 + y 2) ≤ 1 / 2 →
      ‖fderiv ℝ (coefErrA p r) y‖ ≤ C * tameErrorS p r (y 0) (y 0 ^ 2 + y 2) ∧
      ‖fderiv ℝ (coefErrB p r) y‖ ≤ C * tameErrorS p r (y 0) (y 0 ^ 2 + y 2) ∧
      ‖fderiv ℝ (coefErrD p r) y‖ ≤ C * tameErrorS p r (y 0) (y 0 ^ 2 + y 2) ∧
      ‖fderiv ℝ (coefErrT p r) y‖ ≤ C * tameErrorS p r (y 0) (y 0 ^ 2 + y 2) := by
  obtain ⟨C, hC, hj⟩ := scalar_tame_matched_jets_q r hr
  set Aα := Real.exp ((M ^ 2 + M - r ^ 2) / 2) with hAα
  have hAα0 : 0 ≤ Aα := (Real.exp_pos _).le
  refine ⟨C * (r + (2 * |M| + 1) * (1 + Aα)), by positivity, ?_⟩
  intro p y hp hp2 hy hq he
  set e := tameErrorS p r (y 0) (y 0 ^ 2 + y 2) with he_def
  have he0 : 0 ≤ e := by
    rw [he_def]; unfold tameErrorS; have := p.property.1; positivity
  have hy0 := abs_coord_le_of_norm_le y M hy 0
  have hM : |y 0| ≤ |M| := hy0.trans (le_abs_self M)
  have hqM : y 0 ^ 2 + y 2 ≤ M ^ 2 + M := (clipq_mem y M hy).2.trans' (le_max_left _ _)
  have hα : dynamicAlpha r y ≤ Aα := by
    unfold dynamicAlpha; exact Real.exp_le_exp.2 (by linarith)
  have hα0 : 0 < dynamicAlpha r y := Real.exp_pos _
  have j10 : ∀ i : Fin 4, |matchedScalarJet i 1 0 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ)| ≤
      C * r * e := by
    intro i
    have := hj 1 0 (by norm_num) (by norm_num) p (y 0) (y 0 ^ 2 + y 2) hp hq.le he i
    apply abs_div_le_of_le_mul _ _ _ hp
    have h' : |matchedScalarJet i 1 0 p r (y 0) (y 0 ^ 2 + y 2)| ≤ C * r * (p : ℝ) * e := by
      simpa using this
    linarith
  have j01 : ∀ i : Fin 4, i ≠ 0 →
      |matchedScalarJet i 0 1 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ)| ≤ C / 2 * e := by
    intro i hi
    have := hj 0 1 (by norm_num) (by norm_num) p (y 0) (y 0 ^ 2 + y 2) hp hq.le he i
    apply abs_div_le_of_le_mul _ _ _ hp
    have h' : |matchedScalarJet i 0 1 p r (y 0) (y 0 ^ 2 + y 2)| ≤ C * 2⁻¹ * (p : ℝ) * e := by
      simpa [hi, he_def] using this
    linarith
  have j01A : |matchedScalarJet 0 0 1 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ) -
      dynamicAlpha r y / 2| ≤ C / 2 * e * dynamicAlpha r y := by
    have := hj 0 1 (by norm_num) (by norm_num) p (y 0) (y 0 ^ 2 + y 2) hp hq.le he 0
    have e1 : matchedScalarJet 0 0 1 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ) -
        dynamicAlpha r y / 2 =
        (matchedScalarJet 0 0 1 p r (y 0) (y 0 ^ 2 + y 2) -
          (p : ℝ) * (dynamicAlpha r y / 2)) / (p : ℝ) := by
      field_simp
    rw [e1]
    apply abs_div_le_of_le_mul _ _ _ hp
    have h' : |matchedScalarJet 0 0 1 p r (y 0) (y 0 ^ 2 + y 2) -
        (p : ℝ) * (dynamicAlpha r y / 2)| ≤ C * 2⁻¹ * (p : ℝ) * e * dynamicAlpha r y := by
      have h2 : (if (0 : Fin 4) = 0 ∧ (0 : ℕ) = 0 then
          r ^ 0 * (1 / 2 : ℝ) ^ 1 * (p : ℝ) * Real.exp ((y 0 ^ 2 + y 2 - r ^ 2) / 2) else 0) =
          (p : ℝ) * (dynamicAlpha r y / 2) := by
        simp [dynamicAlpha]; ring
      rw [h2] at this
      simpa [dynamicAlpha, he_def] using this
    nlinarith
  have hu : |matchedScalarJet 0 0 1 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ) -
      dynamicAlpha r y / 2| ≤ C / 2 * e * Aα :=
    j01A.trans (mul_le_mul_of_nonneg_left hα (by positivity))
  have hK : 0 ≤ C * e * ((2 * |M| + 1) + (|M| + 1 / 2) * Aα) := by positivity
  have hother : ∀ i : Fin 4, i ≠ 0 →
      ‖normJetDeriv i p r y‖ ≤ C * (r + (2 * |M| + 1) * (1 + Aα)) * e := by
    intro i hi
    unfold normJetDeriv
    refine (norm_coord_comb_le _ _).trans ?_
    have h1 := j10 i
    have h2 := j01 i hi
    have h3 : |2 * y 0 * (matchedScalarJet i 0 1 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ))| ≤
        2 * |M| * (C / 2 * e) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num)) h2 (abs_nonneg _)
        (by positivity)
    have h4 := abs_add_le (matchedScalarJet i 1 0 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ))
      (2 * y 0 * (matchedScalarJet i 0 1 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ)))
    nlinarith [mul_nonneg (mul_nonneg hC he0) hAα0, mul_nonneg hC he0,
      mul_nonneg (mul_nonneg hC he0) (abs_nonneg M)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(coefErrA_hasFDerivAt S1 p r y hp hp2 hq).fderiv]
    unfold coefErrADeriv
    refine (norm_coord_comb_le _ _).trans ?_
    have h1 := j10 0
    have h3 : |2 * y 0 * (matchedScalarJet 0 0 1 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ) -
        dynamicAlpha r y / 2)| ≤ 2 * |M| * (C / 2 * e * Aα) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num)) hu (abs_nonneg _)
        (by positivity)
    have h4 := abs_add_le (matchedScalarJet 0 1 0 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ))
      (2 * y 0 * (matchedScalarJet 0 0 1 p r (y 0) (y 0 ^ 2 + y 2) / (p : ℝ) -
        dynamicAlpha r y / 2))
    nlinarith [mul_nonneg (mul_nonneg hC he0) hAα0, mul_nonneg hC he0,
      mul_nonneg (mul_nonneg hC he0) (abs_nonneg M)]
  · rw [(coefErrB_hasFDerivAt S1 p r y hp hp2 hq).fderiv]
    exact hother 1 (by decide)
  · rw [(coefErrD_hasFDerivAt S1 p r y hp hp2 hq).fderiv]
    exact hother 2 (by decide)
  · rw [(coefErrT_hasFDerivAt S1 p r y hp hp2 hq).fderiv]
    exact hother 3 (by decide)

/-- Uniform bound of the clipped jets on a ball of states. -/
theorem matchedScalarJet_clip_bound (r M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 4) (a b : Fin 3) (p : unitInterval) (y : DynamicState),
      0 < (p : ℝ) → (p : ℝ) ≤ 1 / 2 → ‖y‖ ≤ M →
      |matchedScalarJet i a b p r (y 0) (max (y 0 ^ 2 + y 2) 0)| ≤ C * (p : ℝ) := by
  obtain ⟨C, hC, h⟩ := matchedScalarJet_uniform_bound r (M ^ 2 + M)
  refine ⟨C, hC, fun i a b p y hp hp2 hy => ?_⟩
  have hq := clipq_mem y M hy
  exact h i a b p (y 0) _ hp hp2 hq.1 hq.2

/-- `actA` in terms of the clipped jet. -/
theorem actA_eq_clip (p : unitInterval) (r : ℝ) :
    actA p r = fun y => matchedScalarJet 0 0 0 p r (y 0) (max (y 0 ^ 2 + y 2) 0) / (p : ℝ) := by
  funext y
  have : scalarCoefA p r (y 0) (y 0 ^ 2 + y 2) = matchedScalarJet 0 0 0 p r (y 0) (y 0 ^ 2 + y 2) := by
    simp [matchedScalarJet]
  simp only [actA]
  rw [this, matchedScalarJet_clip]

/-- `actB` in terms of the clipped jet. -/
theorem actB_eq_clip (p : unitInterval) (r : ℝ) :
    actB p r = fun y => matchedScalarJet 1 0 0 p r (y 0) (max (y 0 ^ 2 + y 2) 0) / (p : ℝ) := by
  funext y
  have : scalarCoefB p r (y 0) (y 0 ^ 2 + y 2) = matchedScalarJet 1 0 0 p r (y 0) (y 0 ^ 2 + y 2) := by
    simp [matchedScalarJet]
  simp only [actB]
  rw [this, matchedScalarJet_clip]

/-- `actD0` in terms of the clipped jet. -/
theorem actD0_eq_clip (p : unitInterval) (r : ℝ) :
    actD0 p r = fun y => matchedScalarJet 2 0 0 p r (y 0) (max (y 0 ^ 2 + y 2) 0) / (p : ℝ) := by
  funext y
  have : scalarCoefD0 p r (y 0) (y 0 ^ 2 + y 2) = matchedScalarJet 2 0 0 p r (y 0) (y 0 ^ 2 + y 2) := by
    simp [matchedScalarJet]
  simp only [actD0]
  rw [this, matchedScalarJet_clip]

/-- `actDt` in terms of the clipped jet. -/
theorem actDt_eq_clip (p : unitInterval) (r : ℝ) :
    actDt p r = fun y => matchedScalarJet 3 0 0 p r (y 0) (max (y 0 ^ 2 + y 2) 0) / (p : ℝ) := by
  funext y
  have : scalarCoefDtheta p r (y 0) (y 0 ^ 2 + y 2) = matchedScalarJet 3 0 0 p r (y 0) (y 0 ^ 2 + y 2) := by
    simp [matchedScalarJet]
  simp only [actDt]
  rw [this, matchedScalarJet_clip]

/-- Value bounds for the normalized actual coefficients, uniform in `p ∈ (0, 1/2]`
and valid at every state of a ball (including `q ≤ 0`). -/
theorem actCoef_bounded (r M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : unitInterval) (y : DynamicState), 0 < (p : ℝ) → (p : ℝ) ≤ 1 / 2 →
      ‖y‖ ≤ M → |actA p r y| ≤ C ∧ |actB p r y| ≤ C ∧ |actD0 p r y| ≤ C ∧ |actDt p r y| ≤ C := by
  obtain ⟨C, hC, h⟩ := matchedScalarJet_clip_bound r M
  refine ⟨C, hC, fun p y hp hp2 hy => ?_⟩
  have key : ∀ i : Fin 4, |matchedScalarJet i 0 0 p r (y 0) (max (y 0 ^ 2 + y 2) 0) / (p : ℝ)| ≤ C := by
    intro i
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    exact h i 0 0 p y hp hp2 hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [actA_eq_clip]; exact key 0
  · rw [actB_eq_clip]; exact key 1
  · rw [actD0_eq_clip]; exact key 2
  · rw [actDt_eq_clip]; exact key 3

/-- Lipschitz estimate of the clipped normalized jets on a ball, uniformly in `p` and `i`. -/
theorem matchedScalarJet_clip_lipschitz (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (r M : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (i : Fin 4) (p : unitInterval), 0 < (p : ℝ) → (p : ℝ) ≤ 1 / 2 →
      ∀ y y' : DynamicState, ‖y‖ ≤ M → ‖y'‖ ≤ M →
      |matchedScalarJet i 0 0 p r (y 0) (max (y 0 ^ 2 + y 2) 0) / (p : ℝ) -
        matchedScalarJet i 0 0 p r (y' 0) (max (y' 0 ^ 2 + y' 2) 0) / (p : ℝ)| ≤
        L * ‖y - y'‖ := by
  obtain ⟨C, hC, h⟩ := matchedScalarJet_uniform_bound r (M ^ 2 + M)
  refine ⟨C * (2 * |M| + 2), by positivity, fun i p hp hp2 y y' hy hy' => ?_⟩
  have hM : 0 ≤ M := (norm_nonneg y).trans hy
  have hq := clipq_mem y M hy
  have hq' := clipq_mem y' M hy'
  set q := max (y 0 ^ 2 + y 2) 0 with hqdef
  set q' := max (y' 0 ^ 2 + y' 2) 0 with hqdef'
  -- mean value in t
  have hT : |matchedScalarJet i 0 0 p r (y 0) q - matchedScalarJet i 0 0 p r (y' 0) q| ≤
      C * (p : ℝ) * |y 0 - y' 0| := by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t => matchedScalarJet i 0 0 p r t q) (f' := fun t => matchedScalarJet i 1 0 p r t q)
      (s := Set.univ) (C := C * (p : ℝ)) (x := y' 0) (y := y 0)
      (fun t _ => (matchedScalarJet_signal i 0 0 p r t q).hasDerivWithinAt)
      (fun t _ => by
        rw [Real.norm_eq_abs]; exact h i 1 0 p t q hp hp2 hq.1 hq.2)
      convex_univ (Set.mem_univ _) (Set.mem_univ _)
    simpa [Real.norm_eq_abs] using this
  -- mean value in q
  have hQ : |matchedScalarJet i 0 0 p r (y' 0) q - matchedScalarJet i 0 0 p r (y' 0) q'| ≤
      C * (p : ℝ) * |q - q'| := by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => matchedScalarJet i 0 0 p r (y' 0) s) (f' := fun s => matchedScalarJet i 0 1 p r (y' 0) s)
      (s := Set.Icc 0 (M ^ 2 + M)) (C := C * (p : ℝ)) (x := q') (y := q)
      (fun s hs => (matchedScalarJet_variance S1 i 0 0 p r (y' 0) s hs.1).mono
        (fun z hz => hz.1))
      (fun s hs => by
        rw [Real.norm_eq_abs]; exact h i 0 1 p (y' 0) s hp hp2 hs.1 hs.2)
      (convex_Icc _ _) ⟨hq'.1, hq'.2⟩ ⟨hq.1, hq.2⟩
    simpa [Real.norm_eq_abs, abs_sub_comm] using this
  have hqd : |q - q'| ≤ (2 * |M| + 1) * ‖y - y'‖ := by
    have e1 : |q - q'| ≤ |(y 0 ^ 2 + y 2) - (y' 0 ^ 2 + y' 2)| := abs_max_sub_max_le_abs _ _ _
    have d0 : |y 0 - y' 0| ≤ ‖y - y'‖ := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (y - y') 0
    have d2 : |y 2 - y' 2| ≤ ‖y - y'‖ := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (y - y') 2
    have a0 := abs_coord_le_of_norm_le y M hy 0
    have a0' := abs_coord_le_of_norm_le y' M hy' 0
    have e2 : |(y 0 ^ 2 + y 2) - (y' 0 ^ 2 + y' 2)| ≤
        |y 0 - y' 0| * |y 0 + y' 0| + |y 2 - y' 2| := by
      have : (y 0 ^ 2 + y 2) - (y' 0 ^ 2 + y' 2) =
          (y 0 - y' 0) * (y 0 + y' 0) + (y 2 - y' 2) := by ring
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
    have e3 : |y 0 + y' 0| ≤ 2 * |M| := by
      have := abs_add_le (y 0) (y' 0)
      have hMM : M ≤ |M| := le_abs_self M
      linarith
    have e4 : |y 0 - y' 0| * |y 0 + y' 0| ≤ ‖y - y'‖ * (2 * |M|) :=
      mul_le_mul d0 e3 (abs_nonneg _) (norm_nonneg _)
    nlinarith
  have hdiff : |matchedScalarJet i 0 0 p r (y 0) q - matchedScalarJet i 0 0 p r (y' 0) q'| ≤
      (C * (2 * |M| + 2)) * ‖y - y'‖ * (p : ℝ) := by
    have e := abs_sub_le (matchedScalarJet i 0 0 p r (y 0) q)
      (matchedScalarJet i 0 0 p r (y' 0) q) (matchedScalarJet i 0 0 p r (y' 0) q')
    have d0 : |y 0 - y' 0| ≤ ‖y - y'‖ := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (y - y') 0
    have b1 : C * (p : ℝ) * |y 0 - y' 0| ≤ C * (p : ℝ) * ‖y - y'‖ :=
      mul_le_mul_of_nonneg_left d0 (mul_nonneg hC hp.le)
    have b2 : C * (p : ℝ) * |q - q'| ≤ C * (p : ℝ) * ((2 * |M| + 1) * ‖y - y'‖) :=
      mul_le_mul_of_nonneg_left hqd (mul_nonneg hC hp.le)
    nlinarith
  rw [← sub_div, abs_div, abs_of_pos hp, div_le_iff₀ hp]
  exact hdiff

/-- The actual coefficients are Lipschitz on balls, uniformly in `p ∈ (0, 1/2]`, at all states
(the clipping at `q ≤ 0` is built in). -/
theorem actCoef_lipschitzOn (S1 : SparseSGD.External.GaussianSteinCertificate 1) (r M : ℝ) :
    ∃ L : NNReal, ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) ≤ 1 / 2 →
      LipschitzOnWith L (actA p r) (Metric.closedBall 0 M) ∧
      LipschitzOnWith L (actB p r) (Metric.closedBall 0 M) ∧
      LipschitzOnWith L (actD0 p r) (Metric.closedBall 0 M) ∧
      LipschitzOnWith L (actDt p r) (Metric.closedBall 0 M) := by
  obtain ⟨L, hL, h⟩ := matchedScalarJet_clip_lipschitz S1 r M
  refine ⟨L.toNNReal, fun p hp hp2 => ?_⟩
  have key : ∀ i : Fin 4, LipschitzOnWith L.toNNReal
      (fun y : DynamicState => matchedScalarJet i 0 0 p r (y 0) (max (y 0 ^ 2 + y 2) 0) / (p : ℝ))
      (Metric.closedBall 0 M) := by
    intro i
    refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL]
    exact h i p hp hp2 y y' (by simpa using hy) (by simpa using hy')
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [actA_eq_clip]; exact key 0
  · rw [actB_eq_clip]; exact key 1
  · rw [actD0_eq_clip]; exact key 2
  · rw [actDt_eq_clip]; exact key 3

end
end SparseSGD.Logistic.V2
