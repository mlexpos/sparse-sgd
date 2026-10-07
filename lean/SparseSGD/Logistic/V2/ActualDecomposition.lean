import SparseSGD.Logistic.V2.ActualCoefficientDerivs

/-!
# Decomposition of the actual drift map

The actual one-step map is `y + h • (dynamicField r Δ* Φ* y + e(y))`, where `e = AP.err`.
This file bounds `e` and its derivative by `K * varrho`, uniformly over admissible `AP`
with `p` small.

* `coefInc` is the increment with coefficient offsets `(a, b, d0) = (α + s5, -1 + s6, 1 + s7)`,
  smooth in `(y, s)` jointly; `AP.inc r a y = coefInc r y (sAct a y)` and the base field is
  `coefInc r y (sBase Δ* Φ* ρ)`.
* `coefInc_param_bounds`, `coefInc_comp_bounds`: Lipschitz bounds in the parameters and the
  derivative bound for `y ↦ coefInc y (s y) - coefInc y s*`.
* `AP_decomposition_phys` (sup bound), `AP_decomposition_reg` (plus derivative, `q > 0`),
  `AP_decomposition_near` (ball around `y*`, with the Lipschitz bound by convexity).
* `AP_fderiv_le`: `‖D (a.map)‖ ≤ 1 + L h` on balls, without differentiability, via a Lipschitz
  bound for `AP.inc`.
-/

namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic Metric Set
open scoped NNReal
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

/-- Increment with coefficient offsets: `s = (h, δ, κ, ν, ρ, a-α, b+1, d0-1)`. -/
def coefInc (r : ℝ) (y : DynamicState) (s : Fin 8 → ℝ) : DynamicState :=
  dynamicIncrement r (dynamicIncrementData y (s 0) (s 1) (s 2) (dynamicAlpha r y + s 5)
    (-1 + s 6) (1 + s 7) (s 3) (s 4))

/-- Parameter vector of an `AP` at a state. -/
def sAct (r : ℝ) (a : AP) (y : DynamicState) : Fin 8 → ℝ :=
  ![a.h, a.delta, a.kappa, a.w * actDt a.p r y, a.rho, coefErrA a.p r y, coefErrB a.p r y,
    coefErrD a.p r y]

/-- Base parameter vector (`h = 0`, `κ = 2Φ*/Δ*`, `ν = 0`, no coefficient offsets). -/
def sBase (deltaS PhiS rho : ℝ) : Fin 8 → ℝ :=
  ![0, deltaS, 2 * PhiS / deltaS, 0, rho, 0, 0, 0]

/-- `coefInc` is smooth in `(y, s)` jointly. -/
theorem contDiff_coefInc (r : ℝ) :
    ContDiff ℝ ⊤ (fun w : DynamicState × (Fin 8 → ℝ) => coefInc r w.1 w.2) := by
  have hd : ContDiff ℝ ⊤ (fun w : DynamicState × (Fin 8 → ℝ) =>
      dynamicIncrementData w.1 (w.2 0) (w.2 1) (w.2 2) (dynamicAlpha r w.1 + w.2 5)
        (-1 + w.2 6) (1 + w.2 7) (w.2 3) (w.2 4)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp [dynamicIncrementData, dynamicAlpha] <;> fun_prop
  exact (contDiff_dynamicIncrement r).comp hd

/-- The increment of an `AP` is `coefInc` at `sAct`. -/
theorem AP.inc_eq_coefInc (r : ℝ) (a : AP) (y : DynamicState) :
    a.inc r y = coefInc r y (sAct r a y) := by
  have e1 : dynamicAlpha r y + coefErrA a.p r y = actA a.p r y := by simp [coefErrA]
  have e2 : -1 + coefErrB a.p r y = actB a.p r y := by simp [coefErrB]
  have e3 : 1 + coefErrD a.p r y = actD0 a.p r y := by simp [coefErrD]
  simp only [AP.inc, coefInc, sAct]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have h5 : (![a.h, a.delta, a.kappa, a.w * actDt a.p r y, a.rho, coefErrA a.p r y,
      coefErrB a.p r y, coefErrD a.p r y] : Fin 8 → ℝ) 5 = coefErrA a.p r y := rfl
  have h6 : (![a.h, a.delta, a.kappa, a.w * actDt a.p r y, a.rho, coefErrA a.p r y,
      coefErrB a.p r y, coefErrD a.p r y] : Fin 8 → ℝ) 6 = coefErrB a.p r y := rfl
  have h7 : (![a.h, a.delta, a.kappa, a.w * actDt a.p r y, a.rho, coefErrA a.p r y,
      coefErrB a.p r y, coefErrD a.p r y] : Fin 8 → ℝ) 7 = coefErrD a.p r y := rfl
  rw [h5, h6, h7, e1, e2, e3]
  rfl

/-- The base field is `coefInc` at `sBase`, for every `ρ`. -/
theorem dynamicField_eq_coefInc (r deltaS PhiS rho : ℝ) (y : DynamicState) :
    dynamicField r deltaS PhiS y = coefInc r y (sBase deltaS PhiS rho) := by
  rw [← dynamicIncrement_zero_eq_field r deltaS PhiS rho y]
  simp [coefInc, sBase, dynamicIncrementData]

/-- `AP.err` as a difference of two parameter values of `coefInc`. -/
theorem AP.err_eq_coefInc_sub (r deltaS PhiS : ℝ) (a : AP) :
    a.err r deltaS PhiS = fun y => coefInc r y (sAct r a y) - coefInc r y (sBase deltaS PhiS a.rho) := by
  funext y
  rw [AP.err, AP.inc_eq_coefInc, dynamicField_eq_coefInc r deltaS PhiS a.rho]

/-- Uniform Lipschitz dependence of `coefInc` on the parameter vector, and the `C^1` bound of
the difference in the state. -/
theorem coefInc_param_bounds (r M : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : DynamicState) (s s0 : Fin 8 → ℝ),
      ‖y‖ ≤ M → ‖s‖ ≤ M → ‖s0‖ ≤ M →
      ‖coefInc r y s - coefInc r y s0‖ ≤ K * ‖s - s0‖ ∧
      (DifferentiableAt ℝ (fun y' => coefInc r y' s - coefInc r y' s0) y ∧
        ‖fderiv ℝ (fun y' => coefInc r y' s - coefInc r y' s0) y‖ ≤ K * ‖s - s0‖) := by
  set G : DynamicState × (Fin 8 → ℝ) → DynamicState := fun w => coefInc r w.1 w.2 with hG
  have hGs : ContDiff ℝ ⊤ G := contDiff_coefInc r
  obtain ⟨KG, hKG⟩ := hGs.contDiffOn.exists_lipschitzOnWith (s := closedBall 0 M) (by simp)
    (convex_closedBall 0 M) (isCompact_closedBall 0 M)
  have hD : ContDiff ℝ 1 (fderiv ℝ G) := hGs.fderiv_right (by simp)
  obtain ⟨KD, hKD⟩ := hD.contDiffOn.exists_lipschitzOnWith (s := closedBall 0 M) (by simp)
    (convex_closedBall 0 M) (isCompact_closedBall 0 M)
  refine ⟨(KG : ℝ) + KD, by positivity, ?_⟩
  intro y s s0 hy hs hs0
  have hmem : ∀ (u : DynamicState) (t : Fin 8 → ℝ), ‖u‖ ≤ M → ‖t‖ ≤ M →
      (u, t) ∈ closedBall (0 : DynamicState × (Fin 8 → ℝ)) M := by
    intro u t hu ht
    simp only [mem_closedBall, dist_zero_right, Prod.norm_def]
    exact max_le hu ht
  have hnorm : ∀ (u : DynamicState) (t t0 : Fin 8 → ℝ),
      ‖((u, t) : DynamicState × (Fin 8 → ℝ)) - (u, t0)‖ = ‖t - t0‖ := by
    intro u t t0
    simp [Prod.norm_def]
  have hKGn : (0:ℝ) ≤ KG := KG.2
  have hKDn : (0:ℝ) ≤ KD := KD.2
  have hdiff : Differentiable ℝ G := hGs.differentiable (by simp)
  set ι : DynamicState →L[ℝ] DynamicState × (Fin 8 → ℝ) :=
    (ContinuousLinearMap.id ℝ DynamicState).prod 0 with hι
  have hιn : ‖ι‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    simp [hι, Prod.norm_def]
  have hpart : ∀ (u : DynamicState) (t : Fin 8 → ℝ),
      HasFDerivAt (fun y' : DynamicState => G (y', t)) ((fderiv ℝ G (u, t)).comp ι) u := by
    intro u t
    have h1 : HasFDerivAt (fun x : DynamicState => (x, t)) ι u :=
      (hasFDerivAt_id u).prodMk (hasFDerivAt_const t u)
    exact HasFDerivAt.comp u (hdiff (u, t)).hasFDerivAt h1
  have hder : HasFDerivAt (fun y' : DynamicState => G (y', s) - G (y', s0))
        (((fderiv ℝ G (y, s)) - (fderiv ℝ G (y, s0))).comp ι) y := by
    have := (hpart y s).sub (hpart y s0)
    simpa [ContinuousLinearMap.sub_comp] using this
  have hderb : ‖((fderiv ℝ G (y, s)) - (fderiv ℝ G (y, s0))).comp ι‖ ≤
      ((KD : ℝ) * ‖s - s0‖) := by
    have h1 := hKD.norm_sub_le (hmem y s hy hs) (hmem y s0 hy hs0)
    rw [hnorm] at h1
    calc _ ≤ ‖(fderiv ℝ G (y, s)) - (fderiv ℝ G (y, s0))‖ * ‖ι‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖(fderiv ℝ G (y, s)) - (fderiv ℝ G (y, s0))‖ * 1 :=
          mul_le_mul_of_nonneg_left hιn (norm_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact h1
  have hKle : (KD : ℝ) * ‖s - s0‖ ≤ ((KG : ℝ) + KD) * ‖s - s0‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  refine ⟨?_, hder.differentiableAt, ?_⟩
  · have := hKG.norm_sub_le (hmem y s hy hs) (hmem y s0 hy hs0)
    rw [hnorm] at this
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · rw [hder.fderiv]
    exact hderb.trans hKle

/-- Derivative bound for `y ↦ coefInc y (s y) - coefInc y s*` with a differentiable parameter
path `s`: `K (‖s y - s*‖ + ‖D s y‖)`. -/
theorem coefInc_comp_bounds (r M : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : DynamicState) (s : DynamicState → Fin 8 → ℝ) (s0 : Fin 8 → ℝ),
      ‖y‖ ≤ M → ‖s y‖ ≤ M → ‖s0‖ ≤ M → DifferentiableAt ℝ s y →
      DifferentiableAt ℝ (fun y' => coefInc r y' (s y') - coefInc r y' s0) y ∧
      ‖fderiv ℝ (fun y' => coefInc r y' (s y') - coefInc r y' s0) y‖ ≤
        K * (‖s y - s0‖ + ‖fderiv ℝ s y‖) := by
  set G : DynamicState × (Fin 8 → ℝ) → DynamicState := fun w => coefInc r w.1 w.2 with hG
  have hGs : ContDiff ℝ ⊤ G := contDiff_coefInc r
  obtain ⟨KD, hKD⟩ := (hGs.fderiv_right (m := 1) (by simp)).contDiffOn.exists_lipschitzOnWith
    (s := closedBall 0 M) (by simp) (convex_closedBall 0 M) (isCompact_closedBall 0 M)
  have hcont : Continuous (fderiv ℝ G) := (hGs.fderiv_right (m := 1) (by simp)).continuous
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : DynamicState × (Fin 8 → ℝ)) M).exists_bound_of_continuousOn
    hcont.continuousOn
  set B' : ℝ := max B 0 with hB'
  have hB0' : 0 ≤ B' := le_max_right _ _
  have hKDn : (0:ℝ) ≤ KD := KD.2
  refine ⟨(KD : ℝ) + B', by positivity, ?_⟩
  intro y s s0 hy hsy hs0 hsd
  have hmem : ∀ (u : DynamicState) (t : Fin 8 → ℝ), ‖u‖ ≤ M → ‖t‖ ≤ M →
      (u, t) ∈ closedBall (0 : DynamicState × (Fin 8 → ℝ)) M := by
    intro u t hu ht
    simp only [mem_closedBall, dist_zero_right, Prod.norm_def]
    exact max_le hu ht
  have hnorm : ∀ (u : DynamicState) (t t0 : Fin 8 → ℝ),
      ‖((u, t) : DynamicState × (Fin 8 → ℝ)) - (u, t0)‖ = ‖t - t0‖ := by
    intro u t t0
    simp [Prod.norm_def]
  have hdiff : Differentiable ℝ G := hGs.differentiable (by simp)
  set ι : DynamicState →L[ℝ] DynamicState × (Fin 8 → ℝ) :=
    (ContinuousLinearMap.id ℝ DynamicState).prod 0 with hι
  set κ : DynamicState →L[ℝ] DynamicState × (Fin 8 → ℝ) :=
    (0 : DynamicState →L[ℝ] DynamicState).prod (fderiv ℝ s y) with hκ
  have hιn : ‖ι‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    simp [hι, Prod.norm_def]
  have hκn : ‖κ‖ ≤ ‖fderiv ℝ s y‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    simp only [hκ, ContinuousLinearMap.prod_apply, Prod.norm_def, ContinuousLinearMap.zero_apply,
      norm_zero]
    refine max_le (by positivity) (ContinuousLinearMap.le_opNorm _ _)
  have hpart : ∀ (u : DynamicState) (t : Fin 8 → ℝ),
      HasFDerivAt (fun y' : DynamicState => G (y', t)) ((fderiv ℝ G (u, t)).comp ι) u := by
    intro u t
    have h1 : HasFDerivAt (fun x : DynamicState => (x, t)) ι u :=
      (hasFDerivAt_id u).prodMk (hasFDerivAt_const t u)
    exact HasFDerivAt.comp u (hdiff (u, t)).hasFDerivAt h1
  have hs' : HasFDerivAt s (fderiv ℝ s y) y := hsd.hasFDerivAt
  have hpath : HasFDerivAt (fun y' : DynamicState => G (y', s y'))
      ((fderiv ℝ G (y, s y)).comp (ι + κ)) y := by
    have h1 : HasFDerivAt (fun x : DynamicState => (x, s x)) (ι + κ) y := by
      have := (hasFDerivAt_id y).prodMk hs'
      have hιk : ι + κ = (ContinuousLinearMap.id ℝ DynamicState).prod (fderiv ℝ s y) := by
        refine ContinuousLinearMap.ext fun v => Prod.ext ?_ ?_ <;> simp [hι, hκ]
      rw [hιk]
      exact this
    exact HasFDerivAt.comp y (hdiff (y, s y)).hasFDerivAt h1
  have hder : HasFDerivAt (fun y' : DynamicState => G (y', s y') - G (y', s0))
      (((fderiv ℝ G (y, s y)) - (fderiv ℝ G (y, s0))).comp ι +
        (fderiv ℝ G (y, s y)).comp κ) y := by
    have := hpath.sub (hpart y s0)
    have hop : (fderiv ℝ G (y, s y)).comp (ι + κ) - (fderiv ℝ G (y, s0)).comp ι =
        ((fderiv ℝ G (y, s y)) - (fderiv ℝ G (y, s0))).comp ι + (fderiv ℝ G (y, s y)).comp κ := by
      rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.sub_comp]; abel
    rw [← hop]
    exact this
  refine ⟨hder.differentiableAt, ?_⟩
  rw [hder.fderiv]
  have hb1 : ‖((fderiv ℝ G (y, s y)) - (fderiv ℝ G (y, s0))).comp ι‖ ≤ (KD : ℝ) * ‖s y - s0‖ := by
    have h1 := hKD.norm_sub_le (hmem y (s y) hy hsy) (hmem y s0 hy hs0)
    rw [hnorm] at h1
    calc _ ≤ ‖(fderiv ℝ G (y, s y)) - (fderiv ℝ G (y, s0))‖ * ‖ι‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖(fderiv ℝ G (y, s y)) - (fderiv ℝ G (y, s0))‖ * 1 :=
          mul_le_mul_of_nonneg_left hιn (norm_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact h1
  have hb2 : ‖(fderiv ℝ G (y, s y)).comp κ‖ ≤ B' * ‖fderiv ℝ s y‖ := by
    calc _ ≤ ‖fderiv ℝ G (y, s y)‖ * ‖κ‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ B' * ‖fderiv ℝ s y‖ := by
        apply mul_le_mul ((hB _ (hmem y (s y) hy hsy)).trans (le_max_left _ _)) hκn
          (norm_nonneg _) hB0'
  calc _ ≤ ‖((fderiv ℝ G (y, s y)) - (fderiv ℝ G (y, s0))).comp ι‖ +
        ‖(fderiv ℝ G (y, s y)).comp κ‖ := norm_add_le _ _
    _ ≤ (KD : ℝ) * ‖s y - s0‖ + B' * ‖fderiv ℝ s y‖ := add_le_add hb1 hb2
    _ ≤ _ := by
      have := norm_nonneg (s y - s0); have := norm_nonneg (fderiv ℝ s y)
      nlinarith [mul_nonneg hKDn (norm_nonneg (fderiv ℝ s y)),
        mul_nonneg hB0' (norm_nonneg (s y - s0))]

/-- `varrho` is nonnegative. -/
theorem AP.varrho_nonneg (deltaS PhiS : ℝ) (a : AP) : 0 ≤ a.varrho deltaS PhiS := by
  unfold AP.varrho
  have := a.p.property.1
  positivity

/-- `p ≤ varrho`. -/
theorem AP.p_le_varrho (deltaS PhiS : ℝ) (a : AP) : (a.p : ℝ) ≤ a.varrho deltaS PhiS := by
  unfold AP.varrho
  have := abs_nonneg a.h; have := abs_nonneg (a.delta - deltaS)
  have := abs_nonneg (a.Phi - PhiS)
  linarith

/-- `|h| ≤ varrho`. -/
theorem AP.abs_h_le_varrho (deltaS PhiS : ℝ) (a : AP) : |a.h| ≤ a.varrho deltaS PhiS := by
  unfold AP.varrho
  have := abs_nonneg (a.delta - deltaS); have := abs_nonneg (a.Phi - PhiS)
  have := a.p.property.1
  linarith

/-- `|delta - deltaS| ≤ varrho`. -/
theorem AP.abs_delta_le_varrho (deltaS PhiS : ℝ) (a : AP) :
    |a.delta - deltaS| ≤ a.varrho deltaS PhiS := by
  unfold AP.varrho
  have := abs_nonneg a.h; have := abs_nonneg (a.Phi - PhiS)
  have := a.p.property.1
  linarith

/-- `|Phi - PhiS| ≤ varrho`. -/
theorem AP.abs_Phi_le_varrho (deltaS PhiS : ℝ) (a : AP) :
    |a.Phi - PhiS| ≤ a.varrho deltaS PhiS := by
  unfold AP.varrho
  have := abs_nonneg a.h; have := abs_nonneg (a.delta - deltaS)
  have := a.p.property.1
  linarith

/-- Lipschitz bound for `2 Phi / delta` (copy of `kappa_diff` of `V2/RecursionTame.lean`, restated
here so that this file does not import `RecursionTame`). -/
theorem actKappaDiff (deltaS PhiS delta Phi : ℝ) (hd : 0 < deltaS) (hP : 0 ≤ PhiS)
    (hdelta : deltaS / 2 ≤ delta) :
    |2 * Phi / delta - 2 * PhiS / deltaS| ≤
      (4 / deltaS) * |Phi - PhiS| + (4 * PhiS / deltaS ^ 2) * |delta - deltaS| := by
  have hpos : 0 < delta := by linarith
  have e : 2 * Phi / delta - 2 * PhiS / deltaS =
      2 * (Phi - PhiS) * (1 / delta) + 2 * PhiS * (deltaS - delta) * (1 / (delta * deltaS)) := by
    field_simp; ring
  have h1 : |1 / delta| ≤ 2 / deltaS := by
    rw [abs_of_pos (by positivity), div_le_div_iff₀ hpos hd]; linarith
  have h2 : |1 / (delta * deltaS)| ≤ 2 / deltaS ^ 2 := by
    rw [abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [e]
  calc _ ≤ |2 * (Phi - PhiS) * (1 / delta)| + |2 * PhiS * (deltaS - delta) * (1 / (delta * deltaS))| :=
        abs_add_le _ _
    _ ≤ (4 / deltaS) * |Phi - PhiS| + (4 * PhiS / deltaS ^ 2) * |delta - deltaS| := by
      have a1 : |2 * (Phi - PhiS) * (1 / delta)| ≤ (4 / deltaS) * |Phi - PhiS| := by
        rw [abs_mul, abs_mul]
        have : |(2:ℝ)| = 2 := abs_of_pos two_pos
        rw [this]
        calc 2 * |Phi - PhiS| * |1 / delta| ≤ 2 * |Phi - PhiS| * (2 / deltaS) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = _ := by ring
      have a2 : |2 * PhiS * (deltaS - delta) * (1 / (delta * deltaS))| ≤
          (4 * PhiS / deltaS ^ 2) * |delta - deltaS| := by
        rw [abs_mul, abs_mul, abs_mul, abs_sub_comm deltaS delta]
        have : |(2:ℝ)| = 2 := abs_of_pos two_pos
        rw [this, abs_of_nonneg hP]
        calc 2 * PhiS * |delta - deltaS| * |1 / (delta * deltaS)|
            ≤ 2 * PhiS * |delta - deltaS| * (2 / deltaS ^ 2) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = _ := by ring
      linarith

/-- In the admissible tube the temperature `kappa` is nonnegative, bounded, and within
`O(varrho)` of `2 PhiS / deltaS`. -/
theorem AP.kappa_bounds (deltaS PhiS : ℝ) (hd : 0 < deltaS) (hP : 0 ≤ PhiS) (a : AP)
    (ha : a.Adm deltaS PhiS) :
    0 ≤ a.kappa ∧ a.kappa ≤ 2 * PhiS / deltaS + (4 / deltaS + 4 * PhiS / deltaS ^ 2) ∧
    |a.kappa - 2 * PhiS / deltaS| ≤ (4 / deltaS + 4 * PhiS / deltaS ^ 2) * a.varrho deltaS PhiS := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ha
  have hdl : deltaS / 2 ≤ a.delta := by have := (abs_le.1 h1).1; linarith
  have hk := actKappaDiff deltaS PhiS a.delta a.Phi hd hP hdl
  have hkap : a.kappa = 2 * a.Phi / a.delta := rfl
  have hv0 := AP.varrho_nonneg deltaS PhiS a
  have a1 := AP.abs_delta_le_varrho deltaS PhiS a
  have a2 := AP.abs_Phi_le_varrho deltaS PhiS a
  have c1 : 0 ≤ 4 / deltaS := by positivity
  have c2 : 0 ≤ 4 * PhiS / deltaS ^ 2 := by positivity
  have hb : |a.kappa - 2 * PhiS / deltaS| ≤
      (4 / deltaS + 4 * PhiS / deltaS ^ 2) * a.varrho deltaS PhiS := by
    rw [hkap]
    refine hk.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left a1 c2, mul_le_mul_of_nonneg_left a2 c1]
  refine ⟨h5.trans' h4, ?_, hb⟩
  have := (abs_le.1 hb).2
  have hm : (4 / deltaS + 4 * PhiS / deltaS ^ 2) * a.varrho deltaS PhiS ≤
      (4 / deltaS + 4 * PhiS / deltaS ^ 2) :=
    mul_le_of_le_one_right (by positivity) h8
  linarith

/-- Uniform bounds for the parameter vector `sAct r a y`: it is bounded, within `K1 varrho` of the
base vector, the tame error is `≤ 1/2` and `≤ E varrho`, and `w ≤ Kw`. -/
theorem AP_param_bounds (r deltaS PhiS : ℝ) (hr : 0 < r) (hd : 0 < deltaS) (hP : 0 ≤ PhiS)
    (M : ℝ) :
    ∃ Ms K1 E Kw p0 : ℝ, 0 ≤ Ms ∧ 0 ≤ K1 ∧ 0 ≤ E ∧ 0 ≤ Kw ∧ 0 < p0 ∧
      ∀ a : AP, a.Adm deltaS PhiS → (a.p : ℝ) ≤ p0 → ∀ y : DynamicState, ‖y‖ ≤ M → 0 ≤ y 2 →
        ‖sAct r a y‖ ≤ Ms ∧ ‖sBase deltaS PhiS a.rho‖ ≤ Ms ∧
        ‖sAct r a y - sBase deltaS PhiS a.rho‖ ≤ K1 * a.varrho deltaS PhiS ∧
        tameErrorS a.p r (y 0) (y 0 ^ 2 + y 2) ≤ 1 / 2 ∧
        tameErrorS a.p r (y 0) (y 0 ^ 2 + y 2) ≤ E * a.varrho deltaS PhiS ∧
        a.w ≤ Kw := by
  obtain ⟨E, hE0, hE⟩ := tameErrorS_le_mul r M
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 4 / deltaS + 4 * PhiS / deltaS ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨Kk, hKk⟩ : ∃ Kk : ℝ, Kk = 2 * PhiS / deltaS + c := ⟨_, rfl⟩
  have hKk0 : 0 ≤ Kk := by rw [hKk]; positivity
  obtain ⟨Aα, hAα⟩ : ∃ Aα : ℝ, Aα = Real.exp ((M ^ 2 + M - r ^ 2) / 2) := ⟨_, rfl⟩
  have hAα0 : 0 ≤ Aα := by rw [hAα]; positivity
  obtain ⟨Ms, hMs⟩ : ∃ Ms : ℝ, Ms = 3 + 2 * deltaS + 7 * Kk + 3 * Aα := ⟨_, rfl⟩
  have hMs0 : 0 ≤ Ms := by rw [hMs]; positivity
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = 1 + c + 12 * Kk * E + 6 * Aα * E + 8 * E := ⟨_, rfl⟩
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  refine ⟨Ms, K1, E, Kk, 1 / (2 * (E + 1)), hMs0, hK10, hE0, hKk0, by positivity, ?_⟩
  intro a ha hp y hy hy2
  have ha' := ha
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ha'
  have hv0 := AP.varrho_nonneg deltaS PhiS a
  have hpv := AP.p_le_varrho deltaS PhiS a
  have hhv := AP.abs_h_le_varrho deltaS PhiS a
  have hδv := AP.abs_delta_le_varrho deltaS PhiS a
  obtain ⟨hk0, hkK, hkd⟩ := AP.kappa_bounds deltaS PhiS hd hP a ha
  rw [← hc, ← hKk] at hkK
  rw [← hc] at hkd
  have hpp : (0 : ℝ) < a.p := h6
  -- the tame error
  set e := tameErrorS a.p r (y 0) (y 0 ^ 2 + y 2) with he_def
  have he0 : 0 ≤ e := by
    rw [he_def]; unfold tameErrorS; have := a.p.property.1; positivity
  have hy0 := abs_coord_le_of_norm_le y M hy 0
  have hqM : y 0 ^ 2 + y 2 ≤ M ^ 2 + M := (clipq_mem y M hy).2.trans' (le_max_left _ _)
  have heEp : e ≤ E * (a.p : ℝ) := hE a.p (y 0) (y 0 ^ 2 + y 2) hy0 hqM
  have hEp0 : E * (a.p : ℝ) ≤ 1 / 2 := by
    have h1' : E * (a.p : ℝ) ≤ E * (1 / (2 * (E + 1))) := mul_le_mul_of_nonneg_left hp hE0
    have h2' : E * (1 / (2 * (E + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have he_half : e ≤ 1 / 2 := heEp.trans hEp0
  have heEv : e ≤ E * a.varrho deltaS PhiS :=
    heEp.trans (mul_le_mul_of_nonneg_left hpv hE0)
  obtain ⟨hA, hB, hD, hT⟩ := scalar_tame_values r hr a.p y hpp hy2 he_half
  have hα : dynamicAlpha r y ≤ Aα := by
    rw [hAα]; unfold dynamicAlpha; exact Real.exp_le_exp.2 (by linarith)
  have hα0 : 0 < dynamicAlpha r y := Real.exp_pos _
  -- component bounds
  have cA : |coefErrA a.p r y| ≤ 6 * Aα * e := by
    have : |coefErrA a.p r y| ≤ 6 * dynamicAlpha r y * e := hA
    nlinarith [mul_le_mul_of_nonneg_right hα he0]
  have cB : |coefErrB a.p r y| ≤ 2 * e := hB
  have cD : |coefErrD a.p r y| ≤ 6 * e := hD
  have cT : |actDt a.p r y| ≤ 12 * e := hT
  have wT : |a.w * actDt a.p r y| ≤ 12 * Kk * e := by
    rw [abs_mul, abs_of_nonneg h4]
    calc a.w * |actDt a.p r y| ≤ Kk * (12 * e) :=
          mul_le_mul (h5.trans hkK) cT (abs_nonneg _) hKk0
      _ = _ := by ring
  have wT' : |a.w| * |actDt a.p r y| ≤ 12 * Kk * e := by rw [← abs_mul]; exact wT
  have hδ1 : |a.delta| ≤ 2 * deltaS := by
    rw [abs_of_pos (by have := (abs_le.1 h1).1; linarith)]
    have := (abs_le.1 h1).2; linarith
  have hκ1 : |a.kappa| ≤ Kk := by rw [abs_of_nonneg hk0]; exact hkK
  have hh1 : |a.h| ≤ 1 := hhv.trans h8
  have hρ1 : |a.rho| ≤ 1 := by rw [abs_of_nonneg h2]; exact h3
  have he1 : e ≤ 1 := by linarith
  have hKkE : 12 * Kk * e ≤ 6 * Kk := by nlinarith
  have hAe : 6 * Aα * e ≤ 3 * Aα := by nlinarith
  have hΔ2 : |deltaS| = deltaS := abs_of_pos hd
  have hbase : |2 * PhiS / deltaS| ≤ Kk := by
    rw [abs_of_nonneg (by positivity)]; rw [hKk]; linarith
  have hbase' : 2 * |PhiS| / |deltaS| ≤ Kk := by
    rw [abs_of_nonneg hP, hΔ2]; rw [hKk]
    have : 0 ≤ 2 * PhiS / deltaS := by positivity
    linarith
  refine ⟨?_, ?_, ?_, he_half, heEv, h5.trans hkK⟩
  · refine (pi_norm_le_iff_of_nonneg hMs0).2 fun i => ?_
    fin_cases i <;> simp [sAct, Real.norm_eq_abs] <;>
      linarith [abs_nonneg (coefErrA a.p r y)]
  · refine (pi_norm_le_iff_of_nonneg hMs0).2 fun i => ?_
    fin_cases i <;> simp [sBase, Real.norm_eq_abs] <;>
      linarith [abs_nonneg (2 * PhiS / deltaS)]
  · refine (pi_norm_le_iff_of_nonneg (mul_nonneg hK10 hv0)).2 fun i => ?_
    have m1 : 0 ≤ c * a.varrho deltaS PhiS := mul_nonneg hc0 hv0
    have m2 : 0 ≤ Kk * E * a.varrho deltaS PhiS := by positivity
    have m3 : 0 ≤ Aα * E * a.varrho deltaS PhiS := by positivity
    have m4 : 0 ≤ E * a.varrho deltaS PhiS := mul_nonneg hE0 hv0
    have n3 : 12 * Kk * e ≤ 12 * Kk * (E * a.varrho deltaS PhiS) :=
      mul_le_mul_of_nonneg_left heEv (by positivity)
    have n5 : 6 * Aα * e ≤ 6 * Aα * (E * a.varrho deltaS PhiS) :=
      mul_le_mul_of_nonneg_left heEv (by positivity)
    have n6 : 2 * e ≤ 2 * (E * a.varrho deltaS PhiS) := by linarith
    have n7 : 6 * e ≤ 6 * (E * a.varrho deltaS PhiS) := by linarith
    fin_cases i <;> simp [sAct, sBase, Real.norm_eq_abs] <;> rw [hK1] <;>
      linarith [abs_nonneg (coefErrA a.p r y)]

/-- Sup bound of the perturbation `e = AP.err` on physical states of a ball
(`v2 cor:recursion`, decomposition, actual coefficients). -/
theorem AP_decomposition_phys (r deltaS PhiS : ℝ) (hr : 0 < r) (hd : 0 < deltaS) (hP : 0 ≤ PhiS)
    (M : ℝ) :
    ∃ K p0 : ℝ, 0 ≤ K ∧ 0 < p0 ∧ ∀ a : AP, a.Adm deltaS PhiS → (a.p : ℝ) ≤ p0 →
      ∀ y : DynamicState, ‖y‖ ≤ M → 0 ≤ y 2 →
        ‖a.err r deltaS PhiS y‖ ≤ K * a.varrho deltaS PhiS := by
  obtain ⟨Ms, K1, E, Kw, p0, hMs, hK1, hE, hKw, hp0, hPb⟩ :=
    AP_param_bounds r deltaS PhiS hr hd hP M
  obtain ⟨Kc, hKc0, hKc⟩ := coefInc_param_bounds r (max M Ms)
  refine ⟨Kc * K1, p0, by positivity, hp0, ?_⟩
  intro a ha hp y hy hy2
  obtain ⟨b1, b2, b3, -⟩ := hPb a ha hp y hy hy2
  rw [AP.err_eq_coefInc_sub]
  have := (hKc y _ _ (hy.trans (le_max_left _ _)) (b1.trans (le_max_right _ _))
    (b2.trans (le_max_right _ _))).1
  refine this.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left b3 hKc0

/-- Derivative bound of the parameter path `y ↦ sAct r a y` at states with `q > 0`. -/
theorem sAct_deriv_bound (S1 : SparseSGD.External.GaussianSteinCertificate 1) (r : ℝ)
    (hr : 0 < r) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : AP), 0 ≤ a.w → 0 < (a.p : ℝ) → (a.p : ℝ) ≤ 1 / 2 →
      ∀ y : DynamicState, ‖y‖ ≤ M → 0 ≤ y 2 → 0 < y 0 ^ 2 + y 2 →
      tameErrorS a.p r (y 0) (y 0 ^ 2 + y 2) ≤ 1 / 2 →
      DifferentiableAt ℝ (sAct r a) y ∧
      ‖fderiv ℝ (sAct r a) y‖ ≤ C * (1 + a.w) * tameErrorS a.p r (y 0) (y 0 ^ 2 + y 2) := by
  obtain ⟨C, hC, h⟩ := coefErr_deriv_bound S1 r hr M
  refine ⟨C, hC, ?_⟩
  intro a hw hp hp2 y hy hy2 hq he
  obtain ⟨dA, dB, dD, dT⟩ := h a.p y hp hp2 hy hy2 hq he
  set e := tameErrorS a.p r (y 0) (y 0 ^ 2 + y 2) with he_def
  have he0 : 0 ≤ e := by
    rw [he_def]; unfold tameErrorS; have := a.p.property.1; positivity
  have hz : 0 ≤ C * (1 + a.w) * e := by positivity
  have hCe : C * e ≤ C * (1 + a.w) * e := by
    nlinarith [mul_nonneg (mul_nonneg hC he0) hw]
  have hdA := (coefErrA_hasFDerivAt S1 a.p r y hp hp2 hq).differentiableAt
  have hdB := (coefErrB_hasFDerivAt S1 a.p r y hp hp2 hq).differentiableAt
  have hdD := (coefErrD_hasFDerivAt S1 a.p r y hp hp2 hq).differentiableAt
  have hdT := (coefErrT_hasFDerivAt S1 a.p r y hp hp2 hq).differentiableAt
  have hconst : ∀ c : ℝ, (fun _ : DynamicState => c) = fun _ => c := fun _ => rfl
  have hcomp : ∀ i : Fin 8, DifferentiableAt ℝ (fun x => sAct r a x i) y ∧
      ‖fderiv ℝ (fun x => sAct r a x i) y‖ ≤ C * (1 + a.w) * e := by
    intro i
    fin_cases i
    · have : (fun x => sAct r a x ((0 : Fin 8))) = fun _ => a.h := rfl
      refine ⟨?_, ?_⟩ <;> simp [this, hz]
    · have : (fun x => sAct r a x ((1 : Fin 8))) = fun _ => a.delta := rfl
      refine ⟨?_, ?_⟩ <;> simp [this, hz]
    · have : (fun x => sAct r a x ((2 : Fin 8))) = fun _ => a.kappa := rfl
      refine ⟨?_, ?_⟩ <;> simp [this, hz]
    · have hf : (fun x => sAct r a x ((3 : Fin 8))) = fun x => a.w * coefErrT a.p r x := rfl
      refine ⟨?_, ?_⟩
      · simp only [Fin.reduceFinMk, hf]; exact hdT.const_mul _
      · simp only [Fin.reduceFinMk, hf]
        rw [fderiv_const_mul hdT, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
        calc a.w * ‖fderiv ℝ (coefErrT a.p r) y‖ ≤ a.w * (C * e) :=
              mul_le_mul_of_nonneg_left dT hw
          _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hC he0) hw]
    · have : (fun x => sAct r a x ((4 : Fin 8))) = fun _ => a.rho := rfl
      refine ⟨?_, ?_⟩ <;> simp [this, hz]
    · have hf : (fun x => sAct r a x ((5 : Fin 8))) = coefErrA a.p r := rfl
      simp only [Fin.reduceFinMk, hf]
      exact ⟨hdA, dA.trans hCe⟩
    · have hf : (fun x => sAct r a x ((6 : Fin 8))) = coefErrB a.p r := rfl
      simp only [Fin.reduceFinMk, hf]
      exact ⟨hdB, dB.trans hCe⟩
    · have hf : (fun x => sAct r a x ((7 : Fin 8))) = coefErrD a.p r := rfl
      simp only [Fin.reduceFinMk, hf]
      exact ⟨hdD, dD.trans hCe⟩
  have hdiff : DifferentiableAt ℝ (sAct r a) y := differentiableAt_pi.2 fun i => (hcomp i).1
  refine ⟨hdiff, ?_⟩
  have hpi := fderiv_pi (φ := fun i x => sAct r a x i) (x := y) (fun i => (hcomp i).1)
  have hpi' : fderiv ℝ (sAct r a) y =
      ContinuousLinearMap.pi fun i => fderiv ℝ (fun x => sAct r a x i) y := hpi
  rw [hpi']
  refine ContinuousLinearMap.opNorm_le_bound _ hz fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [ContinuousLinearMap.pi_apply]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hcomp i).2 (norm_nonneg _))

/-- Decomposition with derivative: at states with `q > 0` the perturbation `e` is differentiable
with `‖e‖, ‖De‖ ≤ K varrho`. -/
theorem AP_decomposition_reg (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (r deltaS PhiS : ℝ) (hr : 0 < r) (hd : 0 < deltaS) (hP : 0 ≤ PhiS) (M : ℝ) :
    ∃ K p0 : ℝ, 0 ≤ K ∧ 0 < p0 ∧ ∀ a : AP, a.Adm deltaS PhiS → (a.p : ℝ) ≤ p0 →
      ∀ y : DynamicState, ‖y‖ ≤ M → 0 ≤ y 2 → 0 < y 0 ^ 2 + y 2 →
        ‖a.err r deltaS PhiS y‖ ≤ K * a.varrho deltaS PhiS ∧
        DifferentiableAt ℝ (a.err r deltaS PhiS) y ∧
        ‖fderiv ℝ (a.err r deltaS PhiS) y‖ ≤ K * a.varrho deltaS PhiS := by
  obtain ⟨Ms, K1, E, Kw, p0, hMs, hK1, hE, hKw, hp0, hPb⟩ :=
    AP_param_bounds r deltaS PhiS hr hd hP M
  obtain ⟨Kc, hKc0, hKc⟩ := coefInc_param_bounds r (max M Ms)
  obtain ⟨Kc2, hKc20, hKc2⟩ := coefInc_comp_bounds r (max M Ms)
  obtain ⟨Cd, hCd0, hCd⟩ := sAct_deriv_bound S1 r hr M
  refine ⟨Kc * K1 + Kc2 * (K1 + Cd * (1 + Kw) * E), p0, by positivity, hp0, ?_⟩
  intro a ha hp y hy hy2 hq
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hPb a ha hp y hy hy2
  have hv0 := AP.varrho_nonneg deltaS PhiS a
  have hw0 : 0 ≤ a.w := ha.2.2.2.1
  have hpos : 0 < (a.p : ℝ) := ha.2.2.2.2.2.1
  have hp2 : (a.p : ℝ) ≤ 1 / 2 := ha.2.2.2.2.2.2.1
  obtain ⟨hdiff, hDs⟩ := hCd a hw0 hpos hp2 y hy hy2 hq b4
  have hyM : ‖y‖ ≤ max M Ms := hy.trans (le_max_left _ _)
  have hsM : ‖sAct r a y‖ ≤ max M Ms := b1.trans (le_max_right _ _)
  have hs0M : ‖sBase deltaS PhiS a.rho‖ ≤ max M Ms := b2.trans (le_max_right _ _)
  have hfun := AP.err_eq_coefInc_sub r deltaS PhiS a
  obtain ⟨c1, c2⟩ := hKc2 y (sAct r a) (sBase deltaS PhiS a.rho) hyM hsM hs0M hdiff
  have c0 := (hKc y _ _ hyM hsM hs0M).1
  have hDs' : ‖fderiv ℝ (sAct r a) y‖ ≤ Cd * (1 + Kw) * E * a.varrho deltaS PhiS := by
    refine hDs.trans ?_
    have h1 : (1 + a.w) ≤ 1 + Kw := by linarith
    calc Cd * (1 + a.w) * tameErrorS a.p r (y 0) (y 0 ^ 2 + y 2)
        ≤ Cd * (1 + Kw) * (E * a.varrho deltaS PhiS) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hCd0) b5
            (by unfold tameErrorS; have := a.p.property.1; positivity) (by positivity)
      _ = _ := by ring
  rw [hfun]
  refine ⟨?_, c1, ?_⟩
  · refine c0.trans ?_
    calc Kc * ‖sAct r a y - sBase deltaS PhiS a.rho‖ ≤ Kc * (K1 * a.varrho deltaS PhiS) :=
          mul_le_mul_of_nonneg_left b3 hKc0
      _ ≤ _ := by
        nlinarith [mul_nonneg (mul_nonneg hKc20 (by positivity : 0 ≤ K1 + Cd * (1 + Kw) * E)) hv0]
  · refine c2.trans ?_
    calc Kc2 * (‖sAct r a y - sBase deltaS PhiS a.rho‖ + ‖fderiv ℝ (sAct r a) y‖)
        ≤ Kc2 * (K1 * a.varrho deltaS PhiS + Cd * (1 + Kw) * E * a.varrho deltaS PhiS) :=
          mul_le_mul_of_nonneg_left (add_le_add b3 hDs') hKc20
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hKc0 hK1) hv0]

/-- Decomposition near the equilibrium `y* = dynamicCanonicalEquilibrium r deltaS PhiS`
(`PhiS > 0`): on a ball `closedBall y* r0` the perturbation `e` is differentiable, with
`‖e‖, ‖De‖ ≤ K varrho` and `Lip(e) ≤ K varrho`. -/
theorem AP_decomposition_near (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (r deltaS PhiS : ℝ) (hr : 0 < r) (hd : 0 < deltaS) (hP : 0 < PhiS) :
    ∃ K p0 r0 : ℝ, 0 ≤ K ∧ 0 < p0 ∧ 0 < r0 ∧ ∀ a : AP, a.Adm deltaS PhiS →
      (a.p : ℝ) ≤ p0 → ∀ y z : DynamicState,
        ‖y - dynamicCanonicalEquilibrium r deltaS PhiS‖ ≤ r0 →
        ‖z - dynamicCanonicalEquilibrium r deltaS PhiS‖ ≤ r0 →
        ‖a.err r deltaS PhiS y‖ ≤ K * a.varrho deltaS PhiS ∧
        DifferentiableAt ℝ (a.err r deltaS PhiS) y ∧
        ‖fderiv ℝ (a.err r deltaS PhiS) y‖ ≤ K * a.varrho deltaS PhiS ∧
        ‖a.err r deltaS PhiS y - a.err r deltaS PhiS z‖ ≤
          K * a.varrho deltaS PhiS * ‖y - z‖ := by
  set ystar := dynamicCanonicalEquilibrium r deltaS PhiS with hystar
  have hy2 : 0 < ystar 2 := equilibrium_bulk_pos r deltaS PhiS hr hP hd
  obtain ⟨K, p0, hK, hp0, hreg⟩ :=
    AP_decomposition_reg S1 r deltaS PhiS hr hd hP.le (‖ystar‖ + 1)
  refine ⟨K, p0, min 1 (ystar 2 / 2), hK, hp0, lt_min one_pos (by linarith), ?_⟩
  intro a ha hp y z hy hz
  have hr0 : min 1 (ystar 2 / 2) ≤ 1 := min_le_left _ _
  have hr1 : min 1 (ystar 2 / 2) ≤ ystar 2 / 2 := min_le_right _ _
  have hball : ∀ x : DynamicState, ‖x - ystar‖ ≤ min 1 (ystar 2 / 2) →
      ‖x‖ ≤ ‖ystar‖ + 1 ∧ 0 ≤ x 2 ∧ 0 < x 0 ^ 2 + x 2 := by
    intro x hx
    refine ⟨?_, ?_, ?_⟩
    · calc ‖x‖ = ‖(x - ystar) + ystar‖ := by simp
        _ ≤ ‖x - ystar‖ + ‖ystar‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    · have h2 : |x 2 - ystar 2| ≤ ‖x - ystar‖ := by
        simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (x - ystar) 2
      have := (abs_le.1 (h2.trans hx)).1
      linarith
    · have h2 : |x 2 - ystar 2| ≤ ‖x - ystar‖ := by
        simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (x - ystar) 2
      have := (abs_le.1 (h2.trans hx)).1
      nlinarith [sq_nonneg (x 0)]
  have hpt : ∀ x : DynamicState, ‖x - ystar‖ ≤ min 1 (ystar 2 / 2) →
      ‖a.err r deltaS PhiS x‖ ≤ K * a.varrho deltaS PhiS ∧
      DifferentiableAt ℝ (a.err r deltaS PhiS) x ∧
      ‖fderiv ℝ (a.err r deltaS PhiS) x‖ ≤ K * a.varrho deltaS PhiS := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hball x hx
    exact hreg a ha hp x h1 h2 h3
  obtain ⟨b1, b2, b3⟩ := hpt y hy
  refine ⟨b1, b2, b3, ?_⟩
  have hconv : Convex ℝ (closedBall ystar (min 1 (ystar 2 / 2))) := convex_closedBall _ _
  have hmem : ∀ x : DynamicState, ‖x - ystar‖ ≤ min 1 (ystar 2 / 2) →
      x ∈ closedBall ystar (min 1 (ystar 2 / 2)) := fun x hx => by
    rw [mem_closedBall, dist_eq_norm]; exact hx
  exact hconv.norm_image_sub_le_of_norm_fderiv_le (f := a.err r deltaS PhiS)
    (fun x hx => (hpt x (by rw [mem_closedBall, dist_eq_norm] at hx; exact hx)).2.1)
    (fun x hx => (hpt x (by rw [mem_closedBall, dist_eq_norm] at hx; exact hx)).2.2)
    (hmem z hz) (hmem y hy)

/-- Distance of the `data` vector of two states which differ in the coefficients `a, b, d0, nu`
and the state. -/
theorem dynamicIncrementData_sub_norm_le (y y' : DynamicState)
    (h delta kappa a b d0 nu rho a' b' d0' nu' : ℝ) :
    ‖dynamicIncrementData y h delta kappa a b d0 nu rho -
        dynamicIncrementData y' h delta kappa a' b' d0' nu' rho‖ ≤
      ‖y - y'‖ + |a - a'| + |b - b'| + |d0 - d0'| + |nu - nu'| := by
  have hk : ∀ k : Fin 5, |y k - y' k| ≤ ‖y - y'‖ := fun k => by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (y - y') k
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  fin_cases i <;> simp [dynamicIncrementData, Real.norm_eq_abs] <;>
    linarith [hk 0, hk 1, hk 2, hk 3, hk 4, abs_nonneg (a - a'), abs_nonneg (b - b'),
      abs_nonneg (d0 - d0'), abs_nonneg (nu - nu'), abs_nonneg (y 0 - y' 0)]

/-- Size of the `data` vector. -/
theorem dynamicIncrementData_norm_le (y : DynamicState) (h delta kappa a b d0 nu rho : ℝ) :
    ‖dynamicIncrementData y h delta kappa a b d0 nu rho‖ ≤
      ‖y‖ + |h| + |delta| + |kappa| + |a| + |b| + |d0| + |nu| + |rho| := by
  have hk : ∀ k : Fin 5, |y k| ≤ ‖y‖ := fun k => by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm y k
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  fin_cases i <;> simp [dynamicIncrementData, Real.norm_eq_abs] <;>
    linarith [hk 0, hk 1, hk 2, hk 3, hk 4, abs_nonneg h, abs_nonneg delta, abs_nonneg kappa,
      abs_nonneg a, abs_nonneg b, abs_nonneg d0, abs_nonneg nu, abs_nonneg rho, abs_nonneg (y 0)]

/-- `AP.inc` is Lipschitz on balls, uniformly over the admissible tube (no differentiability
and no smallness of `p` beyond `p ≤ 1/2`). -/
theorem AP_inc_lipschitz (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (r deltaS PhiS : ℝ) (hd : 0 < deltaS) (hP : 0 ≤ PhiS) (M : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : AP, a.Adm deltaS PhiS → ∀ y y' : DynamicState, ‖y‖ ≤ M → ‖y'‖ ≤ M →
      ‖a.inc r y - a.inc r y'‖ ≤ L * ‖y - y'‖ := by
  obtain ⟨C, hC, hCb⟩ := actCoef_bounded r M
  obtain ⟨Lc, hLc⟩ := actCoef_lipschitzOn S1 r M
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 4 / deltaS + 4 * PhiS / deltaS ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨Kk, hKk⟩ : ∃ Kk : ℝ, Kk = 2 * PhiS / deltaS + c := ⟨_, rfl⟩
  have hKk0 : 0 ≤ Kk := by rw [hKk]; positivity
  have hM : 0 ≤ M ∨ M < 0 := le_or_gt 0 M
  obtain ⟨Md, hMd⟩ : ∃ Md : ℝ, Md = |M| + 1 + 2 * deltaS + Kk + 3 * C + Kk * C + 1 := ⟨_, rfl⟩
  obtain ⟨KI, hKI⟩ := dynamicIncrement_lipschitz_closedBall r Md
  have hLc0 : (0 : ℝ) ≤ Lc := Lc.2
  have hKI0 : (0 : ℝ) ≤ KI := KI.2
  refine ⟨KI * (1 + 3 * Lc + Kk * Lc), by positivity, ?_⟩
  intro a ha y y' hy hy'
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ha
  have ha' : a.Adm deltaS PhiS := ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  obtain ⟨hk0, hkK, -⟩ := AP.kappa_bounds deltaS PhiS hd hP a ha'
  rw [← hc, ← hKk] at hkK
  have hhv := AP.abs_h_le_varrho deltaS PhiS a
  have hh1 : |a.h| ≤ 1 := hhv.trans h8
  have hδ1 : |a.delta| ≤ 2 * deltaS := by
    rw [abs_of_pos (by have := (abs_le.1 h1).1; linarith)]
    have := (abs_le.1 h1).2; linarith
  have hρ1 : |a.rho| ≤ 1 := by rw [abs_of_nonneg h2]; exact h3
  have hκ1 : |a.kappa| ≤ Kk := by rw [abs_of_nonneg hk0]; exact hkK
  obtain ⟨cA, cB, cD, cT⟩ := hCb a.p y h6 h7 hy
  obtain ⟨cA', cB', cD', cT'⟩ := hCb a.p y' h6 h7 hy'
  have hyb : y ∈ closedBall (0 : DynamicState) M := by simpa using hy
  have hyb' : y' ∈ closedBall (0 : DynamicState) M := by simpa using hy'
  obtain ⟨lA, lB, lD, lT⟩ := hLc a.p h6 h7
  have dA := lA.norm_sub_le hyb hyb'
  have dB := lB.norm_sub_le hyb hyb'
  have dD := lD.norm_sub_le hyb hyb'
  have dT := lT.norm_sub_le hyb hyb'
  simp only [Real.norm_eq_abs] at dA dB dD dT
  have wT : |a.w * actDt a.p r y| ≤ Kk * C := by
    rw [abs_mul, abs_of_nonneg h4]
    exact mul_le_mul (h5.trans hkK) cT (abs_nonneg _) hKk0
  have wT' : |a.w * actDt a.p r y'| ≤ Kk * C := by
    rw [abs_mul, abs_of_nonneg h4]
    exact mul_le_mul (h5.trans hkK) cT' (abs_nonneg _) hKk0
  have wD : |a.w * actDt a.p r y - a.w * actDt a.p r y'| ≤ Kk * (Lc * ‖y - y'‖) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg h4]
    exact mul_le_mul (h5.trans hkK) dT (abs_nonneg _) hKk0
  have hyn : ‖y‖ ≤ |M| := hy.trans (le_abs_self M)
  have hyn' : ‖y'‖ ≤ |M| := hy'.trans (le_abs_self M)
  have hmem : ∀ (x : DynamicState), ‖x‖ ≤ |M| →
      |actA a.p r x| ≤ C → |actB a.p r x| ≤ C → |actD0 a.p r x| ≤ C →
      |a.w * actDt a.p r x| ≤ Kk * C →
      dynamicIncrementData x a.h a.delta a.kappa (actA a.p r x) (actB a.p r x) (actD0 a.p r x)
        (a.w * actDt a.p r x) a.rho ∈ closedBall (0 : Fin 13 → ℝ) Md := by
    intro x hx e1 e2 e3 e4
    rw [mem_closedBall_zero_iff]
    refine (dynamicIncrementData_norm_le _ _ _ _ _ _ _ _ _).trans ?_
    rw [hMd]
    linarith [abs_nonneg (actA a.p r x)]
  have hm1 := hmem y hyn cA cB cD wT
  have hm2 := hmem y' hyn' cA' cB' cD' wT'
  have hL := hKI.norm_sub_le hm1 hm2
  have hdat := dynamicIncrementData_sub_norm_le y y' a.h a.delta a.kappa (actA a.p r y)
    (actB a.p r y) (actD0 a.p r y) (a.w * actDt a.p r y) a.rho (actA a.p r y') (actB a.p r y')
    (actD0 a.p r y') (a.w * actDt a.p r y')
  have hn := norm_nonneg (y - y')
  have hfin : ‖dynamicIncrementData y a.h a.delta a.kappa (actA a.p r y) (actB a.p r y)
      (actD0 a.p r y) (a.w * actDt a.p r y) a.rho -
      dynamicIncrementData y' a.h a.delta a.kappa (actA a.p r y') (actB a.p r y')
        (actD0 a.p r y') (a.w * actDt a.p r y') a.rho‖ ≤ (1 + 3 * Lc + Kk * Lc) * ‖y - y'‖ := by
    refine hdat.trans ?_
    nlinarith [mul_nonneg hLc0 hn, mul_nonneg hKk0 (mul_nonneg hLc0 hn)]
  have hinc : a.inc r y - a.inc r y' =
      dynamicIncrement r (dynamicIncrementData y a.h a.delta a.kappa (actA a.p r y)
        (actB a.p r y) (actD0 a.p r y) (a.w * actDt a.p r y) a.rho) -
      dynamicIncrement r (dynamicIncrementData y' a.h a.delta a.kappa (actA a.p r y')
        (actB a.p r y') (actD0 a.p r y') (a.w * actDt a.p r y') a.rho) := rfl
  rw [hinc]
  refine hL.trans ?_
  refine (mul_le_mul_of_nonneg_left hfin hKI0).trans (le_of_eq ?_)
  ring

/-- Jacobian bound of the actual map on balls, uniformly over admissible parameters with
`h ≥ 0`: `‖D (a.map)(z)‖ ≤ 1 + L h`.  Needs no differentiability: it follows from the Lipschitz
bound of `AP.inc` (`norm_fderiv_le_of_lipschitzOn`). -/
theorem AP_fderiv_le (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (r deltaS PhiS : ℝ) (hr : 0 < r) (hd : 0 < deltaS) (hP : 0 ≤ PhiS) (M : ℝ) :
    ∃ L p0 : ℝ, 0 ≤ L ∧ 0 < p0 ∧ ∀ a : AP, a.Adm deltaS PhiS → 0 ≤ a.h → (a.p : ℝ) ≤ p0 →
      ∀ z : DynamicState, ‖z‖ ≤ M → ‖fderiv ℝ (a.map r) z‖ ≤ 1 + L * a.h := by
  obtain ⟨L, hL0, hL⟩ := AP_inc_lipschitz S1 r deltaS PhiS hd hP (M + 1)
  refine ⟨L, 1, hL0, one_pos, ?_⟩
  intro a ha hh _ z hz
  have hnn : 0 ≤ 1 + L * a.h := by positivity
  have hlip : LipschitzOnWith (1 + L * a.h).toNNReal (a.map r) (closedBall (0 : DynamicState) (M + 1)) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
    rw [Real.coe_toNNReal _ hnn, dist_eq_norm, dist_eq_norm]
    have hy1 : ‖y‖ ≤ M + 1 := by simpa using hy
    have hy1' : ‖y'‖ ≤ M + 1 := by simpa using hy'
    have h1 := hL a ha y y' hy1 hy1'
    have e : a.map r y - a.map r y' = (y - y') + a.h • (a.inc r y - a.inc r y') := by
      simp only [AP.map, smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    nlinarith [mul_le_mul_of_nonneg_left h1 hh, norm_nonneg (y - y')]
  have hnhds : closedBall (0 : DynamicState) (M + 1) ∈ nhds z := by
    refine Metric.mem_nhds_iff.2 ⟨1, one_pos, fun x hx => ?_⟩
    rw [mem_closedBall_zero_iff]
    have hx' : ‖x - z‖ < 1 := by simpa [dist_eq_norm] using hx
    calc ‖x‖ = ‖(x - z) + z‖ := by simp
      _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ M + 1 := by linarith
  have := norm_fderiv_le_of_lipschitzOn ℝ hnhds hlip
  rwa [Real.coe_toNNReal _ hnn] at this

end
end SparseSGD.Logistic.V2
