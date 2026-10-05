import SparseSGD.Logistic.V2.RecursionContraction
import SparseSGD.Logistic.V2.LyapunovCertificate
import SparseSGD.Logistic.V2.Hurwitz
import SparseSGD.Logistic.V2.GlobalConvergence
import SparseSGD.Logistic.DynamicConsistency
import SparseSGD.Logistic.DynamicConvergence

/-!
# v2 `cor:recursion` for the tame drift recursion (instantiation)

Instantiates the abstract `drift_recursion_converges` and `jacobian_products` of
`V2/RecursionContraction.lean` for the tame one-step map `tameDriftMap`
(`dynamicCoefficientStep` with the tame coefficients of `lem:B`: `a = alpha(y)`, `b = -1`,
`d0 = 1`; `dynamicCoefficientStep_eq_increment`), against the base field
`dynamicField r deltaS PhiS` with equilibrium `dynamicCanonicalEquilibrium`.

* `tameDriftMap_decomposition` (v2 `cor:recursion`, decomposition): `Psi = y + h (f + e)`,
  `‖e‖, ‖De‖, Lip(e) <= K varrho` on balls, uniformly over the tube (`TP.Adm`).
* `tameDriftMap_tracking` (v2 `prop:LR34`, finite horizon): tracking and one-step consistency.
* `tame_family`: the conclusion of `cor:recursion` along a one-parameter family `ε ↦ F ε`.
* `cor_recursion_tame` (v2 `cor:recursion`): uniform constants over the whole tube
  (`uniformize` turns the family statement into a uniform one by contradiction).

The uniform-entry hypothesis `hentry` is kept as a hypothesis (it is discharged by
`dynamicField_uniformEntry`).  The Lyapunov certificate comes from `prop_S_ii` and
`exists_lyapunov_certificate`.  Out of scope: the actual Gaussian-coefficient recursion of
`prop:LR34`, which is non-autonomous through `theta ∈ R^d`.
-/

namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic Metric Set
open scoped NNReal Matrix
noncomputable section
set_option maxHeartbeats 1800000

/-- One-step map of the tame drift recursion (v2 `cor:recursion`, tame coefficients of `lem:B`:
`a = alpha(y)`, `b = -1`, `d0 = 1`), with the noise load `kappa = 2 Phi / delta`. -/
def tameDriftMap (r h delta Phi nu rho : ℝ) (y : DynamicState) : DynamicState :=
  y + h • dynamicIncrement r
    (dynamicIncrementData y h delta (2 * Phi / delta) (dynamicAlpha r y) (-1) 1 nu rho)

/-- The increment as a function of the state and the parameter vector
`s = (h, delta, kappa, nu, rho)`, with the tame coefficients. -/
def tameInc (r : ℝ) (y : DynamicState) (s : Fin 5 → ℝ) : DynamicState :=
  dynamicIncrement r
    (dynamicIncrementData y (s 0) (s 1) (s 2) (dynamicAlpha r y) (-1) 1 (s 3) (s 4))

/-- Parameter vector of `tameDriftMap`. -/
def tameParam (h delta Phi nu rho : ℝ) : Fin 5 → ℝ := ![h, delta, 2 * Phi / delta, nu, rho]

theorem tameDriftMap_eq (r h delta Phi nu rho : ℝ) (y : DynamicState) :
    tameDriftMap r h delta Phi nu rho y = y + h • tameInc r y (tameParam h delta Phi nu rho) := by
  simp [tameDriftMap, tameInc, tameParam, dynamicIncrementData]

/-- The perturbation `e` of `tameDriftMap = y + h (f + e)`. -/
def tameErr (r deltaS PhiS h delta Phi nu rho : ℝ) (y : DynamicState) : DynamicState :=
  tameInc r y (tameParam h delta Phi nu rho) - dynamicField r deltaS PhiS y

/-- v2 `cor:recursion`, decomposition: `Psi = y + h (f + e)` exactly. -/
theorem tameDriftMap_decomposition_eq (r deltaS PhiS h delta Phi nu rho : ℝ) (y : DynamicState) :
    tameDriftMap r h delta Phi nu rho y =
      y + h • (dynamicField r deltaS PhiS y + tameErr r deltaS PhiS h delta Phi nu rho y) := by
  rw [tameDriftMap_eq, tameErr]; congr 2; abel

/-- At `h = 0`, `kappa = 2 PhiS/deltaS`, `nu = 0` the tame increment is the base field
(`dynamicIncrement_zero_eq_field`). -/
theorem tameInc_base (r deltaS PhiS rho : ℝ) (y : DynamicState) :
    tameInc r y (tameParam 0 deltaS PhiS 0 rho) = dynamicField r deltaS PhiS y := by
  rw [← dynamicIncrement_zero_eq_field r deltaS PhiS rho y]
  simp [tameInc, tameParam, dynamicIncrementData]

/-- `e` as a difference of two parameter values of the increment. -/
theorem tameErr_eq_sub (r deltaS PhiS h delta Phi nu rho : ℝ) (y : DynamicState) :
    tameErr r deltaS PhiS h delta Phi nu rho y =
      tameInc r y (tameParam h delta Phi nu rho) - tameInc r y (tameParam 0 deltaS PhiS 0 rho) := by
  rw [tameErr, tameInc_base]

/-- The increment is smooth in `(y, s)` jointly. -/
theorem contDiff_tameInc (r : ℝ) :
    ContDiff ℝ ⊤ (fun w : DynamicState × (Fin 5 → ℝ) => tameInc r w.1 w.2) := by
  have hd : ContDiff ℝ ⊤ (fun w : DynamicState × (Fin 5 → ℝ) =>
      dynamicIncrementData w.1 (w.2 0) (w.2 1) (w.2 2) (dynamicAlpha r w.1) (-1) 1 (w.2 3)
        (w.2 4)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp [dynamicIncrementData, dynamicAlpha] <;> fun_prop
  exact (contDiff_dynamicIncrement r).comp hd


/-- Uniform smooth dependence of the tame increment on the parameter vector, in `C^0` and `C^1`
in the state: on a ball, `s ↦ tameInc r y s` is Lipschitz, and the difference of two parameter
values is Lipschitz and has small derivative in `y`.  (Mean value inequality in the parameter
variables, `C^2` smoothness of the increment.) -/
theorem tameInc_param_bounds (r M : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (y z : DynamicState) (s s0 : Fin 5 → ℝ),
      ‖y‖ ≤ M → ‖z‖ ≤ M → ‖s‖ ≤ M → ‖s0‖ ≤ M →
      ‖tameInc r y s - tameInc r y s0‖ ≤ K * ‖s - s0‖ ∧
      (DifferentiableAt ℝ (fun y' => tameInc r y' s - tameInc r y' s0) y ∧
        ‖fderiv ℝ (fun y' => tameInc r y' s - tameInc r y' s0) y‖ ≤ K * ‖s - s0‖) ∧
      ‖(tameInc r y s - tameInc r y s0) - (tameInc r z s - tameInc r z s0)‖ ≤
        K * ‖s - s0‖ * ‖y - z‖ := by
  set G : DynamicState × (Fin 5 → ℝ) → DynamicState := fun w => tameInc r w.1 w.2 with hG
  have hGs : ContDiff ℝ ⊤ G := contDiff_tameInc r
  obtain ⟨KG, hKG⟩ := hGs.contDiffOn.exists_lipschitzOnWith (s := closedBall 0 M) (by simp)
    (convex_closedBall 0 M) (isCompact_closedBall 0 M)
  have hD : ContDiff ℝ 1 (fderiv ℝ G) := hGs.fderiv_right (by simp)
  obtain ⟨KD, hKD⟩ := hD.contDiffOn.exists_lipschitzOnWith (s := closedBall 0 M) (by simp)
    (convex_closedBall 0 M) (isCompact_closedBall 0 M)
  refine ⟨(KG : ℝ) + KD, by positivity, ?_⟩
  intro y z s s0 hy hz hs hs0
  have hmem : ∀ (u : DynamicState) (t : Fin 5 → ℝ), ‖u‖ ≤ M → ‖t‖ ≤ M →
      (u, t) ∈ closedBall (0 : DynamicState × (Fin 5 → ℝ)) M := by
    intro u t hu ht
    simp only [mem_closedBall, dist_zero_right, Prod.norm_def]
    exact max_le hu ht
  have hnorm : ∀ (u : DynamicState) (t t0 : Fin 5 → ℝ), ‖((u, t) : DynamicState × (Fin 5 → ℝ)) - (u, t0)‖ = ‖t - t0‖ := by
    intro u t t0
    simp [Prod.norm_def]
  have hKGn : (0:ℝ) ≤ KG := KG.2
  have hKDn : (0:ℝ) ≤ KD := KD.2
  have hdiff : Differentiable ℝ G := hGs.differentiable (by simp)
  set ι : DynamicState →L[ℝ] DynamicState × (Fin 5 → ℝ) :=
    (ContinuousLinearMap.id ℝ DynamicState).prod 0 with hι
  have hιn : ‖ι‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    simp [hι, Prod.norm_def]
  have hpart : ∀ (u : DynamicState) (t : Fin 5 → ℝ),
      HasFDerivAt (fun y' : DynamicState => G (y', t)) ((fderiv ℝ G (u, t)).comp ι) u := by
    intro u t
    have h1 : HasFDerivAt (fun x : DynamicState => (x, t)) ι u :=
      (hasFDerivAt_id u).prodMk (hasFDerivAt_const t u)
    exact HasFDerivAt.comp u (hdiff (u, t)).hasFDerivAt h1
  have hder : ∀ u : DynamicState, ‖u‖ ≤ M →
      HasFDerivAt (fun y' : DynamicState => G (y', s) - G (y', s0))
        (((fderiv ℝ G (u, s)) - (fderiv ℝ G (u, s0))).comp ι) u := by
    intro u _
    have := (hpart u s).sub (hpart u s0)
    simpa [ContinuousLinearMap.sub_comp] using this
  have hderb : ∀ u : DynamicState, ‖u‖ ≤ M →
      ‖((fderiv ℝ G (u, s)) - (fderiv ℝ G (u, s0))).comp ι‖ ≤ ((KD : ℝ) * ‖s - s0‖) := by
    intro u hu
    have h1 := hKD.norm_sub_le (hmem u s hu hs) (hmem u s0 hu hs0)
    rw [hnorm] at h1
    calc _ ≤ ‖(fderiv ℝ G (u, s)) - (fderiv ℝ G (u, s0))‖ * ‖ι‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖(fderiv ℝ G (u, s)) - (fderiv ℝ G (u, s0))‖ * 1 :=
          mul_le_mul_of_nonneg_left hιn (norm_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact h1
  have hKle : (KD : ℝ) * ‖s - s0‖ ≤ ((KG : ℝ) + KD) * ‖s - s0‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  refine ⟨?_, ⟨(hder y hy).differentiableAt, ?_⟩, ?_⟩
  · have := hKG.norm_sub_le (hmem y s hy hs) (hmem y s0 hy hs0)
    rw [hnorm] at this
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · rw [(hder y hy).fderiv]
    exact (hderb y hy).trans hKle
  · have hmv := (convex_closedBall (0 : DynamicState) M).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun y' : DynamicState => G (y', s) - G (y', s0))
      (f' := fun u => ((fderiv ℝ G (u, s)) - (fderiv ℝ G (u, s0))).comp ι)
      (C := (KD : ℝ) * ‖s - s0‖)
      (fun u hu => (hder u (by simpa using hu)).hasFDerivWithinAt)
      (fun u hu => hderb u (by simpa using hu))
      (by simpa using hz) (by simpa using hy)
    simp only [hG] at hmv
    refine hmv.trans ?_
    have := mul_le_mul_of_nonneg_right hKle (norm_nonneg (y - z))
    exact this


/-- Parameters of the tame drift recursion. -/
structure TP where
  h : ℝ
  delta : ℝ
  Phi : ℝ
  nu : ℝ
  rho : ℝ

/-- `varrho = |h| + |delta - deltaS| + |Phi - PhiS| + |nu|` (v2 `cor:recursion`). -/
def TP.varrho (deltaS PhiS : ℝ) (p : TP) : ℝ :=
  |p.h| + |p.delta - deltaS| + |p.Phi - PhiS| + |p.nu|

/-- The admissible parameter tube: `|delta - deltaS| <= deltaS/2`, `rho in [0,1]`,
`varrho <= 1`. -/
def TP.Adm (deltaS PhiS : ℝ) (p : TP) : Prop :=
  |p.delta - deltaS| ≤ deltaS / 2 ∧ 0 ≤ p.rho ∧ p.rho ≤ 1 ∧ p.varrho deltaS PhiS ≤ 1

theorem TP.varrho_nonneg (deltaS PhiS : ℝ) (p : TP) : 0 ≤ p.varrho deltaS PhiS := by
  unfold TP.varrho; positivity

/-- The map `tameDriftMap` of a parameter tuple. -/
def TP.map (r : ℝ) (p : TP) : DynamicState → DynamicState :=
  tameDriftMap r p.h p.delta p.Phi p.nu p.rho

/-- The perturbation `e` of a parameter tuple. -/
def TP.err (r deltaS PhiS : ℝ) (p : TP) : DynamicState → DynamicState :=
  tameErr r deltaS PhiS p.h p.delta p.Phi p.nu p.rho

theorem TP.map_eq (r deltaS PhiS : ℝ) (p : TP) (y : DynamicState) :
    p.map r y = y + p.h • (dynamicField r deltaS PhiS y + p.err r deltaS PhiS y) :=
  tameDriftMap_decomposition_eq r deltaS PhiS p.h p.delta p.Phi p.nu p.rho y

theorem kappa_diff (deltaS PhiS delta Phi : ℝ) (hd : 0 < deltaS) (hP : 0 ≤ PhiS)
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

/-- Size of the parameter vector in the tube. -/
theorem tameParam_norm_le (deltaS PhiS : ℝ) (hd : 0 < deltaS) (hP : 0 ≤ PhiS) (p : TP)
    (hp : p.Adm deltaS PhiS) :
    ‖tameParam p.h p.delta p.Phi p.nu p.rho‖ ≤ 1 + 2 * deltaS + 4 * (PhiS + 1) / deltaS ∧
    ‖tameParam 0 deltaS PhiS 0 p.rho‖ ≤ 1 + 2 * deltaS + 4 * (PhiS + 1) / deltaS := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hv : |p.h| ≤ 1 ∧ |p.Phi - PhiS| ≤ 1 ∧ |p.nu| ≤ 1 := by
    unfold TP.varrho at h4
    have := abs_nonneg p.h; have := abs_nonneg (p.delta - deltaS)
    have := abs_nonneg (p.Phi - PhiS); have := abs_nonneg p.nu
    refine ⟨by linarith, by linarith, by linarith⟩
  have hdl : deltaS / 2 ≤ p.delta := by
    have := (abs_le.1 h1).1; linarith
  have hdu : p.delta ≤ 3 * deltaS / 2 := by
    have := (abs_le.1 h1).2; linarith
  have hq : 0 ≤ 4 * (PhiS + 1) / deltaS := by positivity
  have hq1 : 0 ≤ 1 + 2 * deltaS := by linarith
  constructor
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    fin_cases i <;> simp [tameParam, Real.norm_eq_abs]
    · linarith [hv.1]
    · rw [abs_of_pos (by linarith)]; linarith
    · have hPh : |p.Phi| ≤ PhiS + 1 := by
        have := abs_sub_abs_le_abs_sub p.Phi PhiS
        rw [abs_of_nonneg hP] at this; linarith [hv.2.1]
      have : 2 * |p.Phi| / |p.delta| ≤ 4 * (PhiS + 1) / deltaS := by
        rw [abs_of_pos (by linarith : 0 < p.delta), div_le_div_iff₀ (by linarith) hd]
        nlinarith [abs_nonneg p.Phi]
      linarith
    · linarith [hv.2.2]
    · rw [abs_of_nonneg h2]; linarith
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    fin_cases i <;> simp [tameParam, Real.norm_eq_abs]
    · linarith
    · rw [abs_of_pos hd]; linarith
    · have : 2 * |PhiS| / |deltaS| ≤ 4 * (PhiS + 1) / deltaS := by
        rw [abs_of_nonneg hP, abs_of_pos hd]
        apply div_le_div_of_nonneg_right _ hd.le; linarith
      linarith
    · linarith
    · rw [abs_of_nonneg h2]; linarith

/-- Distance of the parameter vector to the base one is `O(varrho)`. -/
theorem tameParam_sub_norm_le (deltaS PhiS : ℝ) (hd : 0 < deltaS) (hP : 0 ≤ PhiS) (p : TP)
    (hp : p.Adm deltaS PhiS) :
    ‖tameParam p.h p.delta p.Phi p.nu p.rho - tameParam 0 deltaS PhiS 0 p.rho‖ ≤
      (1 + 4 / deltaS + 4 * PhiS / deltaS ^ 2) * p.varrho deltaS PhiS := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hdl : deltaS / 2 ≤ p.delta := by
    have := (abs_le.1 h1).1; linarith
  have hk := kappa_diff deltaS PhiS p.delta p.Phi hd hP hdl
  have a0 := abs_nonneg p.h; have a1 := abs_nonneg (p.delta - deltaS)
  have a2 := abs_nonneg (p.Phi - PhiS); have a3 := abs_nonneg p.nu
  have c1 : 0 ≤ 4 / deltaS := by positivity
  have c2 : 0 ≤ 4 * PhiS / deltaS ^ 2 := by positivity
  have hv : p.varrho deltaS PhiS = |p.h| + |p.delta - deltaS| + |p.Phi - PhiS| + |p.nu| := rfl
  have hvn := TP.varrho_nonneg deltaS PhiS p
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) hvn)).2 fun i => ?_
  fin_cases i <;> simp [tameParam, Real.norm_eq_abs]
  all_goals nlinarith [mul_nonneg c1 a2, mul_nonneg c2 a1, mul_nonneg c1 a0, mul_nonneg c2 a0,
        mul_nonneg c1 a1, mul_nonneg c2 a2, mul_nonneg c1 a3, mul_nonneg c2 a3]


/-- v2 `cor:recursion`, decomposition `Psi = y + h (f + e)` with `e` of size `varrho`:
on every ball `closedBall 0 M`, uniformly over the tube `|delta - deltaS| <= deltaS/2`,
`rho in [0,1]`, `varrho <= 1`, the perturbation satisfies `‖e‖ <= K varrho`,
`‖D e‖ <= K varrho` and `Lip(e) <= K varrho`. -/
theorem tameDriftMap_decomposition (r deltaS PhiS : ℝ) (hd : 0 < deltaS) (hP : 0 ≤ PhiS)
    (M : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : TP, p.Adm deltaS PhiS →
      (∀ y : DynamicState, p.map r y =
        y + p.h • (dynamicField r deltaS PhiS y + p.err r deltaS PhiS y)) ∧
      ∀ y z : DynamicState, ‖y‖ ≤ M → ‖z‖ ≤ M →
        ‖p.err r deltaS PhiS y‖ ≤ K * p.varrho deltaS PhiS ∧
        (DifferentiableAt ℝ (p.err r deltaS PhiS) y ∧
          ‖fderiv ℝ (p.err r deltaS PhiS) y‖ ≤ K * p.varrho deltaS PhiS) ∧
        ‖p.err r deltaS PhiS y - p.err r deltaS PhiS z‖ ≤
          K * p.varrho deltaS PhiS * ‖y - z‖ := by
  set Ms : ℝ := 1 + 2 * deltaS + 4 * (PhiS + 1) / deltaS with hMs
  have hMs0 : 0 ≤ Ms := by positivity
  obtain ⟨K0, hK0, hK⟩ := tameInc_param_bounds r (max M Ms)
  set K2 : ℝ := 1 + 4 / deltaS + 4 * PhiS / deltaS ^ 2 with hK2
  have hK2' : 0 ≤ K2 := by positivity
  refine ⟨K0 * K2, by positivity, fun p hp => ⟨fun y => tameDriftMap_decomposition_eq _ _ _ _ _ _ _ _ y, ?_⟩⟩
  intro y z hy hz
  obtain ⟨hs1, hs2⟩ := tameParam_norm_le deltaS PhiS hd hP p hp
  have hsub := tameParam_sub_norm_le deltaS PhiS hd hP p hp
  have hfun : p.err r deltaS PhiS = fun y' => tameInc r y' (tameParam p.h p.delta p.Phi p.nu p.rho) -
      tameInc r y' (tameParam 0 deltaS PhiS 0 p.rho) := by
    funext y'; exact tameErr_eq_sub _ _ _ _ _ _ _ _ y'
  have hyM : ‖y‖ ≤ max M Ms := hy.trans (le_max_left _ _)
  have hzM : ‖z‖ ≤ max M Ms := hz.trans (le_max_left _ _)
  obtain ⟨b1, ⟨b2, b3⟩, b4⟩ := hK y z _ _ hyM hzM (hs1.trans (le_max_right _ _))
    (hs2.trans (le_max_right _ _))
  rw [hfun]
  have hv := TP.varrho_nonneg deltaS PhiS p
  have hN : K0 * ‖tameParam p.h p.delta p.Phi p.nu p.rho - tameParam 0 deltaS PhiS 0 p.rho‖ ≤
      K0 * K2 * p.varrho deltaS PhiS := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hsub hK0
  refine ⟨?_, ⟨b2, ?_⟩, ?_⟩
  · beta_reduce
    exact b1.trans hN
  · exact b3.trans hN
  · refine b4.trans ?_
    exact mul_le_mul_of_nonneg_right hN (norm_nonneg _)


theorem TP.h_le_varrho (deltaS PhiS : ℝ) (p : TP) (hh : 0 ≤ p.h) : p.h ≤ p.varrho deltaS PhiS := by
  unfold TP.varrho
  have := abs_nonneg (p.delta - deltaS); have := abs_nonneg (p.Phi - PhiS); have := abs_nonneg p.nu
  rw [abs_of_nonneg hh]; linarith

/-- One orbit step from `x`: `x + h (f x + e x)`; the residual against the Euler step is `h e`. -/
theorem tame_step_residual (r deltaS PhiS : ℝ) (p : TP) (x : DynamicState) :
    p.map r x - (x + p.h • dynamicField r deltaS PhiS x) = p.h • p.err r deltaS PhiS x := by
  have := tameDriftMap_decomposition_eq r deltaS PhiS p.h p.delta p.Phi p.nu p.rho x
  change tameDriftMap r p.h p.delta p.Phi p.nu p.rho x - _ = p.h • tameErr r deltaS PhiS p.h p.delta p.Phi p.nu p.rho x
  rw [this, smul_add]; abel

/-- v2 `cor:recursion` (finite-horizon tracking, `prop:LR34`): for solutions of the tame field
which stay in the ball `M0` on `[0,T]`, the orbit of `tameDriftMap` stays within `CT varrho` of the
solution at the grid times `k h <= T`, uniformly in the tube and `varrho <= varrhoT`.  The proof is
`dynamic_grid_error_of_local_residual` with the local residual `h ‖e‖ <= h K varrho`
(here the coefficient errors `|a - alpha|`, `|b+1|`, `|d0-1|` vanish). -/
theorem tameDriftMap_tracking_of_bound (r deltaS PhiS : ℝ) (hd : 0 < deltaS) (hP : 0 ≤ PhiS)
    (T M0 : ℝ) (hT : 0 ≤ T) :
    ∃ CT vT : ℝ, 0 < CT ∧ 0 < vT ∧ ∀ p : TP, p.Adm deltaS PhiS → 0 ≤ p.h →
      p.varrho deltaS PhiS ≤ vT → ∀ (y0 : DynamicState) (y : ℝ → DynamicState),
      IsODESol (dynamicField r deltaS PhiS) y0 y → (∀ t ∈ Set.Icc 0 T, ‖y t‖ ≤ M0) →
      ∀ k : ℕ, (k : ℝ) * p.h ≤ T →
        ‖(p.map r)^[k] y0 - y ((k : ℝ) * p.h)‖ ≤ CT * p.varrho deltaS PhiS ∧
        ‖(p.map r)^[k] y0 - y ((k : ℝ) * p.h)‖ ≤ 1 := by
  obtain ⟨K, hK0, hK⟩ := tameDriftMap_decomposition r deltaS PhiS hd hP (M0 + 1)
  obtain ⟨L, F, hF0, hLip, hFb⟩ := dynamicField_compact_bounds r deltaS PhiS (M0 + 1)
  set A : ℝ := T * (K + L * F) * Real.exp (T * L) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A + 1, 1 / (A + 1), by linarith, by positivity, ?_⟩
  intro p hp hh hv y0 y hy hyb k hk
  have hvn := TP.varrho_nonneg deltaS PhiS p
  have hhv := TP.h_le_varrho deltaS PhiS p hh
  have hAv : A * p.varrho deltaS PhiS ≤ 1 := by
    have : p.varrho deltaS PhiS * (A + 1) ≤ 1 := by
      rw [le_div_iff₀ (by linarith)] at hv; exact hv
    nlinarith
  have hsmall : (‖(p.map r)^[0] y0 - y 0‖ + T * (K * p.varrho deltaS PhiS + (L : ℝ) * F * p.h)) *
      Real.exp (T * L) ≤ 1 := by
    have h0 : (p.map r)^[0] y0 - y 0 = 0 := by simp [hy.1]
    rw [h0, norm_zero, zero_add]
    calc T * (K * p.varrho deltaS PhiS + (L : ℝ) * F * p.h) * Real.exp (T * L)
        ≤ T * (K * p.varrho deltaS PhiS + (L : ℝ) * F * p.varrho deltaS PhiS) * Real.exp (T * L) := by
          gcongr
      _ = A * p.varrho deltaS PhiS := by rw [hA]; ring
      _ ≤ 1 := hAv
  have hgrid := dynamic_grid_error_of_local_residual r deltaS PhiS (M0 + 1) F p.h
    (K * p.varrho deltaS PhiS) T L k (fun n => (p.map r)^[n] y0) y hh (by positivity) hF0 hk
    (fun t ht => hy.2 t ht.1)
    (fun t ht => by linarith [hyb t ht]) hLip hFb
    (fun n _ hxn => by
      have hres := tame_step_residual r deltaS PhiS p ((p.map r)^[n] y0)
      have hn : (p.map r)^[n + 1] y0 = p.map r ((p.map r)^[n] y0) := Function.iterate_succ_apply' _ _ _
      show ‖(p.map r)^[n + 1] y0 - ((p.map r)^[n] y0 + p.h • dynamicField r deltaS PhiS ((p.map r)^[n] y0))‖ ≤ _
      rw [hn, hres, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
      obtain ⟨-, hb⟩ := hK p hp
      exact mul_le_mul_of_nonneg_left (hb _ _ hxn hxn).1 hh |>.trans (le_of_eq (by ring)))
    (by simpa [hy.1] using hsmall)
  have := hgrid k le_rfl
  have h0 : (p.map r)^[0] y0 - y 0 = 0 := by simp [hy.1]
  have hbd : ‖(p.map r)^[k] y0 - y ((k : ℝ) * p.h)‖ ≤ A * p.varrho deltaS PhiS := by
    refine this.trans ?_
    simp only [h0, norm_zero, zero_add]
    calc T * (K * p.varrho deltaS PhiS + (L : ℝ) * F * p.h) * Real.exp (T * L)
        ≤ T * (K * p.varrho deltaS PhiS + (L : ℝ) * F * p.varrho deltaS PhiS) * Real.exp (T * L) := by
          gcongr
      _ = A * p.varrho deltaS PhiS := by rw [hA]; ring
  refine ⟨hbd.trans ?_, hbd.trans hAv⟩
  exact mul_le_mul_of_nonneg_right (by linarith) hvn

/-- v2 `cor:recursion` (one-step consistency, `prop:LR34`): along a solution which stays in the
ball `M0`, `‖y((k+1)h) - Psi(y(kh))‖ <= C1 h varrho` (Euler error `L F h^2 <= L F h varrho` plus
`h ‖e‖ <= h K varrho`). -/
theorem tameDriftMap_consistency_of_bound (r deltaS PhiS : ℝ) (hd : 0 < deltaS) (hP : 0 ≤ PhiS)
    (M0 : ℝ) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ p : TP, p.Adm deltaS PhiS → 0 ≤ p.h →
      ∀ (y : ℝ → DynamicState),
      (∀ t : ℝ, 0 ≤ t → HasDerivAt y (dynamicField r deltaS PhiS (y t)) t) →
      (∀ t : ℝ, 0 ≤ t → ‖y t‖ ≤ M0) → ∀ k : ℕ,
        ‖y (((k + 1 : ℕ) : ℝ) * p.h) - p.map r (y ((k : ℝ) * p.h))‖ ≤
          C1 * p.h * p.varrho deltaS PhiS := by
  obtain ⟨K, hK0, hK⟩ := tameDriftMap_decomposition r deltaS PhiS hd hP M0
  obtain ⟨L, F, hF0, hLip, hFb⟩ := dynamicField_compact_bounds r deltaS PhiS M0
  refine ⟨L * F + K, by positivity, ?_⟩
  intro p hp hh y hy hyb k
  have hvn := TP.varrho_nonneg deltaS PhiS p
  have hhv := TP.h_le_varrho deltaS PhiS p hh
  have hk0 : 0 ≤ (k : ℝ) * p.h := by positivity
  have heul := dynamic_ode_euler_error r deltaS PhiS M0 F ((k : ℝ) * p.h) p.h L y hh hF0
    (fun s hs => hy s (hk0.trans hs.1)) (fun s hs => hyb s (hk0.trans hs.1)) hFb hLip
  have hres := tame_step_residual r deltaS PhiS p (y ((k : ℝ) * p.h))
  have hid : y (((k + 1 : ℕ) : ℝ) * p.h) - p.map r (y ((k : ℝ) * p.h)) =
      (y ((k : ℝ) * p.h + p.h) - (y ((k : ℝ) * p.h) + p.h • dynamicField r deltaS PhiS (y ((k : ℝ) * p.h)))) -
        p.h • p.err r deltaS PhiS (y ((k : ℝ) * p.h)) := by
    have e1 : ((k + 1 : ℕ) : ℝ) * p.h = (k : ℝ) * p.h + p.h := by push_cast; ring
    rw [e1, ← hres]; abel
  rw [hid]
  obtain ⟨-, hb⟩ := hK p hp
  have hb1 := (hb (y ((k : ℝ) * p.h)) (y ((k : ℝ) * p.h)) (hyb _ hk0) (hyb _ hk0)).1
  calc _ ≤ ‖y ((k : ℝ) * p.h + p.h) - (y ((k : ℝ) * p.h) + p.h • dynamicField r deltaS PhiS (y ((k : ℝ) * p.h)))‖ +
        ‖p.h • p.err r deltaS PhiS (y ((k : ℝ) * p.h))‖ := norm_sub_le _ _
    _ ≤ (L : ℝ) * F * p.h ^ 2 + p.h * (K * p.varrho deltaS PhiS) := by
        refine add_le_add heul ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
        exact mul_le_mul_of_nonneg_left hb1 hh
    _ ≤ (L * F + K) * p.h * p.varrho deltaS PhiS := by
        have : (L : ℝ) * F * p.h ^ 2 ≤ (L : ℝ) * F * p.h * p.varrho deltaS PhiS := by
          rw [pow_two, ← mul_assoc]
          exact mul_le_mul_of_nonneg_left hhv (by positivity)
        nlinarith


/-- Uniform a priori bound for all solutions of the tame field started in a compact physical set
`K`, for all times: the finite-horizon energy bound up to the entry time of `UniformEntry`,
and entry into `closedBall ystar 1` afterwards. -/
theorem solutions_uniform_bound (r deltaS PhiS : ℝ) (hd : 0 < deltaS) (hP : 0 ≤ PhiS)
    (ystar : DynamicState) (K : Set DynamicState) (hK : IsCompact K)
    (hKphys : ∀ y ∈ K, dynamicPhysical y)
    (hentry : UniformEntry (dynamicField r deltaS PhiS) ystar K) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ y0 ∈ K, ∀ y : ℝ → DynamicState,
      IsODESol (dynamicField r deltaS PhiS) y0 y → ∀ t : ℝ, 0 ≤ t → ‖y t‖ ≤ M0 := by
  obtain ⟨T0, hT0, hent⟩ := hentry 1 one_pos
  have hcont : Continuous (dynamicEnergy r deltaS) := by
    unfold dynamicEnergy dynamicAlpha; fun_prop
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hB0 : 0 ≤ B ∨ K = ∅ := by
    rcases K.eq_empty_or_nonempty with h | ⟨y, hy⟩
    · exact Or.inr h
    · exact Or.inl ((norm_nonneg _).trans (hB y hy))
  set B' : ℝ := max B 0 with hB'
  set Mfin : ℝ := 4 * (B' + PhiS * T0 + 2 * r ^ 2 + 1) * (1 + 1 / deltaS) + 1 with hMfin
  have hMfin0 : 0 ≤ Mfin := by positivity
  refine ⟨max Mfin (‖ystar‖ + 1), (le_max_left _ _).trans' hMfin0, ?_⟩
  intro y0 hy0 y hy t ht
  by_cases htT : t ≤ T0
  · have hb := norm_bound_on_interval r deltaS PhiS T0 y hd hP hT0
      (fun s hs => hy.2 s hs.1) (by rw [hy.1]; exact hKphys y0 hy0) t ⟨ht, htT⟩
    refine hb.trans ((le_max_left _ _).trans' ?_)
    have e1 : |dynamicEnergy r deltaS (y 0) + PhiS * T0| ≤ B' + PhiS * T0 := by
      rw [hy.1]
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg (by positivity : 0 ≤ PhiS * T0)]
      have := hB y0 hy0
      rw [Real.norm_eq_abs] at this
      have := this.trans (le_max_left B 0)
      linarith
    rw [hMfin]
    have hpos : 0 ≤ 1 + 1 / deltaS := by positivity
    gcongr
  · have := hent y0 hy0 y hy t (le_of_lt (not_le.1 htT))
    refine (le_max_right _ _).trans' ?_
    calc ‖y t‖ = ‖(y t - ystar) + ystar‖ := by simp
      _ ≤ ‖y t - ystar‖ + ‖ystar‖ := norm_add_le _ _
      _ ≤ ‖ystar‖ + 1 := by linarith


/-- Lyapunov certificate for the Jacobian of the base field at `y*` (from `prop_S_ii` and
`exists_lyapunov_certificate`), together with the strict derivative of the field. -/
theorem tame_base_certificate (r delta Phi : ℝ) (hr : 0 < r) (hdelta : 0 < delta)
    (hPhi : 0 ≤ Phi) :
    ∃ (A P : Matrix (Fin 5) (Fin 5) ℝ) (c : ℝ), 0 < c ∧ Pᵀ = P ∧
      (∀ x : Fin 5 → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ (P *ᵥ x)) ∧
      (∀ x : Fin 5 → ℝ, x ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x) ≤ -c * (x ⬝ᵥ x)) ∧
      HasStrictFDerivAt (dynamicField r delta Phi)
        (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A))
        (dynamicCanonicalEquilibrium r delta Phi) := by
  obtain ⟨hF, hHur⟩ := prop_S_ii r delta Phi hr hdelta hPhi
  set A := jacobianMatrix (dynamicAlpha r (dynamicCanonicalEquilibrium r delta Phi))
    (positiveRoot r Phi) (equilibriumBulk r Phi) delta with hA
  obtain ⟨P, c, hc, hPs, hge, hdec⟩ := exists_lyapunov_certificate A hHur
  refine ⟨A, P, c, hc, hPs, hge, hdec, ?_⟩
  have h1 := (contDiff_dynamicField r delta Phi).contDiffAt.hasStrictFDerivAt (x := dynamicCanonicalEquilibrium r delta Phi) (by simp)
  have h2 := hF.fderiv
  rw [h2] at h1
  exact h1


/-- The conclusion of tame `cor:recursion` for one parameter tuple `p`: a fixed point `y_h` within
`C varrho` of `ystar`, unique in `closedBall ystar s`; exponential convergence of every orbit from
`K`; uniform tracking of every solution from `K`; and exponential decay of the Jacobian products
along every orbit from `K`. -/
def TameGood (r deltaS PhiS : ℝ) (ystar : DynamicState) (K : Set DynamicState)
    (C c s : ℝ) (p : TP) : Prop :=
  ∃ yh : DynamicState, ‖yh - ystar‖ ≤ C * p.varrho deltaS PhiS ∧ p.map r yh = yh ∧
    (∀ z : DynamicState, ‖z - ystar‖ ≤ s → p.map r z = z → z = yh) ∧
    ∀ y0 ∈ K,
      (∀ k : ℕ, ‖(p.map r)^[k] y0 - yh‖ ≤ C * Real.exp (-(c * p.h * k))) ∧
      (∀ y : ℝ → DynamicState, IsODESol (dynamicField r deltaS PhiS) y0 y → ∀ k : ℕ,
        ‖(p.map r)^[k] y0 - y ((k : ℝ) * p.h)‖ ≤ C * p.varrho deltaS PhiS) ∧
      (∀ j m : ℕ, ‖jacProd (p.map r) ((p.map r)^[j] y0) m‖ ≤
        C * Real.exp (-(c * p.h * m)))

/-- v2 `cor:recursion` (tame drift recursion), for a one-parameter family `ε ↦ F ε` of parameter
tuples with step `h = ε` and `varrho → 0`.  The constants depend on the family; the uniform form
over the whole tube is `cor_recursion_tame`.  Instantiates `drift_recursion_converges` and
`jacobian_products` with `b = dynamicField`, the Lyapunov certificate of the Jacobian at `y*`
(`prop_S_ii`), and the perturbation `e` of `tameDriftMap_decomposition`. -/
theorem tame_family (r deltaS PhiS : ℝ) (hr : 0 < r) (hd : 0 < deltaS) (hP : 0 ≤ PhiS)
    (K : Set DynamicState) (hK : IsCompact K) (hKphys : ∀ y ∈ K, dynamicPhysical y)
    (hentry : UniformEntry (dynamicField r deltaS PhiS)
      (dynamicCanonicalEquilibrium r deltaS PhiS) K)
    (F : ℝ → TP)
    (hF1 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → (F ε).Adm deltaS PhiS ∧ (F ε).h = ε)
    (hF2 : ∀ v : ℝ, 0 < v → ∃ ε' : ℝ, 0 < ε' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε' → ε ≤ 1 →
      (F ε).varrho deltaS PhiS ≤ v) :
    ∃ C c s v0 : ℝ, 0 < C ∧ 0 < c ∧ 0 < s ∧ 0 < v0 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (F ε).varrho deltaS PhiS ≤ v0 →
      TameGood r deltaS PhiS (dynamicCanonicalEquilibrium r deltaS PhiS) K C c s (F ε) := by
  classical
  set ystar := dynamicCanonicalEquilibrium r deltaS PhiS with hystar
  have hS : dynamicField r deltaS PhiS ystar = 0 :=
    dynamicCanonicalEquilibrium_is_stationary r deltaS PhiS hr hd hP
  obtain ⟨A, P, c0, hc0, hPs, hge, hdec, hstrict⟩ := tame_base_certificate r deltaS PhiS hr hd hP
  obtain ⟨K1', hK1', hKd1⟩ := tameDriftMap_decomposition r deltaS PhiS hd hP (‖ystar‖ + 1)
  set K1 : ℝ := max K1' 1 with hK1def
  have hK1one : 1 ≤ K1 := le_max_right _ _
  have hK1ge : K1' ≤ K1 := le_max_left _ _
  have hK1pos : 0 < K1 := by linarith
  let e' : ℝ → DynamicState → DynamicState :=
    fun ε => if ε ≤ 1 then (F ε).err r deltaS PhiS else fun _ => 0
  let ρ' : ℝ → ℝ := fun ε => if ε ≤ 1 then K1 * (F ε).varrho deltaS PhiS else ε
  have hρε : ∀ ε : ℝ, 0 < ε → ε ≤ ρ' ε := by
    intro ε hε
    by_cases h1 : ε ≤ 1
    · obtain ⟨hadm, hh⟩ := hF1 ε hε h1
      have := TP.h_le_varrho deltaS PhiS (F ε) (by rw [hh]; exact hε.le)
      have hv := TP.varrho_nonneg deltaS PhiS (F ε)
      simp only [ρ', h1, ↓reduceIte]
      rw [hh] at this
      nlinarith
    · simp [ρ', h1]
  have hnormball : ∀ y : DynamicState, ‖y - ystar‖ ≤ 1 → ‖y‖ ≤ ‖ystar‖ + 1 := by
    intro y hy
    calc ‖y‖ = ‖(y - ystar) + ystar‖ := by simp
      _ ≤ ‖y - ystar‖ + ‖ystar‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have he0 : ∀ ε : ℝ, 0 < ε → ∀ y : DynamicState, ‖y - ystar‖ ≤ 1 → ‖e' ε y‖ ≤ ρ' ε := by
    intro ε hε y hy
    by_cases h1 : ε ≤ 1
    · obtain ⟨hadm, hh⟩ := hF1 ε hε h1
      obtain ⟨-, hb⟩ := hKd1 (F ε) hadm
      have := (hb y y (hnormball y hy) (hnormball y hy)).1
      have hv := TP.varrho_nonneg deltaS PhiS (F ε)
      simp only [e', ρ', h1, ↓reduceIte]
      exact this.trans (by nlinarith)
    · simp [e', ρ', h1, hε.le]
  have he1 : ∀ ε : ℝ, 0 < ε → ∀ y z : DynamicState, ‖y - ystar‖ ≤ 1 → ‖z - ystar‖ ≤ 1 →
      ‖e' ε y - e' ε z‖ ≤ ρ' ε * ‖y - z‖ := by
    intro ε hε y z hy hz
    by_cases h1 : ε ≤ 1
    · obtain ⟨hadm, hh⟩ := hF1 ε hε h1
      obtain ⟨-, hb⟩ := hKd1 (F ε) hadm
      have := (hb y z (hnormball y hy) (hnormball z hz)).2.2
      have hv := TP.varrho_nonneg deltaS PhiS (F ε)
      simp only [e', ρ', h1, ↓reduceIte]
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
    · simp [e', ρ', h1]; positivity
  let H : RecursionSetup 5 :=
    { A := A, P := P, c := c0, hc := hc0, hPs := hPs, hge := hge, hdec := hdec,
      b := dynamicField r deltaS PhiS, ystar := ystar, hb0 := hS, hb := hstrict,
      e := e', ρ := ρ', r0 := 1, hr0 := one_pos, hρε := hρε, he0 := he0, he1 := he1 }
  have hmap : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → driftMap H.b H.e ε = (F ε).map r := by
    intro ε hε h1
    funext y
    have hh := (hF1 ε hε h1).2
    show y + ε • (dynamicField r deltaS PhiS y + (if ε ≤ 1 then (F ε).err r deltaS PhiS
      else fun _ => 0) y) = (F ε).map r y
    simp only [h1, ↓reduceIte]
    rw [TP.map_eq r deltaS PhiS, hh]
  have hex : ∀ y0 ∈ K, ∃ y : ℝ → DynamicState, IsODESol H.b y0 y := by
    intro y0 hy0
    obtain ⟨y, hy0', hy, -⟩ := global_solution_exists r deltaS PhiS y0 hd hP (hKphys y0 hy0)
    exact ⟨y, hy0', hy⟩
  have hent : UniformEntry H.b H.ystar K := hentry
  obtain ⟨M0, hM00, hM0⟩ := solutions_uniform_bound r deltaS PhiS hd hP ystar K hK hKphys hentry
  have hbdd : ∀ T : ℝ, 0 ≤ T → ∃ M : ℝ, 0 ≤ M ∧ ∀ y0 ∈ K, ∀ y : ℝ → DynamicState,
      IsODESol H.b y0 y → ∀ t : ℝ, 0 ≤ t → t ≤ T → ‖y t - H.ystar‖ ≤ M := by
    intro T _
    refine ⟨M0 + ‖ystar‖, by positivity, fun y0 hy0 y hy t ht _ => ?_⟩
    calc ‖y t - ystar‖ ≤ ‖y t‖ + ‖ystar‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [hM0 y0 hy0 y hy t ht]
  have htrack : ∀ T : ℝ, 0 ≤ T → ∃ CT εT : ℝ, 0 < CT ∧ 0 < εT ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εT → ∀ y0 ∈ K, ∀ y : ℝ → DynamicState, IsODESol H.b y0 y →
        ∀ k : ℕ, (k : ℝ) * ε ≤ T →
          ‖(driftMap H.b H.e ε)^[k] y0 - y (k * ε)‖ ≤ CT * H.ρ ε := by
    intro T hT
    obtain ⟨CT, vT, hCT, hvT, htr⟩ := tameDriftMap_tracking_of_bound r deltaS PhiS hd hP T M0 hT
    obtain ⟨ε', hε', hεv⟩ := hF2 vT hvT
    refine ⟨CT, min ε' 1, hCT, lt_min hε' one_pos, ?_⟩
    intro ε hε hεle y0 hy0 y hy k hk
    have h1 : ε ≤ 1 := hεle.trans (min_le_right _ _)
    have h2 : ε ≤ ε' := hεle.trans (min_le_left _ _)
    obtain ⟨hadm, hh⟩ := hF1 ε hε h1
    rw [hmap ε hε h1]
    have := (htr (F ε) hadm (by rw [hh]; exact hε.le) (hεv ε hε h2 h1) y0 y hy
      (fun t ht => hM0 y0 hy0 y hy t ht.1) k (by rw [hh]; exact hk)).1
    rw [hh] at this
    have hρ : H.ρ ε = K1 * (F ε).varrho deltaS PhiS := by
      show (if ε ≤ 1 then K1 * (F ε).varrho deltaS PhiS else ε) = _
      simp [h1]
    rw [hρ]
    refine this.trans ?_
    have hv := TP.varrho_nonneg deltaS PhiS (F ε)
    nlinarith [mul_nonneg (mul_nonneg hCT.le hv) (sub_nonneg.2 hK1one)]
  have hcons : ∃ rc C1 εc : ℝ, 0 < rc ∧ 0 < C1 ∧ 0 < εc ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εc → ∀ y0 ∈ K, ∀ y : ℝ → DynamicState, IsODESol H.b y0 y →
        ∀ k : ℕ, ‖y (k * ε) - H.ystar‖ ≤ rc →
          ‖y (((k + 1 : ℕ) : ℝ) * ε) - driftMap H.b H.e ε (y (k * ε))‖ ≤ C1 * ε * H.ρ ε := by
    obtain ⟨C1, hC1, hcon⟩ := tameDriftMap_consistency_of_bound r deltaS PhiS hd hP M0
    refine ⟨1, C1 + 1, 1, one_pos, by linarith, one_pos, ?_⟩
    intro ε hε h1 y0 hy0 y hy k _
    obtain ⟨hadm, hh⟩ := hF1 ε hε h1
    rw [hmap ε hε h1]
    have := hcon (F ε) hadm (by rw [hh]; exact hε.le) y hy.2 (fun t ht => hM0 y0 hy0 y hy t ht) k
    rw [hh] at this
    have hρ : H.ρ ε = K1 * (F ε).varrho deltaS PhiS := by
      show (if ε ≤ 1 then K1 * (F ε).varrho deltaS PhiS else ε) = _
      simp [h1]
    rw [hρ]
    refine this.trans ?_
    have hv := TP.varrho_nonneg deltaS PhiS (F ε)
    have h3 : 0 ≤ ε * (F ε).varrho deltaS PhiS := mul_nonneg hε.le hv
    nlinarith [mul_nonneg (mul_nonneg hC1 h3) (sub_nonneg.2 hK1one), mul_nonneg hK1pos.le h3]
  have hdb : ∀ y : DynamicState, ‖y - H.ystar‖ ≤ H.r0 → DifferentiableAt ℝ H.b y :=
    fun y _ => (contDiff_dynamicField r deltaS PhiS).differentiable (by simp) y
  have hde : ∀ ε : ℝ, 0 < ε → ∀ y : DynamicState, ‖y - H.ystar‖ ≤ H.r0 →
      DifferentiableAt ℝ (H.e ε) y ∧ ‖fderiv ℝ (H.e ε) y‖ ≤ H.ρ ε := by
    intro ε hε y hy
    by_cases h1 : ε ≤ 1
    · obtain ⟨hadm, hh⟩ := hF1 ε hε h1
      obtain ⟨-, hb⟩ := hKd1 (F ε) hadm
      obtain ⟨-, ⟨hdf, hder⟩, -⟩ := hb y y (hnormball y hy) (hnormball y hy)
      have hv := TP.varrho_nonneg deltaS PhiS (F ε)
      have e1 : H.e ε = (F ε).err r deltaS PhiS := by
        show (if ε ≤ 1 then (F ε).err r deltaS PhiS else fun _ => 0) = _
        simp [h1]
      have hρ : H.ρ ε = K1 * (F ε).varrho deltaS PhiS := by
        show (if ε ≤ 1 then K1 * (F ε).varrho deltaS PhiS else ε) = _
        simp [h1]
      rw [e1, hρ]
      exact ⟨hdf, hder.trans (by nlinarith)⟩
    · have e1 : H.e ε = fun _ => 0 := by
        show (if ε ≤ 1 then (F ε).err r deltaS PhiS else fun _ => 0) = _
        simp [h1]
      have hρ : H.ρ ε = ε := by
        show (if ε ≤ 1 then K1 * (F ε).varrho deltaS PhiS else ε) = _
        simp [h1]
      rw [e1, hρ]
      refine ⟨differentiableAt_const _, ?_⟩
      simp only [fderiv_fun_const, Pi.zero_apply, norm_zero]
      exact hε.le
  obtain ⟨K2, hK2, hKd2⟩ := tameDriftMap_decomposition r deltaS PhiS hd hP (M0 + 1)
  obtain ⟨Lf, hLf⟩ := (isCompact_closedBall (0 : DynamicState) (M0 + 1)).exists_bound_of_continuousOn
    ((contDiff_dynamicField r deltaS PhiS).continuous_fderiv (by simp)).continuousOn
  have hJ : ∀ T : ℝ, 0 ≤ T → ∃ L εL : ℝ, 0 ≤ L ∧ 0 < εL ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εL → ∀ y0 ∈ K, ∀ k : ℕ, (k : ℝ) * ε ≤ T →
        ‖fderiv ℝ (driftMap H.b H.e ε) ((driftMap H.b H.e ε)^[k] y0)‖ ≤ 1 + L * ε := by
    intro T hT
    obtain ⟨CT, vT, hCT, hvT, htr⟩ := tameDriftMap_tracking_of_bound r deltaS PhiS hd hP T M0 hT
    obtain ⟨ε', hε', hεv⟩ := hF2 vT hvT
    refine ⟨max Lf 0 + K2, min ε' 1, by positivity, lt_min hε' one_pos, ?_⟩
    intro ε hε hεle y0 hy0 k hk
    have h1 : ε ≤ 1 := hεle.trans (min_le_right _ _)
    have h2 : ε ≤ ε' := hεle.trans (min_le_left _ _)
    obtain ⟨hadm, hh⟩ := hF1 ε hε h1
    rw [hmap ε hε h1]
    obtain ⟨y, hy⟩ := hex y0 hy0
    have htr' := (htr (F ε) hadm (by rw [hh]; exact hε.le) (hεv ε hε h2 h1) y0 y hy
      (fun t ht => hM0 y0 hy0 y hy t ht.1) k (by rw [hh]; exact hk)).2
    rw [hh] at htr'
    set x := ((F ε).map r)^[k] y0 with hx
    have hxM : ‖x‖ ≤ M0 + 1 := by
      have hyk : ‖y ((k : ℝ) * ε)‖ ≤ M0 :=
        hM0 y0 hy0 y hy _ (by positivity)
      calc ‖x‖ = ‖(x - y ((k : ℝ) * ε)) + y ((k : ℝ) * ε)‖ := by simp
        _ ≤ ‖x - y ((k : ℝ) * ε)‖ + ‖y ((k : ℝ) * ε)‖ := norm_add_le _ _
        _ ≤ M0 + 1 := by linarith
    obtain ⟨-, hb⟩ := hKd2 (F ε) hadm
    obtain ⟨-, ⟨hdf, hder⟩, -⟩ := hb x x hxM hxM
    have hfun : (F ε).map r = fun y => y + (F ε).h • (dynamicField r deltaS PhiS y +
        (F ε).err r deltaS PhiS y) := funext (TP.map_eq r deltaS PhiS (F ε))
    have hfd : HasFDerivAt (dynamicField r deltaS PhiS)
        (fderiv ℝ (dynamicField r deltaS PhiS) x) x :=
      ((contDiff_dynamicField r deltaS PhiS).differentiable (by simp) x).hasFDerivAt
    have hmapd : HasFDerivAt ((F ε).map r) (ContinuousLinearMap.id ℝ DynamicState +
        (F ε).h • (fderiv ℝ (dynamicField r deltaS PhiS) x +
          fderiv ℝ ((F ε).err r deltaS PhiS) x)) x := by
      rw [hfun]
      exact (hasFDerivAt_id x).fun_add ((hfd.fun_add hdf.hasFDerivAt).fun_const_smul _)
    rw [hmapd.fderiv, hh]
    have hLx : ‖fderiv ℝ (dynamicField r deltaS PhiS) x‖ ≤ max Lf 0 :=
      (hLf x (by simpa using hxM)).trans (le_max_left _ _)
    have hv1 : (F ε).varrho deltaS PhiS ≤ 1 := hadm.2.2.2
    have hv0 := TP.varrho_nonneg deltaS PhiS (F ε)
    have hder' : ‖fderiv ℝ ((F ε).err r deltaS PhiS) x‖ ≤ K2 := by
      refine hder.trans ?_
      nlinarith
    calc _ ≤ ‖ContinuousLinearMap.id ℝ DynamicState‖ + ‖ε • (fderiv ℝ (dynamicField r deltaS PhiS) x +
          fderiv ℝ ((F ε).err r deltaS PhiS) x)‖ := norm_add_le _ _
      _ ≤ 1 + ε * (max Lf 0 + K2) := by
        refine add_le_add ContinuousLinearMap.norm_id_le ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
        refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) hε.le
        linarith
      _ = 1 + (max Lf 0 + K2) * ε := by ring
  obtain ⟨ε1, ρ1, C, c, hε1, hρ1, hC, hc, N, ⟨s, hs0, hsN⟩, -, hmain⟩ :=
    drift_recursion_converges H K hK hex hent hbdd htrack hcons
  obtain ⟨ε2, ρ2, Γ, c2, hε2, hρ2, hΓ, hc2, hjac⟩ :=
    jacobian_products H K hex hent htrack hdb hde hJ
  set Cf : ℝ := C * K1 + Γ with hCf
  have hCf0 : 0 < Cf := by positivity
  set cm : ℝ := min c c2 with hcm
  have hcm0 : 0 < cm := lt_min hc hc2
  refine ⟨Cf, cm, s, min (min ε1 ε2) (min (ρ1 / K1) (ρ2 / K1)), hCf0, hcm0, hs0,
    lt_min (lt_min hε1 hε2) (lt_min (by positivity) (by positivity)), ?_⟩
  intro ε hε h1 hv
  obtain ⟨hadm, hh⟩ := hF1 ε hε h1
  have hvn := TP.varrho_nonneg deltaS PhiS (F ε)
  have hεv : ε ≤ (F ε).varrho deltaS PhiS := by
    have := TP.h_le_varrho deltaS PhiS (F ε) (by rw [hh]; exact hε.le)
    rwa [hh] at this
  have hεε1 : ε ≤ ε1 := hεv.trans (hv.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hεε2 : ε ≤ ε2 := hεv.trans (hv.trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hρ : H.ρ ε = K1 * (F ε).varrho deltaS PhiS := by
    show (if ε ≤ 1 then K1 * (F ε).varrho deltaS PhiS else ε) = _
    simp [h1]
  have hρ1' : H.ρ ε ≤ ρ1 := by
    rw [hρ]
    have : (F ε).varrho deltaS PhiS ≤ ρ1 / K1 :=
      hv.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ hK1pos] at this
    linarith
  have hρ2' : H.ρ ε ≤ ρ2 := by
    rw [hρ]
    have : (F ε).varrho deltaS PhiS ≤ ρ2 / K1 :=
      hv.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ hK1pos] at this
    linarith
  obtain ⟨yε, hyN, hfix, huniq, hnear, hall⟩ := hmain ε hε hεε1 hρ1'
  have hmapε := hmap ε hε h1
  have hCρ : ∀ x : ℝ, 0 ≤ x → C * (K1 * x) ≤ Cf * x := by
    intro x hx
    rw [hCf]
    nlinarith [mul_nonneg hΓ.le hx]
  refine ⟨yε, ?_, ?_, ?_, ?_⟩
  · refine hnear.trans ?_
    rw [hρ]
    exact hCρ _ hvn
  · rw [← hmapε]; exact hfix
  · intro z hz hzf
    rw [← hmapε] at hzf
    exact huniq z (hsN (by simpa [dist_eq_norm] using hz)) hzf
  · intro y0 hy0
    obtain ⟨hexp, htk⟩ := hall y0 hy0
    rw [hh, ← hmapε]
    refine ⟨fun k => ?_, fun y hy k => ?_, fun j m => ?_⟩
    · refine (hexp k).trans ?_
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have : Real.exp (-(c * ε * k)) ≤ Real.exp (-(cm * ε * k)) := by
        apply Real.exp_le_exp.2
        have : cm * ε * k ≤ c * ε * k := by
          have := min_le_left c c2
          gcongr
        linarith
      calc C * Real.exp (-(c * ε * k)) ≤ Cf * Real.exp (-(cm * ε * k)) := by
            apply mul_le_mul _ this (Real.exp_pos _).le hCf0.le
            rw [hCf]; nlinarith [mul_nonneg hC.le (sub_nonneg.2 hK1one)]
        _ ≤ _ := le_rfl
    · refine (htk y hy k).trans ?_
      rw [hρ]
      exact hCρ _ hvn
    · have hj := hjac ε hε hεε2 hρ2' y0 hy0 j m
      refine hj.trans ?_
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have : Real.exp (-(c2 * ε * m)) ≤ Real.exp (-(cm * ε * m)) := by
        apply Real.exp_le_exp.2
        have : cm * ε * m ≤ c2 * ε * m := by
          have := min_le_right c c2
          gcongr
        linarith
      apply mul_le_mul _ this (Real.exp_pos _).le hCf0.le
      rw [hCf]; nlinarith [mul_nonneg hC.le (sub_nonneg.2 hK1one), mul_nonneg hC.le (zero_le_one.trans hK1one)]


/-- Uniformization (abstract): if the conclusion `Good` holds with constants for every one-parameter
family `ε ↦ F ε` of admissible points with step `hh (F ε) = ε` and `vr (F ε) → 0`, then it holds
with one set of constants for all admissible points with `vr` small.  Proof by contradiction: a
failing sequence with strictly decreasing steps is turned into such a family. -/
theorem uniformize {X : Type*} (hh vr : X → ℝ) (Adm : X → Prop)
    (Good : ℝ → ℝ → ℝ → X → Prop) (dflt : ℝ → X)
    (hdef : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → Adm (dflt ε) ∧ hh (dflt ε) = ε ∧ vr (dflt ε) = ε)
    (hmono : ∀ (C c s C' c' s' : ℝ) (x : X), Adm x → 0 < hh x → 0 ≤ C → C ≤ C' → c' ≤ c →
      s' ≤ s → Good C c s x → Good C' c' s' x)
    (hhv : ∀ x : X, Adm x → 0 < hh x → hh x ≤ vr x)
    (hfam : ∀ F : ℝ → X, (∀ ε : ℝ, 0 < ε → ε ≤ 1 → Adm (F ε) ∧ hh (F ε) = ε) →
      (∀ v : ℝ, 0 < v → ∃ ε' : ℝ, 0 < ε' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε' → ε ≤ 1 → vr (F ε) ≤ v) →
      ∃ C c s v0 : ℝ, 0 < C ∧ 0 < c ∧ 0 < s ∧ 0 < v0 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        vr (F ε) ≤ v0 → Good C c s (F ε)) :
    ∃ C c s v0 : ℝ, 0 < C ∧ 0 < c ∧ 0 < s ∧ 0 < v0 ∧ ∀ x : X, Adm x → 0 < hh x → vr x ≤ v0 →
      Good C c s x := by
  classical
  by_contra hneg
  push Not at hneg
  have hex : ∀ (n : ℕ) (v : ℝ), ∃ x : X, 0 < v → (Adm x ∧ 0 < hh x ∧ vr x ≤ v ∧
      ¬ Good ((n : ℝ) + 1) (1 / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)) x) := by
    intro n v
    by_cases hv : 0 < v
    · obtain ⟨x, hx1, hx2, hx3, hx4⟩ := hneg ((n : ℝ) + 1) (1 / ((n : ℝ) + 1))
        (1 / ((n : ℝ) + 1)) v (by positivity) (by positivity) (by positivity) hv
      exact ⟨x, fun _ => ⟨hx1, hx2, hx3, hx4⟩⟩
    · exact ⟨dflt 1, fun h => absurd h hv⟩
  choose ψ hψ using hex
  let x : ℕ → X := fun n => Nat.rec (motive := fun _ => X) (ψ 0 1)
    (fun n xn => ψ (n + 1) (min (1 / ((n : ℝ) + 2)) (hh xn / 2))) n
  have hx0 : x 0 = ψ 0 1 := rfl
  have hxs : ∀ n, x (n + 1) = ψ (n + 1) (min (1 / ((n : ℝ) + 2)) (hh (x n) / 2)) := fun n => rfl
  have hP : ∀ n : ℕ, Adm (x n) ∧ 0 < hh (x n) ∧ vr (x n) ≤ 1 / ((n : ℝ) + 1) ∧
      ¬ Good ((n : ℝ) + 1) (1 / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)) (x n) := by
    intro n
    induction n with
    | zero =>
      have := hψ 0 1 one_pos
      rw [hx0]; simpa using this
    | succ n ih =>
      obtain ⟨-, h2, -, -⟩ := ih
      have hv : 0 < min (1 / ((n : ℝ) + 2)) (hh (x n) / 2) :=
        lt_min (by positivity) (by linarith)
      obtain ⟨a, b, c, d⟩ := hψ (n + 1) _ hv
      rw [hxs]
      refine ⟨a, b, ?_, ?_⟩
      · refine c.trans ((min_le_left _ _).trans (le_of_eq ?_))
        push_cast; ring_nf
      · simpa using d
  have hdec : ∀ n : ℕ, hh (x (n + 1)) < hh (x n) := by
    intro n
    obtain ⟨a, b, -, -⟩ := hP (n + 1)
    obtain ⟨-, h2, -, -⟩ := hP n
    have hv : 0 < min (1 / ((n : ℝ) + 2)) (hh (x n) / 2) :=
      lt_min (by positivity) (by linarith)
    obtain ⟨-, -, c, -⟩ := hψ (n + 1) _ hv
    have := hhv _ a b
    rw [hxs] at this ⊢
    have h3 := this.trans c
    have h4 := h3.trans (min_le_right _ _)
    linarith
  have hanti : StrictAnti (fun n => hh (x n)) := strictAnti_nat_of_succ_lt hdec
  let F : ℝ → X := fun ε => if h : ∃ n, hh (x n) = ε then x (Classical.choose h) else dflt ε
  have hFx : ∀ n : ℕ, F (hh (x n)) = x n := by
    intro n
    have h : ∃ m, hh (x m) = hh (x n) := ⟨n, rfl⟩
    have hc := Classical.choose_spec h
    have : Classical.choose h = n := hanti.injective hc
    simp [F, h, this]
  have hF1 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → Adm (F ε) ∧ hh (F ε) = ε := by
    intro ε hε h1
    by_cases h : ∃ n, hh (x n) = ε
    · have hc := Classical.choose_spec h
      have e : F ε = x (Classical.choose h) := by simp [F, h]
      rw [e]
      exact ⟨(hP _).1, hc⟩
    · have e : F ε = dflt ε := by simp [F, h]
      rw [e]
      exact ⟨(hdef ε hε h1).1, (hdef ε hε h1).2.1⟩
  have hF2 : ∀ v : ℝ, 0 < v → ∃ ε' : ℝ, 0 < ε' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε' → ε ≤ 1 →
      vr (F ε) ≤ v := by
    intro v hv
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / v)
    refine ⟨min v (hh (x N)), lt_min hv (hP N).2.1, ?_⟩
    intro ε hε hεle h1
    by_cases h : ∃ n, hh (x n) = ε
    · have hc := Classical.choose_spec h
      have e : F ε = x (Classical.choose h) := by simp [F, h]
      rw [e]
      set n' := Classical.choose h with hn'
      have hnN : N ≤ n' := by
        by_contra hlt
        have := hanti (not_le.1 hlt)
        have h2 := hεle.trans (min_le_right _ _)
        simp only at this
        linarith
      refine (hP n').2.2.1.trans ?_
      have : 1 / v < (n' : ℝ) + 1 := by
        have : (N : ℝ) ≤ n' := by exact_mod_cast hnN
        linarith
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hv] at this
      linarith
    · have e : F ε = dflt ε := by simp [F, h]
      rw [e, (hdef ε hε h1).2.2]
      exact hεle.trans (min_le_left _ _)
  obtain ⟨C, c, s, v0, hC, hc, hs, hv0, hgood⟩ := hfam F hF1 hF2
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max C (1 / c)) (max (1 / s) (1 / v0)))
  obtain ⟨hA, hpos, hvr, hbad⟩ := hP N
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hle : ∀ t : ℝ, t ≤ max (max C (1 / c)) (max (1 / s) (1 / v0)) → t < (N : ℝ) + 1 :=
    fun t ht => by linarith
  have hCN : C ≤ (N : ℝ) + 1 := (hle C ((le_max_left _ _).trans (le_max_left _ _))).le
  have hcN : 1 / ((N : ℝ) + 1) ≤ c := by
    have := hle (1 / c) ((le_max_right _ _).trans (le_max_left _ _))
    rw [div_lt_iff₀ hc] at this
    rw [div_le_iff₀ hN1]; linarith
  have hsN : 1 / ((N : ℝ) + 1) ≤ s := by
    have := hle (1 / s) ((le_max_left _ _).trans (le_max_right _ _))
    rw [div_lt_iff₀ hs] at this
    rw [div_le_iff₀ hN1]; linarith
  have hvN : 1 / ((N : ℝ) + 1) ≤ v0 := by
    have := hle (1 / v0) ((le_max_right _ _).trans (le_max_right _ _))
    rw [div_lt_iff₀ hv0] at this
    rw [div_le_iff₀ hN1]; linarith
  have h1N : 1 / ((N : ℝ) + 1) ≤ 1 := by
    rw [div_le_iff₀ hN1]; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hh1 : hh (x N) ≤ 1 := (hhv _ hA hpos).trans (hvr.trans h1N)
  have hg := hgood (hh (x N)) hpos hh1 (by rw [hFx]; exact hvr.trans hvN)
  rw [hFx] at hg
  exact hbad (hmono C c s _ _ _ (x N) hA hpos hC.le hCN hcN hsN hg)


theorem TameGood.mono (r deltaS PhiS : ℝ) (ystar : DynamicState) (K : Set DynamicState)
    (C c s C' c' s' : ℝ) (p : TP) (hh : 0 < p.h) (hC : C ≤ C') (hc : c' ≤ c) (hs : s' ≤ s)
    (hC0 : 0 ≤ C) (hv : 0 ≤ p.varrho deltaS PhiS)
    (hg : TameGood r deltaS PhiS ystar K C c s p) : TameGood r deltaS PhiS ystar K C' c' s' p := by
  obtain ⟨yh, h1, h2, h3, h4⟩ := hg
  refine ⟨yh, h1.trans (mul_le_mul_of_nonneg_right hC hv), h2,
    fun z hz hzf => h3 z (hz.trans hs) hzf, fun y0 hy0 => ?_⟩
  obtain ⟨e1, e2, e3⟩ := h4 y0 hy0
  have hex : ∀ m : ℕ, C * Real.exp (-(c * p.h * m)) ≤ C' * Real.exp (-(c' * p.h * m)) := by
    intro m
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    apply mul_le_mul hC _ (Real.exp_pos _).le (hC0.trans hC)
    apply Real.exp_le_exp.2
    have : c' * p.h * m ≤ c * p.h * m := by gcongr
    linarith
  exact ⟨fun k => (e1 k).trans (hex k),
    fun y hy k => (e2 y hy k).trans (mul_le_mul_of_nonneg_right hC hv),
    fun j m => (e3 j m).trans (hex m)⟩

/-- v2 `cor:recursion` (tame drift recursion), uniform form.  Assume `r > 0`, `deltaS > 0`,
`PhiS >= 0`, `K` compact and physical, and the uniform-entry property `hentry` of the base ODE
(proved for the LR5 field by `dynamicField_uniformEntry`).  Then there are `C, c, varrho0, s > 0`
such that for all `h > 0`, `|delta - deltaS| <= deltaS/2`, `rho in [0,1]` and
`varrho = |h| + |delta - deltaS| + |Phi - PhiS| + |nu| <= varrho0`, the tame drift map
`Psi = tameDriftMap r h delta Phi nu rho` has a fixed point `y_h` with `‖y_h - y*‖ <= C varrho`,
unique in `closedBall y* s` (which contains `closedBall y* (C varrho)`, as `C varrho0 <= s`);
`‖Psi^k y0 - y_h‖ <= C exp(-c h k)` for every `y0` in `K`; `‖Psi^k y0 - y(k h)‖ <= C varrho`
for every solution `y` from `y0`; and the Jacobian products along the orbit satisfy
`‖J_{j+m-1} ∘ ⋯ ∘ J_j‖ <= C exp(-c h m)`.  Out of scope: the actual Gaussian-coefficient
recursion of `prop:LR34`, which is non-autonomous through `theta ∈ R^d`; only the tame
instantiation of `lem:B` (`a = alpha(y)`, `b = -1`, `d0 = 1`) is treated here. -/
theorem cor_recursion_tame (r deltaS PhiS : ℝ) (hr : 0 < r) (hd : 0 < deltaS) (hP : 0 ≤ PhiS)
    (K : Set DynamicState) (hK : IsCompact K) (hKphys : ∀ y ∈ K, dynamicPhysical y)
    (hentry : UniformEntry (dynamicField r deltaS PhiS)
      (dynamicCanonicalEquilibrium r deltaS PhiS) K) :
    ∃ C c v0 s : ℝ, 0 < C ∧ 0 < c ∧ 0 < v0 ∧ v0 ≤ 1 ∧ 0 < s ∧ C * v0 ≤ s ∧
      ∀ h delta Phi nu rho : ℝ, 0 < h → |delta - deltaS| ≤ deltaS / 2 → 0 ≤ rho → rho ≤ 1 →
        |h| + |delta - deltaS| + |Phi - PhiS| + |nu| ≤ v0 →
        ∃ yh : DynamicState,
          ‖yh - dynamicCanonicalEquilibrium r deltaS PhiS‖ ≤
            C * (|h| + |delta - deltaS| + |Phi - PhiS| + |nu|) ∧
          tameDriftMap r h delta Phi nu rho yh = yh ∧
          (∀ z : DynamicState, ‖z - dynamicCanonicalEquilibrium r deltaS PhiS‖ ≤ s →
            tameDriftMap r h delta Phi nu rho z = z → z = yh) ∧
          ∀ y0 ∈ K,
            (∀ k : ℕ, ‖(tameDriftMap r h delta Phi nu rho)^[k] y0 - yh‖ ≤
              C * Real.exp (-(c * h * k))) ∧
            (∀ y : ℝ → DynamicState, IsODESol (dynamicField r deltaS PhiS) y0 y → ∀ k : ℕ,
              ‖(tameDriftMap r h delta Phi nu rho)^[k] y0 - y ((k : ℝ) * h)‖ ≤
                C * (|h| + |delta - deltaS| + |Phi - PhiS| + |nu|)) ∧
            (∀ j m : ℕ, ‖jacProd (tameDriftMap r h delta Phi nu rho)
                ((tameDriftMap r h delta Phi nu rho)^[j] y0) m‖ ≤ C * Real.exp (-(c * h * m))) := by
  obtain ⟨C, c, s, v0, hC, hc, hs, hv0, hgood⟩ := uniformize (X := TP) TP.h (TP.varrho deltaS PhiS)
    (TP.Adm deltaS PhiS)
    (TameGood r deltaS PhiS (dynamicCanonicalEquilibrium r deltaS PhiS) K)
    (fun ε => ⟨ε, deltaS, PhiS, 0, 0⟩)
    (fun ε hε h1 => by
      refine ⟨⟨by simp only [sub_self, abs_zero]; positivity, le_rfl, zero_le_one, ?_⟩, rfl, ?_⟩
      · simp [TP.varrho, abs_of_pos hε, h1]
      · simp [TP.varrho, abs_of_pos hε])
    (fun C c s C' c' s' x _ hh hC0 hC hc hs hg =>
      TameGood.mono r deltaS PhiS _ K C c s C' c' s' x hh hC hc hs hC0
        (TP.varrho_nonneg deltaS PhiS x) hg)
    (fun x _ hh => TP.h_le_varrho deltaS PhiS x hh.le)
    (fun F hF1 hF2 => tame_family r deltaS PhiS hr hd hP K hK hKphys hentry F hF1 hF2)
  refine ⟨C, c, min (min v0 1) (s / C), s, hC, hc, lt_min (lt_min hv0 one_pos) (by positivity),
    (min_le_left _ _).trans (min_le_right _ _), hs, ?_, ?_⟩
  · have : min (min v0 1) (s / C) ≤ s / C := min_le_right _ _
    rw [le_div_iff₀ hC] at this
    linarith
  intro h delta Phi nu rho hh hdelta hρ0 hρ1 hv
  have hv0' : |h| + |delta - deltaS| + |Phi - PhiS| + |nu| ≤ v0 :=
    hv.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hv1 : |h| + |delta - deltaS| + |Phi - PhiS| + |nu| ≤ 1 :=
    hv.trans ((min_le_left _ _).trans (min_le_right _ _))
  exact hgood ⟨h, delta, Phi, nu, rho⟩ ⟨hdelta, hρ0, hρ1, hv1⟩ hh hv0'


/-- v2 `cor:recursion`, decomposition on `closedBall ystar 1` (the statement of `T1` in the
form used by `RecursionSetup`): `‖e‖ <= K varrho` and `Lip(e) <= K varrho` on the unit ball
around any point `ystar`. -/
theorem tameDriftMap_decomposition_near (r deltaS PhiS : ℝ) (hd : 0 < deltaS) (hP : 0 ≤ PhiS)
    (ystar : DynamicState) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : TP, p.Adm deltaS PhiS →
      (∀ y : DynamicState, p.map r y =
        y + p.h • (dynamicField r deltaS PhiS y + p.err r deltaS PhiS y)) ∧
      ∀ y z : DynamicState, ‖y - ystar‖ ≤ 1 → ‖z - ystar‖ ≤ 1 →
        ‖p.err r deltaS PhiS y‖ ≤ K * p.varrho deltaS PhiS ∧
        ‖p.err r deltaS PhiS y - p.err r deltaS PhiS z‖ ≤
          K * p.varrho deltaS PhiS * ‖y - z‖ := by
  obtain ⟨K, hK0, hK⟩ := tameDriftMap_decomposition r deltaS PhiS hd hP (‖ystar‖ + 1)
  refine ⟨K, hK0, fun p hp => ⟨(hK p hp).1, fun y z hy hz => ?_⟩⟩
  have hb : ∀ w : DynamicState, ‖w - ystar‖ ≤ 1 → ‖w‖ ≤ ‖ystar‖ + 1 := fun w hw =>
    calc ‖w‖ = ‖(w - ystar) + ystar‖ := by simp
      _ ≤ ‖w - ystar‖ + ‖ystar‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  obtain ⟨h1, -, h3⟩ := (hK p hp).2 y z (hb y hy) (hb z hz)
  exact ⟨h1, h3⟩

/-- v2 `cor:recursion` (finite-horizon tracking and one-step consistency of `prop:LR34`, tame
coefficients): from a compact physical `K` with uniform entry, for every horizon `T` there are
`CT, varrhoT, C1 > 0` such that for `varrho <= varrhoT`, every solution `y` from `K` is tracked by
the orbit, `‖Psi^k y0 - y(k h)‖ <= CT varrho` for `k h <= T`, and
`‖y((k+1) h) - Psi(y(k h))‖ <= C1 h varrho` for all `k`.  These are the `htrack` and `hcons`
hypotheses of `drift_recursion_converges`. -/
theorem tameDriftMap_tracking (r deltaS PhiS : ℝ) (hd : 0 < deltaS) (hP : 0 ≤ PhiS)
    (ystar : DynamicState) (K : Set DynamicState) (hK : IsCompact K)
    (hKphys : ∀ y ∈ K, dynamicPhysical y)
    (hentry : UniformEntry (dynamicField r deltaS PhiS) ystar K) (T : ℝ) (hT : 0 ≤ T) :
    ∃ CT vT C1 : ℝ, 0 < CT ∧ 0 < vT ∧ 0 ≤ C1 ∧ ∀ p : TP, p.Adm deltaS PhiS → 0 ≤ p.h →
      p.varrho deltaS PhiS ≤ vT → ∀ y0 ∈ K, ∀ y : ℝ → DynamicState,
      IsODESol (dynamicField r deltaS PhiS) y0 y →
        (∀ k : ℕ, (k : ℝ) * p.h ≤ T →
          ‖(p.map r)^[k] y0 - y ((k : ℝ) * p.h)‖ ≤ CT * p.varrho deltaS PhiS) ∧
        (∀ k : ℕ, ‖y (((k + 1 : ℕ) : ℝ) * p.h) - p.map r (y ((k : ℝ) * p.h))‖ ≤
          C1 * p.h * p.varrho deltaS PhiS) := by
  obtain ⟨M0, hM00, hM0⟩ := solutions_uniform_bound r deltaS PhiS hd hP ystar K hK hKphys hentry
  obtain ⟨CT, vT, hCT, hvT, htr⟩ := tameDriftMap_tracking_of_bound r deltaS PhiS hd hP T M0 hT
  obtain ⟨C1, hC1, hcon⟩ := tameDriftMap_consistency_of_bound r deltaS PhiS hd hP M0
  refine ⟨CT, vT, C1, hCT, hvT, hC1, fun p hp hh hv y0 hy0 y hy => ⟨fun k hk => ?_, fun k => ?_⟩⟩
  · exact (htr p hp hh hv y0 y hy (fun t ht => hM0 y0 hy0 y hy t ht.1) k hk).1
  · exact hcon p hp hh y hy.2 (fun t ht => hM0 y0 hy0 y hy t ht) k

end
end SparseSGD.Logistic.V2
