import SparseSGD.Logistic.V2.ActualInvariance

/-!
# v2 `cor:recursion` for the actual Gaussian-coefficient drift recursion

Final assembly of Corollary G.17 for `actualDriftMap` (the drift recursion with the actual
Gaussian coefficients), obtained from the tame template of `V2/RecursionTame.lean`:

* `ActualGood` / `ActualGood.mono`: the conclusion of `cor:recursion` for one parameter tuple
  `a : AP` (analogue of `TameGood`).
* `actual_family`: the conclusion along a one-parameter family `ε ↦ F ε` with step `h = ε` and
  `varrho → 0` (analogue of `tame_family`), using `AP_decomposition_near`,
  `AP_tracking_of_bound`, `AP_consistency_of_bound` and `AP_fderiv_le`.
* `uniformize_le`: the uniformization argument of `uniformize`, where the default family only
  needs `vr (dflt ε) ≤ 2 ε`.
* `cor_recursion_actual`: the uniform statement for the model parameters `AP.ofModel`.
* `cor_recursion_actual_dynamicDriftMap`: the same statement for orbits of `dynamicDriftMap`
  with realizing parameters `θ_k`.

The Gaussian Stein certificates `S1` (variance derivatives) and `S2` (physical invariance) are
explicit hypotheses, never axioms.
-/

namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic Metric Set
noncomputable section
set_option maxHeartbeats 1800000

/-- The conclusion of `cor:recursion` for one parameter tuple `a : AP` of the actual recursion:
a fixed point `y_h` within `C varrho` of `ystar`, unique in `closedBall ystar s`; exponential
convergence of every orbit from `K`; uniform tracking of every solution from `K`; and
exponential decay of the Jacobian products along every orbit from `K`. -/
def ActualGood (r deltaS PhiS : ℝ) (ystar : DynamicState) (K : Set DynamicState)
    (C c s : ℝ) (a : AP) : Prop :=
  ∃ yh : DynamicState, ‖yh - ystar‖ ≤ C * a.varrho deltaS PhiS ∧ a.map r yh = yh ∧
    (∀ z : DynamicState, ‖z - ystar‖ ≤ s → a.map r z = z → z = yh) ∧
    ∀ y0 ∈ K,
      (∀ k : ℕ, ‖(a.map r)^[k] y0 - yh‖ ≤ C * Real.exp (-(c * a.h * k))) ∧
      (∀ y : ℝ → DynamicState, IsODESol (dynamicField r deltaS PhiS) y0 y → ∀ k : ℕ,
        ‖(a.map r)^[k] y0 - y ((k : ℝ) * a.h)‖ ≤ C * a.varrho deltaS PhiS) ∧
      (∀ j m : ℕ, ‖jacProd (a.map r) ((a.map r)^[j] y0) m‖ ≤
        C * Real.exp (-(c * a.h * m)))

/-- Monotonicity of `ActualGood` in the constants (larger `C`, smaller `c`, smaller `s`). -/
theorem ActualGood.mono (r deltaS PhiS : ℝ) (ystar : DynamicState) (K : Set DynamicState)
    (C c s C' c' s' : ℝ) (a : AP) (hh : 0 < a.h) (hC : C ≤ C') (hc : c' ≤ c) (hs : s' ≤ s)
    (hC0 : 0 ≤ C) (hv : 0 ≤ a.varrho deltaS PhiS)
    (hg : ActualGood r deltaS PhiS ystar K C c s a) :
    ActualGood r deltaS PhiS ystar K C' c' s' a := by
  obtain ⟨yh, h1, h2, h3, h4⟩ := hg
  refine ⟨yh, h1.trans (mul_le_mul_of_nonneg_right hC hv), h2,
    fun z hz hzf => h3 z (hz.trans hs) hzf, fun y0 hy0 => ?_⟩
  obtain ⟨e1, e2, e3⟩ := h4 y0 hy0
  have hex : ∀ m : ℕ, C * Real.exp (-(c * a.h * m)) ≤ C' * Real.exp (-(c' * a.h * m)) := by
    intro m
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    apply mul_le_mul hC _ (Real.exp_pos _).le (hC0.trans hC)
    apply Real.exp_le_exp.2
    have : c' * a.h * m ≤ c * a.h * m := by gcongr
    linarith
  exact ⟨fun k => (e1 k).trans (hex k),
    fun y hy k => (e2 y hy k).trans (mul_le_mul_of_nonneg_right hC hv),
    fun j m => (e3 j m).trans (hex m)⟩

/-- v2 `cor:recursion` (actual coefficients), for a one-parameter family `ε ↦ F ε` of admissible
model-type parameter tuples with step `h = ε` and `varrho → 0` (`εbar = 1/2`).  The constants
depend on the family; the uniform form is `cor_recursion_actual`.  Copy of `tame_family` with
`AP_decomposition_near` (radius `r0` in place of `1`), `AP_tracking_of_bound`,
`AP_consistency_of_bound` and `AP_fderiv_le`. -/
theorem actual_family (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (S2 : SparseSGD.External.GaussianSteinCertificate 2)
    (r deltaS PhiS : ℝ) (hr : 0 < r) (hd : 0 < deltaS) (hP : 0 < PhiS)
    (K : Set DynamicState) (hK : IsCompact K) (hKphys : ∀ y ∈ K, dynamicPhysical y)
    (hentry : UniformEntry (dynamicField r deltaS PhiS)
      (dynamicCanonicalEquilibrium r deltaS PhiS) K)
    (F : ℝ → AP)
    (hF1 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      (F ε).Adm deltaS PhiS ∧ (F ε).Model ∧ (F ε).h = ε)
    (hF2 : ∀ v : ℝ, 0 < v → ∃ ε' : ℝ, 0 < ε' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε' → ε ≤ 1 / 2 →
      (F ε).varrho deltaS PhiS ≤ v) :
    ∃ C c s v0 : ℝ, 0 < C ∧ 0 < c ∧ 0 < s ∧ 0 < v0 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      (F ε).varrho deltaS PhiS ≤ v0 →
      ActualGood r deltaS PhiS (dynamicCanonicalEquilibrium r deltaS PhiS) K C c s (F ε) := by
  classical
  set ystar := dynamicCanonicalEquilibrium r deltaS PhiS with hystar
  have hS : dynamicField r deltaS PhiS ystar = 0 :=
    dynamicCanonicalEquilibrium_is_stationary r deltaS PhiS hr hd hP.le
  obtain ⟨A, P, c0, hc0, hPs, hge, hdec, hstrict⟩ :=
    tame_base_certificate r deltaS PhiS hr hd hP.le
  obtain ⟨K1', p0n, r0, hK1', hp0n, hr0, hnear⟩ :=
    AP_decomposition_near S1 r deltaS PhiS hr hd hP
  obtain ⟨M0, hM00, hM0⟩ := solutions_uniform_bound r deltaS PhiS hd hP.le ystar K hK hKphys hentry
  obtain ⟨Lf, p0f, hLf0, hp0f, hfd⟩ := AP_fderiv_le S1 r deltaS PhiS hr hd hP.le (M0 + 1)
  obtain ⟨C1, p0c, hC10, hp0c, hcon⟩ := AP_consistency_of_bound r deltaS PhiS hr hd hP.le M0
  set K1 : ℝ := max K1' 1 with hK1def
  have hK1one : 1 ≤ K1 := le_max_right _ _
  have hK1ge : K1' ≤ K1 := le_max_left _ _
  have hK1pos : 0 < K1 := by linarith
  set v1 : ℝ := min (min p0n p0c) p0f with hv1def
  have hv1pos : 0 < v1 := lt_min (lt_min hp0n hp0c) hp0f
  obtain ⟨ε1', hε1', hε1v⟩ := hF2 v1 hv1pos
  set εG : ℝ := min ε1' (1 / 2) with hεGdef
  have hεG0 : 0 < εG := lt_min hε1' (by norm_num)
  have hgood : ∀ ε : ℝ, 0 < ε → ε ≤ εG →
      (F ε).Adm deltaS PhiS ∧ (F ε).Model ∧ (F ε).h = ε ∧
        (F ε).varrho deltaS PhiS ≤ v1 ∧ ((F ε).p : ℝ) ≤ p0n ∧ ((F ε).p : ℝ) ≤ p0c ∧
        ((F ε).p : ℝ) ≤ p0f := by
    intro ε hε h1
    have h2 : ε ≤ 1 / 2 := h1.trans (min_le_right _ _)
    have h3 : ε ≤ ε1' := h1.trans (min_le_left _ _)
    obtain ⟨hadm, hmod, hh⟩ := hF1 ε hε h2
    have hv := hε1v ε hε h3 h2
    have hp := AP.p_le_varrho deltaS PhiS (F ε)
    exact ⟨hadm, hmod, hh, hv, hp.trans (hv.trans ((min_le_left _ _).trans (min_le_left _ _))),
      hp.trans (hv.trans ((min_le_left _ _).trans (min_le_right _ _))),
      hp.trans (hv.trans (min_le_right _ _))⟩
  let e' : ℝ → DynamicState → DynamicState :=
    fun ε => if ε ≤ εG then (F ε).err r deltaS PhiS else fun _ => 0
  let ρ' : ℝ → ℝ := fun ε => if ε ≤ εG then K1 * (F ε).varrho deltaS PhiS else ε
  have hρε : ∀ ε : ℝ, 0 < ε → ε ≤ ρ' ε := by
    intro ε hε
    by_cases h1 : ε ≤ εG
    · obtain ⟨hadm, hmod, hh, -⟩ := hgood ε hε h1
      have := AP.h_le_varrho deltaS PhiS (F ε) (by rw [hh]; exact hε.le)
      have hv := AP.varrho_nonneg deltaS PhiS (F ε)
      simp only [ρ', h1, ↓reduceIte]
      rw [hh] at this
      nlinarith
    · simp [ρ', h1]
  have he0 : ∀ ε : ℝ, 0 < ε → ∀ y : DynamicState, ‖y - ystar‖ ≤ r0 → ‖e' ε y‖ ≤ ρ' ε := by
    intro ε hε y hy
    by_cases h1 : ε ≤ εG
    · obtain ⟨hadm, hmod, hh, hv1, hpn, -⟩ := hgood ε hε h1
      have := (hnear (F ε) hadm hpn y y hy hy).1
      have hv := AP.varrho_nonneg deltaS PhiS (F ε)
      simp only [e', ρ', h1, ↓reduceIte]
      exact this.trans (by nlinarith)
    · simp [e', ρ', h1, hε.le]
  have he1 : ∀ ε : ℝ, 0 < ε → ∀ y z : DynamicState, ‖y - ystar‖ ≤ r0 → ‖z - ystar‖ ≤ r0 →
      ‖e' ε y - e' ε z‖ ≤ ρ' ε * ‖y - z‖ := by
    intro ε hε y z hy hz
    by_cases h1 : ε ≤ εG
    · obtain ⟨hadm, hmod, hh, hv1, hpn, -⟩ := hgood ε hε h1
      have := (hnear (F ε) hadm hpn y z hy hz).2.2.2
      have hv := AP.varrho_nonneg deltaS PhiS (F ε)
      simp only [e', ρ', h1, ↓reduceIte]
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
    · simp [e', ρ', h1]; positivity
  let H : RecursionSetup 5 :=
    { A := A, P := P, c := c0, hc := hc0, hPs := hPs, hge := hge, hdec := hdec,
      b := dynamicField r deltaS PhiS, ystar := ystar, hb0 := hS, hb := hstrict,
      e := e', ρ := ρ', r0 := r0, hr0 := hr0, hρε := hρε, he0 := he0, he1 := he1 }
  have hmap : ∀ ε : ℝ, 0 < ε → ε ≤ εG → driftMap H.b H.e ε = (F ε).map r := by
    intro ε hε h1
    funext y
    have hh := (hgood ε hε h1).2.2.1
    show y + ε • (dynamicField r deltaS PhiS y + (if ε ≤ εG then (F ε).err r deltaS PhiS
      else fun _ => 0) y) = (F ε).map r y
    simp only [h1, ↓reduceIte]
    rw [AP.map_eq r deltaS PhiS, hh]
  have hρG : ∀ ε : ℝ, ε ≤ εG → H.ρ ε = K1 * (F ε).varrho deltaS PhiS := by
    intro ε h1
    show (if ε ≤ εG then K1 * (F ε).varrho deltaS PhiS else ε) = _
    simp [h1]
  have hex : ∀ y0 ∈ K, ∃ y : ℝ → DynamicState, IsODESol H.b y0 y := by
    intro y0 hy0
    obtain ⟨y, hy0', hy, -⟩ := global_solution_exists r deltaS PhiS y0 hd hP.le (hKphys y0 hy0)
    exact ⟨y, hy0', hy⟩
  have hent : UniformEntry H.b H.ystar K := hentry
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
    obtain ⟨CT, vT, hCT, hvT, htr⟩ := AP_tracking_of_bound S2 r deltaS PhiS hr hd hP.le T M0 hT
    obtain ⟨ε', hε', hεv⟩ := hF2 vT hvT
    refine ⟨CT, min ε' εG, hCT, lt_min hε' hεG0, ?_⟩
    intro ε hε hεle y0 hy0 y hy k hk
    have h1 : ε ≤ εG := hεle.trans (min_le_right _ _)
    have h2 : ε ≤ ε' := hεle.trans (min_le_left _ _)
    have h3 : ε ≤ 1 / 2 := h1.trans (min_le_right _ _)
    obtain ⟨hadm, hmod, hh, -⟩ := hgood ε hε h1
    rw [hmap ε hε h1]
    have := (htr (F ε) hadm hmod (hεv ε hε h2 h3) y0 y (hKphys y0 hy0) hy
      (fun t ht => hM0 y0 hy0 y hy t ht.1) k (by rw [hh]; exact hk)).1
    rw [hh] at this
    rw [hρG ε h1]
    refine this.trans ?_
    have hv := AP.varrho_nonneg deltaS PhiS (F ε)
    nlinarith [mul_nonneg (mul_nonneg hCT.le hv) (sub_nonneg.2 hK1one)]
  have hcons : ∃ rc C1' εc : ℝ, 0 < rc ∧ 0 < C1' ∧ 0 < εc ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εc → ∀ y0 ∈ K, ∀ y : ℝ → DynamicState, IsODESol H.b y0 y →
        ∀ k : ℕ, ‖y (k * ε) - H.ystar‖ ≤ rc →
          ‖y (((k + 1 : ℕ) : ℝ) * ε) - driftMap H.b H.e ε (y (k * ε))‖ ≤ C1' * ε * H.ρ ε := by
    refine ⟨1, C1 + 1, εG, one_pos, by linarith, hεG0, ?_⟩
    intro ε hε h1 y0 hy0 y hy k _
    obtain ⟨hadm, hmod, hh, hv1, hpn, hpc, -⟩ := hgood ε hε h1
    rw [hmap ε hε h1]
    have := hcon (F ε) hadm hmod hpc y (by rw [hy.1]; exact hKphys y0 hy0) hy.2
      (fun t ht => hM0 y0 hy0 y hy t ht) k
    rw [hh] at this
    rw [hρG ε h1]
    refine this.trans ?_
    have hv := AP.varrho_nonneg deltaS PhiS (F ε)
    have h3 : 0 ≤ ε * (F ε).varrho deltaS PhiS := mul_nonneg hε.le hv
    nlinarith [mul_nonneg (mul_nonneg hC10 h3) (sub_nonneg.2 hK1one), mul_nonneg hK1pos.le h3]
  have hdb : ∀ y : DynamicState, ‖y - H.ystar‖ ≤ H.r0 → DifferentiableAt ℝ H.b y :=
    fun y _ => (contDiff_dynamicField r deltaS PhiS).differentiable (by simp) y
  have hde : ∀ ε : ℝ, 0 < ε → ∀ y : DynamicState, ‖y - H.ystar‖ ≤ H.r0 →
      DifferentiableAt ℝ (H.e ε) y ∧ ‖fderiv ℝ (H.e ε) y‖ ≤ H.ρ ε := by
    intro ε hε y hy
    by_cases h1 : ε ≤ εG
    · obtain ⟨hadm, hmod, hh, hv1, hpn, -⟩ := hgood ε hε h1
      obtain ⟨-, hdf, hder, -⟩ := hnear (F ε) hadm hpn y y hy hy
      have hv := AP.varrho_nonneg deltaS PhiS (F ε)
      have e1 : H.e ε = (F ε).err r deltaS PhiS := by
        show (if ε ≤ εG then (F ε).err r deltaS PhiS else fun _ => 0) = _
        simp [h1]
      rw [e1, hρG ε h1]
      exact ⟨hdf, hder.trans (by nlinarith)⟩
    · have e1 : H.e ε = fun _ => 0 := by
        show (if ε ≤ εG then (F ε).err r deltaS PhiS else fun _ => 0) = _
        simp [h1]
      have hρ : H.ρ ε = ε := by
        show (if ε ≤ εG then K1 * (F ε).varrho deltaS PhiS else ε) = _
        simp [h1]
      rw [e1, hρ]
      refine ⟨differentiableAt_const _, ?_⟩
      simp only [fderiv_fun_const, Pi.zero_apply, norm_zero]
      exact hε.le
  have hJ : ∀ T : ℝ, 0 ≤ T → ∃ L εL : ℝ, 0 ≤ L ∧ 0 < εL ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εL → ∀ y0 ∈ K, ∀ k : ℕ, (k : ℝ) * ε ≤ T →
        ‖fderiv ℝ (driftMap H.b H.e ε) ((driftMap H.b H.e ε)^[k] y0)‖ ≤ 1 + L * ε := by
    intro T hT
    obtain ⟨CT, vT, hCT, hvT, htr⟩ := AP_tracking_of_bound S2 r deltaS PhiS hr hd hP.le T M0 hT
    obtain ⟨ε', hε', hεv⟩ := hF2 vT hvT
    refine ⟨Lf, min ε' εG, hLf0, lt_min hε' hεG0, ?_⟩
    intro ε hε hεle y0 hy0 k hk
    have h1 : ε ≤ εG := hεle.trans (min_le_right _ _)
    have h2 : ε ≤ ε' := hεle.trans (min_le_left _ _)
    have h3 : ε ≤ 1 / 2 := h1.trans (min_le_right _ _)
    obtain ⟨hadm, hmod, hh, hv1, hpn, hpc, hpf⟩ := hgood ε hε h1
    rw [hmap ε hε h1]
    obtain ⟨y, hy⟩ := hex y0 hy0
    have htr' := (htr (F ε) hadm hmod (hεv ε hε h2 h3) y0 y (hKphys y0 hy0) hy
      (fun t ht => hM0 y0 hy0 y hy t ht.1) k (by rw [hh]; exact hk)).2
    rw [hh] at htr'
    set x := ((F ε).map r)^[k] y0 with hx
    have hxM : ‖x‖ ≤ M0 + 1 := by
      have hyk : ‖y ((k : ℝ) * ε)‖ ≤ M0 :=
        hM0 y0 hy0 y hy _ (by positivity)
      calc ‖x‖ = ‖(x - y ((k : ℝ) * ε)) + y ((k : ℝ) * ε)‖ := by simp
        _ ≤ ‖x - y ((k : ℝ) * ε)‖ + ‖y ((k : ℝ) * ε)‖ := norm_add_le _ _
        _ ≤ M0 + 1 := by linarith
    have := hfd (F ε) hadm (by rw [hh]; exact hε.le) hpf x hxM
    rwa [hh] at this
  obtain ⟨ε1, ρ1, C, c, hε1, hρ1, hC, hc, N, ⟨s, hs0, hsN⟩, -, hmain⟩ :=
    drift_recursion_converges H K hK hex hent hbdd htrack hcons
  obtain ⟨ε2, ρ2, Γ, c2, hε2, hρ2, hΓ, hc2, hjac⟩ :=
    jacobian_products H K hex hent htrack hdb hde hJ
  set Cf : ℝ := C * K1 + Γ with hCf
  have hCf0 : 0 < Cf := by positivity
  set cm : ℝ := min c c2 with hcm
  have hcm0 : 0 < cm := lt_min hc hc2
  refine ⟨Cf, cm, s, min (min (min ε1 ε2) (min (ρ1 / K1) (ρ2 / K1))) εG, hCf0, hcm0, hs0,
    lt_min (lt_min (lt_min hε1 hε2) (lt_min (by positivity) (by positivity))) hεG0, ?_⟩
  intro ε hε h1' hv
  have hvn := AP.varrho_nonneg deltaS PhiS (F ε)
  have hεv : ε ≤ (F ε).varrho deltaS PhiS := by
    have := AP.h_le_varrho deltaS PhiS (F ε) (by rw [(hF1 ε hε h1').2.2]; exact hε.le)
    rwa [(hF1 ε hε h1').2.2] at this
  have h1 : ε ≤ εG := hεv.trans (hv.trans (min_le_right _ _))
  obtain ⟨hadm, hmod, hh, -⟩ := hgood ε hε h1
  have hεε1 : ε ≤ ε1 :=
    hεv.trans (hv.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))))
  have hεε2 : ε ≤ ε2 :=
    hεv.trans (hv.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))))
  have hρ : H.ρ ε = K1 * (F ε).varrho deltaS PhiS := hρG ε h1
  have hρ1' : H.ρ ε ≤ ρ1 := by
    rw [hρ]
    have : (F ε).varrho deltaS PhiS ≤ ρ1 / K1 :=
      hv.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    rw [le_div_iff₀ hK1pos] at this
    linarith
  have hρ2' : H.ρ ε ≤ ρ2 := by
    rw [hρ]
    have : (F ε).varrho deltaS PhiS ≤ ρ2 / K1 :=
      hv.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    rw [le_div_iff₀ hK1pos] at this
    linarith
  obtain ⟨yε, hyN, hfix, huniq, hnear', hall⟩ := hmain ε hε hεε1 hρ1'
  have hmapε := hmap ε hε h1
  have hCρ : ∀ x : ℝ, 0 ≤ x → C * (K1 * x) ≤ Cf * x := by
    intro x hx
    rw [hCf]
    nlinarith [mul_nonneg hΓ.le hx]
  refine ⟨yε, ?_, ?_, ?_, ?_⟩
  · refine hnear'.trans ?_
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
      rw [hCf]; nlinarith [mul_nonneg hC.le (sub_nonneg.2 hK1one),
        mul_nonneg hC.le (zero_le_one.trans hK1one)]

/-- Uniformization (abstract), variant of `uniformize` with `εbar = 1/2` and a default family
satisfying only `vr (dflt ε) ≤ 2 ε`.  If `Good` holds with constants for every one-parameter
family `ε ↦ F ε` of admissible points with step `hh (F ε) = ε` and `vr (F ε) → 0`, then it
holds with one set of constants for all admissible points with `vr` small. -/
theorem uniformize_le {X : Type*} (hh vr : X → ℝ) (Adm : X → Prop)
    (Good : ℝ → ℝ → ℝ → X → Prop) (dflt : ℝ → X)
    (hdef : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Adm (dflt ε) ∧ hh (dflt ε) = ε ∧ vr (dflt ε) ≤ 2 * ε)
    (hmono : ∀ (C c s C' c' s' : ℝ) (x : X), Adm x → 0 < hh x → 0 ≤ C → C ≤ C' → c' ≤ c →
      s' ≤ s → Good C c s x → Good C' c' s' x)
    (hhv : ∀ x : X, Adm x → 0 < hh x → hh x ≤ vr x)
    (hfam : ∀ F : ℝ → X, (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Adm (F ε) ∧ hh (F ε) = ε) →
      (∀ v : ℝ, 0 < v → ∃ ε' : ℝ, 0 < ε' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε' → ε ≤ 1 / 2 →
        vr (F ε) ≤ v) →
      ∃ C c s v0 : ℝ, 0 < C ∧ 0 < c ∧ 0 < s ∧ 0 < v0 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
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
  have hF1 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Adm (F ε) ∧ hh (F ε) = ε := by
    intro ε hε h1
    by_cases h : ∃ n, hh (x n) = ε
    · have hc := Classical.choose_spec h
      have e : F ε = x (Classical.choose h) := by simp [F, h]
      rw [e]
      exact ⟨(hP _).1, hc⟩
    · have e : F ε = dflt ε := by simp [F, h]
      rw [e]
      exact ⟨(hdef ε hε h1).1, (hdef ε hε h1).2.1⟩
  have hF2 : ∀ v : ℝ, 0 < v → ∃ ε' : ℝ, 0 < ε' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε' → ε ≤ 1 / 2 →
      vr (F ε) ≤ v := by
    intro v hv
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / v)
    refine ⟨min (v / 2) (hh (x N)), lt_min (by positivity) (hP N).2.1, ?_⟩
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
      rw [e]
      refine (hdef ε hε h1).2.2.trans ?_
      have := hεle.trans (min_le_left _ _)
      linarith
  obtain ⟨C, c, s, v0, hC, hc, hs, hv0, hgood⟩ := hfam F hF1 hF2
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max (max C (1 / c)) (max (1 / s) (1 / v0))) 2)
  obtain ⟨hA, hpos, hvr, hbad⟩ := hP N
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hle : ∀ t : ℝ, t ≤ max (max (max C (1 / c)) (max (1 / s) (1 / v0))) 2 →
      t < (N : ℝ) + 1 :=
    fun t ht => by linarith
  have hCN : C ≤ (N : ℝ) + 1 :=
    (hle C (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _))).le
  have hcN : 1 / ((N : ℝ) + 1) ≤ c := by
    have := hle (1 / c) (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
    rw [div_lt_iff₀ hc] at this
    rw [div_le_iff₀ hN1]; linarith
  have hsN : 1 / ((N : ℝ) + 1) ≤ s := by
    have := hle (1 / s) (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
    rw [div_lt_iff₀ hs] at this
    rw [div_le_iff₀ hN1]; linarith
  have hvN : 1 / ((N : ℝ) + 1) ≤ v0 := by
    have := hle (1 / v0) (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
    rw [div_lt_iff₀ hv0] at this
    rw [div_le_iff₀ hN1]; linarith
  have h1N : 1 / ((N : ℝ) + 1) ≤ 1 / 2 := by
    have := hle 2 (le_max_right _ _)
    rw [div_le_div_iff₀ hN1 (by norm_num)]
    linarith
  have hh1 : hh (x N) ≤ 1 / 2 := (hhv _ hA hpos).trans (hvr.trans h1N)
  have hg := hgood (hh (x N)) hpos hh1 (by rw [hFx]; exact hvr.trans hvN)
  rw [hFx] at hg
  exact hbad (hmono C c s _ _ _ (x N) hA hpos hC.le hCN hcN hsN hg)

/-- v2 `cor:recursion` (actual Gaussian-coefficient drift recursion), uniform form.  For
`r, deltaS, PhiS > 0`, a compact physical set `K` with the uniform-entry property of the base
ODE, there are `C, c, v0, s > 0` such that for every model parameter tuple
`(d, B, eta, beta, p)` with `2 ≤ d`, `|eta p/(1-beta) - deltaS| ≤ deltaS/2` and
`varrho = (1-beta) + |eta p/(1-beta) - deltaS| + |Phi_{d,B}(eta) - PhiS| + p ≤ v0`, the map
`actualDriftMap` has a fixed point within `C varrho` of the equilibrium, unique in
`closedBall y* s`; orbits from `K` converge to it at rate `exp(-c (1-beta) k)`; they track every
ODE solution within `C varrho` at the times `k (1-beta)`; and the Jacobian products along the
orbit decay as `C exp(-c (1-beta) m)`.  The Gaussian Stein certificates `S1`, `S2` are
hypotheses. -/
theorem cor_recursion_actual
    (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (S2 : SparseSGD.External.GaussianSteinCertificate 2)
    (r deltaS PhiS : ℝ) (hr : 0 < r) (hd : 0 < deltaS) (hP : 0 < PhiS)
    (K : Set DynamicState) (hK : IsCompact K) (hKphys : ∀ y ∈ K, dynamicPhysical y)
    (hentry : UniformEntry (dynamicField r deltaS PhiS)
      (dynamicCanonicalEquilibrium r deltaS PhiS) K) :
    ∃ C c v0 s : ℝ, 0 < C ∧ 0 < c ∧ 0 < v0 ∧ v0 ≤ 1 ∧ 0 < s ∧ C * v0 ≤ s ∧
      ∀ (d B : ℕ) (eta beta : ℝ) (p : unitInterval), 2 ≤ d → 0 < B → 0 < eta → 0 < 1 - beta →
        0 < (p:ℝ) → |eta * (p:ℝ) / (1 - beta) - deltaS| ≤ deltaS / 2 →
        (1 - beta) + |eta * (p:ℝ) / (1 - beta) - deltaS| + |dynamicSourceLoad d B eta - PhiS| +
          (p:ℝ) ≤ v0 →
        ∃ yh : DynamicState,
          ‖yh - dynamicCanonicalEquilibrium r deltaS PhiS‖ ≤
            C * ((1 - beta) + |eta * (p:ℝ) / (1 - beta) - deltaS| +
              |dynamicSourceLoad d B eta - PhiS| + (p:ℝ)) ∧
          actualDriftMap d B eta beta p r yh = yh ∧
          (∀ z : DynamicState, ‖z - dynamicCanonicalEquilibrium r deltaS PhiS‖ ≤ s →
            actualDriftMap d B eta beta p r z = z → z = yh) ∧
          ∀ y0 ∈ K,
            (∀ k : ℕ, ‖(actualDriftMap d B eta beta p r)^[k] y0 - yh‖ ≤
              C * Real.exp (-(c * (1 - beta) * k))) ∧
            (∀ y : ℝ → DynamicState, IsODESol (dynamicField r deltaS PhiS) y0 y → ∀ k : ℕ,
              ‖(actualDriftMap d B eta beta p r)^[k] y0 - y ((k : ℝ) * (1 - beta))‖ ≤
                C * ((1 - beta) + |eta * (p:ℝ) / (1 - beta) - deltaS| +
                  |dynamicSourceLoad d B eta - PhiS| + (p:ℝ))) ∧
            (∀ j m : ℕ, ‖jacProd (actualDriftMap d B eta beta p r)
              ((actualDriftMap d B eta beta p r)^[j] y0) m‖ ≤
                C * Real.exp (-(c * (1 - beta) * m))) := by
  obtain ⟨dflt, hdflt⟩ : ∃ dflt : ℝ → AP, ∀ ε, dflt ε =
      ⟨ε, deltaS, PhiS, 0, 1, Set.projIcc (0 : ℝ) 1 zero_le_one (ε / 2)⟩ :=
    ⟨_, fun _ => rfl⟩
  have hpd : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ((dflt ε).p : ℝ) = ε / 2 := by
    intro ε hε h1
    rw [hdflt]
    exact congrArg Subtype.val
      (Set.projIcc_of_mem (zero_le_one' ℝ) (⟨by positivity, by linarith⟩ : ε / 2 ∈ Set.Icc (0 : ℝ) 1))
  have hdef : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ((dflt ε).Adm deltaS PhiS ∧ (dflt ε).Model) ∧ (dflt ε).h = ε ∧
        (dflt ε).varrho deltaS PhiS ≤ 2 * ε := by
    intro ε hε h1
    have hp := hpd ε hε h1
    have hk : (dflt ε).kappa = 2 * PhiS / deltaS := by simp [AP.kappa, hdflt]
    have hvv : (dflt ε).varrho deltaS PhiS = ε + ε / 2 := by
      simp [AP.varrho, hdflt, abs_of_pos hε]
      simpa [hdflt] using hp
    have hkpos : 0 ≤ 2 * PhiS / deltaS := by positivity
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
    · simp [hdflt]; positivity
    · simp [hdflt]
    · simp [hdflt]
    · simp [hdflt]
    · rw [hk]; simpa [hdflt] using hkpos
    · rw [hp]; positivity
    · rw [hp]; linarith
    · rw [hvv]; linarith
    · simp only [hdflt]; exact hε
    · simp [hdflt]
    · simp [hdflt]
    · rw [hvv]; linarith
  obtain ⟨C, c, s, v0, hC, hc, hs, hv0, hgood⟩ := uniformize_le (X := AP) AP.h
    (AP.varrho deltaS PhiS) (fun a => a.Adm deltaS PhiS ∧ a.Model)
    (ActualGood r deltaS PhiS (dynamicCanonicalEquilibrium r deltaS PhiS) K) dflt hdef
    (fun C c s C' c' s' x _ hh hC0 hC hc hs hg =>
      ActualGood.mono r deltaS PhiS _ K C c s C' c' s' x hh hC hc hs hC0
        (AP.varrho_nonneg deltaS PhiS x) hg)
    (fun x _ hh => AP.h_le_varrho deltaS PhiS x hh.le)
    (fun F hF1 hF2 => actual_family S1 S2 r deltaS PhiS hr hd hP K hK hKphys hentry F
      (fun ε hε h1 => ⟨(hF1 ε hε h1).1.1, (hF1 ε hε h1).1.2, (hF1 ε hε h1).2⟩) hF2)
  refine ⟨C, c, min (min v0 (1 / 2)) (s / C), s, hC, hc,
    lt_min (lt_min hv0 (by norm_num)) (by positivity),
    (min_le_left _ _).trans ((min_le_right _ _).trans (by norm_num)), hs, ?_, ?_⟩
  · have : min (min v0 (1 / 2)) (s / C) ≤ s / C := min_le_right _ _
    rw [le_div_iff₀ hC] at this
    linarith
  intro d B eta beta p hd2 hB heta hbeta hp hdel hv
  have hvar : (AP.ofModel d B eta beta p).varrho deltaS PhiS =
      (1 - beta) + |eta * (p:ℝ) / (1 - beta) - deltaS| + |dynamicSourceLoad d B eta - PhiS| +
        (p:ℝ) := by
    simp only [AP.varrho, AP.ofModel]
    rw [abs_of_pos hbeta]
  have hv0' : (AP.ofModel d B eta beta p).varrho deltaS PhiS ≤ v0 := by
    rw [hvar]; exact hv.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hv12 : (AP.ofModel d B eta beta p).varrho deltaS PhiS ≤ 1 / 2 := by
    rw [hvar]; exact hv.trans ((min_le_left _ _).trans (min_le_right _ _))
  obtain ⟨hw0, hwk⟩ := AP.ofModel_w_le_kappa d B eta beta p hd2 hB hp hbeta heta
  obtain ⟨hρ0, hρ1⟩ := AP.ofModel_rho d B eta beta p hB
  have hadm : (AP.ofModel d B eta beta p).Adm deltaS PhiS :=
    ⟨hdel, hρ0, hρ1, hw0, hwk, hp, (AP.p_le_varrho deltaS PhiS _).trans hv12,
      hv12.trans (by norm_num)⟩
  have hmod := AP.ofModel_model d B eta beta p hB hp hbeta
  have hmapeq := AP.ofModel_map d B eta beta p r hB heta.ne' hbeta.ne' hp.ne'
  have hg := hgood (AP.ofModel d B eta beta p) ⟨hadm, hmod⟩ hmod.1 hv0'
  have hhh : (AP.ofModel d B eta beta p).h = 1 - beta := rfl
  unfold ActualGood at hg
  rw [hmapeq, hhh, hvar] at hg
  exact hg

/-- Remark-level corollary of `cor_recursion_actual` for orbits of `dynamicDriftMap`: if
`x` is an orbit of `dynamicDriftMap` along parameters `theta k` whose summaries
(`signalCoord mu (theta k) = x k 0`, `‖theta k‖² = x k 0² + x k 2`) are realized, then it is an
orbit of `actualDriftMap` (`orbit_eq_actualDriftMap`), and it converges to the fixed point
`yh` of `cor_recursion_actual` at rate `C exp(-c (1-beta) k)`, for the base radius `r mu`. -/
theorem cor_recursion_actual_dynamicDriftMap
    (S1 : SparseSGD.External.GaussianSteinCertificate 1)
    (S2 : SparseSGD.External.GaussianSteinCertificate 2)
    (deltaS PhiS : ℝ) (hd : 0 < deltaS) (hP : 0 < PhiS) {d : ℕ} (mu : Vec d) (hr : 0 < r mu)
    (K : Set DynamicState) (hK : IsCompact K) (hKphys : ∀ y ∈ K, dynamicPhysical y)
    (hentry : UniformEntry (dynamicField (r mu) deltaS PhiS)
      (dynamicCanonicalEquilibrium (r mu) deltaS PhiS) K) :
    ∃ C c v0 s : ℝ, 0 < C ∧ 0 < c ∧ 0 < v0 ∧ v0 ≤ 1 ∧ 0 < s ∧ C * v0 ≤ s ∧
      ∀ (B : ℕ) (eta beta : ℝ) (p : unitInterval), 2 ≤ d → 0 < B → 0 < eta → 0 < 1 - beta →
        0 < (p:ℝ) → |eta * (p:ℝ) / (1 - beta) - deltaS| ≤ deltaS / 2 →
        (1 - beta) + |eta * (p:ℝ) / (1 - beta) - deltaS| + |dynamicSourceLoad d B eta - PhiS| +
          (p:ℝ) ≤ v0 →
        ∃ yh : DynamicState,
          ‖yh - dynamicCanonicalEquilibrium (r mu) deltaS PhiS‖ ≤
            C * ((1 - beta) + |eta * (p:ℝ) / (1 - beta) - deltaS| +
              |dynamicSourceLoad d B eta - PhiS| + (p:ℝ)) ∧
          ∀ (theta : ℕ → Vec d) (x : ℕ → DynamicState), x 0 ∈ K →
            (∀ k, signalCoord mu (theta k) = x k 0) → (∀ k, ‖theta k‖ ^ 2 = x k 0 ^ 2 + x k 2) →
            (∀ k, x (k + 1) = dynamicDriftMap (B := B) eta beta p mu (theta k) (x k)) →
            ∀ k : ℕ, ‖x k - yh‖ ≤ C * Real.exp (-(c * (1 - beta) * k)) := by
  obtain ⟨C, c, v0, s, hC, hc, hv0, hv1, hs, hCs, hmain⟩ :=
    cor_recursion_actual S1 S2 (r mu) deltaS PhiS hr hd hP K hK hKphys hentry
  refine ⟨C, c, v0, s, hC, hc, hv0, hv1, hs, hCs, ?_⟩
  intro B eta beta p hd2 hB heta hbeta hp hdel hv
  obtain ⟨yh, h1, -, -, h4⟩ := hmain d B eta beta p hd2 hB heta hbeta hp hdel hv
  refine ⟨yh, h1, ?_⟩
  intro theta x hx0 ht hq hx k
  have horb : ∀ k : ℕ, x k = (actualDriftMap d B eta beta p (r mu))^[k] (x 0) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [orbit_eq_actualDriftMap eta beta p mu theta x hr ht hq hx k,
        Function.iterate_succ_apply', ← ih]
  rw [horb k]
  exact (h4 (x 0) hx0).1 k

end
end SparseSGD.Logistic.V2
