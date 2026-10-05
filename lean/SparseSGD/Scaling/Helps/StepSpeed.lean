import SparseSGD.Scaling.Helps.ExactRate

/-!
# Step speed: `rho(F)`, the retention cap and the merged `lem:step_speed` (v2)

Paper labels (v2): `lem:step_speed` = `lem:helps-onecopy` (merged, `beta in [0,1)`),
`rem:retention-cap` (a), and the step-6 facts used by `critical-batch-v2`.

The spectral radius `rho(F)` of the mean matrix `F` (characteristic polynomial
`z^2 - (1+beta-w) z + beta`) is defined as `meanRadius beta w`, the maximal modulus of a root
of `meanRoots beta w`.  We prove

* finiteness / non-emptiness of the roots and attainment of the supremum;
* the closed forms (for `0 <= beta`, `t = 1 + beta - w`):
  `meanRadius = sqrt beta` if `t^2 <= 4 beta` and `(|t| + sqrt (t^2 - 4 beta)) / 2` otherwise;
* `beta <= meanRadius^2 <= stepRadius` (`0 <= beta < 1`, `0 <= w`, `0 <= u_n`), with
  `stepRadius = meanRadius^2` when `u_n = 0` (any `beta >= 0`);
* `1 - 4 eps Delta <= stepRadius` for `0 <= beta < 1` (the `beta = 0` case included);
* `meanRadius^2 = beta` iff `t^2 <= 4 beta` (`w = 1` at `beta = 0`);
* symmetry `w <-> 2(1+beta) - w`, monotonicity, and `meanRadius < 1`.

Caveat: the tex statement `Lambda <= ln(1/beta)` is only formalized for `0 < beta`
(`Real.log 0 = 0` in Lean; at `beta = 0` the tex value is `+infinity`, the bound is vacuous).
It is `perStepRate_le_neg_log_beta` of `ExactRate.lean`, cited in `lem_step_speed`.
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD

noncomputable section

/-! ### The roots of the mean matrix -/

/-- The eigenvalues of the mean matrix `F`: roots of `z^2 - (1+beta-w) z + beta`
(v2 `lem:step_speed`, definition of `rho(F)`). -/
def meanRoots (β w : ℝ) : Set ℂ :=
  {z : ℂ | z ^ 2 - (1 + (β : ℂ) - (w : ℂ)) * z + (β : ℂ) = 0}

/-- The spectral radius `rho(F)` of the mean matrix: maximal modulus of an eigenvalue
(v2 `lem:step_speed`). -/
def meanRadius (β w : ℝ) : ℝ := sSup (norm '' meanRoots β w)

/-- The mean quadratic as a polynomial over `ℂ`. -/
def meanPoly (β w : ℝ) : Polynomial ℂ :=
  Polynomial.C (1 : ℂ) * Polynomial.X ^ 2
    + Polynomial.C (-(1 + (β : ℂ) - (w : ℂ))) * Polynomial.X + Polynomial.C (β : ℂ)

theorem meanPoly_eval (β w : ℝ) (z : ℂ) :
    (meanPoly β w).eval z = z ^ 2 - (1 + (β : ℂ) - (w : ℂ)) * z + (β : ℂ) := by
  simp [meanPoly]; ring

theorem meanPoly_degree (β w : ℝ) : (meanPoly β w).degree = 2 :=
  Polynomial.degree_quadratic one_ne_zero

/-- v2 `lem:step_speed` (definition of `rho(F)`): the eigenvalue set is finite. -/
theorem meanRoots_finite (β w : ℝ) : (meanRoots β w).Finite := by
  have hn : meanPoly β w ≠ 0 := by
    intro h
    have := meanPoly_degree β w
    rw [h] at this
    simp at this
  have h := Polynomial.finite_setOfPred_isRoot hn
  simpa only [Polynomial.IsRoot, meanPoly_eval, meanRoots] using h

/-- v2 `lem:step_speed` (definition of `rho(F)`): the eigenvalue set is nonempty. -/
theorem meanRoots_nonempty (β w : ℝ) : (meanRoots β w).Nonempty := by
  obtain ⟨z, hz⟩ := Complex.exists_root (f := meanPoly β w)
    (by rw [meanPoly_degree]; norm_num)
  refine ⟨z, ?_⟩
  have h := hz
  rw [Polynomial.IsRoot.def, meanPoly_eval] at h
  exact h

/-- v2 `lem:step_speed`: the supremum defining `rho(F)` is attained. -/
theorem meanRadius_attained (β w : ℝ) : ∃ z ∈ meanRoots β w, ‖z‖ = meanRadius β w := by
  have hne := (meanRoots_nonempty β w).image norm
  have hfin := (meanRoots_finite β w).image norm
  obtain ⟨z, hz, h⟩ := hne.csSup_mem hfin
  exact ⟨z, hz, h⟩

/-- Every eigenvalue of `F` has modulus at most `meanRadius`. -/
theorem norm_le_meanRadius (β w : ℝ) {z : ℂ} (hz : z ∈ meanRoots β w) :
    ‖z‖ ≤ meanRadius β w :=
  le_csSup ((meanRoots_finite β w).image norm).bddAbove ⟨z, hz, rfl⟩

theorem meanRadius_nonneg (β w : ℝ) : 0 ≤ meanRadius β w := by
  obtain ⟨z, _, h⟩ := meanRadius_attained β w
  rw [← h]; exact norm_nonneg z

/-- A root of the mean quadratic is a real root or has `|z|^2 = beta`. -/
theorem meanRoot_cases (β w : ℝ) {z : ℂ} (hz : z ∈ meanRoots β w) :
    (∃ x : ℝ, z = (x : ℂ) ∧ x ^ 2 - (1 + β - w) * x + β = 0) ∨ ‖z‖ ^ 2 = β := by
  have hz' : z ^ 2 - (((1 + β - w : ℝ)) : ℂ) * z + (β : ℂ) = 0 := by
    have : z ^ 2 - (1 + (β : ℂ) - (w : ℂ)) * z + (β : ℂ) = 0 := hz
    push_cast
    exact this
  rcases quad_root_cases _ _ z hz' with him | hn
  · left
    have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
    refine ⟨z.re, hzr, ?_⟩
    rw [hzr] at hz'
    have := congrArg Complex.re hz'
    simpa [pow_two] using this
  · right; exact hn

/-- A real root `x` satisfies `(2x - t)^2 = t^2 - 4 beta`, `t = 1 + beta - w`. -/
theorem real_root_sq (β w x : ℝ) (h : x ^ 2 - (1 + β - w) * x + β = 0) :
    (2 * x - (1 + β - w)) ^ 2 = (1 + β - w) ^ 2 - 4 * β := by
  linear_combination 4 * h

/-- If `t^2 <= 4 beta` then every eigenvalue of `F` has `|z|^2 = beta`. -/
theorem meanRoot_norm_sq_of_le (β w : ℝ) (hD : (1 + β - w) ^ 2 ≤ 4 * β) {z : ℂ}
    (hz : z ∈ meanRoots β w) : ‖z‖ ^ 2 = β := by
  rcases meanRoot_cases β w hz with ⟨x, rfl, hx⟩ | h
  · have h1 := real_root_sq β w x hx
    have h2 : 2 * x - (1 + β - w) = 0 := by nlinarith [sq_nonneg (2 * x - (1 + β - w))]
    have h3 : (1 + β - w) ^ 2 = 4 * β := by
      have : (2 * x - (1 + β - w)) ^ 2 = 0 := by rw [h2]; ring
      linarith
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have : x = (1 + β - w) / 2 := by linarith
    rw [this]; nlinarith
  · exact h

/-- Upper bound on every eigenvalue modulus. -/
theorem meanRoot_norm_le_max (β w : ℝ) {z : ℂ} (hz : z ∈ meanRoots β w) :
    ‖z‖ ≤ max (Real.sqrt β)
      ((|1 + β - w| + Real.sqrt ((1 + β - w) ^ 2 - 4 * β)) / 2) := by
  rcases meanRoot_cases β w hz with ⟨x, rfl, hx⟩ | h
  · have h1 := real_root_sq β w x hx
    have hs : Real.sqrt ((1 + β - w) ^ 2 - 4 * β) = |2 * x - (1 + β - w)| := by
      rw [← h1, Real.sqrt_sq_eq_abs]
    refine le_trans ?_ (le_max_right _ _)
    rw [Complex.norm_real, Real.norm_eq_abs, hs]
    have := le_abs_self (2 * x - (1 + β - w))
    have := neg_abs_le (2 * x - (1 + β - w))
    have := le_abs_self (1 + β - w)
    have := neg_abs_le (1 + β - w)
    rw [abs_le]
    constructor <;> linarith
  · refine le_trans ?_ (le_max_left _ _)
    have : ‖z‖ = Real.sqrt β := by rw [← h, Real.sqrt_sq (norm_nonneg z)]
    rw [this]

theorem abs_le_two_sqrt (β t : ℝ) (hβ : 0 ≤ β) (h : t ^ 2 ≤ 4 * β) : |t| ≤ 2 * Real.sqrt β := by
  have e : (2 * Real.sqrt β) ^ 2 = 4 * β := by rw [mul_pow, Real.sq_sqrt hβ]; ring
  have h0 : 0 ≤ Real.sqrt β := Real.sqrt_nonneg _
  by_contra hc
  push Not at hc
  nlinarith [sq_abs t, abs_nonneg t]

theorem two_sqrt_lt_abs (β t : ℝ) (hβ : 0 ≤ β) (h : 4 * β < t ^ 2) : 2 * Real.sqrt β < |t| := by
  have e : (2 * Real.sqrt β) ^ 2 = 4 * β := by rw [mul_pow, Real.sq_sqrt hβ]; ring
  have h0 : 0 ≤ Real.sqrt β := Real.sqrt_nonneg _
  by_contra hc
  push Not at hc
  nlinarith [sq_abs t, abs_nonneg t]

/-- Main closed form (unified): for `0 <= beta`,
`rho(F) = max (sqrt beta) ((|t| + sqrt (t^2 - 4 beta)) / 2)` with `t = 1 + beta - w`
(Lean's `sqrt` of a negative number is `0`). -/
theorem meanRadius_eq_max (β w : ℝ) (hβ : 0 ≤ β) :
    meanRadius β w = max (Real.sqrt β)
      ((|1 + β - w| + Real.sqrt ((1 + β - w) ^ 2 - 4 * β)) / 2) := by
  apply le_antisymm
  · obtain ⟨z, hz, hn⟩ := meanRadius_attained β w
    rw [← hn]; exact meanRoot_norm_le_max β w hz
  · by_cases hD : (1 + β - w) ^ 2 ≤ 4 * β
    · obtain ⟨z, hz⟩ := meanRoots_nonempty β w
      have hn2 := meanRoot_norm_sq_of_le β w hD hz
      have hn : ‖z‖ = Real.sqrt β := by rw [← hn2, Real.sqrt_sq (norm_nonneg z)]
      have hs0 : Real.sqrt ((1 + β - w) ^ 2 - 4 * β) = 0 :=
        Real.sqrt_eq_zero_of_nonpos (by linarith)
      have ha := abs_le_two_sqrt β _ hβ hD
      refine max_le ?_ ?_
      · rw [← hn]; exact norm_le_meanRadius β w hz
      · rw [hs0]
        have := norm_le_meanRadius β w hz
        linarith
    · push Not at hD
      set t := 1 + β - w with ht
      set r := Real.sqrt (t ^ 2 - 4 * β) with hr
      have hr2 : r ^ 2 = t ^ 2 - 4 * β := Real.sq_sqrt (by linarith)
      have hr0 : 0 ≤ r := Real.sqrt_nonneg _
      have hlt := two_sqrt_lt_abs β t hβ hD
      have hsq : Real.sqrt β ≤ (|t| + r) / 2 := by linarith
      -- an explicit real root of maximal modulus
      have hroot : ∃ x : ℝ, x ^ 2 - t * x + β = 0 ∧ |x| = (|t| + r) / 2 := by
        by_cases ht0 : 0 ≤ t
        · refine ⟨(t + r) / 2, by nlinarith, ?_⟩
          rw [abs_of_nonneg (by linarith), abs_of_nonneg ht0]
        · push Not at ht0
          refine ⟨(t - r) / 2, by nlinarith, ?_⟩
          rw [abs_of_neg (by linarith), abs_of_neg ht0]; ring
      obtain ⟨x, hx, hxa⟩ := hroot
      have hxm : (x : ℂ) ∈ meanRoots β w := by
        show (x : ℂ) ^ 2 - (1 + (β : ℂ) - (w : ℂ)) * (x : ℂ) + (β : ℂ) = 0
        have := congrArg (fun y : ℝ => (y : ℂ)) hx
        simp only [Complex.ofReal_zero] at this
        push_cast at this
        rw [ht] at this
        push_cast at this
        linear_combination this
      have := norm_le_meanRadius β w hxm
      rw [Complex.norm_real, Real.norm_eq_abs, hxa] at this
      exact max_le (le_trans hsq this) this

/-- v2 `lem:step_speed`, closed form for `t^2 <= 4 beta`, `0 <= beta`:
`rho(F) = sqrt beta` (`t = 1 + beta - w`). -/
theorem meanRadius_of_le (β w : ℝ) (hβ : 0 ≤ β) (hD : (1 + β - w) ^ 2 ≤ 4 * β) :
    meanRadius β w = Real.sqrt β := by
  rw [meanRadius_eq_max β w hβ]
  have hs0 : Real.sqrt ((1 + β - w) ^ 2 - 4 * β) = 0 :=
    Real.sqrt_eq_zero_of_nonpos (by linarith)
  have ha := abs_le_two_sqrt β _ hβ hD
  rw [hs0]
  exact max_eq_left (by linarith)

/-- v2 `lem:step_speed`, closed form for `t^2 > 4 beta`, `0 <= beta`:
`rho(F) = (|t| + sqrt (t^2 - 4 beta)) / 2` (`t = 1 + beta - w`). -/
theorem meanRadius_of_gt (β w : ℝ) (hβ : 0 ≤ β) (hD : 4 * β < (1 + β - w) ^ 2) :
    meanRadius β w = (|1 + β - w| + Real.sqrt ((1 + β - w) ^ 2 - 4 * β)) / 2 := by
  rw [meanRadius_eq_max β w hβ]
  have hlt := two_sqrt_lt_abs β _ hβ hD
  have hr0 : 0 ≤ Real.sqrt ((1 + β - w) ^ 2 - 4 * β) := Real.sqrt_nonneg _
  exact max_eq_right (by linarith)

/-! ### (i) `beta <= rho(F)^2 <= rho(L)` -/

/-- v2 `lem:step_speed` (i) / `rem:retention-cap` (a): `beta <= rho(F)^2`
(any `w`, `0 <= beta`). -/
theorem beta_le_meanRadius_sq (β w : ℝ) (hβ : 0 ≤ β) : β ≤ meanRadius β w ^ 2 := by
  have h : Real.sqrt β ≤ meanRadius β w := by
    rw [meanRadius_eq_max β w hβ]; exact le_max_left _ _
  have := pow_le_pow_left₀ (Real.sqrt_nonneg β) h 2
  rwa [Real.sq_sqrt hβ] at this

/-- v2 `lem:step_speed` (i): `rho(F)^2 <= rho(T)` for `0 <= beta < 1`, `0 <= w`, `0 <= u_n`
(`T` is the linear part of `eq:L1`; `stepRadius p = rho(T)`). -/
theorem meanRadius_sq_le_stepRadius (p : Params) (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw : 0 ≤ p.w) (hun : 0 ≤ p.noise) : meanRadius p.beta p.w ^ 2 ≤ stepRadius p := by
  obtain ⟨z, hz, hn⟩ := meanRadius_attained p.beta p.w
  rw [← hn]
  rcases meanRoot_cases p.beta p.w hz with ⟨x, rfl, hx⟩ | h
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact sq_le_stepRadius_of_meanEig p hx hb0 hb1.le hw hun
  · rw [h]; exact beta_le_stepRadius p hb0 hb1.le hw hun

/-- v2 `lem:step_speed` (i), equality clause (`u_n = 0`): the noise-free `rho(T)` equals
`rho(F)^2`.  Valid for every `beta >= 0` (the tex clause `rho(T) = rho(F)^2 if u_n = 0`). -/
theorem stepRadius_noiseFree_eq_meanRadius_sq (p : Params) (hb0 : 0 ≤ p.beta)
    (hn : p.noise = 0) : stepRadius p = meanRadius p.beta p.w ^ 2 := by
  obtain ⟨b, w, un, a⟩ := p
  change un = 0 at hn
  subst hn
  change 0 ≤ b at hb0
  show stepRadius ⟨b, w, 0, a⟩ = meanRadius b w ^ 2
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (1 + b - w) ^ 2 - 2 * b := ⟨_, rfl⟩
  apply le_antisymm
  · obtain ⟨y, hy, hyn⟩ := stepRadius_attained ⟨b, w, 0, a⟩
    rw [← hyn]
    rw [mem_stepRoots_noiseFree b w a s hs] at hy
    rcases hy with h | h
    · subst h
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
      exact beta_le_meanRadius_sq b w hb0
    · obtain ⟨z, hz2⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < 2 by norm_num)
      subst hz2
      have hfac : (z ^ 2 + (b : ℂ) - (1 + (b : ℂ) - (w : ℂ)) * z)
          * (z ^ 2 + (b : ℂ) + (1 + (b : ℂ) - (w : ℂ)) * z) = 0 := by
        rw [hs] at h
        push_cast at h
        linear_combination h
      have hzn : ‖z ^ 2‖ = ‖z‖ ^ 2 := norm_pow z 2
      rw [hzn]
      have hle : ‖z‖ ≤ meanRadius b w := by
        rcases mul_eq_zero.1 hfac with h1 | h1
        · exact norm_le_meanRadius b w (show z ∈ meanRoots b w from by
            show z ^ 2 - (1 + (b : ℂ) - (w : ℂ)) * z + (b : ℂ) = 0
            linear_combination h1)
        · have : -z ∈ meanRoots b w := by
            show (-z) ^ 2 - (1 + (b : ℂ) - (w : ℂ)) * (-z) + (b : ℂ) = 0
            linear_combination h1
          have := norm_le_meanRadius b w this
          rwa [norm_neg] at this
      exact pow_le_pow_left₀ (norm_nonneg z) hle 2
  · obtain ⟨z, hz, hzn⟩ := meanRadius_attained b w
    rw [← hzn, ← norm_pow]
    have hz' : z ^ 2 - (1 + (b : ℂ) - (w : ℂ)) * z + (b : ℂ) = 0 := hz
    have hmem : z ^ 2 ∈ stepRoots (⟨b, w, 0, a⟩ : Params) := by
      rw [mem_stepRoots_noiseFree b w a s hs]
      right
      rw [hs]
      push_cast
      linear_combination (z ^ 2 + (b : ℂ) + (1 + (b : ℂ) - (w : ℂ)) * z) * hz'
    exact norm_le_stepRadius _ hmem

/-- v2 `lem:step_speed` (i), consequence: `Lambda <= -ln beta` for `0 < beta < 1`
(restated from `ExactRate.perStepRate_le_neg_log_beta`; not formalized at `beta = 0`
where `Lambda <= +infinity` is vacuous and `Real.log 0 = 0`). -/
theorem perStepRate_le_neg_log_beta' (p : Params) (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw : 0 < p.w) (hun : 0 ≤ p.noise) : perStepRate p ≤ -Real.log p.beta :=
  perStepRate_le_neg_log_beta p hb0 hb1 hw hun

/-! ### (ii) the curvature cap, `beta in [0,1)` -/

/-- v2 `lem:step_speed` (ii): for `0 <= beta < 1`, `w = eps^2 Delta > 0`, `u_n >= 0` and
`4 eps Delta < 1`: `1 - 4 eps Delta <= rho(T)` and `Lambda <= -ln (1 - 4 eps Delta)`.
`beta = 0` is included (there `eps = 1`, `Delta = w`); for `beta > 0` this is
`one_sub_four_le_stepRadius`. -/
theorem perStepRate_le_curvature_cap (p : Params) (Delta : ℝ) (hb0 : 0 ≤ p.beta)
    (hb1 : p.beta < 1) (hw : 0 < p.w) (hun : 0 ≤ p.noise)
    (hDelta : p.w = p.eps ^ 2 * Delta) (h4 : 4 * p.eps * Delta < 1) :
    1 - 4 * p.eps * Delta ≤ stepRadius p ∧
      perStepRate p ≤ -Real.log (1 - 4 * p.eps * Delta) := by
  rcases hb0.eq_or_lt with hb | hb
  · -- beta = 0
    have hb' : p.beta = 0 := hb.symm
    have he : p.eps = 1 := by simp [Params.eps, hb']
    rw [he] at hDelta h4 ⊢
    have hDw : Delta = p.w := by linarith
    rw [hDw] at h4 ⊢
    have hrad : 1 - 4 * 1 * p.w ≤ stepRadius p := by
      rw [stepRadius_beta_zero p hb', totalLoad_beta_zero p hb']
      refine le_trans ?_ (le_abs_self _)
      nlinarith [mul_nonneg hw.le hun, sq_nonneg p.w]
    refine ⟨hrad, ?_⟩
    unfold perStepRate
    have := Real.log_le_log (by linarith) hrad
    linarith
  · exact ⟨one_sub_four_le_stepRadius p Delta hb hb1 hw hun hDelta h4,
      (perStepRate_le_onecopy p Delta hb hb1 hw hun hDelta).2 h4⟩

/-- Bundle, v2 `lem:step_speed` = `lem:helps-onecopy` for `beta in [0,1)`:
(i) `beta <= rho(F)^2 <= rho(T)`, equality `rho(T) = rho(F)^2` when `u_n = 0`, and
`Lambda <= -ln beta` for `0 < beta`; (ii) the curvature cap when `4 eps Delta < 1`. -/
theorem lem_step_speed (p : Params) (Delta : ℝ) (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw : 0 < p.w) (hun : 0 ≤ p.noise) (hDelta : p.w = p.eps ^ 2 * Delta) :
    (p.beta ≤ meanRadius p.beta p.w ^ 2 ∧ meanRadius p.beta p.w ^ 2 ≤ stepRadius p ∧
      (p.noise = 0 → stepRadius p = meanRadius p.beta p.w ^ 2) ∧
      (0 < p.beta → perStepRate p ≤ -Real.log p.beta)) ∧
    (4 * p.eps * Delta < 1 →
      1 - 4 * p.eps * Delta ≤ stepRadius p ∧
        perStepRate p ≤ -Real.log (1 - 4 * p.eps * Delta)) :=
  ⟨⟨beta_le_meanRadius_sq p.beta p.w hb0,
    meanRadius_sq_le_stepRadius p hb0 hb1 hw.le hun,
    stepRadius_noiseFree_eq_meanRadius_sq p hb0,
    fun hb => perStepRate_le_neg_log_beta p hb hb1 hw hun⟩,
   perStepRate_le_curvature_cap p Delta hb0 hb1 hw hun hDelta⟩

/-! ### `rem:retention-cap` (a), `beta in [0,1)` -/

/-- v2 `rem:retention-cap` (a): for `0 <= beta`, `rho(F)^2 = beta` iff `(1+beta-w)^2 <= 4 beta`. -/
theorem meanRadius_sq_eq_beta_iff (β w : ℝ) (hβ : 0 ≤ β) :
    meanRadius β w ^ 2 = β ↔ (1 + β - w) ^ 2 ≤ 4 * β := by
  constructor
  · intro h
    by_contra hD
    push Not at hD
    rw [meanRadius_of_gt β w hβ hD] at h
    set t := 1 + β - w
    have hr2 : Real.sqrt (t ^ 2 - 4 * β) ^ 2 = t ^ 2 - 4 * β := Real.sq_sqrt (by linarith)
    have hr0 : 0 < Real.sqrt (t ^ 2 - 4 * β) := Real.sqrt_pos.2 (by linarith)
    nlinarith [sq_abs t, abs_nonneg t, mul_nonneg (abs_nonneg t) hr0.le]
  · intro hD
    rw [meanRadius_of_le β w hβ hD, Real.sq_sqrt hβ]

/-- v2 `rem:retention-cap` (a) at `beta = 0`: `rho(F)^2 = 0` iff `w = 1`. -/
theorem meanRadius_sq_eq_zero_iff (w : ℝ) : meanRadius 0 w ^ 2 = 0 ↔ w = 1 := by
  rw [meanRadius_sq_eq_beta_iff 0 w le_rfl]
  constructor
  · intro h
    have : (1 + 0 - w) ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    linarith
  · rintro rfl; norm_num

/-- v2 `rem:retention-cap` (a), noise-free radius form for `beta in [0,1)` (any `beta >= 0`):
`rho(T) = beta` iff `(1+beta-w)^2 <= 4 beta`; at `beta = 0` this is `w = 1`. -/
theorem stepRadius_noiseFree_eq_beta_iff_of_nonneg (beta w a : ℝ) (hb0 : 0 ≤ beta) :
    stepRadius (⟨beta, w, 0, a⟩ : Params) = beta ↔ (1 + beta - w) ^ 2 ≤ 4 * beta := by
  rw [stepRadius_noiseFree_eq_meanRadius_sq (⟨beta, w, 0, a⟩ : Params) hb0 rfl]
  exact meanRadius_sq_eq_beta_iff beta w hb0

/-! ### Step 6 facts: symmetry, monotonicity, `rho(F) < 1` -/

theorem mem_meanRoots_symm (β w : ℝ) (z : ℂ) :
    z ∈ meanRoots β (2 * (1 + β) - w) ↔ -z ∈ meanRoots β w := by
  show z ^ 2 - (1 + (β : ℂ) - ((2 * (1 + β) - w : ℝ) : ℂ)) * z + (β : ℂ) = 0 ↔
    (-z) ^ 2 - (1 + (β : ℂ) - (w : ℂ)) * (-z) + (β : ℂ) = 0
  push_cast
  constructor <;> intro h <;> linear_combination h

/-- v2 `critical-batch-v2` (step 6): `rho(F)` is symmetric under `w <-> 2(1+beta) - w`
(the roots are negated). -/
theorem meanRadius_symm (β w : ℝ) : meanRadius β (2 * (1 + β) - w) = meanRadius β w := by
  have himg : norm '' meanRoots β (2 * (1 + β) - w) = norm '' meanRoots β w := by
    ext r
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨-z, (mem_meanRoots_symm β w z).1 hz, norm_neg z⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨-z, (mem_meanRoots_symm β w (-z)).2 (by rwa [neg_neg]), norm_neg z⟩
  unfold meanRadius
  rw [himg]

/-- The profile `a |-> max (sqrt beta) ((a + sqrt (a^2 - 4 beta)) / 2)` is monotone on `a >= 0`. -/
theorem radProfile_mono (β a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    max (Real.sqrt β) ((a + Real.sqrt (a ^ 2 - 4 * β)) / 2)
      ≤ max (Real.sqrt β) ((b + Real.sqrt (b ^ 2 - 4 * β)) / 2) := by
  apply max_le_max le_rfl
  have : Real.sqrt (a ^ 2 - 4 * β) ≤ Real.sqrt (b ^ 2 - 4 * β) :=
    Real.sqrt_le_sqrt (by nlinarith)
  linarith

theorem meanRadius_eq_profile (β w : ℝ) (hβ : 0 ≤ β) :
    meanRadius β w = max (Real.sqrt β)
      ((|1 + β - w| + Real.sqrt (|1 + β - w| ^ 2 - 4 * β)) / 2) := by
  rw [meanRadius_eq_max β w hβ, sq_abs]

/-- v2 `critical-batch-v2` (step 6): `rho(F)` is antitone in `w` on `w <= 1 + beta`
(`0 <= beta`). -/
theorem meanRadius_antitoneOn_Iic (β : ℝ) (hβ : 0 ≤ β) :
    AntitoneOn (meanRadius β) (Set.Iic (1 + β)) := by
  intro w₁ h₁ w₂ h₂ h12
  have h1 : (w₁ : ℝ) ≤ 1 + β := h₁
  have h2 : (w₂ : ℝ) ≤ 1 + β := h₂
  rw [meanRadius_eq_profile β w₁ hβ, meanRadius_eq_profile β w₂ hβ,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + β - w₁),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + β - w₂)]
  exact radProfile_mono β _ _ (by linarith) (by linarith)

/-- v2 `critical-batch-v2` (step 6): `rho(F)` is monotone in `w` on `w >= 1 + beta`
(`0 <= beta`). -/
theorem meanRadius_monotoneOn_Ici (β : ℝ) (hβ : 0 ≤ β) :
    MonotoneOn (meanRadius β) (Set.Ici (1 + β)) := by
  intro w₁ h₁ w₂ h₂ h12
  have h1 : 1 + β ≤ w₁ := h₁
  have h2 : 1 + β ≤ w₂ := h₂
  rw [meanRadius_eq_profile β w₁ hβ, meanRadius_eq_profile β w₂ hβ,
    abs_of_nonpos (by linarith : 1 + β - w₁ ≤ 0),
    abs_of_nonpos (by linarith : 1 + β - w₂ ≤ 0)]
  exact radProfile_mono β _ _ (by linarith) (by linarith)

/-- v2 `critical-batch-v2` (step 6): `rho(F)` is antitone in `w` on `(0, 1 + beta]`. -/
theorem meanRadius_antitoneOn (β : ℝ) (hβ : 0 ≤ β) :
    AntitoneOn (meanRadius β) (Set.Ioc 0 (1 + β)) :=
  (meanRadius_antitoneOn_Iic β hβ).mono (fun _ h => h.2)

/-- v2 `critical-batch-v2` (step 6): `rho(F)` is monotone in `w` on `[1 + beta, 2 (1 + beta))`. -/
theorem meanRadius_monotoneOn (β : ℝ) (hβ : 0 ≤ β) :
    MonotoneOn (meanRadius β) (Set.Ico (1 + β) (2 * (1 + β))) :=
  (meanRadius_monotoneOn_Ici β hβ).mono (fun _ h => h.1)

/-- v2 `critical-batch-v2` (step 6): `rho(F) < 1` for `0 <= beta < 1`, `0 < w < 2 (1 + beta)`. -/
theorem meanRadius_lt_one (β w : ℝ) (hb0 : 0 ≤ β) (hb1 : β < 1) (hw : 0 < w)
    (hw2 : w < 2 * (1 + β)) : meanRadius β w < 1 := by
  have h1 := stepRadius_noiseFree_lt_one β w 0 hb0 hb1 hw hw2
  have h2 : stepRadius (⟨β, w, 0, 0⟩ : Params) = meanRadius β w ^ 2 :=
    stepRadius_noiseFree_eq_meanRadius_sq (⟨β, w, 0, 0⟩ : Params) hb0 rfl
  rw [h2] at h1
  have h0 := meanRadius_nonneg β w
  by_contra hc
  push Not at hc
  nlinarith

end

end SparseSGD.Scaling.Helps
