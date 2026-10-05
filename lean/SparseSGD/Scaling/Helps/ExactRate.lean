import SparseSGD.Scaling.Helps.StepMatrix
import SparseSGD.Probability.LeastSquares.Stability

/-!
# Exact per-step bounds (momentum-helps appendix)

Paper labels: `rem:retention-cap` (a), the noise-free radius form, `lem:helps-sgd`,
`lem:helps-onecopy`.

Everything here is algebraic once the real-root lower bound
`le_stepRadius_of_stepCharPolyR_nonpos` (S6) of `StepMatrix.lean` is available; no Gelfand
formula is used.

* (E1, E2) retention cap: the noise perturbation of the characteristic polynomial is exactly
  `-2 w eps u_n z (z + beta)`, which is `<= 0` for real `z >= 0`; hence `beta <= radius`
  and `l^2 <= radius` for every real eigenvalue `l` of the mean matrix `F`.
* (E3) the noise-free radius is `beta` exactly on `(1 - sqrt beta)^2 <= w <= (1 + sqrt beta)^2`,
  and is `< 1` for `0 < w < 2 (1 + beta)`.
* (E4, E5) plain SGD (`beta = 0`), `lem:helps-sgd`.
* (E6) one copy, `lem:helps-onecopy`.

Hypotheses added to the tex statements are listed in the docstrings of the theorems.
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD

noncomputable section

/-! ### E1, E2: the retention cap (rem:retention-cap (a)) -/

/-- (E1) `rem:retention-cap` (a), first half: `beta <= stepRadius`, since
`stepCharPoly(beta) = -4 w (1-beta) u_n beta^2 <= 0`. -/
theorem stepCharPolyR_at_beta (beta w un : ℝ) :
    stepCharPolyR beta w un beta = -(4 * w * (1 - beta) * un * beta ^ 2) := by
  simp only [stepCharPolyR]; ring

/-- (E1) `rem:retention-cap` (a): `beta <= rho(L)`; hypotheses `0 <= beta <= 1`, `0 <= w`,
`0 <= u_n`. -/
theorem beta_le_stepRadius (p : Params) (hb0 : 0 ≤ p.beta) (hb1 : p.beta ≤ 1)
    (hw : 0 ≤ p.w) (hun : 0 ≤ p.noise) : p.beta ≤ stepRadius p := by
  apply le_stepRadius_of_stepCharPolyR_nonpos p hb0
  rw [stepCharPolyR_at_beta]
  have : 0 ≤ 4 * p.w * (1 - p.beta) * p.noise * p.beta ^ 2 := by
    have : 0 ≤ 1 - p.beta := by linarith
    positivity
  linarith

/-- The quartic identity behind (E2): with `t = 1 + beta - w`,
`(l^2)^2 - (t^2 - 2 beta) l^2 + beta^2 = (l^2 + beta - t l)(l^2 + beta + t l)`. -/
theorem quartic_factor (beta w l : ℝ) :
    (l ^ 2) ^ 2 - ((1 + beta - w) ^ 2 - 2 * beta) * l ^ 2 + beta ^ 2
      = (l ^ 2 + beta - (1 + beta - w) * l) * (l ^ 2 + beta + (1 + beta - w) * l) := by
  ring

/-- (E2) `rem:retention-cap` (a), second half: if `l` is a real eigenvalue of the mean matrix
`F` (a root of `l^2 - (1+beta-w) l + beta`), then `l^2 <= rho(L)`.  Hypotheses `0 <= beta <= 1`,
`0 <= w`, `0 <= u_n` (the tex lists `beta <= 1`; `0 <= beta` is needed for `l^2 + beta >= 0`). -/
theorem sq_le_stepRadius_of_meanEig (p : Params) {l : ℝ}
    (hl : l ^ 2 - (1 + p.beta - p.w) * l + p.beta = 0)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta ≤ 1) (hw : 0 ≤ p.w) (hun : 0 ≤ p.noise) :
    l ^ 2 ≤ stepRadius p := by
  apply le_stepRadius_of_stepCharPolyR_nonpos p (sq_nonneg l)
  have hq : (l ^ 2) ^ 2 - ((1 + p.beta - p.w) ^ 2 - 2 * p.beta) * l ^ 2 + p.beta ^ 2 = 0 := by
    have h0 : l ^ 2 + p.beta - (1 + p.beta - p.w) * l = 0 := by linarith
    rw [quartic_factor, h0, zero_mul]
  unfold stepCharPolyR
  rw [hq, mul_zero, zero_sub]
  have : 0 ≤ 2 * p.w * (1 - p.beta) * p.noise * l ^ 2 * (l ^ 2 + p.beta) := by
    have : 0 ≤ 1 - p.beta := by linarith
    positivity
  linarith

/-! ### E3: the noise-free radius -/

/-- A complex root of a real quadratic `z^2 - s z + q` is real or has `|z|^2 = q`. -/
theorem quad_root_cases (s q : ℝ) (z : ℂ) (h : z ^ 2 - (s : ℂ) * z + (q : ℂ) = 0) :
    z.im = 0 ∨ ‖z‖ ^ 2 = q := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  by_cases hi : z.im = 0
  · exact Or.inl hi
  · right
    have h2 : 2 * z.re - s = 0 := by
      have : z.im * (2 * z.re - s) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hi
      · exact h
    rw [Complex.sq_norm, Complex.normSq_apply]
    rw [show s = 2 * z.re by linarith] at hre
    linarith

/-- Membership in the root set of the noise-free step map; `s = (1+beta-w)^2 - 2 beta`. -/
theorem mem_stepRoots_noiseFree (beta w a s : ℝ) (hs : s = (1 + beta - w) ^ 2 - 2 * beta)
    (z : ℂ) :
    z ∈ stepRoots (⟨beta, w, 0, a⟩ : Params) ↔
      z = beta ∨ z ^ 2 - (s : ℂ) * z + ((beta ^ 2 : ℝ) : ℂ) = 0 := by
  have key : stepCharPoly beta w 0 z
      = (z - beta) * (z ^ 2 - (s : ℂ) * z + ((beta ^ 2 : ℝ) : ℂ)) := by
    simp only [stepCharPoly, hs]
    push_cast
    ring
  show stepCharPoly beta w 0 z = 0 ↔ _
  rw [key, mul_eq_zero, sub_eq_zero]

/-- `(1 + beta - w)^2 <= 4 beta` iff `(1 - sqrt beta)^2 <= w <= (1 + sqrt beta)^2`
(for `0 <= beta`). -/
theorem sq_le_four_iff (beta w : ℝ) (hb : 0 ≤ beta) :
    (1 + beta - w) ^ 2 ≤ 4 * beta ↔
      (1 - Real.sqrt beta) ^ 2 ≤ w ∧ w ≤ (1 + Real.sqrt beta) ^ 2 := by
  have hr : Real.sqrt beta ^ 2 = beta := Real.sq_sqrt hb
  have hr0 : 0 ≤ Real.sqrt beta := Real.sqrt_nonneg _
  set r := Real.sqrt beta with hrdef
  constructor
  · intro h
    have h' : (1 + beta - w) ^ 2 ≤ (2 * r) ^ 2 := by nlinarith
    obtain ⟨h1, h2⟩ := abs_le_of_sq_le_sq' h' (by linarith)
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    have e1 : 1 + beta - w - 2 * r ≤ 0 := by nlinarith
    have e2 : 0 ≤ 1 + beta - w + 2 * r := by nlinarith
    nlinarith [mul_nonpos_of_nonpos_of_nonneg e1 e2]

/-- If `(1+beta-w)^2 <= 4 beta` (and `0 < beta`), every root of the noise-free characteristic
polynomial has modulus `beta`. -/
theorem norm_root_noiseFree_eq (beta w a : ℝ) (hb : 0 < beta)
    (ht : (1 + beta - w) ^ 2 ≤ 4 * beta) {z : ℂ}
    (hz : z ∈ stepRoots (⟨beta, w, 0, a⟩ : Params)) : ‖z‖ = beta := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (1 + beta - w) ^ 2 - 2 * beta := ⟨_, rfl⟩
  rw [mem_stepRoots_noiseFree beta w a s hs] at hz
  rcases hz with h | h
  · subst h; simp [abs_of_pos hb]
  · rcases quad_root_cases s (beta ^ 2) z h with him | hn
    · have hzr : z = (z.re : ℂ) := by
        apply Complex.ext <;> simp [him]
      rw [hzr] at h
      have h2 : z.re ^ 2 - s * z.re + beta ^ 2 = 0 := by
        have := congrArg Complex.re h
        simpa [pow_two] using this
      have h3 : (2 * z.re - s) ^ 2 = (1 + beta - w) ^ 2 * ((1 + beta - w) ^ 2 - 4 * beta) := by
        rw [hs] at h2 ⊢; nlinarith
      have h4 : (1 + beta - w) ^ 2 * ((1 + beta - w) ^ 2 - 4 * beta) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
      have h5 : 2 * z.re - s = 0 := by nlinarith [sq_nonneg (2 * z.re - s)]
      have h6 : z.re ^ 2 = beta ^ 2 := by nlinarith
      rw [hzr, Complex.norm_real, Real.norm_eq_abs]
      have : |z.re| ^ 2 = beta ^ 2 := by rw [sq_abs]; exact h6
      nlinarith [abs_nonneg z.re]
    · nlinarith [norm_nonneg z]

/-- (E3) `rem:retention-cap`, radius form: for `0 < beta` (the tex's `beta < 1`, `w > 0` are not
needed),
the noise-free `rho(L)` equals `beta` iff `(1 - sqrt beta)^2 <= w <= (1 + sqrt beta)^2`. -/
theorem stepRadius_noiseFree_eq_beta_iff (beta w a : ℝ) (hb0 : 0 < beta) :
    stepRadius (⟨beta, w, 0, a⟩ : Params) = beta ↔
      (1 - Real.sqrt beta) ^ 2 ≤ w ∧ w ≤ (1 + Real.sqrt beta) ^ 2 := by
  rw [← sq_le_four_iff beta w hb0.le]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (1 + beta - w) ^ 2 - 2 * beta := ⟨_, rfl⟩
    have hs2 : 2 * beta < s := by rw [hs]; linarith
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = s ^ 2 - 4 * beta ^ 2 := ⟨_, rfl⟩
    have hDpos : 0 < D := by rw [hD]; nlinarith
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (s + Real.sqrt D) / 2 := ⟨_, rfl⟩
    have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hDpos.le
    have hsqpos : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
    have hroot : r ^ 2 - s * r + beta ^ 2 = 0 := by
      rw [hr]; nlinarith
    have hrb : beta < r := by rw [hr]; linarith
    have hmem : ((r : ℝ) : ℂ) ∈ stepRoots (⟨beta, w, 0, a⟩ : Params) := by
      rw [mem_stepRoots_noiseFree beta w a s hs]
      right
      have := congrArg (fun x : ℝ => (x : ℂ)) hroot
      simp only [Complex.ofReal_zero] at this
      push_cast at this ⊢
      linear_combination this
    have := norm_le_stepRadius (⟨beta, w, 0, a⟩ : Params) hmem
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
    linarith
  · intro ht
    obtain ⟨z, hz, hn⟩ := stepRadius_attained (⟨beta, w, 0, a⟩ : Params)
    rw [← hn]
    exact norm_root_noiseFree_eq beta w a hb0 ht hz

/-- (E3) For `0 <= beta < 1` and `0 < w < 2 (1 + beta)`, the noise-free radius is `< 1`
(the tex states it for `beta in (0,1)`; the proof also covers `beta = 0`). -/
theorem stepRadius_noiseFree_lt_one (beta w a : ℝ) (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (hw : 0 < w) (hw2 : w < 2 * (1 + beta)) :
    stepRadius (⟨beta, w, 0, a⟩ : Params) < 1 := by
  obtain ⟨z, hz, hn⟩ := stepRadius_attained (⟨beta, w, 0, a⟩ : Params)
  rw [← hn]
  have ht2 : (1 + beta - w) ^ 2 < (1 + beta) ^ 2 := by nlinarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (1 + beta - w) ^ 2 - 2 * beta := ⟨_, rfl⟩
  rw [mem_stepRoots_noiseFree beta w a s hs] at hz
  rcases hz with h | h
  · subst h
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]; exact hb1
  · rcases quad_root_cases s (beta ^ 2) z h with him | hn2
    · have hzr : z = (z.re : ℂ) := by
        apply Complex.ext <;> simp [him]
      rw [hzr] at h
      have h2 : z.re ^ 2 - s * z.re + beta ^ 2 = 0 := by
        have := congrArg Complex.re h
        simpa [pow_two] using this
      have hs1 : s < 2 := by rw [hs]; nlinarith
      have hs2 : -2 < s := by rw [hs]; nlinarith [sq_nonneg (1 + beta - w)]
      have hg1 : 0 < 1 - s + beta ^ 2 := by rw [hs]; nlinarith
      have hg2 : 0 < 1 + s + beta ^ 2 := by rw [hs]; nlinarith [sq_nonneg (1 + beta - w)]
      rw [hzr, Complex.norm_real, Real.norm_eq_abs]
      have hxlt : z.re < 1 := by
        by_contra hc
        push Not at hc
        nlinarith [mul_nonneg (sub_nonneg.2 hc) (show (0 : ℝ) ≤ z.re + 1 - s by linarith)]
      have hxgt : -1 < z.re := by
        by_contra hc
        push Not at hc
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ -(z.re + 1) by linarith)
          (show (0 : ℝ) ≤ -(z.re - 1 - s) by linarith)]
      rw [abs_lt]; exact ⟨hxgt, hxlt⟩
    · have hb2 : beta ^ 2 < 1 := by nlinarith
      nlinarith [norm_nonneg z]

/-! ### E4: plain SGD, `beta = 0` (lem:helps-sgd) -/

/-- (E4) `lem:helps-sgd`: at `beta = 0`, `stepCharPoly 0 w u_n z = z^2 (z - (1 - 2w(1-u)))`
with `u = u_n + w/2`. -/
theorem stepCharPoly_beta_zero (w un : ℝ) (z : ℂ) :
    stepCharPoly 0 w un z = z ^ 2 * (z - ((1 - 2 * w * (1 - (un + w / 2)) : ℝ) : ℂ)) := by
  simp only [stepCharPoly]
  push_cast
  ring

/-- At `beta = 0`, `u = u_n + w/2`. -/
theorem totalLoad_beta_zero (p : Params) (hb : p.beta = 0) :
    p.totalLoad = p.noise + p.w / 2 := by
  simp [Params.totalLoad, Params.curvature, hb]

/-- (E4) `lem:helps-sgd`: the `(1,1)` entry of the step map at `beta = 0` is
`R' = (1 - 2w(1-u)) R + 2 w * additive`. -/
theorem step_R_beta_zero (p : Params) (hb : p.beta = 0) (s : Moments) :
    (p.step s).R = (1 - 2 * p.w * (1 - p.totalLoad)) * s.R + 2 * p.w * p.additive := by
  rw [totalLoad_beta_zero p hb]
  simp [Params.step, Params.eps, hb]
  ring

/-- (E4) `lem:helps-sgd`: `rho(L) = |1 - 2w(1-u)|` at `beta = 0`. -/
theorem stepRadius_beta_zero (p : Params) (hb : p.beta = 0) :
    stepRadius p = |1 - 2 * p.w * (1 - p.totalLoad)| := by
  rw [totalLoad_beta_zero p hb]
  set c : ℝ := 1 - 2 * p.w * (1 - (p.noise + p.w / 2)) with hc
  have hroot : ∀ z : ℂ, z ∈ stepRoots p ↔ z ^ 2 * (z - (c : ℂ)) = 0 := by
    intro z
    show stepCharPoly p.beta p.w p.noise z = 0 ↔ _
    rw [hb, stepCharPoly_beta_zero]
  apply le_antisymm
  · obtain ⟨z, hz, hn⟩ := stepRadius_attained p
    rw [← hn]
    rcases mul_eq_zero.1 ((hroot z).1 hz) with h | h
    · have : z = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h
      rw [this]; simp
    · have : z = c := sub_eq_zero.1 h
      rw [this, Complex.norm_real, Real.norm_eq_abs]
  · have hmem : (c : ℂ) ∈ stepRoots p := (hroot _).2 (by simp)
    have := norm_le_stepRadius p hmem
    rwa [Complex.norm_real, Real.norm_eq_abs] at this

/-- (E4) The real inequality `w (1 - (u_n + w/2)) <= 1/2` for `w >= 0`, `u_n >= 0`. -/
theorem sgd_load_bound (w un : ℝ) (hw : 0 ≤ w) (hun : 0 ≤ un) :
    w * (1 - (un + w / 2)) ≤ 1 / 2 := by
  by_cases h : un < 1
  · nlinarith [sq_nonneg (w - (1 - un)), mul_pos (sub_pos.2 h) (show (0 : ℝ) < 1 - un + 1 by linarith)]
  · push Not at h
    nlinarith [mul_nonneg hw (sub_nonneg.2 h), sq_nonneg w]

/-- (E4) `lem:helps-sgd`: `w (1-u) <= 1/2` at `beta = 0` (`0 <= w`, `0 <= u_n`). -/
theorem w_mul_one_sub_load_le_half (p : Params) (hb : p.beta = 0) (hw : 0 ≤ p.w)
    (hun : 0 ≤ p.noise) : p.w * (1 - p.totalLoad) ≤ 1 / 2 := by
  rw [totalLoad_beta_zero p hb]; exact sgd_load_bound _ _ hw hun

/-- (E4) `lem:helps-sgd`: for `beta = 0`, `w > 0`, `u_n >= 0`: `rho(L) < 1` iff `u < 1`. -/
theorem stepRadius_lt_one_iff_beta_zero (p : Params) (hb : p.beta = 0) (hw : 0 < p.w)
    (hun : 0 ≤ p.noise) : stepRadius p < 1 ↔ p.totalLoad < 1 := by
  rw [stepRadius_beta_zero p hb]
  have hle := w_mul_one_sub_load_le_half p hb hw.le hun
  rw [abs_lt]
  constructor
  · rintro ⟨_, h⟩
    by_contra hc
    push Not at hc
    have : p.w * (1 - p.totalLoad) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hw.le (by linarith)
    linarith
  · intro h
    have : 0 < p.w * (1 - p.totalLoad) := mul_pos hw (by linarith)
    constructor <;> linarith

/-- (E4) `lem:helps-sgd`: if `beta = 0`, `w > 0`, `u_n >= 0` and `u < 1`, then
`0 <= 1 - 2w(1-u) < 1`, and the per-step rate is `-log (1 - 2w(1-u))`. -/
theorem sgd_coeff_bounds (p : Params) (hb : p.beta = 0) (hw : 0 < p.w) (hun : 0 ≤ p.noise)
    (hu : p.totalLoad < 1) :
    0 ≤ 1 - 2 * p.w * (1 - p.totalLoad) ∧ 1 - 2 * p.w * (1 - p.totalLoad) < 1 ∧
      perStepRate p = -Real.log (1 - 2 * p.w * (1 - p.totalLoad)) := by
  have hle := w_mul_one_sub_load_le_half p hb hw.le hun
  have hpos : 0 < p.w * (1 - p.totalLoad) := mul_pos hw (by linarith)
  have h0 : 0 ≤ 1 - 2 * p.w * (1 - p.totalLoad) := by linarith
  refine ⟨h0, by linarith, ?_⟩
  unfold perStepRate
  rw [stepRadius_beta_zero p hb, abs_of_nonneg h0]

/-! ### E5: least squares at `beta = 0` -/

section LS

open SparseSGD.Probability.LeastSquares MeasureTheory

/-- (E5) `w = eta * p` for LS at `beta = 0`. -/
theorem ls_params_w_beta_zero (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (eta : ℝ) :
    (params d B p ν 0 eta).w = eta * p := by
  simp [params, oracleParams]

/-- (E5) `noise = eta (d + 2 - p)/(2B)` for LS at `beta = 0` (`0 < p`). -/
theorem ls_params_noise_beta_zero (d B : ℕ) (p : unitInterval) (hp : (p : ℝ) ≠ 0)
    (ν : Measure ℝ) (eta : ℝ) :
    (params d B p ν 0 eta).noise = eta * (((d : ℝ) + 2 - p) / (2 * B)) := by
  simp only [params, oracleParams, vinc]
  by_cases hB : (B : ℝ) = 0
  · simp [hB]
  · field_simp

/-- (E5) `lem:helps-sgd` (LS part): `u = eta / eta_+(0)`. -/
theorem ls_totalLoad_beta_zero (d B : ℕ) (p : unitInterval) (hp : (p : ℝ) ≠ 0)
    (ν : Measure ℝ) (eta : ℝ) :
    (params d B p ν 0 eta).totalLoad = eta / criticalRate d B p 0 := by
  rw [params_totalLoad d B p hp, criticalRate, div_inv_eq_mul]

/-- (E5) `lem:helps-sgd` (LS part): `2 w (1-u) = 2 eta p (1 - eta/eta_+(0))`. -/
theorem ls_two_w_one_sub_load (d B : ℕ) (p : unitInterval) (hp : (p : ℝ) ≠ 0)
    (ν : Measure ℝ) (eta : ℝ) :
    2 * (params d B p ν 0 eta).w * (1 - (params d B p ν 0 eta).totalLoad)
      = 2 * eta * p * (1 - eta / criticalRate d B p 0) := by
  rw [ls_params_w_beta_zero, ls_totalLoad_beta_zero d B p hp]; ring

/-- (E5) `lem:helps-sgd` (LS part): over `eta in (0, eta_+(0))` the supremum of `2w(1-u)` is
attained, equals `p eta_+(0) / 2`, at `eta = eta_+(0)/2`, and this value is `< 1`.
Hypotheses `0 < B`, `0 < p`. -/
theorem ls_beta_zero_sup (d B : ℕ) (hB : 0 < B) (p : unitInterval) (hp : 0 < (p : ℝ))
    (ν : Measure ℝ) :
    IsGreatest ((fun eta : ℝ => 2 * (params d B p ν 0 eta).w * (1 - (params d B p ν 0 eta).totalLoad))
        '' Set.Ioo 0 (criticalRate d B p 0)) ((p : ℝ) * criticalRate d B p 0 / 2) ∧
      (p : ℝ) * criticalRate d B p 0 / 2 < 1 := by
  have hp' : (p : ℝ) ≠ 0 := hp.ne'
  have hi : 0 < inverseCriticalRate d B p 0 :=
    inverseCriticalRate_pos d B hB p 0 le_rfl zero_lt_one
  set i := inverseCriticalRate d B p 0 with hidef
  have hc : criticalRate d B p 0 = i⁻¹ := rfl
  have hcpos : 0 < criticalRate d B p 0 := by rw [hc]; exact inv_pos.2 hi
  refine ⟨⟨⟨criticalRate d B p 0 / 2, ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only
    rw [ls_two_w_one_sub_load d B p hp']
    field_simp
    ring
  · rintro y ⟨eta, ⟨he0, he1⟩, rfl⟩
    simp only
    rw [ls_two_w_one_sub_load d B p hp', hc, div_inv_eq_mul]
    have key : (p : ℝ) * i⁻¹ / 2 - 2 * eta * p * (1 - eta * i)
        = p * (1 - 2 * eta * i) ^ 2 / (2 * i) := by
      field_simp
      ring
    have : 0 ≤ (p : ℝ) * (1 - 2 * eta * i) ^ 2 / (2 * i) := by positivity
    linarith
  · have hB' : (0 : ℝ) < B := by exact_mod_cast hB
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hp1 : (p : ℝ) ≤ 1 := p.2.2
    have hfirst : 0 < ((d : ℝ) + 2 - p) / (2 * B) := div_pos (by linarith) (by positivity)
    have hip : (p : ℝ) / 2 < i := by
      rw [hidef]; unfold inverseCriticalRate; simp only [sub_zero, add_zero, div_one, mul_one]
      linarith
    rw [hc]
    have : (p : ℝ) * i⁻¹ / 2 = ((p : ℝ) / 2) / i := by field_simp
    rw [this, div_lt_one hi]
    exact hip

end LS

/-! ### E6: one copy (lem:helps-onecopy) -/

/-- (E6) `lem:helps-onecopy`, first half: `Lambda <= -log beta` (`= ebar`), for `0 < beta < 1`,
`w > 0`, `u_n >= 0`. -/
theorem perStepRate_le_neg_log_beta (p : Params) (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw : 0 < p.w) (hun : 0 ≤ p.noise) : perStepRate p ≤ -Real.log p.beta := by
  have h := beta_le_stepRadius p hb0.le hb1.le hw.le hun
  unfold perStepRate
  have := Real.log_le_log hb0 h
  linarith

/-- (E6) `f(1 - 2 eps Delta) = -eps^2 Delta (1 - (4 - 2 eps) Delta)` for
`f(l) = l^2 - (1 + beta - w) l + beta`, `beta = 1 - eps`, `w = eps^2 Delta`. -/
theorem meanChar_at_one_sub (eps Delta : ℝ) :
    (1 - 2 * eps * Delta) ^ 2 - (1 + (1 - eps) - eps ^ 2 * Delta) * (1 - 2 * eps * Delta)
        + (1 - eps) = -(eps ^ 2 * Delta * (1 - (4 - 2 * eps) * Delta)) := by
  ring

/-- (E6) `lem:helps-onecopy`: if `(4 - 2 eps) Delta < 1` (`0 < eps < 1`, `0 < Delta`), the mean
matrix `F` has a real eigenvalue in `(1 - 2 eps Delta, 1)` (IVT: `f(1) = w > 0 > f(1 - 2 eps Delta)`). -/
theorem exists_real_meanEig_Ioo (eps Delta : ℝ) (he0 : 0 < eps) (hD : 0 < Delta)
    (h : (4 - 2 * eps) * Delta < 1) :
    ∃ l : ℝ, 1 - 2 * eps * Delta < l ∧ l < 1 ∧
      l ^ 2 - (1 + (1 - eps) - eps ^ 2 * Delta) * l + (1 - eps) = 0 := by
  set f : ℝ → ℝ := fun l => l ^ 2 - (1 + (1 - eps) - eps ^ 2 * Delta) * l + (1 - eps) with hf
  have hcont : ContinuousOn f (Set.Icc (1 - 2 * eps * Delta) 1) := by
    have : Continuous f := by rw [hf]; fun_prop
    exact this.continuousOn
  have hf1 : f 1 = eps ^ 2 * Delta := by rw [hf]; ring
  have hfa : f (1 - 2 * eps * Delta) = -(eps ^ 2 * Delta * (1 - (4 - 2 * eps) * Delta)) := by
    rw [hf]; exact meanChar_at_one_sub eps Delta
  have hpos : 0 < eps ^ 2 * Delta := by positivity
  have hneg : f (1 - 2 * eps * Delta) < 0 := by
    rw [hfa]
    have : 0 < eps ^ 2 * Delta * (1 - (4 - 2 * eps) * Delta) :=
      mul_pos hpos (by linarith)
    linarith
  have hab : 1 - 2 * eps * Delta ≤ 1 := by nlinarith [mul_pos he0 hD]
  have hmem : (0 : ℝ) ∈ Set.Icc (f (1 - 2 * eps * Delta)) (f 1) := ⟨hneg.le, by rw [hf1]; exact hpos.le⟩
  obtain ⟨l, ⟨hl1, hl2⟩, hl0⟩ := intermediate_value_Icc hab hcont hmem
  refine ⟨l, ?_, ?_, hl0⟩
  · refine lt_of_le_of_ne hl1 ?_
    rintro rfl
    linarith
  · refine lt_of_le_of_ne hl2 ?_
    rintro rfl
    rw [hf1] at hl0
    linarith

/-- (E6) `lem:helps-onecopy`, second half, radius form: for `beta = 1 - eps in (0,1)`,
`w = eps^2 Delta > 0`, `u_n >= 0` and `4 eps Delta < 1`, `1 - 4 eps Delta <= rho(L)`. -/
theorem one_sub_four_le_stepRadius (p : Params) (Delta : ℝ) (hb0 : 0 < p.beta)
    (hb1 : p.beta < 1) (hw : 0 < p.w) (hun : 0 ≤ p.noise) (hDelta : p.w = p.eps ^ 2 * Delta)
    (h4 : 4 * p.eps * Delta < 1) : 1 - 4 * p.eps * Delta ≤ stepRadius p := by
  have hbe : p.beta = 1 - p.eps := by simp [Params.eps]
  have he0 : 0 < p.eps := by simp only [Params.eps]; linarith
  have he1 : p.eps < 1 := by simp only [Params.eps]; linarith
  have hD : 0 < Delta := by
    have : 0 < p.eps ^ 2 * Delta := hDelta ▸ hw
    exact (mul_pos_iff_of_pos_left (by positivity)).1 this
  have hbr := beta_le_stepRadius p hb0.le hb1.le hw.le hun
  by_cases hc : (4 - 2 * p.eps) * Delta < 1
  · obtain ⟨l, hl1, hl2, hl0⟩ := exists_real_meanEig_Ioo p.eps Delta he0 hD hc
    have hl0' : l ^ 2 - (1 + p.beta - p.w) * l + p.beta = 0 := by
      rw [hbe, hDelta]; exact hl0
    have h2 := sq_le_stepRadius_of_meanEig p hl0' hb0.le hb1.le hw.le hun
    have hpos : 0 < 1 - 2 * p.eps * Delta := by linarith
    nlinarith [sq_nonneg (2 * p.eps * Delta)]
  · push Not at hc
    have : p.eps ≤ 4 * p.eps * Delta := by
      nlinarith [mul_pos he0 hD, mul_pos (mul_pos he0 he0) hD]
    linarith

/-- (E6) `lem:helps-onecopy`: for `beta = 1 - eps in (0,1)`, `w = eps^2 Delta > 0`, `u_n >= 0`:
`Lambda <= -log beta`, and if `4 eps Delta < 1` also `Lambda <= -log (1 - 4 eps Delta)`. -/
theorem perStepRate_le_onecopy (p : Params) (Delta : ℝ) (hb0 : 0 < p.beta)
    (hb1 : p.beta < 1) (hw : 0 < p.w) (hun : 0 ≤ p.noise) (hDelta : p.w = p.eps ^ 2 * Delta) :
    perStepRate p ≤ -Real.log p.beta ∧
      (4 * p.eps * Delta < 1 → perStepRate p ≤ -Real.log (1 - 4 * p.eps * Delta)) := by
  refine ⟨perStepRate_le_neg_log_beta p hb0 hb1 hw hun, fun h4 => ?_⟩
  have h := one_sub_four_le_stepRadius p Delta hb0 hb1 hw hun hDelta h4
  unfold perStepRate
  have := Real.log_le_log (by linarith) h
  linarith

end

end SparseSGD.Scaling.Helps
