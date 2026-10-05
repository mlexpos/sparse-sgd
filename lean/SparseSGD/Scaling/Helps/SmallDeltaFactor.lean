import Mathlib
import SparseSGD.Scaling.Helps.ExactRate
import SparseSGD.Scaling.Helps.RootPerturbation

/-!
# `lem:small_delta`, part 2: the quadratic factor and the rightmost eigenvalue

Formalizes the "other roots" step of the proof of `lem:small_delta` in
`paper/appendix/momentum_helps.tex`.  Let `f(z) = z^3 + a2 z^2 + a1 z + a0` with
`|a2 - 3| ≤ 0.024`, `1.97 ≤ a1 ≤ 2.11`, `0 < a0 ≤ 0.08`, and let `z_s` be a real root with
`-0.06 ≤ z_s ≤ 0`.  Then `f(z) = (z - z_s)(z^2 + b z + c)` with `b = a2 + z_s`,
`c = a1 + z_s b`; the roots of the quadratic have real part `≤ -0.7` and modulus `≤ 3.1`, and
for `0 < ε ≤ 1/50` the rightmost eigenvalue `1 + ε z` of the step matrix is the slow one.
-/

namespace SparseSGD.Scaling.Helps

noncomputable section

/-- `b = a2 + z_s`, the linear coefficient of the quadratic factor. -/
def slowFactorB (a2 zs : ℝ) : ℝ := a2 + zs

/-- `c = a1 + z_s b`, the constant coefficient of the quadratic factor. -/
def slowFactorC (a2 a1 zs : ℝ) : ℝ := a1 + zs * (a2 + zs)

/-- (F1) v2 `lem:small_delta` (factorization): the cubic factors through its slow root, and the
quadratic factor has coefficients `2.9 ≤ b ≤ 3.03`, `1.78 ≤ c ≤ 2.11`. -/
theorem cubic_factor_slow (a2 a1 a0 zs : ℝ)
    (h2 : |a2 - 3| ≤ 0.024) (h1l : 1.97 ≤ a1) (h1u : a1 ≤ 2.11) (_h0 : 0 < a0) (_h0' : a0 ≤ 0.08)
    (hzs : zs ^ 3 + a2 * zs ^ 2 + a1 * zs + a0 = 0) (hz1 : -0.06 ≤ zs) (hz2 : zs ≤ 0) :
    (∀ z : ℂ, z ^ 3 + (a2 : ℂ) * z ^ 2 + (a1 : ℂ) * z + (a0 : ℂ) =
        (z - (zs : ℂ)) * (z ^ 2 + (slowFactorB a2 zs : ℂ) * z + (slowFactorC a2 a1 zs : ℂ))) ∧
      2.9 ≤ slowFactorB a2 zs ∧ slowFactorB a2 zs ≤ 3.03 ∧
      1.78 ≤ slowFactorC a2 a1 zs ∧ slowFactorC a2 a1 zs ≤ 2.11 := by
  have hzsC : (zs : ℂ) ^ 3 + (a2 : ℂ) * (zs : ℂ) ^ 2 + (a1 : ℂ) * (zs : ℂ) + (a0 : ℂ) = 0 := by
    exact_mod_cast hzs
  obtain ⟨ha2l, ha2u⟩ := abs_le.1 h2
  have hb1 : 2.9 ≤ slowFactorB a2 zs := by unfold slowFactorB; norm_num at ha2l ⊢; linarith
  have hb2 : slowFactorB a2 zs ≤ 3.03 := by unfold slowFactorB; norm_num at ha2u ⊢; linarith
  refine ⟨?_, hb1, hb2, ?_, ?_⟩
  · intro z
    unfold slowFactorB slowFactorC
    push_cast
    linear_combination hzsC
  · unfold slowFactorC
    unfold slowFactorB at hb1 hb2
    norm_num at hz1 ⊢
    nlinarith
  · unfold slowFactorC
    unfold slowFactorB at hb1 hb2
    nlinarith

/-- A complex root of `z^2 + b z + c` with `2.9 ≤ b ≤ 3.03`, `1.78 ≤ c ≤ 2.11` has real part at
most `-0.7` and modulus at most `3.1`. -/
theorem quad_fast_root_bound (b c : ℝ) (hb1 : 2.9 ≤ b) (hb2 : b ≤ 3.03) (hc1 : 1.78 ≤ c)
    (hc2 : c ≤ 2.11) (z : ℂ) (hz : z ^ 2 + (b : ℂ) * z + (c : ℂ) = 0) :
    z.re ≤ -0.7 ∧ ‖z‖ ≤ 3.1 := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp [pow_two] at hre him
  have hn : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  by_cases hi : z.im = 0
  · have hx : z.re * z.re + b * z.re + c = 0 := by rw [hi] at hre; linarith
    have hxle : z.re ≤ -0.7 := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_pos (show (0:ℝ) < z.re + 0.7 by linarith)
        (show (0:ℝ) < z.re + b - 0.7 by linarith)]
    refine ⟨hxle, ?_⟩
    have hxb : -b < z.re := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_nonneg (show (0:ℝ) ≤ -b - z.re by linarith)
        (show (0:ℝ) ≤ -z.re by linarith)]
    have : ‖z‖ ^ 2 ≤ 3.1 ^ 2 := by rw [hn, hi]; nlinarith
    nlinarith [norm_nonneg z]
  · have h2 : 2 * z.re + b = 0 := by
      have : z.im * (2 * z.re + b) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hi
      · exact h
    have hx : z.re = -b / 2 := by linarith
    refine ⟨by linarith, ?_⟩
    have hy : z.im * z.im = z.re * z.re + b * z.re + c := by linarith
    have : ‖z‖ ^ 2 = c := by
      rw [hn, hy]; rw [hx]; ring
    nlinarith [norm_nonneg z]

/-- (F2) v2 `lem:small_delta` (the other roots): every root of the quadratic factor has
`re ≤ -0.7` and `‖z‖ ≤ 3.1`; hence every root of the cubic is `z_s` or such a fast root. -/
theorem fast_roots_bound (a2 a1 a0 zs : ℝ)
    (h2 : |a2 - 3| ≤ 0.024) (h1l : 1.97 ≤ a1) (h1u : a1 ≤ 2.11) (h0 : 0 < a0) (h0' : a0 ≤ 0.08)
    (hzs : zs ^ 3 + a2 * zs ^ 2 + a1 * zs + a0 = 0) (hz1 : -0.06 ≤ zs) (hz2 : zs ≤ 0) :
    (∀ z : ℂ, z ^ 2 + (slowFactorB a2 zs : ℂ) * z + (slowFactorC a2 a1 zs : ℂ) = 0 →
        z.re ≤ -0.7 ∧ ‖z‖ ≤ 3.1) ∧
      ∀ z ∈ cubicRoots (a2 : ℂ) (a1 : ℂ) (a0 : ℂ),
        z = (zs : ℂ) ∨ (z.re ≤ -0.7 ∧ ‖z‖ ≤ 3.1) := by
  obtain ⟨hfac, hb1, hb2, hc1, hc2⟩ :=
    cubic_factor_slow a2 a1 a0 zs h2 h1l h1u h0 h0' hzs hz1 hz2
  have hq : ∀ z : ℂ, z ^ 2 + (slowFactorB a2 zs : ℂ) * z + (slowFactorC a2 a1 zs : ℂ) = 0 →
      z.re ≤ -0.7 ∧ ‖z‖ ≤ 3.1 := fun z hz =>
    quad_fast_root_bound _ _ hb1 hb2 hc1 hc2 z hz
  refine ⟨hq, ?_⟩
  intro z hz
  have hz' : z ^ 3 + (a2 : ℂ) * z ^ 2 + (a1 : ℂ) * z + (a0 : ℂ) = 0 := hz
  rw [hfac z] at hz'
  rcases mul_eq_zero.1 hz' with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (hq z h)

/-- (F3, fast roots) v2 `lem:small_delta` (eigenvalue modulus): for a root `z` with
`re z ≤ -0.7`, `‖z‖ ≤ 3.1` and `0 < ε ≤ 1/50`, `‖1 + ε z‖^2 ≤ 1 - ε`. -/
theorem norm_one_add_sq_le_of_fast (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 50) (z : ℂ)
    (hre : z.re ≤ -0.7) (hn : ‖z‖ ≤ 3.1) : ‖1 + (ε : ℂ) * z‖ ^ 2 ≤ 1 - ε := by
  have hsq : ‖1 + (ε : ℂ) * z‖ ^ 2 = 1 + 2 * ε * z.re + ε ^ 2 * ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [hsq]
  have hz2 : ‖z‖ ^ 2 ≤ 3.1 ^ 2 := by nlinarith [norm_nonneg z]
  have : ε ^ 2 * ‖z‖ ^ 2 ≤ ε ^ 2 * 9.61 := by nlinarith [sq_nonneg ε]
  nlinarith

/-- (F3) v2 `lem:small_delta` (the rightmost eigenvalue): for `0 < ε ≤ 1/50`, every fast root has
`‖1 + ε z‖^2 ≤ 1 - ε`; `0 < 1 + ε z_s ≤ 1`; and `‖1 + ε z‖ ≤ 1 + ε z_s` for every root `z` of
the cubic. -/
theorem eigenvalue_max (a2 a1 a0 zs : ℝ)
    (h2 : |a2 - 3| ≤ 0.024) (h1l : 1.97 ≤ a1) (h1u : a1 ≤ 2.11) (h0 : 0 < a0) (h0' : a0 ≤ 0.08)
    (hzs : zs ^ 3 + a2 * zs ^ 2 + a1 * zs + a0 = 0) (hz1 : -0.06 ≤ zs) (hz2 : zs ≤ 0)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 50) :
    (∀ z : ℂ, z ^ 2 + (slowFactorB a2 zs : ℂ) * z + (slowFactorC a2 a1 zs : ℂ) = 0 →
        ‖1 + (ε : ℂ) * z‖ ^ 2 ≤ 1 - ε) ∧
      (0 < 1 + ε * zs ∧ 1 + ε * zs ≤ 1) ∧
      ∀ z ∈ cubicRoots (a2 : ℂ) (a1 : ℂ) (a0 : ℂ), ‖1 + (ε : ℂ) * z‖ ≤ 1 + ε * zs := by
  obtain ⟨hq, hroots⟩ := fast_roots_bound a2 a1 a0 zs h2 h1l h1u h0 h0' hzs hz1 hz2
  have hfast : ∀ z : ℂ, z ^ 2 + (slowFactorB a2 zs : ℂ) * z + (slowFactorC a2 a1 zs : ℂ) = 0 →
      ‖1 + (ε : ℂ) * z‖ ^ 2 ≤ 1 - ε := fun z hz =>
    norm_one_add_sq_le_of_fast ε hε0 hε z (hq z hz).1 (hq z hz).2
  have hpos : 0 < 1 + ε * zs := by nlinarith
  have hle : 1 + ε * zs ≤ 1 := by nlinarith
  refine ⟨hfast, ⟨hpos, hle⟩, ?_⟩
  intro z hz
  rcases hroots z hz with h | h
  · subst h
    have : ‖1 + (ε : ℂ) * (zs : ℂ)‖ = 1 + ε * zs := by
      have : (1 : ℂ) + (ε : ℂ) * (zs : ℂ) = ((1 + ε * zs : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    exact this.le
  · have hs := norm_one_add_sq_le_of_fast ε hε0 hε z h.1 h.2
    by_contra hcon
    push Not at hcon
    have h3 : (1 - 0.06 * ε) ≤ 1 + ε * zs := by nlinarith
    nlinarith [norm_nonneg (1 + (ε : ℂ) * z)]

/-- (F3, sSup form) v2 `lem:small_delta`: the supremum of `‖1 + ε z‖` over the roots of the cubic
is `1 + ε z_s`, and it is attained at `z_s`. -/
theorem eigenvalue_max_isGreatest (a2 a1 a0 zs : ℝ)
    (h2 : |a2 - 3| ≤ 0.024) (h1l : 1.97 ≤ a1) (h1u : a1 ≤ 2.11) (h0 : 0 < a0) (h0' : a0 ≤ 0.08)
    (hzs : zs ^ 3 + a2 * zs ^ 2 + a1 * zs + a0 = 0) (hz1 : -0.06 ≤ zs) (hz2 : zs ≤ 0)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 50) :
    IsGreatest ((fun z : ℂ => ‖1 + (ε : ℂ) * z‖) '' cubicRoots (a2 : ℂ) (a1 : ℂ) (a0 : ℂ))
        (1 + ε * zs) ∧
      sSup ((fun z : ℂ => ‖1 + (ε : ℂ) * z‖) '' cubicRoots (a2 : ℂ) (a1 : ℂ) (a0 : ℂ)) =
        1 + ε * zs := by
  obtain ⟨_, ⟨hpos, _⟩, hmax⟩ := eigenvalue_max a2 a1 a0 zs h2 h1l h1u h0 h0' hzs hz1 hz2 ε hε0 hε
  have hmem : (zs : ℂ) ∈ cubicRoots (a2 : ℂ) (a1 : ℂ) (a0 : ℂ) := by
    show (zs : ℂ) ^ 3 + (a2 : ℂ) * (zs : ℂ) ^ 2 + (a1 : ℂ) * (zs : ℂ) + (a0 : ℂ) = 0
    exact_mod_cast hzs
  have hG : IsGreatest ((fun z : ℂ => ‖1 + (ε : ℂ) * z‖) '' cubicRoots (a2 : ℂ) (a1 : ℂ) (a0 : ℂ))
      (1 + ε * zs) := by
    refine ⟨⟨(zs : ℂ), hmem, ?_⟩, ?_⟩
    · have : (1 : ℂ) + (ε : ℂ) * (zs : ℂ) = ((1 + ε * zs : ℝ) : ℂ) := by push_cast; ring
      show ‖1 + (ε : ℂ) * (zs : ℂ)‖ = 1 + ε * zs
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    · rintro _ ⟨z, hz, rfl⟩
      exact hmax z hz
  exact ⟨hG, hG.csSup_eq⟩

end

end SparseSGD.Scaling.Helps
