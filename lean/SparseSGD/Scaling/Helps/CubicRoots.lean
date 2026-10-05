import SparseSGD.Continuum.PerronRate

/-!
# Cubic toolkit for `r_c` (momentum-helps appendix)

Real/complex root toolkit for the continuum characteristic cubic
`χ(z;Δ,u) = z^3+3z^2+(2+4Δ)z+4Δ(1-u)` and the rate
`r_c(Δ,u) = continuumPerronRate Δ u`, together with the algebraic parts of
`v2 lem:speedup` (i), (ii) and (iv) (first sentence).

Paper labels: `helps-intro` (`r_c` defined for all `Δ>0`, `u≥0`), `v2 lem:speedup`.
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD

noncomputable section

/-- `helps-intro`: the root set is nonempty for all parameters (fundamental theorem of algebra). -/
theorem continuumCharacteristicRoots_nonempty_any (delta u : ℝ) :
    (continuumCharacteristicRoots delta u).Nonempty := by
  let P : Polynomial ℂ := Polynomial.C 1 * Polynomial.X^3 + Polynomial.C 3*Polynomial.X^2+
    Polynomial.C (2+4*(delta : ℂ))*Polynomial.X+Polynomial.C (4*(delta : ℂ)*(1-(u : ℂ)))
  have hdeg : 0 < P.degree := by
    have := Polynomial.degree_cubic (a := (1 : ℂ)) (b := 3) (c := 2+4*(delta : ℂ))
      (d := 4*(delta : ℂ)*(1-(u : ℂ))) one_ne_zero
    rw [show P = _ from rfl, this]
    norm_num
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  refine ⟨z, ?_⟩
  have hz' := hz
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, P, one_mul] at hz'
  exact hz'

/-- `helps-intro`: every root has real part at most `-r_c`. -/
theorem re_le_neg_continuumPerronRate {delta u : ℝ} {z : ℂ}
    (hz : z ∈ continuumCharacteristicRoots delta u) :
    z.re ≤ -continuumPerronRate delta u := by
  unfold continuumPerronRate
  rw [neg_neg]
  exact le_csSup ((continuumCharacteristicRoots_finite delta u).image Complex.re).bddAbove
    ⟨z, hz, rfl⟩

/-- `helps-intro`: real roots of the complex root set are the zeros of `spectrumPolynomial`. -/
theorem ofReal_mem_roots_iff (delta u x : ℝ) :
    (x : ℂ) ∈ continuumCharacteristicRoots delta u ↔ spectrumPolynomial delta u x = 0 := by
  unfold continuumCharacteristicRoots spectrumPolynomial
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- A real zero of `spectrumPolynomial` is `≥ x` whenever the polynomial is `≤ 0` at `x`. -/
theorem exists_real_root_ge {delta u x : ℝ} (hx : spectrumPolynomial delta u x ≤ 0) :
    ∃ y, x ≤ y ∧ spectrumPolynomial delta u y = 0 := by
  set B : ℝ := max x (1 + |2+4*delta| + |4*delta*(1-u)|) with hB
  have hBx : x ≤ B := le_max_left _ _
  have hB1 : 1 + |2+4*delta| + |4*delta*(1-u)| ≤ B := le_max_right _ _
  have h1 : 1 ≤ B := by
    have := abs_nonneg (2+4*delta); have := abs_nonneg (4*delta*(1-u)); linarith
  have hpos : 0 ≤ spectrumPolynomial delta u B := by
    unfold spectrumPolynomial
    have ha := neg_abs_le (2+4*delta)
    have hb := neg_abs_le (4*delta*(1-u))
    have hc : (|2+4*delta| + |4*delta*(1-u)|) ≤ B := by linarith
    have hB0 : 0 ≤ B := by linarith
    nlinarith [mul_nonneg hB0 hB0, mul_nonneg (mul_nonneg hB0 hB0) hB0,
      mul_le_mul_of_nonneg_left hc hB0, abs_nonneg (2+4*delta), abs_nonneg (4*delta*(1-u)),
      mul_le_mul_of_nonneg_left ha hB0]
  have hcont : ContinuousOn (spectrumPolynomial delta u) (Set.Icc x B) := by
    unfold spectrumPolynomial; fun_prop
  obtain ⟨y, hy, hpy⟩ := intermediate_value_Icc hBx hcont
    (show 0 ∈ Set.Icc (spectrumPolynomial delta u x) (spectrumPolynomial delta u B) from
      ⟨hx, hpos⟩)
  exact ⟨y, hy.1, hpy⟩

/-- `helps-intro`/`lem:speedup`: `χ(x) ≤ 0` forces `r_c ≤ -x`. -/
theorem continuumPerronRate_le_of_nonpos {delta u x : ℝ}
    (hx : spectrumPolynomial delta u x ≤ 0) : continuumPerronRate delta u ≤ -x := by
  obtain ⟨y, hxy, hy⟩ := exists_real_root_ge hx
  have := re_le_neg_continuumPerronRate ((ofReal_mem_roots_iff delta u y).2 hy)
  simp only [Complex.ofReal_re] at this
  linarith

/-- Strict version: `χ(x) < 0` forces `r_c < -x`. -/
theorem continuumPerronRate_lt_of_neg {delta u x : ℝ}
    (hx : spectrumPolynomial delta u x < 0) : continuumPerronRate delta u < -x := by
  obtain ⟨y, hxy, hy⟩ := exists_real_root_ge hx.le
  have hne : x ≠ y := by
    rintro rfl; rw [hy] at hx; exact lt_irrefl _ hx
  have := re_le_neg_continuumPerronRate ((ofReal_mem_roots_iff delta u y).2 hy)
  simp only [Complex.ofReal_re] at this
  have := lt_of_le_of_ne hxy hne
  linarith

/-- Rightmost-root criterion: if `x > -1` is a real root with `3x²+6x+2+4Δ > 0`, then every
root of `χ` has real part `≤ x`, so `r_c = -x`. -/
theorem continuumPerronRate_eq_of_rightmost {delta u x : ℝ}
    (hroot : spectrumPolynomial delta u x = 0) (hx : -1 < x)
    (hq : 0 < 3*x^2+6*x+2+4*delta) : continuumPerronRate delta u = -x := by
  have hmem : (x : ℂ) ∈ continuumCharacteristicRoots delta u :=
    (ofReal_mem_roots_iff delta u x).2 hroot
  have hle : ∀ z ∈ continuumCharacteristicRoots delta u, z.re ≤ x := by
    intro z hz
    have hz' : z^3+3*z^2+(2+4*(delta : ℂ))*z+4*(delta : ℂ)*(1-(u : ℂ)) = 0 := hz
    have hroot' : (x : ℂ)^3+3*(x : ℂ)^2+(2+4*(delta : ℂ))*(x : ℂ)+
        4*(delta : ℂ)*(1-(u : ℂ)) = 0 := by
      have := (ofReal_mem_roots_iff delta u x).2 hroot
      exact this
    have hfac : (z - x) * (z^2+(3+(x:ℂ))*z+((x:ℂ)^2+3*(x:ℂ)+2+4*(delta:ℂ))) = 0 := by
      linear_combination hz' - hroot'
    rcases mul_eq_zero.1 hfac with h | h
    · have : z = x := sub_eq_zero.1 h
      rw [this]; simp
    · have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
      by_contra hgt'
      have hgt := not_le.1 hgt'
      by_cases hb : z.im = 0
      · rw [hb] at hre
        nlinarith
      · have h2 : 2 * z.re + 3 + x = 0 := by
          have : z.im * (2 * z.re + 3 + x) = 0 := by linarith
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hb
          · exact h
        linarith
  have hgreat : IsGreatest (Complex.re '' continuumCharacteristicRoots delta u) x :=
    ⟨⟨(x : ℂ), hmem, by simp⟩, by rintro _ ⟨z, hz, rfl⟩; exact hle z hz⟩
  unfold continuumPerronRate
  rw [hgreat.csSup_eq]

/-- `helps-intro`: the rate at zero load, `r_c(Δ,0) = 1 - √(max 0 (1-4Δ))`. -/
theorem continuumPerronRate_zero_load {delta : ℝ} (_hd : 0 < delta) :
    continuumPerronRate delta 0 = 1 - Real.sqrt (max 0 (1 - 4*delta)) := by
  rcases lt_or_ge delta (1/4) with h | h
  · have hpos : 0 < 1 - 4*delta := by linarith
    rw [max_eq_right hpos.le]
    set s := Real.sqrt (1 - 4*delta) with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 hpos
    have hs2 : s^2 = 1 - 4*delta := Real.sq_sqrt hpos.le
    have := continuumPerronRate_eq_of_rightmost (delta := delta) (u := 0) (x := -1 + s)
      (by unfold spectrumPolynomial; nlinarith) (by linarith) (by nlinarith)
    rw [this]; ring
  · have hneg : 1 - 4*delta ≤ 0 := by linarith
    rw [max_eq_left hneg, Real.sqrt_zero]
    have hmem : ((-1 : ℝ) : ℂ) ∈ continuumCharacteristicRoots delta 0 := by
      rw [ofReal_mem_roots_iff]; unfold spectrumPolynomial; ring
    have hle : ∀ z ∈ continuumCharacteristicRoots delta 0, z.re ≤ -1 := by
      intro z hz
      have hz' : z^3+3*z^2+(2+4*(delta : ℂ))*z+4*(delta : ℂ)*(1-((0:ℝ) : ℂ)) = 0 := hz
      have hfac : (z + 1) * (z^2 + 2*z + 4*(delta:ℂ)) = 0 := by
        simp at hz'; linear_combination hz'
      rcases mul_eq_zero.1 hfac with h | h
      · have := congrArg Complex.re h
        simp at this; linarith
      · have hre := congrArg Complex.re h
        have him := congrArg Complex.im h
        simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
        by_cases hb : z.im = 0
        · rw [hb] at hre
          nlinarith [sq_nonneg (z.re + 1)]
        · have : z.im * (2 * z.re + 2) = 0 := by linarith
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hb
          · linarith
    have hgreat : IsGreatest (Complex.re '' continuumCharacteristicRoots delta 0) (-1) :=
      ⟨⟨_, hmem, by simp⟩, by rintro _ ⟨z, hz, rfl⟩; exact hle z hz⟩
    unfold continuumPerronRate
    rw [hgreat.csSup_eq]; ring

/-- `v2 lem:speedup`: the ratio `Γ(Δ,u) = r_c(Δ,u)/(2Δ(1-u))`. -/
def speedupRatio (Delta u : ℝ) : ℝ := continuumPerronRate Delta u / (2*Delta*(1-u))

/-- `v2 lem:speedup (i)`: `Γ < 2` for `Δ>0`, `u ∈ (0,1)`. (Fails at `u = 0`, where `Γ(1/4,0)=2`.) -/
theorem speedupRatio_lt_two {Delta u : ℝ} (hD : 0 < Delta) (hu0 : 0 < u) (hu1 : u < 1) :
    speedupRatio Delta u < 2 := by
  unfold speedupRatio
  have hden : 0 < 2*Delta*(1-u) := by
    have : 0 < 1 - u := by linarith
    positivity
  rw [div_lt_iff₀ hden]
  set q := 4*Delta*(1-u) with hq
  have hneg : spectrumPolynomial Delta u (-q) < 0 := by
    have hq0 : 0 < q := by have : 0 < 1 - u := by linarith
                           positivity
    have : spectrumPolynomial Delta u (-q) = -q*((1-q)^2+4*Delta*u) := by
      unfold spectrumPolynomial; rw [hq]; ring
    rw [this]
    have : 0 < (1-q)^2+4*Delta*u := by positivity
    nlinarith
  have := continuumPerronRate_lt_of_neg hneg
  rw [hq] at this
  linarith

/-- `v2 lem:speedup (ii)`: `r_c(1/4, a³) = 1 - a` for `a ∈ (0,1)`. -/
theorem continuumPerronRate_quarter_cube {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    continuumPerronRate (1/4) (a^3) = 1 - a := by
  have := continuumPerronRate_eq_of_rightmost (delta := 1/4) (u := a^3) (x := a - 1)
    (by unfold spectrumPolynomial; ring) (by linarith) (by nlinarith)
  rw [this]; ring

/-- `v2 lem:speedup (ii)`: `Γ(1/4, a³) = 2/(1+a+a²)`. -/
theorem speedupRatio_quarter_cube {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    speedupRatio (1/4) (a^3) = 2 / (1 + a + a^2) := by
  unfold speedupRatio
  rw [continuumPerronRate_quarter_cube ha0 ha1]
  have h1 : 1 - a ≠ 0 := by linarith
  have h2 : 1 + a + a^2 ≠ 0 := by positivity
  have h3 : 1 - a^3 ≠ 0 := by
    have : 1 - a^3 = (1-a)*(1+a+a^2) := by ring
    rw [this]; exact mul_ne_zero h1 h2
  field_simp
  ring

/-- `v2 lem:speedup (ii)`, `u`-form: with `a = u^(1/3)`. -/
theorem speedupRatio_quarter {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    speedupRatio (1/4) u =
      2 / (1 + u^((1/3 : ℝ)) + (u^((1/3 : ℝ)))^2) := by
  have hcube : (u^((1/3 : ℝ)))^3 = u := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
  have ha0 : 0 < u^((1/3 : ℝ)) := Real.rpow_pos_of_pos hu0 _
  have ha1 : u^((1/3 : ℝ)) < 1 := Real.rpow_lt_one hu0.le hu1 (by norm_num)
  have := speedupRatio_quarter_cube ha0 ha1
  rw [hcube] at this
  exact this

/-- `v2 lem:speedup (iv)`: the identity `χ(-2Δ(1-u)) = -4Δ²(1-u)(2Δ(1-u)²+3u-1)`. -/
theorem spectrumPolynomial_at_neg_two (Delta u : ℝ) :
    spectrumPolynomial Delta u (-(2*Delta*(1-u))) =
      -4*Delta^2*(1-u)*(2*Delta*(1-u)^2+3*u-1) := by
  unfold spectrumPolynomial; ring

/-- `v2 lem:speedup (iv)`, first sentence: `Γ < 1` for `u ∈ [1/3,1)`, `Δ>0`. -/
theorem speedupRatio_lt_one {Delta u : ℝ} (hD : 0 < Delta) (hu0 : 1/3 ≤ u) (hu1 : u < 1) :
    speedupRatio Delta u < 1 := by
  unfold speedupRatio
  have h1u : 0 < 1 - u := by linarith
  have hden : 0 < 2*Delta*(1-u) := by positivity
  rw [div_lt_one hden]
  have hneg : spectrumPolynomial Delta u (-(2*Delta*(1-u))) < 0 := by
    rw [spectrumPolynomial_at_neg_two]
    have hb : 0 < 2*Delta*(1-u)^2+3*u-1 := by
      have : 0 < Delta*(1-u)^2 := by positivity
      linarith
    have : 0 < Delta^2*(1-u)*(2*Delta*(1-u)^2+3*u-1) := by positivity
    linarith
  have := continuumPerronRate_lt_of_neg hneg
  linarith

end
end SparseSGD.Scaling.Helps
