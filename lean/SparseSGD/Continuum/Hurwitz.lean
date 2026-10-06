import SparseSGD.Continuum.Spectrum

namespace SparseSGD

theorem det_complex_scalar_one_sub_continuumGenerator (delta u : ℝ) (z : ℂ)
    (hd : delta ≠ 0) :
    Matrix.det (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      (continuumGenerator delta u).map Complex.ofReal) =
      z ^ 3 + 3 * z ^ 2 + (2 + 4 * (delta : ℂ)) * z +
        4 * (delta : ℂ) * (1 - (u : ℂ)) := by
  rw [Matrix.det_fin_three]
  simp [continuumGenerator, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  have hdc : (delta : ℂ) ≠ 0 := by exact_mod_cast hd
  field_simp
  <;> ring

/-- All roots of the continuum characteristic polynomial lie in the open left
half-plane for a subcritical nonnegative feedback. This is a direct cubic argument. -/
theorem continuum_roots_re_neg (delta u : ℝ) (hd : 0 < delta)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (z : ℂ)
    (hz : z ^ 3 + 3 * z ^ 2 + (2 + 4 * (delta : ℂ)) * z +
      4 * (delta : ℂ) * (1 - (u : ℂ)) = 0) : z.re < 0 := by
  by_contra hn
  have hx : 0 ≤ z.re := le_of_not_gt hn
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp only [Complex.add_re, Complex.mul_re, Complex.sub_re,
    Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re, Complex.zero_im, Complex.one_re,
    Complex.one_im] at hr hi
  have hreal : z.re ^ 3 - 3 * z.re * z.im ^ 2 +
      3 * (z.re ^ 2 - z.im ^ 2) + (2 + 4 * delta) * z.re +
      4 * delta * (1 - u) = 0 := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im] at hr
    nlinarith [hr]
  have himag : z.im * (3 * z.re ^ 2 - z.im ^ 2 + 6 * z.re + 2 + 4 * delta) = 0 := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im] at hi
    nlinarith [hi]
  rcases mul_eq_zero.mp himag with hy | hy
  · have hc : 0 < 4 * delta * (1 - u) := by positivity
    rw [hy] at hreal
    nlinarith [sq_nonneg z.re, pow_nonneg hx 3, mul_nonneg (le_of_lt hd) hx]
  · have hc : 0 ≤ delta * u := mul_nonneg hd.le hu0
    have hx3 : 0 ≤ z.re ^ 3 := pow_nonneg hx 3
    have hdx : 0 ≤ delta * z.re := mul_nonneg hd.le hx
    have hxy := congrArg (fun a : ℝ => z.re * a) hy
    nlinarith [sq_nonneg z.re]

/-- The complex characteristic roots of the actual three-coordinate generator
have strictly negative real part. -/
theorem continuumGenerator_hurwitz (delta u : ℝ) (hd : 0 < delta)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (z : ℂ)
    (hz : Matrix.det (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      (continuumGenerator delta u).map Complex.ofReal) = 0) : z.re < 0 := by
  rw [det_complex_scalar_one_sub_continuumGenerator delta u z hd.ne'] at hz
  exact continuum_roots_re_neg delta u hd hu0 hu1 z hz

theorem exists_nonneg_spectrum_root (delta u : ℝ) (hd : 0 < delta)
    (hu : 1 ≤ u) : ∃ x : ℝ, 0 ≤ x ∧ spectrumPolynomial delta u x = 0 := by
  let a := 4 * delta * (u - 1)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hleft : spectrumPolynomial delta u 0 ≤ 0 := by
    rw [spectrumPolynomial_at_zero]
    nlinarith
  have hright : 0 ≤ spectrumPolynomial delta u (a + 1) := by
    have ht : 0 ≤ a + 1 := by linarith
    have hdt : 0 ≤ delta * (a + 1) := mul_nonneg hd.le ht
    have hcube : 0 ≤ (a + 1) ^ 3 := pow_nonneg ht 3
    have hsq := sq_nonneg (a + 1)
    have hae : a = 4 * delta * (u - 1) := rfl
    unfold spectrumPolynomial
    nlinarith
  have hcont : ContinuousOn (spectrumPolynomial delta u) (Set.Icc 0 (a + 1)) := by
    unfold spectrumPolynomial
    fun_prop
  obtain ⟨x, hx, hroot⟩ := intermediate_value_Icc (by linarith : 0 ≤ a + 1)
    hcont ⟨hleft, hright⟩
  exact ⟨x, hx.1, hroot⟩

/-- Exact algebraic stability threshold, stated for all characteristic roots. -/
theorem continuumGenerator_hurwitz_iff (delta u : ℝ) (hd : 0 < delta)
    (hu : 0 ≤ u) :
    (∀ z : ℂ, Matrix.det (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      (continuumGenerator delta u).map Complex.ofReal) = 0 → z.re < 0) ↔ u < 1 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨x, hx, hp⟩ := exists_nonneg_spectrum_root delta u hd (le_of_not_gt hn)
    have hz : Matrix.det ((x : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
        (continuumGenerator delta u).map Complex.ofReal) = 0 := by
      rw [det_complex_scalar_one_sub_continuumGenerator delta u x hd.ne']
      unfold spectrumPolynomial at hp
      exact_mod_cast hp
    have := h x hz
    simpa using (not_lt_of_ge hx this)
  · intro h z hz
    exact continuumGenerator_hurwitz delta u hd hu h z hz

end SparseSGD
