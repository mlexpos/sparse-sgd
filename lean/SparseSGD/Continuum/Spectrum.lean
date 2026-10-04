import SparseSGD.Foundations

namespace SparseSGD

noncomputable section

def continuumGenerator (delta u : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, -2 * delta; 2 * u / delta, -2, 2; 1, -delta, -1]

def spectrumPolynomial (delta u x : ℝ) : ℝ :=
  x ^ 3 + 3 * x ^ 2 + (2 + 4 * delta) * x + 4 * delta * (1 - u)

theorem det_scalar_one_sub_continuumGenerator (delta u x : ℝ) (hd : delta ≠ 0) :
    Matrix.det (x • (1 : Matrix (Fin 3) (Fin 3) ℝ) - continuumGenerator delta u) =
      spectrumPolynomial delta u x := by
  rw [Matrix.det_fin_three]
  simp [continuumGenerator, spectrumPolynomial, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply]
  field_simp
  <;> ring

theorem spectrumPolynomial_at_u_sub_one (delta u : ℝ) :
    spectrumPolynomial delta u (u - 1) = -u * (1 - u ^ 2) := by
  simp [spectrumPolynomial]
  ring

theorem spectrumPolynomial_at_zero (delta u : ℝ) :
    spectrumPolynomial delta u 0 = 4 * delta * (1 - u) := by
  simp [spectrumPolynomial]

theorem exists_spectrum_root_between (delta u : ℝ) (hd : 0 < delta)
    (hu0 : 0 < u) (hu1 : u < 1) :
    ∃ x, u - 1 < x ∧ x < 0 ∧ spectrumPolynomial delta u x = 0 := by
  have hleft : spectrumPolynomial delta u (u - 1) < 0 := by
    rw [spectrumPolynomial_at_u_sub_one]
    have : 0 < 1 - u ^ 2 := by nlinarith
    nlinarith
  have hright : 0 < spectrumPolynomial delta u 0 := by
    rw [spectrumPolynomial_at_zero]
    nlinarith
  have hcont : ContinuousOn (spectrumPolynomial delta u) (Set.Icc (u - 1) 0) := by
    unfold spectrumPolynomial
    fun_prop
  have hmem := intermediate_value_Icc (by linarith) hcont
    (show 0 ∈ Set.Icc (spectrumPolynomial delta u (u - 1))
      (spectrumPolynomial delta u 0) by constructor <;> linarith)
  rcases hmem with ⟨x, hx, hpx⟩
  have hxleft : u - 1 < x := by
    by_contra h
    have heq : x = u - 1 := by linarith [hx.1]
    subst x
    linarith [hleft, hpx]
  have hxright : x < 0 := by
    by_contra h
    have heq : x = 0 := by linarith [hx.2]
    subst x
    linarith [hright, hpx]
  exact ⟨x, hxleft, hxright, hpx⟩

end
end SparseSGD
