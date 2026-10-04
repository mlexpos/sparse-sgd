import SparseSGD.Continuum.Hurwitz
import SparseSGD.Continuum.ExponentialStability

namespace SparseSGD
noncomputable section

def continuumCharacteristicRoots (delta u : ℝ) : Set ℂ :=
  {z | z^3+3*z^2+(2+4*(delta : ℂ))*z+4*(delta : ℂ)*(1-(u : ℂ)) = 0}

/-- Negative of the largest real part of the actual characteristic roots. -/
def continuumPerronRate (delta u : ℝ) : ℝ :=
  -sSup (Complex.re '' continuumCharacteristicRoots delta u)

theorem continuumCharacteristicRoots_finite (delta u : ℝ) :
    (continuumCharacteristicRoots delta u).Finite := by
  let P : Polynomial ℂ := Polynomial.X^3+Polynomial.C 3*Polynomial.X^2+
    Polynomial.C (2+4*(delta : ℂ))*Polynomial.X+Polynomial.C (4*(delta : ℂ)*(1-(u : ℂ)))
  have hn : P ≠ 0 := by
    intro hz
    have h := congrArg (fun q : Polynomial ℂ => q.coeff 3) hz
    simp only [P, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h
    norm_num at h
  have h := Polynomial.finite_setOfPred_isRoot hn
  simpa only [Polynomial.IsRoot,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C,P,continuumCharacteristicRoots] using h

theorem continuumCharacteristicRoots_nonempty (delta u : ℝ) (hd : 0 < delta)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (continuumCharacteristicRoots delta u).Nonempty := by
  rcases eq_or_lt_of_le hu0 with hz | hp
  · refine ⟨-1, ?_⟩
    simp [continuumCharacteristicRoots,← hz]
    ring
  · obtain ⟨x,hx0,hx1,hx⟩ := exists_spectrum_root_between delta u hd hp hu1
    refine ⟨(x : ℂ), ?_⟩
    change (x : ℂ)^3+3*(x : ℂ)^2+(2+4*(delta : ℂ))*(x : ℂ)+4*(delta : ℂ)*(1-(u : ℂ)) = 0
    unfold spectrumPolynomial at hx
    exact_mod_cast hx

theorem continuumPerronRate_attained (delta u : ℝ) (hd : 0 < delta)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ z ∈ continuumCharacteristicRoots delta u, z.re = -continuumPerronRate delta u := by
  have hne := (continuumCharacteristicRoots_nonempty delta u hd hu0 hu1).image Complex.re
  have hfin := (continuumCharacteristicRoots_finite delta u).image Complex.re
  obtain ⟨z,hz,hre⟩ := hne.csSup_mem hfin
  exact ⟨z,hz,by simpa only [continuumPerronRate,neg_neg] using hre⟩

theorem continuumPerronRate_pos (delta u : ℝ) (hd : 0 < delta)
    (hu0 : 0 ≤ u) (hu1 : u < 1) : 0 < continuumPerronRate delta u := by
  obtain ⟨z,hz,hre⟩ := continuumPerronRate_attained delta u hd hu0 hu1
  have h := continuum_roots_re_neg delta u hd hu0 hu1 z hz
  linarith

/-- The strict Perron-rate inequality in source L3(c), for the actual maximum. -/
theorem continuumPerronRate_lt_one_sub_load (delta u : ℝ) (hd : 0 < delta)
    (hu0 : 0 < u) (hu1 : u < 1) : continuumPerronRate delta u < 1-u := by
  obtain ⟨x,hx0,hx1,hx⟩ := exists_spectrum_root_between delta u hd hu0 hu1
  have hz : (x : ℂ) ∈ continuumCharacteristicRoots delta u := by
    change (x : ℂ)^3+3*(x : ℂ)^2+(2+4*(delta : ℂ))*(x : ℂ)+4*(delta : ℂ)*(1-(u : ℂ)) = 0
    unfold spectrumPolynomial at hx
    exact_mod_cast hx
  have hle : x ≤ sSup (Complex.re '' continuumCharacteristicRoots delta u) :=
    le_csSup ((continuumCharacteristicRoots_finite delta u).image Complex.re).bddAbove
      ⟨(x : ℂ),hz,rfl⟩
  unfold continuumPerronRate
  linarith

end
end SparseSGD
