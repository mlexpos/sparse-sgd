import Mathlib

/-!
# v2 prop:W1, algebraic part (large-Delta linearization)

Fast ordering `(theta, ytilde, R, Ctilde, Vtilde)` (note `C` before `V`, unlike
`DynamicState`).  This file proves the matrix identities `Omega^T H + H Omega = 0`,
`D^T H + H D = -S`, positivity of `H`, the characteristic polynomial and frequency
discriminant of `Omega`, the null vectors and `lambda_0`, the oscillatory eigenvectors, the
Rayleigh damping shifts `mu_j = -N_j/(2 D_j) < 0`, and the trace identity
`lambda_0 + 2 mu_1 + 2 mu_2 = -4`.  The analytic perturbation step (eigenvalue expansion in
`Delta^{-1/2}`) is not part of this file.

Hypothesis note: the oscillatory-eigenvector formulas need `theta != 0` (otherwise `nu^2`
may equal the signal frequency `a(1+theta^2)` and `s` is undefined); in the paper
`theta* = r/alpha* > 0`.
-/

namespace SparseSGD.Logistic.V2
noncomputable section

/-- v2 prop:W1: the fast-limit matrix `Omega = DF(x*)` in the fast ordering
`(theta, ytilde, R, Ctilde, Vtilde)`, with `a = alpha*`. -/
def fastOmega (a theta R : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, -1, 0, 0, 0;
     a * (1 + theta ^ 2), 0, a * theta / 2, 0, 0;
     0, 0, 0, -2, 0;
     a * theta * R, 0, a * (1 + R / 2), 0, -1;
     0, 0, 0, 2 * a, 0]

/-- v2 prop:W1: the damping matrix `D = DG(x*) = diag(0,-1,0,-1,-2)`. -/
def fastDamping : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.diagonal ![0, -1, 0, -1, -2]

/-- v2 prop:W1: Hessian `H` of the fast Lyapunov function at `x*`. -/
def fastHessian (a theta R : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![a * (1 + theta ^ 2), 0, a * theta / 2, 0, 0;
     0, 1, 0, 0, 0;
     a * theta / 2, 0, a * (R + 2) / (4 * R), 0, 0;
     0, 0, 0, 1 / R, 0;
     0, 0, 0, 0, 1 / (2 * a * R)]

/-- v2 prop:W1: the dissipation Hessian `S = diag(0,2,0,2/R,2/(aR))`. -/
def fastDissipation (a R : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.diagonal ![0, 2, 0, 2 / R, 2 / (a * R)]

/-- v2 prop:W1: `Omega^T H + H Omega = 0`. -/
theorem omega_skew (a theta R : ℝ) (ha : a ≠ 0) (hR : R ≠ 0) :
    (fastOmega a theta R).transpose * fastHessian a theta R +
      fastHessian a theta R * fastOmega a theta R = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fastOmega, fastHessian, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    (try field_simp) <;> (try ring)

/-- v2 prop:W1: `D` entrywise. -/
theorem fastDamping_eq : fastDamping =
    !![0, 0, 0, 0, 0; 0, -1, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, -1, 0; 0, 0, 0, 0, -2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fastDamping]

/-- v2 prop:W1: `S` entrywise. -/
theorem fastDissipation_eq (a R : ℝ) : fastDissipation a R =
    !![0, 0, 0, 0, 0; 0, 2, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 2 / R, 0;
      0, 0, 0, 0, 2 / (a * R)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fastDissipation]

/-- v2 prop:W1: `D^T H + H D = -S`. -/
theorem damping_lyapunov (a theta R : ℝ) (ha : a ≠ 0) (hR : R ≠ 0) :
    fastDamping.transpose * fastHessian a theta R +
      fastHessian a theta R * fastDamping = -fastDissipation a R := by
  rw [fastDamping_eq, fastDissipation_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fastHessian, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    (try field_simp) <;> (try ring)

/-- v2 prop:W1: `H` and `D` commute. -/
theorem hessian_damping_comm (a theta R : ℝ) :
    fastHessian a theta R * fastDamping = fastDamping * fastHessian a theta R := by
  rw [fastDamping_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fastHessian, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- v2 prop:W1: `H` is symmetric. -/
theorem fastHessian_symm (a theta R : ℝ) :
    (fastHessian a theta R).transpose = fastHessian a theta R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fastHessian]

/-- v2 prop:W1: trace of `Omega` is `0`. -/
theorem trace_omega (a theta R : ℝ) : Matrix.trace (fastOmega a theta R) = 0 := by
  simp [Matrix.trace, fastOmega, Fin.sum_univ_succ]

/-- v2 prop:W1: trace of `D` is `-4`. -/
theorem trace_damping : Matrix.trace fastDamping = -4 := by
  simp [Matrix.trace, fastDamping, Fin.sum_univ_succ]
  norm_num

/-- v2 prop:W1: the quadratic form of `H`, written out. -/
theorem fastHessian_quadratic (a theta R : ℝ) (x : Fin 5 → ℝ) :
    x ⬝ᵥ (fastHessian a theta R).mulVec x =
      a * (1 + theta ^ 2) * x 0 ^ 2 + a * theta * x 0 * x 2 +
        a * (R + 2) / (4 * R) * x 2 ^ 2 + x 1 ^ 2 + x 3 ^ 2 / R + x 4 ^ 2 / (2 * a * R) := by
  simp [fastHessian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- v2 prop:W1: `H` is positive definite for `a, R > 0`. -/
theorem fastHessian_pos (a theta R : ℝ) (ha : 0 < a) (hR : 0 < R) (x : Fin 5 → ℝ)
    (hx : x ≠ 0) : 0 < x ⬝ᵥ (fastHessian a theta R).mulVec x := by
  rw [fastHessian_quadratic]
  have hid : a * (1 + theta ^ 2) * x 0 ^ 2 + a * theta * x 0 * x 2 +
        a * (R + 2) / (4 * R) * x 2 ^ 2 + x 1 ^ 2 + x 3 ^ 2 / R + x 4 ^ 2 / (2 * a * R) =
      a * (theta * x 0 + x 2 / 2) ^ 2 + a * x 0 ^ 2 + a / (2 * R) * x 2 ^ 2 + x 1 ^ 2 +
        x 3 ^ 2 / R + x 4 ^ 2 / (2 * a * R) := by
    field_simp
    ring
  rw [hid]
  have t0 : 0 ≤ a * (theta * x 0 + x 2 / 2) ^ 2 := by positivity
  have t1 : 0 ≤ a * x 0 ^ 2 := by positivity
  have t2 : 0 ≤ a / (2 * R) * x 2 ^ 2 := by positivity
  have t3 : 0 ≤ x 1 ^ 2 := by positivity
  have t4 : 0 ≤ x 3 ^ 2 / R := by positivity
  have t5 : 0 ≤ x 4 ^ 2 / (2 * a * R) := by positivity
  by_contra hneg
  have hz : a * x 0 ^ 2 = 0 ∧ a / (2 * R) * x 2 ^ 2 = 0 ∧ x 1 ^ 2 = 0 ∧ x 3 ^ 2 / R = 0 ∧
      x 4 ^ 2 / (2 * a * R) = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  obtain ⟨h1, h2, h3, h4, h5⟩ := hz
  apply hx
  have e0 : x 0 = 0 := by
    have := (mul_eq_zero.mp h1).resolve_left ha.ne'
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have e2 : x 2 = 0 := by
    have hpos : a / (2 * R) ≠ 0 := by positivity
    have := (mul_eq_zero.mp h2).resolve_left hpos
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have e1 : x 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h3
  have e3 : x 3 = 0 := by
    have := (div_eq_zero_iff.mp h4).resolve_right hR.ne'
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have e4 : x 4 = 0 := by
    have hpos : 2 * a * R ≠ 0 := by positivity
    have := (div_eq_zero_iff.mp h5).resolve_right hpos
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  ext i
  fin_cases i <;> simp [e0, e1, e2, e3, e4]

/-- v2 prop:W1: characteristic polynomial of `Omega`, over `C`. -/
theorem omega_charpoly (a theta R : ℝ) (z : ℂ) :
    Matrix.det (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
        (fastOmega a theta R).map Complex.ofReal) =
      z * (z ^ 4 + (a : ℂ) * (5 + (theta : ℂ) ^ 2 + R) * z ^ 2 +
        (a : ℂ) ^ 2 * (4 + 4 * (theta : ℂ) ^ 2 + R)) := by
  rw [Matrix.det_succ_row_zero]
  simp [fastOmega, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove,
    Matrix.one_apply]
  ring


/-- v2 prop:W1 (generic Rayleigh lemma): the sesquilinear form `v* M v` for a real matrix `M`
and a complex vector `v`. -/
def cquad (M : Matrix (Fin 5) (Fin 5) ℝ) (v : Fin 5 → ℂ) : ℂ :=
  ∑ i, ∑ j, star (v i) * (M i j : ℂ) * v j

/-- v2 prop:W1: the candidate left eigenvector `w = H conj(v)`. -/
def leftVec (H : Matrix (Fin 5) (Fin 5) ℝ) (v : Fin 5 → ℂ) : Fin 5 → ℂ :=
  (H.map Complex.ofReal).mulVec (star v)

/-- v2 prop:W1: `v* (M+N) v = v* M v + v* N v`. -/
theorem cquad_add (M N : Matrix (Fin 5) (Fin 5) ℝ) (v : Fin 5 → ℂ) :
    cquad (M + N) v = cquad M v + cquad N v := by
  simp only [cquad, Matrix.add_apply, Complex.ofReal_add, mul_add, add_mul,
    Finset.sum_add_distrib]

/-- v2 prop:W1: `v* (-M) v = -(v* M v)`. -/
theorem cquad_neg (M : Matrix (Fin 5) (Fin 5) ℝ) (v : Fin 5 → ℂ) :
    cquad (-M) v = - cquad M v := by
  simp only [cquad, Matrix.neg_apply, Complex.ofReal_neg, mul_neg, neg_mul,
    Finset.sum_neg_distrib]

/-- v2 prop:W1: `conj (v* M v) = v* M^T v`. -/
theorem cquad_star (M : Matrix (Fin 5) (Fin 5) ℝ) (v : Fin 5 → ℂ) :
    star (cquad M v) = cquad M.transpose v := by
  simp only [cquad, star_sum, star_mul', Complex.star_def, Complex.conj_ofReal,
    Matrix.transpose_apply, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- v2 prop:W1: `<H conj v, D v> = v* H^T D v`. -/
theorem leftVec_dot (H D : Matrix (Fin 5) (Fin 5) ℝ) (v : Fin 5 → ℂ) :
    leftVec H v ⬝ᵥ (D.map Complex.ofReal).mulVec v = cquad (H.transpose * D) v := by
  simp only [leftVec, cquad, dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Pi.star_apply, Fin.sum_univ_five,
    Complex.ofReal_add, Complex.ofReal_mul]
  ring


/-- Entrywise complexification is multiplicative. -/
theorem map_ofReal_mul (A B : Matrix (Fin 5) (Fin 5) ℝ) :
    (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal :=
  Complex.ofRealHom.mapMatrix.map_mul A B

/-- Complex conjugation commutes with a real matrix acting on a complex vector. -/
theorem star_mulVec_map (A : Matrix (Fin 5) (Fin 5) ℝ) (v : Fin 5 → ℂ) :
    star ((A.map Complex.ofReal).mulVec v) = (A.map Complex.ofReal).mulVec (star v) := by
  ext i
  simp [Matrix.mulVec, dotProduct, star_sum]

/-- v2 prop:W1: `<H conj v, v> = v* H^T v`. -/
theorem leftVec_dot_self (H : Matrix (Fin 5) (Fin 5) ℝ) (v : Fin 5 → ℂ) :
    leftVec H v ⬝ᵥ v = cquad H.transpose v := by
  have h := leftVec_dot H 1 v
  simpa using h

/-- v2 prop:W1 (generic lemma): if `Omega^T H + H Omega = 0` and `Omega v = i nu v`, then
`w = H conj(v)` satisfies `Omega^T w = i nu w`. -/
theorem leftVec_eigen (Ω H : Matrix (Fin 5) (Fin 5) ℝ)
    (hΩ : Ω.transpose * H + H * Ω = 0) (ν : ℝ) (v : Fin 5 → ℂ)
    (hv : (Ω.map Complex.ofReal).mulVec v = (Complex.I * ν) • v) :
    (Ω.map Complex.ofReal).transpose.mulVec (leftVec H v) = (Complex.I * ν) • leftVec H v := by
  have h1 : Ω.transpose * H = -(H * Ω) := eq_neg_of_add_eq_zero_left hΩ
  have h2 : (Ω.map Complex.ofReal).mulVec (star v) = -((Complex.I * ν) • star v) := by
    rw [← star_mulVec_map, hv]
    ext i
    simp
  unfold leftVec
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_map, ← map_ofReal_mul, h1]
  have h3 : ((-(H * Ω)).map Complex.ofReal) = -((H.map Complex.ofReal) * (Ω.map Complex.ofReal)) := by
    rw [← map_ofReal_mul]
    ext i j
    simp
  rw [h3, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, h2]
  simp [Matrix.mulVec_smul, Matrix.mulVec_neg]


/-- v2 prop:W1: `v* H v` is real for symmetric `H`. -/
theorem cquad_real_of_symm (H : Matrix (Fin 5) (Fin 5) ℝ) (hH : H.transpose = H)
    (v : Fin 5 → ℂ) : (cquad H v).im = 0 := by
  have h := cquad_star H v
  rw [hH] at h
  exact Complex.conj_eq_iff_im.mp h

/-- v2 prop:W1 (generic lemma): with `Omega^T H + H Omega = 0`, `D^T H + H D = -S`, `H`
symmetric and `Omega v = i nu v`, the left eigenvector `w = H conj(v)` gives
`Re(<w, D v>/<w, v>) = -(v* S v)/(2 v* H v)`. -/
theorem rayleigh_generic (Ω D H S : Matrix (Fin 5) (Fin 5) ℝ)
    (hΩ : Ω.transpose * H + H * Ω = 0) (hD : D.transpose * H + H * D = -S)
    (hH : H.transpose = H) (ν : ℝ) (v : Fin 5 → ℂ)
    (hv : (Ω.map Complex.ofReal).mulVec v = (Complex.I * ν) • v)
    (hne : (cquad H v).re ≠ 0) :
    (Ω.map Complex.ofReal).transpose.mulVec (leftVec H v) = (Complex.I * ν) • leftVec H v ∧
    leftVec H v ⬝ᵥ v = cquad H v ∧
    ((leftVec H v ⬝ᵥ (D.map Complex.ofReal).mulVec v) / (leftVec H v ⬝ᵥ v)).re =
      -(cquad S v).re / (2 * (cquad H v).re) := by
  refine ⟨leftVec_eigen Ω H hΩ ν v hv, ?_, ?_⟩
  · rw [leftVec_dot_self, hH]
  · have hr : leftVec H v ⬝ᵥ v = ((cquad H v).re : ℂ) := by
      rw [leftVec_dot_self, hH]
      exact (Complex.ext (by simp) (by simpa using cquad_real_of_symm H hH v))
    rw [hr, Complex.div_ofReal_re, leftVec_dot, hH]
    have hx : star (cquad (H * D) v) = cquad (D.transpose * H) v := by
      rw [cquad_star, Matrix.transpose_mul, hH]
    have hsum : cquad (H * D) v + star (cquad (H * D) v) = -(cquad S v) := by
      rw [hx, ← cquad_add, add_comm, hD, cquad_neg]
    have hre : 2 * (cquad (H * D) v).re = -(cquad S v).re := by
      have := congrArg Complex.re hsum
      simp [Complex.add_re] at this
      linarith
    rw [show -(cquad S v).re / (2 * (cquad H v).re) =
      (2 * (cquad (H * D) v).re) / (2 * (cquad H v).re) by rw [hre]]
    field_simp



/-! ### Frequencies -/

/-- v2 prop:W1: the quartic `nu^4 - a(5+theta^2+R) nu^2 + a^2(4+4 theta^2+R)`,
written as a quadratic in `x = nu^2`. -/
def freqQuartic (a theta R x : ℝ) : ℝ :=
  x ^ 2 - a * (5 + theta ^ 2 + R) * x + a ^ 2 * (4 + 4 * theta ^ 2 + R)

/-- v2 prop:W1: the discriminant factor `(theta^2-3)^2 + R(R+6+2 theta^2)`. -/
def freqDisc (theta R : ℝ) : ℝ := (theta ^ 2 - 3) ^ 2 + R * (R + 6 + 2 * theta ^ 2)

/-- v2 prop:W1: the smaller root `nu_1^2`. -/
def freqSq1 (a theta R : ℝ) : ℝ :=
  a * ((5 + theta ^ 2 + R) - Real.sqrt (freqDisc theta R)) / 2

/-- v2 prop:W1: the larger root `nu_2^2`. -/
def freqSq2 (a theta R : ℝ) : ℝ :=
  a * ((5 + theta ^ 2 + R) + Real.sqrt (freqDisc theta R)) / 2

/-- v2 prop:W1: the discriminant identity. -/
theorem frequency_discriminant (a theta R : ℝ) :
    (a * (5 + theta ^ 2 + R)) ^ 2 - 4 * (a ^ 2 * (4 + 4 * theta ^ 2 + R)) =
      a ^ 2 * freqDisc theta R := by
  unfold freqDisc
  ring

/-- v2 prop:W1: the discriminant is positive for `R > 0`. -/
theorem freqDisc_pos (theta R : ℝ) (hR : 0 < R) : 0 < freqDisc theta R := by
  unfold freqDisc
  have : 0 < R * (R + 6 + 2 * theta ^ 2) := by positivity
  nlinarith [sq_nonneg (theta ^ 2 - 3)]

/-- v2 prop:W1: the roots `nu_1^2 < nu_2^2` are positive and distinct, and they are all
the roots of the quartic in `nu^2`. -/
theorem frequency_roots (a theta R : ℝ) (ha : 0 < a) (hR : 0 < R) :
    0 < freqSq1 a theta R ∧ freqSq1 a theta R < freqSq2 a theta R ∧
    freqQuartic a theta R (freqSq1 a theta R) = 0 ∧
    freqQuartic a theta R (freqSq2 a theta R) = 0 ∧
    ∀ x, freqQuartic a theta R x = 0 → x = freqSq1 a theta R ∨ x = freqSq2 a theta R := by
  have hd := freqDisc_pos theta R hR
  have hs : Real.sqrt (freqDisc theta R) ^ 2 = freqDisc theta R := Real.sq_sqrt hd.le
  have hspos : 0 < Real.sqrt (freqDisc theta R) := Real.sqrt_pos.mpr hd
  have hfac : ∀ x, freqQuartic a theta R x = (x - freqSq1 a theta R) * (x - freqSq2 a theta R) := by
    intro x
    unfold freqQuartic freqSq1 freqSq2
    have h2 : Real.sqrt (freqDisc theta R) ^ 2 =
        (theta ^ 2 - 3) ^ 2 + R * (R + 6 + 2 * theta ^ 2) := hs
    generalize Real.sqrt (freqDisc theta R) = s at h2 ⊢
    linear_combination (a ^ 2 / 4) * h2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold freqSq1
    have : Real.sqrt (freqDisc theta R) < 5 + theta ^ 2 + R := by
      rw [Real.sqrt_lt' (by positivity)]
      unfold freqDisc
      nlinarith
    have : 0 < (5 + theta ^ 2 + R) - Real.sqrt (freqDisc theta R) := by linarith
    positivity
  · unfold freqSq1 freqSq2
    nlinarith
  · rw [hfac]; ring
  · rw [hfac]; ring
  · intro x hx
    rw [hfac] at hx
    rcases mul_eq_zero.mp hx with h | h
    · left; linarith
    · right; linarith

/-- v2 prop:W1: at `R = 0` the roots are `a(1+theta^2)` and `4a` (the signal and bulk
frequencies). -/
theorem frequency_quartic_R_zero (a theta x : ℝ) :
    freqQuartic a theta 0 x = (x - a * (1 + theta ^ 2)) * (x - 4 * a) := by
  unfold freqQuartic
  ring

/-! ### Null vectors -/

/-- v2 prop:W1: right null vector `v_0` of `Omega`. -/
def nullRight (a theta R : ℝ) : Fin 5 → ℝ :=
  ![-theta / (2 * (1 + theta ^ 2)), 0, 1, 0, a * (1 + R / (2 * (1 + theta ^ 2)))]

/-- v2 prop:W1: left null vector `w_0` of `Omega`. -/
def nullLeft (a : ℝ) : Fin 5 → ℝ := ![0, 0, a, 0, 1]

/-- v2 prop:W1: `Omega v_0 = 0`. -/
theorem omega_null_right (a theta R : ℝ) :
    (fastOmega a theta R).mulVec (nullRight a theta R) = 0 := by
  have h : (1 + theta ^ 2) ≠ 0 := by positivity
  ext i
  fin_cases i <;> simp [fastOmega, nullRight, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    field_simp <;> ring

/-- v2 prop:W1: `Omega^T w_0 = 0`. -/
theorem omega_null_left (a theta R : ℝ) :
    (fastOmega a theta R).transpose.mulVec (nullLeft a) = 0 := by
  ext i
  fin_cases i <;> simp [fastOmega, nullLeft, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- v2 prop:W1: `<w_0, v_0> = a(2+rho)`. -/
theorem null_pairing (a theta R : ℝ) :
    nullLeft a ⬝ᵥ nullRight a theta R = a * (2 + R / (2 * (1 + theta ^ 2))) := by
  simp [nullLeft, nullRight, dotProduct, Fin.sum_univ_succ]
  ring

/-- v2 prop:W1: `<w_0, D v_0> = -2a(1+rho)`. -/
theorem null_damping_pairing (a theta R : ℝ) :
    nullLeft a ⬝ᵥ fastDamping.mulVec (nullRight a theta R) =
      -2 * a * (1 + R / (2 * (1 + theta ^ 2))) := by
  rw [fastDamping_eq]
  simp [nullLeft, nullRight, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring

/-- v2 prop:W1: the real eigenvalue `lambda_0 = -(2+2 rho)/(2+rho)`,
`rho = R/(2(1+theta^2))`. -/
theorem lambda_zero (a theta R : ℝ) (ha : a ≠ 0) (hR : 0 ≤ R) :
    (nullLeft a ⬝ᵥ fastDamping.mulVec (nullRight a theta R)) /
        (nullLeft a ⬝ᵥ nullRight a theta R) =
      -(2 + 2 * (R / (2 * (1 + theta ^ 2)))) / (2 + R / (2 * (1 + theta ^ 2))) := by
  have hρ : 0 ≤ R / (2 * (1 + theta ^ 2)) := by positivity
  have h2 : (2 + R / (2 * (1 + theta ^ 2))) ≠ 0 := by positivity
  rw [null_pairing, null_damping_pairing]
  field_simp


/-! ### Oscillatory eigenvectors -/

/-- v2 prop:W1: the ratio `s = v_theta / v_R`. -/
def oscS (a theta nu : ℝ) : ℝ := -(a * theta / 2) / (a * (1 + theta ^ 2) - nu ^ 2)

/-- v2 prop:W1: the eigenvector `v = (s, -i nu s, 1, -i nu/2, -a)` of `Omega` for `i nu`. -/
def oscVec (a theta nu : ℝ) : Fin 5 → ℂ :=
  ![(oscS a theta nu : ℂ), -(Complex.I * nu * (oscS a theta nu : ℂ)), 1,
    -(Complex.I * nu / 2), -(a : ℂ)]

/-- v2 prop:W1: a root `nu^2` of the quartic is never the signal frequency `a(1+theta^2)`
(the quartic there equals `-a^2 R theta^2`). -/
theorem freqQuartic_signal (a theta R : ℝ) :
    freqQuartic a theta R (a * (1 + theta ^ 2)) = -(a ^ 2 * R * theta ^ 2) := by
  unfold freqQuartic
  ring

/-- v2 prop:W1: a root `nu^2` of the quartic is never the signal frequency. -/
theorem nu_sq_ne (a theta R nu : ℝ) (ha : a ≠ 0) (hθ : theta ≠ 0) (hR : R ≠ 0)
    (hq : freqQuartic a theta R (nu ^ 2) = 0) : nu ^ 2 ≠ a * (1 + theta ^ 2) := by
  intro h
  rw [h, freqQuartic_signal] at hq
  have : a ^ 2 * R * theta ^ 2 ≠ 0 := by positivity
  exact this (by linarith)

/-- v2 prop:W1: the two real scalar identities behind the row-by-row solution. -/
theorem osc_scalar_identities (a theta R nu : ℝ) (ha : a ≠ 0) (hθ : theta ≠ 0) (hR : R ≠ 0)
    (hq : freqQuartic a theta R (nu ^ 2) = 0) :
    a * (1 + theta ^ 2) * oscS a theta nu + a * theta / 2 = nu ^ 2 * oscS a theta nu ∧
    a * theta * R * oscS a theta nu + a * (2 + R / 2) = nu ^ 2 / 2 := by
  have hd : a * (1 + theta ^ 2) - nu ^ 2 ≠ 0 := sub_ne_zero.mpr (nu_sq_ne a theta R nu ha hθ hR hq).symm
  have hsd : oscS a theta nu * (a * (1 + theta ^ 2) - nu ^ 2) = -(a * theta / 2) := by
    unfold oscS
    field_simp
  constructor
  · linear_combination hsd
  · have : (a * theta * R * oscS a theta nu + a * (2 + R / 2) - nu ^ 2 / 2) *
        (a * (1 + theta ^ 2) - nu ^ 2) = 0 := by
      unfold freqQuartic at hq
      linear_combination (a * theta * R) * hsd + (1 / 2) * hq
    have := (mul_eq_zero.mp this).resolve_right hd
    linarith

/-- v2 prop:W1: `Omega v = i nu v` for the explicit oscillatory vector. -/
theorem omega_oscillatory_eigenvector (a theta R nu : ℝ) (ha : a ≠ 0) (hθ : theta ≠ 0)
    (hR : R ≠ 0) (hq : freqQuartic a theta R (nu ^ 2) = 0) :
    ((fastOmega a theta R).map Complex.ofReal).mulVec (oscVec a theta nu) =
      (Complex.I * nu) • oscVec a theta nu := by
  obtain ⟨h1, h3⟩ := osc_scalar_identities a theta R nu ha hθ hR hq
  have h1c : (a : ℂ) * (1 + (theta : ℂ) ^ 2) * (oscS a theta nu : ℂ) + a * theta / 2 =
      (nu : ℂ) ^ 2 * (oscS a theta nu : ℂ) := by exact_mod_cast h1
  have h3c : (a : ℂ) * theta * R * (oscS a theta nu : ℂ) + a * (2 + (R : ℂ) / 2) =
      (nu : ℂ) ^ 2 / 2 := by exact_mod_cast h3
  ext i
  fin_cases i <;> simp [fastOmega, oscVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · linear_combination h1c + ((nu : ℂ) ^ 2 * (oscS a theta nu : ℂ)) * Complex.I_sq
  · ring
  · linear_combination h3c + ((nu : ℂ) ^ 2 / 2) * Complex.I_sq
  · ring


/-! ### Rayleigh shifts -/

/-- v2 prop:W1: the numerator `N = 2 nu^2 s^2 + (nu^2+4a)/(2R)` of the damping shift. -/
def raylN (a R nu s : ℝ) : ℝ := 2 * nu ^ 2 * s ^ 2 + (nu ^ 2 + 4 * a) / (2 * R)

/-- v2 prop:W1: the denominator `D = (a(1+theta^2)+nu^2)s^2 + a theta s + (a(R+4)+nu^2)/(4R)`. -/
def raylD (a theta R nu s : ℝ) : ℝ :=
  (a * (1 + theta ^ 2) + nu ^ 2) * s ^ 2 + a * theta * s + (a * (R + 4) + nu ^ 2) / (4 * R)

/-- v2 prop:W1: `v* S v = N` for the explicit oscillatory vector. -/
theorem cquad_S_osc (a theta R nu : ℝ) (ha : a ≠ 0) (hR : R ≠ 0) :
    cquad (fastDissipation a R) (oscVec a theta nu) = (raylN a R nu (oscS a theta nu) : ℂ) := by
  rw [fastDissipation_eq]
  have h2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  simp [cquad, oscVec, Fin.sum_univ_succ, raylN, h2]
  field_simp
  linear_combination (-(4 * (R : ℂ) * (nu : ℂ) ^ 2 * (oscS a theta nu : ℂ) ^ 2 +
    (nu : ℂ) ^ 2)) * Complex.I_sq

/-- v2 prop:W1: `v* H v = D` for the explicit oscillatory vector. -/
theorem cquad_H_osc (a theta R nu : ℝ) (ha : a ≠ 0) (hR : R ≠ 0) :
    cquad (fastHessian a theta R) (oscVec a theta nu) =
      (raylD a theta R nu (oscS a theta nu) : ℂ) := by
  have h2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  simp [cquad, oscVec, fastHessian, Fin.sum_univ_succ, raylD, h2]
  field_simp
  linear_combination (-(16 * (R : ℂ) * (oscS a theta nu : ℂ) ^ 2 + 4) * (nu : ℂ) ^ 2) *
    Complex.I_sq


/-- v2 prop:W1: `D_j > 0` (the quadratic in `s` has negative discriminant). -/
theorem raylD_pos (a theta R nu s : ℝ) (ha : 0 < a) (hR : 0 < R) :
    0 < raylD a theta R nu s := by
  unfold raylD
  have hA : 0 < a * (1 + theta ^ 2) + nu ^ 2 := by positivity
  have hc : 0 < 4 * (a * (1 + theta ^ 2) + nu ^ 2) * ((a * (R + 4) + nu ^ 2) / (4 * R)) -
      (a * theta) ^ 2 := by
    have e : 4 * (a * (1 + theta ^ 2) + nu ^ 2) * ((a * (R + 4) + nu ^ 2) / (4 * R)) -
        (a * theta) ^ 2 = (a ^ 2 * (R + 4 + 4 * theta ^ 2) + nu ^ 2 * (a * (R + 4) + a * (1 + theta ^ 2))
          + nu ^ 4) / R := by
      field_simp
      ring
    rw [e]
    positivity
  have key : 4 * (a * (1 + theta ^ 2) + nu ^ 2) *
      ((a * (1 + theta ^ 2) + nu ^ 2) * s ^ 2 + a * theta * s + (a * (R + 4) + nu ^ 2) / (4 * R)) =
      (2 * (a * (1 + theta ^ 2) + nu ^ 2) * s + a * theta) ^ 2 +
        (4 * (a * (1 + theta ^ 2) + nu ^ 2) * ((a * (R + 4) + nu ^ 2) / (4 * R)) -
          (a * theta) ^ 2) := by ring
  have hpos : 0 < 4 * (a * (1 + theta ^ 2) + nu ^ 2) *
      ((a * (1 + theta ^ 2) + nu ^ 2) * s ^ 2 + a * theta * s +
        (a * (R + 4) + nu ^ 2) / (4 * R)) := by
    rw [key]
    have := sq_nonneg (2 * (a * (1 + theta ^ 2) + nu ^ 2) * s + a * theta)
    linarith
  exact pos_of_mul_pos_right hpos (by positivity)

/-- v2 prop:W1: `N_j > 0`. -/
theorem raylN_pos (a R nu s : ℝ) (ha : 0 < a) (hR : 0 < R) : 0 < raylN a R nu s := by
  unfold raylN
  positivity

/-- v2 prop:W1 (damping shift): for the explicit oscillatory eigenvector `v` and the left
eigenvector `w = H conj(v)`, the damping-induced first-order shift of the eigenvalue
`i nu sqrt(Delta)` has real part `mu = -N/(2D)`. -/
theorem rayleigh_shift (a theta R nu : ℝ) (ha : 0 < a) (hθ : theta ≠ 0) (hR : 0 < R)
    (hq : freqQuartic a theta R (nu ^ 2) = 0) :
    ((fastOmega a theta R).map Complex.ofReal).transpose.mulVec
        (leftVec (fastHessian a theta R) (oscVec a theta nu)) =
      (Complex.I * nu) • leftVec (fastHessian a theta R) (oscVec a theta nu) ∧
    ((leftVec (fastHessian a theta R) (oscVec a theta nu) ⬝ᵥ
          (fastDamping.map Complex.ofReal).mulVec (oscVec a theta nu)) /
        (leftVec (fastHessian a theta R) (oscVec a theta nu) ⬝ᵥ oscVec a theta nu)).re =
      -(raylN a R nu (oscS a theta nu)) / (2 * raylD a theta R nu (oscS a theta nu)) := by
  have ha' : a ≠ 0 := ha.ne'
  have hR' : R ≠ 0 := hR.ne'
  have hev := omega_oscillatory_eigenvector a theta R nu ha' hθ hR' hq
  have hD := raylD_pos a theta R nu (oscS a theta nu) ha hR
  have hHre : (cquad (fastHessian a theta R) (oscVec a theta nu)).re =
      raylD a theta R nu (oscS a theta nu) := by
    rw [cquad_H_osc a theta R nu ha' hR']; simp
  have hSre : (cquad (fastDissipation a R) (oscVec a theta nu)).re =
      raylN a R nu (oscS a theta nu) := by
    rw [cquad_S_osc a theta R nu ha' hR']; simp
  have hg := rayleigh_generic (fastOmega a theta R) fastDamping (fastHessian a theta R)
    (fastDissipation a R) (omega_skew a theta R ha' hR') (damping_lyapunov a theta R ha' hR')
    (fastHessian_symm a theta R) nu (oscVec a theta nu) hev (by rw [hHre]; exact hD.ne')
  refine ⟨?_, ?_⟩
  · exact hg.1
  · rw [hg.2.2, hHre, hSre]

/-- v2 prop:W1: `mu_j < 0`. -/
theorem rayleigh_shift_neg (a theta R nu : ℝ) (ha : 0 < a) (hR : 0 < R) :
    -(raylN a R nu (oscS a theta nu)) / (2 * raylD a theta R nu (oscS a theta nu)) < 0 := by
  have h1 := raylN_pos a R nu (oscS a theta nu) ha hR
  have h2 := raylD_pos a theta R nu (oscS a theta nu) ha hR
  have : 0 < raylN a R nu (oscS a theta nu) / (2 * raylD a theta R nu (oscS a theta nu)) := by
    positivity
  rw [neg_div]; linarith


/-! ### The trace identity -/

/-- v2 prop:W1: `lambda_0`, in the explicit form `-(2+2 rho)/(2+rho)`. -/
def lambdaZero (theta R : ℝ) : ℝ :=
  -(2 + 2 * (R / (2 * (1 + theta ^ 2)))) / (2 + R / (2 * (1 + theta ^ 2)))

/-- v2 prop:W1: `lambdaZero` is the quotient `<w_0, D v_0>/<w_0, v_0>`. -/
theorem lambda_zero_eq (a theta R : ℝ) (ha : a ≠ 0) (hR : 0 ≤ R) :
    (nullLeft a ⬝ᵥ fastDamping.mulVec (nullRight a theta R)) /
        (nullLeft a ⬝ᵥ nullRight a theta R) = lambdaZero theta R :=
  lambda_zero a theta R ha hR

/-- Auxiliary: the scalar `K = (4+4 theta^2+R) * ((theta^2-3)^2 + R(R+6+2 theta^2))`. -/
def traceK (theta R : ℝ) : ℝ := (4 + 4 * theta ^ 2 + R) * freqDisc theta R

/-- Auxiliary polynomial `U` in the reduction of `N/D` modulo the quartic. -/
def traceU (theta R : ℝ) : ℝ :=
  R^3 + 10*R^2*theta^2 + 10*R^2 + 17*R*theta^4 + 46*R*theta^2 + 29*R + 8*theta^6 - 24*theta^4 - 8*theta^2 + 24

/-- Auxiliary polynomial `V` in the reduction of `N/D` modulo the quartic. -/
def traceV (theta R : ℝ) : ℝ :=
  -4*R*theta^2 + 4*R - 4*theta^4 + 8*theta^2 + 12

/-- On a root `x = nu^2` of the quartic, `N/D = (aU + V x)/(aK)`; this is the polynomial
certificate behind the trace identity. -/
theorem rayl_ratio_root (a theta R nu : ℝ) (ha : 0 < a) (hθ : theta ≠ 0) (hR : 0 < R)
    (hq : freqQuartic a theta R (nu ^ 2) = 0) :
    raylN a R nu (oscS a theta nu) / raylD a theta R nu (oscS a theta nu) =
      (a * traceU theta R + traceV theta R * nu ^ 2) / (a * traceK theta R) := by
  have ha' : a ≠ 0 := ha.ne'
  have hR' : R ≠ 0 := hR.ne'
  have hD := raylD_pos a theta R nu (oscS a theta nu) ha hR
  have hdisc := freqDisc_pos theta R hR
  have hK : 0 < traceK theta R := by unfold traceK; positivity
  have hd : a * (1 + theta ^ 2) - nu ^ 2 ≠ 0 :=
    sub_ne_zero.mpr (nu_sq_ne a theta R nu ha' hθ hR' hq).symm
  set x := nu ^ 2 with hx
  have hN : raylN a R nu (oscS a theta nu) * (4 * R * (a * (1 + theta ^ 2) - x) ^ 2) =
      2*R*a^2*theta^2*x + 8*a^3*theta^4 + 16*a^3*theta^2 + 8*a^3 + 2*a^2*theta^4*x - 12*a^2*theta^2*x - 14*a^2*x - 4*a*theta^2*x^2 + 4*a*x^2 + 2*x^3 := by
    unfold raylN oscS
    rw [← hx]
    field_simp
    ring
  have hDn : raylD a theta R nu (oscS a theta nu) * (4 * R * (a * (1 + theta ^ 2) - x) ^ 2) =
      R*a^3*theta^2 + R*a^3 + R*a^2*theta^2*x - 2*R*a^2*x + R*a*x^2 + 4*a^3*theta^4 + 8*a^3*theta^2 + 4*a^3 + a^2*theta^4*x - 6*a^2*theta^2*x - 7*a^2*x - 2*a*theta^2*x^2 + 2*a*x^2 + x^3 := by
    unfold raylD oscS
    rw [← hx]
    field_simp
    ring
  have hcert : (2*R*a^2*theta^2*x + 8*a^3*theta^4 + 16*a^3*theta^2 + 8*a^3 + 2*a^2*theta^4*x - 12*a^2*theta^2*x - 14*a^2*x - 4*a*theta^2*x^2 + 4*a*x^2 + 2*x^3) * (a * traceK theta R) -
      (a * traceU theta R + traceV theta R * x) *
        (R*a^3*theta^2 + R*a^3 + R*a^2*theta^2*x - 2*R*a^2*x + R*a*x^2 + 4*a^3*theta^4 + 8*a^3*theta^2 + 4*a^3 + a^2*theta^4*x - 6*a^2*theta^2*x - 7*a^2*x - 2*a*theta^2*x^2 + 2*a*x^2 + x^3) =
      (-R^3*a^2*theta^2 - R^3*a^2 - 2*R^2*a^2*theta^4 - 4*R^2*a^2*theta^2 - 2*R^2*a^2 - R*a^2*theta^6 + 17*R*a^2*theta^4 + 37*R*a^2*theta^2 + 19*R*a^2 - 16*a^2*theta^6 + 16*a^2*theta^4 + 80*a^2*theta^2 + 48*a^2 + x^2*(4*R*theta^2 - 4*R + 4*theta^4 - 8*theta^2 - 12) + x*(R^3*a + 10*R^2*a*theta^2 + 2*R^2*a + 5*R*a*theta^4 + 22*R*a*theta^2 - 15*R*a - 4*a*theta^6 + 20*a*theta^4 - 12*a*theta^2 - 36*a)) * freqQuartic a theta R x := by
    unfold freqQuartic traceK traceU traceV freqDisc
    ring
  rw [hq, mul_zero] at hcert
  rw [div_eq_div_iff hD.ne' (by positivity)]
  have hpos : 4 * R * (a * (1 + theta ^ 2) - x) ^ 2 ≠ 0 := by positivity
  apply mul_right_cancel₀ hpos
  have e : raylN a R nu (oscS a theta nu) * (a * traceK theta R) * (4 * R * (a * (1 + theta ^ 2) - x) ^ 2) =
      (raylN a R nu (oscS a theta nu) * (4 * R * (a * (1 + theta ^ 2) - x) ^ 2)) *
        (a * traceK theta R) := by ring
  have e' : (a * traceU theta R + traceV theta R * x) * raylD a theta R nu (oscS a theta nu) *
      (4 * R * (a * (1 + theta ^ 2) - x) ^ 2) =
      (a * traceU theta R + traceV theta R * x) *
        (raylD a theta R nu (oscS a theta nu) * (4 * R * (a * (1 + theta ^ 2) - x) ^ 2)) := by ring
  rw [e, e', hN, hDn]
  linarith

/-- v2 prop:W1 (trace identity): `lambda_0 + 2 mu_1 + 2 mu_2 = -4`. Here `nu_1, nu_2` are
square roots of the two roots of the quartic. -/
theorem lambda_mu_trace (a theta R nu1 nu2 : ℝ) (ha : 0 < a) (hθ : theta ≠ 0) (hR : 0 < R)
    (h1 : nu1 ^ 2 = freqSq1 a theta R) (h2 : nu2 ^ 2 = freqSq2 a theta R) :
    lambdaZero theta R +
      2 * (-(raylN a R nu1 (oscS a theta nu1)) / (2 * raylD a theta R nu1 (oscS a theta nu1))) +
      2 * (-(raylN a R nu2 (oscS a theta nu2)) / (2 * raylD a theta R nu2 (oscS a theta nu2)))
      = -4 := by
  obtain ⟨-, -, hq1, hq2, -⟩ := frequency_roots a theta R ha hR
  rw [← h1] at hq1
  rw [← h2] at hq2
  have e1 := rayl_ratio_root a theta R nu1 ha hθ hR hq1
  have e2 := rayl_ratio_root a theta R nu2 ha hθ hR hq2
  have hD1 := raylD_pos a theta R nu1 (oscS a theta nu1) ha hR
  have hD2 := raylD_pos a theta R nu2 (oscS a theta nu2) ha hR
  have hK : 0 < traceK theta R := by
    unfold traceK; have := freqDisc_pos theta R hR; positivity
  have hsum : nu1 ^ 2 + nu2 ^ 2 = a * (5 + theta ^ 2 + R) := by
    rw [h1, h2]; unfold freqSq1 freqSq2; ring
  have step : ∀ N D : ℝ, 0 < D → 2 * (-N / (2 * D)) = -(N / D) := by
    intro N D hD; field_simp
  rw [step _ _ hD1, step _ _ hD2, e1, e2]
  have hρ : (2 + R / (2 * (1 + theta ^ 2))) ≠ 0 := by positivity
  have h1theta : (1 + theta ^ 2) ≠ 0 := by positivity
  unfold lambdaZero
  have hKne := hK.ne'
  field_simp
  have hnu : nu2 ^ 2 = a * (5 + theta ^ 2 + R) - nu1 ^ 2 := by linarith
  rw [hnu]
  unfold traceK traceU traceV freqDisc
  ring
end
end SparseSGD.Logistic.V2
