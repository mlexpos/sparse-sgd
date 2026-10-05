import SparseSGD.Continuum.Hurwitz
import SparseSGD.Logistic.SourceAssumptions
import SparseSGD.Logistic.DynamicField

/-! # v2 Proposition S (ii): the Jacobian of the LR5 field at `y*` is Hurwitz

Coordinates are `(theta, Y, R, V, C)`, as in `DynamicState`.  With
`a = alpha*`, `b = Phi/delta`, the Jacobian `A` at the equilibrium satisfies
the Lyapunov matrix equation `A^T H + H A = -S` with `H` the Hessian of the
v2 Lyapunov function and `S` the Hessian of the dissipation (`b > 0`).  An
observability argument upgrades the semi-definite dissipation to strict
Hurwitz stability.  The zero-load case `Phi* = 0` is treated by reducing the
`(R,V,C)` block to the continuum cubic of `Continuum/Hurwitz.lean`.
-/

namespace SparseSGD.Logistic.V2
open Matrix
noncomputable section

/-- The Jacobian of eq:LR5 at the equilibrium (`a = alpha*`, `theta = theta*`,
`R = R*`), rows and columns in the order `(theta,Y,R,V,C)`. -/
def jacobianMatrix (a theta R delta : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, -delta, 0, 0, 0;
     a * (1 + theta ^ 2), -1, a * theta / 2, 0, 0;
     0, 0, 0, 0, -2 * delta;
     0, 0, 0, -2, 2 * a;
     a * theta * R, 0, a * (1 + R / 2), -delta, -1]

/-- Hessian of the v2 Lyapunov function at `y*` (`b = Phi*/delta`). -/
def hessianMatrix (a theta R delta b : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![a * (1 + theta ^ 2) / delta, 0, a * theta / (2 * delta), 0, 0;
     0, 1, 0, 0, 0;
     a * theta / (2 * delta), 0, a / (4 * delta) + b / (2 * R ^ 2), 0, 0;
     0, 0, 0, 1 / (2 * b), 0;
     0, 0, 0, 0, 1 / R]

/-- Hessian of the dissipation at `y*` (`b = Phi*/delta`). -/
def dissipationMatrix (R b : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.diagonal ![0, 2, 0, 2 / b, 2 / R]

theorem hessianMatrix_isSymm (a theta R delta b : ℝ) :
    (hessianMatrix a theta R delta b).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hessianMatrix]

/-- v2 prop:S (ii): the Lyapunov matrix equation `A^T H + H A = -S`, valid when
`a R = delta b` (that is `alpha* R* = Phi*`). -/
theorem lyapunov_matrix_equation (a theta R delta b : ℝ)
    (hd : delta ≠ 0) (hR : R ≠ 0) (hb : b ≠ 0) (hab : a * R = delta * b) :
    (jacobianMatrix a theta R delta)ᵀ * hessianMatrix a theta R delta b +
      hessianMatrix a theta R delta b * jacobianMatrix a theta R delta =
        -dissipationMatrix R b := by
  have ha : a = delta * b / R := by field_simp; linarith
  subst ha
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jacobianMatrix, hessianMatrix, dissipationMatrix, Matrix.mul_apply,
      Fin.sum_univ_five] <;>
    field_simp <;> ring

/-- v2 prop:S (ii), generic lemma: a Lyapunov matrix equation turns the
real and imaginary parts of an eigenvector into an identity between the real
part of the eigenvalue and the two quadratic forms. -/
theorem eigen_re_identity {n : ℕ} (A H S : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsSymm) (hAHS : Aᵀ * H + H * A = -S)
    (x y : Fin n → ℝ) (p q : ℝ)
    (hx : A *ᵥ x = p • x - q • y) (hy : A *ᵥ y = q • x + p • y) :
    2 * p * (x ⬝ᵥ (H *ᵥ x) + y ⬝ᵥ (H *ᵥ y)) = -(x ⬝ᵥ (S *ᵥ x) + y ⬝ᵥ (S *ᵥ y)) := by
  have hvm : ∀ v : Fin n → ℝ, v ᵥ* H = H *ᵥ v := by
    intro v
    calc v ᵥ* H = v ᵥ* Hᵀ := by rw [hH.eq]
      _ = H *ᵥ v := Matrix.vecMul_transpose H v
  have key : ∀ u : Fin n → ℝ, (A *ᵥ u) ⬝ᵥ (H *ᵥ u) + (H *ᵥ u) ⬝ᵥ (A *ᵥ u) =
      -(u ⬝ᵥ (S *ᵥ u)) := by
    intro u
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => u ⬝ᵥ (M *ᵥ u)) hAHS
    simp only [Matrix.add_mulVec, dotProduct_add, Matrix.neg_mulVec, dotProduct_neg] at h1
    have e1 : u ⬝ᵥ (Aᵀ *ᵥ (H *ᵥ u)) = (A *ᵥ u) ⬝ᵥ (H *ᵥ u) := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have e2 : u ⬝ᵥ (H *ᵥ (A *ᵥ u)) = (H *ᵥ u) ⬝ᵥ (A *ᵥ u) := by
      rw [Matrix.dotProduct_mulVec, hvm]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h1
    rw [← e1, ← e2]
    exact h1
  have kx := key x
  have ky := key y
  rw [hx] at kx
  rw [hy] at ky
  have hxy : x ⬝ᵥ (H *ᵥ y) = y ⬝ᵥ (H *ᵥ x) := by
    have h2 : y ⬝ᵥ (H *ᵥ x) = (H *ᵥ y) ⬝ᵥ x := by
      rw [Matrix.dotProduct_mulVec, hvm]
    rw [h2, dotProduct_comm]
  simp only [sub_dotProduct, add_dotProduct, smul_dotProduct, dotProduct_sub,
    dotProduct_add, dotProduct_smul, smul_eq_mul] at kx ky
  rw [dotProduct_comm (H *ᵥ x) y, dotProduct_comm (H *ᵥ x) x] at kx
  rw [dotProduct_comm (H *ᵥ y) x, dotProduct_comm (H *ᵥ y) y] at ky
  rw [hxy] at ky
  linarith

/-- Explicit expansion of the Hessian quadratic form as a sum of squares. -/
theorem hessian_quadratic_form (a theta R delta b : ℝ) (x : Fin 5 → ℝ) :
    x ⬝ᵥ (hessianMatrix a theta R delta b *ᵥ x) =
      a / delta * ((theta * x 0 + x 2 / 2) ^ 2 + x 0 ^ 2) + x 1 ^ 2 +
        b / (2 * R ^ 2) * x 2 ^ 2 + x 3 ^ 2 / (2 * b) + x 4 ^ 2 / R := by
  simp [hessianMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  ring

/-- v2 prop:S (ii): the Hessian of the Lyapunov function at `y*` is positive
definite.  The `(theta,R)` block has determinant
`a^2/(4 delta^2) + a (1+theta^2) b/(2 delta R^2) > 0`. -/
theorem hessian_pos (a theta R delta b : ℝ) (ha : 0 < a) (hd : 0 < delta)
    (hb : 0 < b) (hR : 0 < R) (x : Fin 5 → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ (hessianMatrix a theta R delta b *ᵥ x) := by
  rw [hessian_quadratic_form]
  have h1 : 0 < a / delta := div_pos ha hd
  have h2 : 0 < b / (2 * R ^ 2) := by positivity
  have h3 : 0 < 1 / (2 * b) := by positivity
  have h4 : 0 < 1 / R := by positivity
  by_contra hle
  rw [not_lt] at hle
  have t1 : 0 ≤ a / delta * ((theta * x 0 + x 2 / 2) ^ 2 + x 0 ^ 2) := by positivity
  have t2 : 0 ≤ x 1 ^ 2 := sq_nonneg _
  have t3 : 0 ≤ b / (2 * R ^ 2) * x 2 ^ 2 := by positivity
  have t4 : 0 ≤ x 3 ^ 2 / (2 * b) := by positivity
  have t5 : 0 ≤ x 4 ^ 2 / R := by positivity
  have e1 : a / delta * ((theta * x 0 + x 2 / 2) ^ 2 + x 0 ^ 2) = 0 := by linarith
  have e2 : x 1 ^ 2 = 0 := by linarith
  have e3 : b / (2 * R ^ 2) * x 2 ^ 2 = 0 := by linarith
  have e4 : x 3 ^ 2 / (2 * b) = 0 := by linarith
  have e5 : x 4 ^ 2 / R = 0 := by linarith
  have f1 : (theta * x 0 + x 2 / 2) ^ 2 + x 0 ^ 2 = 0 := by
    rcases mul_eq_zero.mp e1 with h | h
    · exact absurd h h1.ne'
    · exact h
  have x0 : x 0 = 0 := by nlinarith [sq_nonneg (theta * x 0 + x 2 / 2), sq_nonneg (x 0)]
  have x2 : x 2 = 0 := by
    rcases mul_eq_zero.mp e3 with h | h
    · exact absurd h h2.ne'
    · exact pow_eq_zero_iff (by norm_num) |>.mp h
  have x1 : x 1 = 0 := pow_eq_zero_iff (by norm_num) |>.mp e2
  have x3 : x 3 = 0 := by
    have : x 3 ^ 2 = 0 := by
      have := (div_eq_zero_iff.mp e4)
      rcases this with h | h
      · exact h
      · exact absurd h (by positivity)
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have x4 : x 4 = 0 := by
    have : x 4 ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp e5 with h | h
      · exact h
      · exact absurd h hR.ne'
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  apply hx
  ext i
  fin_cases i <;> simpa

/-- v2 prop:S (ii): observability.  Since the `(theta,R)` block of the
`Y`- and `C`-rows has determinant `a^2 (2+2 theta^2+R)/2`, a vector with
`x_1 = x_3 = x_4 = 0` and `(A x)_1 = (A x)_4 = 0` vanishes. -/
theorem observability (a theta R delta : ℝ) (ha : 0 < a)
    (hq : 2 + 2 * theta ^ 2 + R ≠ 0) (x : Fin 5 → ℝ)
    (h1 : x 1 = 0) (h3 : x 3 = 0) (h4 : x 4 = 0)
    (hY : (jacobianMatrix a theta R delta *ᵥ x) 1 = 0)
    (hC : (jacobianMatrix a theta R delta *ᵥ x) 4 = 0) : x = 0 := by
  simp [jacobianMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_five, h1, h3, h4] at hY hC
  have hdet : a ^ 2 * (2 + 2 * theta ^ 2 + R) / 2 ≠ 0 := by positivity
  have hx0 : x 0 = 0 := by
    have : a ^ 2 * (2 + 2 * theta ^ 2 + R) / 2 * x 0 = 0 := by
      linear_combination (a * (1 + R / 2)) * hY - (a * theta / 2) * hC
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hdet
    · exact h
  have hx2 : x 2 = 0 := by
    have : a ^ 2 * (2 + 2 * theta ^ 2 + R) / 2 * x 2 = 0 := by
      linear_combination (a * (1 + theta ^ 2)) * hC - (a * theta * R) * hY
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hdet
    · exact h
  ext i
  fin_cases i <;> simpa

/-- A root of the characteristic determinant has a nonzero complex eigenvector. -/
theorem exists_eigenvector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (z : ℂ)
    (h : Matrix.det (z • (1 : Matrix (Fin n) (Fin n) ℂ) - A.map Complex.ofReal) = 0) :
    ∃ v : Fin n → ℂ, v ≠ 0 ∧ (A.map Complex.ofReal) *ᵥ v = z • v := by
  obtain ⟨v, hv, hm⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hm
  exact (sub_eq_zero.mp hm).symm

/-- Real and imaginary parts of a complex eigenvector of a real matrix. -/
theorem eigenvector_re_im {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (z : ℂ)
    (v : Fin n → ℂ) (hv : (A.map Complex.ofReal) *ᵥ v = z • v) :
    A *ᵥ (fun i => (v i).re) = z.re • (fun i => (v i).re) - z.im • (fun i => (v i).im) ∧
    A *ᵥ (fun i => (v i).im) = z.im • (fun i => (v i).re) + z.re • (fun i => (v i).im) := by
  constructor
  · ext i
    have := congrArg Complex.re (congrFun hv i)
    simp [Matrix.mulVec, dotProduct, Complex.re_sum] at this ⊢
    simpa [Complex.mul_re] using this
  · ext i
    have := congrArg Complex.im (congrFun hv i)
    simp [Matrix.mulVec, dotProduct, Complex.im_sum] at this ⊢
    simpa [Complex.mul_im, add_comm] using this

/-- v2 prop:S (ii), `Phi* > 0`: the Jacobian at `y*` is Hurwitz. -/
theorem jacobian_hurwitz_pos_load (a theta R delta b : ℝ) (ha : 0 < a) (hd : 0 < delta)
    (hR : 0 < R) (hb : 0 < b) (hab : a * R = delta * b) (z : ℂ)
    (hz : Matrix.det (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
      (jacobianMatrix a theta R delta).map Complex.ofReal) = 0) : z.re < 0 := by
  by_contra hnn
  rw [not_lt] at hnn
  obtain ⟨v, hv0, hv⟩ := exists_eigenvector _ z hz
  obtain ⟨hx, hy⟩ := eigenvector_re_im _ z v hv
  set x : Fin 5 → ℝ := fun i => (v i).re with hxdef
  set y : Fin 5 → ℝ := fun i => (v i).im with hydef
  have hL := lyapunov_matrix_equation a theta R delta b hd.ne' hR.ne' hb.ne' hab
  have hid := eigen_re_identity _ _ _ (hessianMatrix_isSymm a theta R delta b) hL x y
    z.re z.im hx hy
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hv0
    ext i
    have h1 := congrFun hh.1 i
    have h2 := congrFun hh.2 i
    simp only [hxdef, hydef, Pi.zero_apply] at h1 h2
    exact Complex.ext (by simpa using h1) (by simpa using h2)
  have hpos : 0 < x ⬝ᵥ (hessianMatrix a theta R delta b *ᵥ x) +
      y ⬝ᵥ (hessianMatrix a theta R delta b *ᵥ y) := by
    have n1 : 0 ≤ x ⬝ᵥ (hessianMatrix a theta R delta b *ᵥ x) := by
      by_cases h : x = 0
      · simp [h]
      · exact (hessian_pos a theta R delta b ha hd hb hR x h).le
    have n2 : 0 ≤ y ⬝ᵥ (hessianMatrix a theta R delta b *ᵥ y) := by
      by_cases h : y = 0
      · simp [h]
      · exact (hessian_pos a theta R delta b ha hd hb hR y h).le
    rcases hxy with h | h
    · linarith [hessian_pos a theta R delta b ha hd hb hR x h]
    · linarith [hessian_pos a theta R delta b ha hd hb hR y h]
  have hSx : ∀ w : Fin 5 → ℝ, w ⬝ᵥ (dissipationMatrix R b *ᵥ w) =
      2 * w 1 ^ 2 + 2 / b * w 3 ^ 2 + 2 / R * w 4 ^ 2 := by
    intro w
    simp [dissipationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    ring
  have hlhs : 0 ≤ 2 * z.re * (x ⬝ᵥ (hessianMatrix a theta R delta b *ᵥ x) +
      y ⬝ᵥ (hessianMatrix a theta R delta b *ᵥ y)) := by positivity
  rw [hid, hSx x, hSx y] at hlhs
  have hb2 : 0 < 2 / b := by positivity
  have hR2 : 0 < 2 / R := by positivity
  have t1 : 0 ≤ 2 * x 1 ^ 2 := by positivity
  have t2 : 0 ≤ 2 / b * x 3 ^ 2 := by positivity
  have t3 : 0 ≤ 2 / R * x 4 ^ 2 := by positivity
  have t4 : 0 ≤ 2 * y 1 ^ 2 := by positivity
  have t5 : 0 ≤ 2 / b * y 3 ^ 2 := by positivity
  have t6 : 0 ≤ 2 / R * y 4 ^ 2 := by positivity
  have sq0 : ∀ (c w : ℝ), 0 < c → c * w ^ 2 = 0 → w = 0 := by
    intro c w hc h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hc.ne'
    · exact pow_eq_zero_iff (by norm_num) |>.mp h
  have x1 : x 1 = 0 := sq0 2 _ (by norm_num) (by linarith)
  have y1 : y 1 = 0 := sq0 2 _ (by norm_num) (by linarith)
  have x3 : x 3 = 0 := sq0 _ _ hb2 (by linarith)
  have y3 : y 3 = 0 := sq0 _ _ hb2 (by linarith)
  have x4 : x 4 = 0 := sq0 _ _ hR2 (by linarith)
  have y4 : y 4 = 0 := sq0 _ _ hR2 (by linarith)
  have hq : 2 + 2 * theta ^ 2 + R ≠ 0 := by positivity
  have hx0 : x = 0 := by
    apply observability a theta R delta ha hq x x1 x3 x4
    · rw [hx]; simp [x1, y1]
    · rw [hx]; simp [x4, y4]
  have hy0 : y = 0 := by
    apply observability a theta R delta ha hq y y1 y3 y4
    · rw [hy]; simp [x1, y1]
    · rw [hy]; simp [x4, y4]
  rw [hx0, hy0] at hpos
  simp at hpos


/-- The `(R,V,C)` block of the Jacobian at zero load. -/
def zeroLoadBulkBlock (a delta : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, -2 * delta; 0, -2, 2 * a; a, -delta, -1]

theorem det_zeroLoadBulkBlock (a delta : ℝ) (z : ℂ) :
    Matrix.det (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      (zeroLoadBulkBlock a delta).map Complex.ofReal) =
      z ^ 3 + 3 * z ^ 2 + (2 + 4 * ((a * delta : ℝ) : ℂ)) * z +
        4 * ((a * delta : ℝ) : ℂ) * (1 - ((0 : ℝ) : ℂ)) := by
  rw [Matrix.det_fin_three]
  simp [zeroLoadBulkBlock, Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- Elementary: `z^2 + z + c = 0` with `c > 0` forces `Re z < 0`. -/
theorem quadratic_roots_re_neg (c : ℝ) (hc : 0 < c) (z : ℂ)
    (hz : z ^ 2 + z + (c : ℂ) = 0) : z.re < 0 := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hr hi
  by_contra hn
  rw [not_lt] at hn
  have hq : z.im * (2 * z.re + 1) = 0 := by linarith
  rcases mul_eq_zero.mp hq with h | h
  · rw [h] at hr
    nlinarith
  · nlinarith

/-- v2 prop:S (ii), `Phi* = 0`: the Jacobian at `y*` is Hurwitz.  The
characteristic polynomial is `(z+1)(z^2+2z+4 delta a)(z^2+z+delta a(1+theta^2))`. -/
theorem jacobian_hurwitz_zero_load (a theta delta : ℝ) (ha : 0 < a) (hd : 0 < delta)
    (z : ℂ)
    (hz : Matrix.det (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
      (jacobianMatrix a theta 0 delta).map Complex.ofReal) = 0) : z.re < 0 := by
  obtain ⟨v, hv0, hv⟩ := exists_eigenvector _ z hz
  have r0 := congrFun hv 0
  have r1 := congrFun hv 1
  have r2 := congrFun hv 2
  have r3 := congrFun hv 3
  have r4 := congrFun hv 4
  simp [jacobianMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_five] at r0 r1 r2 r3 r4
  by_cases hb : v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0
  · obtain ⟨h2, h3, h4⟩ := hb
    rw [h2] at r1
    have hdc : (delta : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hv0' : v 0 ≠ 0 := by
      intro h
      apply hv0
      have h1' : v 1 = 0 := by
        rw [h] at r0
        have : (delta : ℂ) * v 1 = 0 := by linear_combination -r0
        rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' hdc
        · exact h'
      ext i
      fin_cases i <;> simp [h, h1', h2, h3, h4]
    apply quadratic_roots_re_neg (delta * a * (1 + theta ^ 2)) (by positivity) z
    have : (z ^ 2 + z + ((delta * a * (1 + theta ^ 2) : ℝ) : ℂ)) * v 0 = 0 := by
      push_cast
      linear_combination (-z - 1) * r0 + (delta : ℂ) * r1
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hv0'
  · have hw : (![v 2, v 3, v 4] : Fin 3 → ℂ) ≠ 0 := by
      intro h
      apply hb
      refine ⟨?_, ?_, ?_⟩
      · simpa using congrFun h 0
      · simpa using congrFun h 1
      · simpa using congrFun h 2
    have hdet : Matrix.det (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
        (zeroLoadBulkBlock a delta).map Complex.ofReal) = 0 := by
      apply Matrix.exists_mulVec_eq_zero_iff.mp
      refine ⟨_, hw, ?_⟩
      ext i
      fin_cases i
      · simp [zeroLoadBulkBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
          Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
        linear_combination -r2
      · simp [zeroLoadBulkBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
          Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
        linear_combination -r3
      · simp [zeroLoadBulkBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
          Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
        linear_combination -r4
    rw [det_zeroLoadBulkBlock] at hdet
    exact SparseSGD.continuum_roots_re_neg (a * delta) 0 (by positivity) le_rfl
      (by norm_num) z hdet

/-- The coordinate projection as a continuous linear map. -/
abbrev hurwitzProj (i : Fin 5) : DynamicState →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ) i

theorem hasFDerivAt_dynamicAlpha (r : ℝ) (y : DynamicState) :
    HasFDerivAt (dynamicAlpha r)
      ((dynamicAlpha r y * y 0) • hurwitzProj 0 + (dynamicAlpha r y / 2) • hurwitzProj 2) y := by
  have h0 : HasFDerivAt (fun y : DynamicState => y 0) (hurwitzProj 0) y := (hurwitzProj 0).hasFDerivAt
  have h2 : HasFDerivAt (fun y : DynamicState => y 2) (hurwitzProj 2) y := (hurwitzProj 2).hasFDerivAt
  have harg : HasFDerivAt (fun y : DynamicState => (y 0 ^ 2 + y 2 - r ^ 2) / 2)
      ((y 0) • hurwitzProj 0 + (1 / 2 : ℝ) • hurwitzProj 2) y := by
    convert (((h0.mul h0).add h2).sub_const (r ^ 2)).const_mul (1 / 2 : ℝ) using 1
    · funext p
      change (p 0 ^ 2 + p 2 - r ^ 2) / 2 = (1 / 2 : ℝ) * (p 0 * p 0 + p 2 - r ^ 2)
      ring
    · ext w
      simp
      ring
  convert harg.exp using 1
  · rfl
  · ext w
    simp [dynamicAlpha]
    ring

/-- The Frechet derivative of `dynamicField` at any state with `C = 0` is the
explicit Jacobian matrix evaluated at `(alpha, theta, R)`. -/
theorem hasFDerivAt_dynamicField_of_C_zero (r delta Phi : ℝ) (y : DynamicState)
    (hC : y 4 = 0) :
    HasFDerivAt (dynamicField r delta Phi)
      (LinearMap.toContinuousLinearMap
        (Matrix.toLin' (jacobianMatrix (dynamicAlpha r y) (y 0) (y 2) delta))) y := by
  have hα := hasFDerivAt_dynamicAlpha r y
  have p0 : HasFDerivAt (fun y : DynamicState => y 0) (hurwitzProj 0) y := (hurwitzProj 0).hasFDerivAt
  have p1 : HasFDerivAt (fun y : DynamicState => y 1) (hurwitzProj 1) y := (hurwitzProj 1).hasFDerivAt
  have p2 : HasFDerivAt (fun y : DynamicState => y 2) (hurwitzProj 2) y := (hurwitzProj 2).hasFDerivAt
  have p3 : HasFDerivAt (fun y : DynamicState => y 3) (hurwitzProj 3) y := (hurwitzProj 3).hasFDerivAt
  have p4 : HasFDerivAt (fun y : DynamicState => y 4) (hurwitzProj 4) y := (hurwitzProj 4).hasFDerivAt
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · have h : HasFDerivAt (fun y : DynamicState => dynamicField r delta Phi y 0)
        ((-delta) • hurwitzProj 1) y := p1.const_mul (-delta)
    refine h.congr_fderiv ?_
    ext w
    simp [jacobianMatrix, dotProduct, Fin.sum_univ_five]
  · have h : HasFDerivAt (fun y : DynamicState => dynamicField r delta Phi y 1)
        (-hurwitzProj 1 + (dynamicAlpha r y • hurwitzProj 0 + y 0 •
          ((dynamicAlpha r y * y 0) • hurwitzProj 0 + (dynamicAlpha r y / 2) • hurwitzProj 2))) y :=
      (p1.neg.add (hα.mul p0)).sub_const r
    refine h.congr_fderiv ?_
    ext w
    simp [jacobianMatrix, dotProduct, Fin.sum_univ_five]
    ring
  · have h : HasFDerivAt (fun y : DynamicState => dynamicField r delta Phi y 2)
        ((-2 * delta) • hurwitzProj 4) y := p4.const_mul (-2 * delta)
    refine h.congr_fderiv ?_
    ext w
    simp [jacobianMatrix, dotProduct, Fin.sum_univ_five]
  · have h : HasFDerivAt (fun y : DynamicState => dynamicField r delta Phi y 3)
        ((-2 : ℝ) • hurwitzProj 3 + (2 : ℝ) • (dynamicAlpha r y • hurwitzProj 4 + y 4 •
          ((dynamicAlpha r y * y 0) • hurwitzProj 0 + (dynamicAlpha r y / 2) • hurwitzProj 2))) y :=
      by
        convert (((p3.const_mul (-2)).add ((hα.mul p4).const_mul 2)).add_const
          (2 * Phi / delta)) using 1
        funext y
        simp [dynamicField]
        ring
    refine h.congr_fderiv ?_
    ext w
    simp [jacobianMatrix, dotProduct, Fin.sum_univ_five, hC]
    ring
  · have h : HasFDerivAt (fun y : DynamicState => dynamicField r delta Phi y 4)
        (-hurwitzProj 4 + (dynamicAlpha r y • hurwitzProj 2 + y 2 •
          ((dynamicAlpha r y * y 0) • hurwitzProj 0 + (dynamicAlpha r y / 2) • hurwitzProj 2)) -
          delta • hurwitzProj 3) y :=
      (p4.neg.add (hα.mul p2)).sub (p3.const_mul delta)
    refine h.congr_fderiv ?_
    ext w
    simp [jacobianMatrix, dotProduct, Fin.sum_univ_five]
    ring

/-- v2 prop:S (ii): the Frechet derivative of eq:LR5 at `y*` is the explicit
Jacobian matrix `jacobianMatrix a theta* R* delta`, with `a = alpha*`. -/
theorem hasFDerivAt_dynamicField_equilibrium (r delta Phi : ℝ) :
    HasFDerivAt (dynamicField r delta Phi)
      (LinearMap.toContinuousLinearMap
        (Matrix.toLin' (jacobianMatrix
          (dynamicAlpha r (dynamicCanonicalEquilibrium r delta Phi))
          (positiveRoot r Phi) (equilibriumBulk r Phi) delta)))
      (dynamicCanonicalEquilibrium r delta Phi) :=
  hasFDerivAt_dynamicField_of_C_zero r delta Phi _ rfl

/-- v2 prop:S (ii): the Jacobian of eq:LR5 at `y*` is Hurwitz, for every
`r > 0`, `delta > 0`, `Phi >= 0`.  Combines the Frechet derivative with the
positive-load (`A^T H + H A = -S` plus observability) and zero-load
(continuum cubic) arguments. -/
theorem prop_S_ii (r delta Phi : ℝ) (hr : 0 < r) (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) :
    HasFDerivAt (dynamicField r delta Phi)
      (LinearMap.toContinuousLinearMap
        (Matrix.toLin' (jacobianMatrix
          (dynamicAlpha r (dynamicCanonicalEquilibrium r delta Phi))
          (positiveRoot r Phi) (equilibriumBulk r Phi) delta)))
      (dynamicCanonicalEquilibrium r delta Phi) ∧
    ∀ z : ℂ, Matrix.det (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
      (jacobianMatrix
          (dynamicAlpha r (dynamicCanonicalEquilibrium r delta Phi))
          (positiveRoot r Phi) (equilibriumBulk r Phi) delta).map Complex.ofReal) = 0 →
      z.re < 0 := by
  refine ⟨hasFDerivAt_dynamicField_equilibrium r delta Phi, ?_⟩
  intro z hz
  have hstat := dynamicCanonicalEquilibrium_is_stationary r delta Phi hr hdelta hPhi
  set y := dynamicCanonicalEquilibrium r delta Phi with hy
  set a := dynamicAlpha r y with ha
  have hapos : 0 < a := Real.exp_pos _
  have hy0 : y 0 = positiveRoot r Phi := rfl
  have hy1 : y 1 = 0 := rfl
  have hy2 : y 2 = equilibriumBulk r Phi := rfl
  have hy3 : y 3 = Phi / delta := rfl
  have hy4 : y 4 = 0 := rfl
  have e1 : a * positiveRoot r Phi = r := by
    have h := congrFun hstat 1
    simp only [dynamicField, Pi.zero_apply] at h
    rw [hy0, hy1] at h
    simp at h
    linarith
  have e2 : a * equilibriumBulk r Phi = Phi := by
    have h := congrFun hstat 4
    simp only [dynamicField, Pi.zero_apply] at h
    rw [hy2, hy3, hy4] at h
    have : delta * (Phi / delta) = Phi := by field_simp
    simp at h
    linarith
  rcases hPhi.eq_or_lt with h0 | hpos
  · have hR0 : equilibriumBulk r Phi = 0 := by simp [equilibriumBulk, ← h0]
    rw [hR0] at hz
    exact jacobian_hurwitz_zero_load a (positiveRoot r Phi) delta hapos hdelta z hz
  · have hθ : 0 < positiveRoot r Phi := (positiveRoot_spec r Phi hr hPhi).1
    have hR : 0 < equilibriumBulk r Phi := by
      unfold equilibriumBulk
      positivity
    refine jacobian_hurwitz_pos_load a (positiveRoot r Phi) (equilibriumBulk r Phi) delta
      (Phi / delta) hapos hdelta hR (by positivity) ?_ z hz
    rw [e2]
    field_simp

end
end SparseSGD.Logistic.V2
