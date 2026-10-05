import SparseSGD.Foundations
import SparseSGD.Continuum.Spectrum

/-!
# Per-step linear map of the second-moment recursion (momentum-helps appendix)

Paper labels: `sec:helps-rate` (definition of `Lambda`), `lem:helps-transfer` (Step 1).

The noise-free (additive `= 0`) step map `Params.step` is linear in `(R,V,C)`.  We record
its `3 x 3` matrix, its characteristic polynomial in closed form, the spectral radius as
the maximal modulus of the roots of that polynomial, and the per-step rate
`Lambda = -log rho`.  Mathlib's `spectralRadius` is deliberately not used.

Caveat: `Real.log 0 = 0`, so `perStepRate` does not encode `Lambda = infinity` when the
radius vanishes; downstream statements must assume `0 < stepRadius p` or be stated in
terms of `stepRadius`.
-/

namespace SparseSGD.Scaling.Helps

open Matrix

noncomputable section

/-- (S1) The matrix of `L(Sigma) = F Sigma F^T + 2 w eps u_n Sigma_11 b b^T` in the
coordinates `(R,V,C) = (Sigma_11, Sigma_22, Sigma_12)`. -/
def stepLinearMatrix (p : Params) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(1 - p.w) ^ 2 + 2 * p.w * p.eps * p.noise, p.beta ^ 2, -2 * p.beta * (1 - p.w);
     p.w ^ 2 + 2 * p.w * p.eps * p.noise, p.beta ^ 2, 2 * p.w * p.beta;
     p.w * (1 - p.w) - 2 * p.w * p.eps * p.noise, -p.beta ^ 2, p.beta * (1 - 2 * p.w)]

/-- (S2) `stepLinearMatrix` is the matrix of the noise-free step map `Params.step`
(sec:helps-rate, lem:helps-transfer Step 1). -/
theorem stepLinearMatrix_mulVec (p : Params) (s : Moments) :
    (stepLinearMatrix p).mulVec ![s.R, s.V, s.C] =
      ![(({ p with additive := 0 } : Params).step s).R,
        (({ p with additive := 0 } : Params).step s).V,
        (({ p with additive := 0 } : Params).step s).C] := by
  ext i
  fin_cases i <;>
    simp [stepLinearMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Params.step,
      Params.eps] <;> ring

/-- (S3) Closed-form characteristic polynomial (complex variable). -/
def stepCharPoly (beta w un : ℝ) (z : ℂ) : ℂ :=
  (z - beta) * (z ^ 2 - (((1 + beta - w) ^ 2 - 2 * beta : ℝ) : ℂ) * z + (beta : ℂ) ^ 2)
    - 2 * (w : ℂ) * (1 - (beta : ℂ)) * (un : ℂ) * z * (z + beta)

/-- (S4) Real-variable version of `stepCharPoly`. -/
def stepCharPolyR (beta w un x : ℝ) : ℝ :=
  (x - beta) * (x ^ 2 - ((1 + beta - w) ^ 2 - 2 * beta) * x + beta ^ 2)
    - 2 * w * (1 - beta) * un * x * (x + beta)

theorem stepCharPoly_ofReal (beta w un x : ℝ) :
    stepCharPoly beta w un (x : ℂ) = ((stepCharPolyR beta w un x : ℝ) : ℂ) := by
  simp [stepCharPoly, stepCharPolyR]

/-- (S4) `det (z - L) = stepCharPoly` (sec:helps-rate, lem:helps-transfer Step 1). -/
theorem det_stepLinearMatrix (p : Params) (z : ℂ) :
    Matrix.det (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - (stepLinearMatrix p).map (↑))
      = stepCharPoly p.beta p.w p.noise z := by
  rw [Matrix.det_fin_three]
  simp [stepLinearMatrix, stepCharPoly, Params.eps, Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- (S4) Real-variable determinant identity. -/
theorem det_stepLinearMatrix_real (p : Params) (x : ℝ) :
    Matrix.det (x • (1 : Matrix (Fin 3) (Fin 3) ℝ) - stepLinearMatrix p)
      = stepCharPolyR p.beta p.w p.noise x := by
  rw [Matrix.det_fin_three]
  simp [stepLinearMatrix, stepCharPolyR, Params.eps, Matrix.sub_apply, Matrix.smul_apply]
  ring

/-! ### Expanded form and roots -/

/-- Coefficients of `stepCharPoly` as a monic cubic. -/
def stepC2 (beta w un : ℝ) : ℝ :=
  -(((1 + beta - w) ^ 2 - 2 * beta) + beta) - 2 * w * (1 - beta) * un
def stepC1 (beta w un : ℝ) : ℝ :=
  beta ^ 2 + beta * ((1 + beta - w) ^ 2 - 2 * beta) - 2 * w * (1 - beta) * un * beta
def stepC0 (beta : ℝ) : ℝ := -beta ^ 3

theorem stepCharPolyR_expand (beta w un x : ℝ) :
    stepCharPolyR beta w un x =
      x ^ 3 + stepC2 beta w un * x ^ 2 + stepC1 beta w un * x + stepC0 beta := by
  simp only [stepCharPolyR, stepC2, stepC1, stepC0]; ring

theorem stepCharPoly_expand (beta w un : ℝ) (z : ℂ) :
    stepCharPoly beta w un z =
      z ^ 3 + (stepC2 beta w un : ℂ) * z ^ 2 + (stepC1 beta w un : ℂ) * z
        + (stepC0 beta : ℂ) := by
  simp only [stepCharPoly, stepC2, stepC1, stepC0]; push_cast; ring

/-- The monic cubic `stepCharPoly` as a polynomial over `ℂ`. -/
def stepPoly (beta w un : ℝ) : Polynomial ℂ :=
  Polynomial.C (1 : ℂ) * Polynomial.X ^ 3 + Polynomial.C (stepC2 beta w un : ℂ) * Polynomial.X ^ 2
    + Polynomial.C (stepC1 beta w un : ℂ) * Polynomial.X + Polynomial.C (stepC0 beta : ℂ)

theorem stepPoly_eval (beta w un : ℝ) (z : ℂ) :
    (stepPoly beta w un).eval z = stepCharPoly beta w un z := by
  simp [stepPoly, stepCharPoly_expand]

theorem stepPoly_degree (beta w un : ℝ) : (stepPoly beta w un).degree = 3 :=
  Polynomial.degree_cubic one_ne_zero

/-- (S5) The roots of the characteristic polynomial: the eigenvalues of `L`. -/
def stepRoots (p : Params) : Set ℂ :=
  {z | stepCharPoly p.beta p.w p.noise z = 0}

theorem stepRoots_finite (p : Params) : (stepRoots p).Finite := by
  have hn : stepPoly p.beta p.w p.noise ≠ 0 := by
    intro h
    have := stepPoly_degree p.beta p.w p.noise
    rw [h] at this
    simp at this
  have h := Polynomial.finite_setOfPred_isRoot hn
  simpa only [Polynomial.IsRoot, stepPoly_eval, stepRoots] using h

theorem stepRoots_nonempty (p : Params) : (stepRoots p).Nonempty := by
  obtain ⟨z, hz⟩ := Complex.exists_root (f := stepPoly p.beta p.w p.noise)
    (by rw [stepPoly_degree]; norm_num)
  refine ⟨z, ?_⟩
  have h := hz
  rw [Polynomial.IsRoot.def, stepPoly_eval] at h
  exact h

/-- (S5) The spectral radius of `L` (maximal modulus of an eigenvalue); sec:helps-rate. -/
def stepRadius (p : Params) : ℝ := sSup (norm '' stepRoots p)

/-- (S5) The per-step rate `Lambda = -log rho(L)` (sec:helps-rate).  Note `Real.log 0 = 0`. -/
def perStepRate (p : Params) : ℝ := -Real.log (stepRadius p)

theorem stepRadius_attained (p : Params) : ∃ z ∈ stepRoots p, ‖z‖ = stepRadius p := by
  have hne := (stepRoots_nonempty p).image norm
  have hfin := (stepRoots_finite p).image norm
  obtain ⟨z, hz, h⟩ := hne.csSup_mem hfin
  exact ⟨z, hz, h⟩

/-- (S5) Every eigenvalue has modulus at most `stepRadius`. -/
theorem norm_le_stepRadius (p : Params) {z : ℂ} (hz : z ∈ stepRoots p) :
    ‖z‖ ≤ stepRadius p :=
  le_csSup ((stepRoots_finite p).image norm).bddAbove ⟨z, hz, rfl⟩

theorem stepRadius_nonneg (p : Params) : 0 ≤ stepRadius p := by
  obtain ⟨z, _, h⟩ := stepRadius_attained p
  rw [← h]; exact norm_nonneg z

/-- (S5) A real eigenvalue of modulus `x` gives `x ≤ stepRadius`. -/
theorem abs_le_stepRadius_of_real_root (p : Params) {x : ℝ}
    (hx : stepCharPolyR p.beta p.w p.noise x = 0) : |x| ≤ stepRadius p := by
  have hz : (x : ℂ) ∈ stepRoots p := by
    show stepCharPoly p.beta p.w p.noise (x : ℂ) = 0
    rw [stepCharPoly_ofReal, hx]; simp
  simpa using norm_le_stepRadius p hz

/-- (S6) The real cubic is eventually nonnegative: there is `y ≥ x` with value `≥ 0`. -/
theorem exists_stepCharPolyR_nonneg (beta w un x : ℝ) :
    ∃ y, x ≤ y ∧ 0 ≤ stepCharPolyR beta w un y := by
  set M : ℝ := 1 + |stepC2 beta w un| + |stepC1 beta w un| + |stepC0 beta| with hM
  have hM1 : 1 ≤ M := by
    have := abs_nonneg (stepC2 beta w un); have := abs_nonneg (stepC1 beta w un)
    have := abs_nonneg (stepC0 beta); linarith
  refine ⟨max x M, le_max_left _ _, ?_⟩
  set y := max x M with hy
  have hyM : M ≤ y := le_max_right _ _
  have hy1 : 1 ≤ y := le_trans hM1 hyM
  have hy0 : 0 ≤ y := by linarith
  rw [stepCharPolyR_expand]
  have hyy : y ≤ y ^ 2 := by nlinarith
  have hy2 : 1 ≤ y ^ 2 := by nlinarith
  have h2 : stepC2 beta w un * y ^ 2 ≥ -(|stepC2 beta w un| * y ^ 2) := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le (stepC2 beta w un)) (sq_nonneg y)
    linarith
  have h1 : stepC1 beta w un * y ≥ -(|stepC1 beta w un| * y ^ 2) := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le (stepC1 beta w un)) hy0
    have h' := mul_le_mul_of_nonneg_left hyy (abs_nonneg (stepC1 beta w un))
    linarith
  have h0 : stepC0 beta ≥ -(|stepC0 beta| * y ^ 2) := by
    have := neg_abs_le (stepC0 beta)
    have h' := mul_le_mul_of_nonneg_left hy2 (abs_nonneg (stepC0 beta))
    linarith
  have hy3 : y ^ 3 ≥ (1 + |stepC2 beta w un| + |stepC1 beta w un| + |stepC0 beta|) * y ^ 2 := by
    have := mul_le_mul_of_nonneg_right hyM (sq_nonneg y)
    rw [hM] at this
    nlinarith
  nlinarith [sq_nonneg y]

/-- (S6) Real-root lower bound: if `x ≥ 0` and the characteristic polynomial is `≤ 0`
at `x`, then `x ≤ stepRadius` (IVT; the cubic tends to `+infinity`). -/
theorem le_stepRadius_of_stepCharPolyR_nonpos (p : Params) {x : ℝ} (_hx : 0 ≤ x)
    (h : stepCharPolyR p.beta p.w p.noise x ≤ 0) : x ≤ stepRadius p := by
  obtain ⟨y, hxy, hy⟩ := exists_stepCharPolyR_nonneg p.beta p.w p.noise x
  have hcont : ContinuousOn (stepCharPolyR p.beta p.w p.noise) (Set.Icc x y) := by
    have : Continuous (stepCharPolyR p.beta p.w p.noise) := by
      unfold stepCharPolyR; fun_prop
    exact this.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Icc (stepCharPolyR p.beta p.w p.noise x)
      (stepCharPolyR p.beta p.w p.noise y) := ⟨h, hy⟩
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc hxy hcont hmem
  have := abs_le_stepRadius_of_real_root p hr0
  have hr' : x ≤ |r| := le_trans hr.1 (le_abs_self r)
  linarith

/-! ### Value at one -/

/-- (S7) `stepCharPoly beta w un 1 = 2 w (1-beta)(1+beta)(1 - totalLoad)` when `1+beta ≠ 0`
(sec:helps-rate). -/
theorem stepCharPolyR_one (p : Params) (h : 1 + p.beta ≠ 0) :
    stepCharPolyR p.beta p.w p.noise 1 = 2 * p.w * (1 - p.beta) * (1 + p.beta) * (1 - p.totalLoad) := by
  unfold stepCharPolyR Params.totalLoad Params.curvature
  field_simp
  ring

theorem stepCharPoly_one (p : Params) (h : 1 + p.beta ≠ 0) :
    stepCharPoly p.beta p.w p.noise 1 =
      2 * (p.w : ℂ) * (1 - (p.beta : ℂ)) * (1 + (p.beta : ℂ)) * (1 - (p.totalLoad : ℂ)) := by
  have := stepCharPoly_ofReal p.beta p.w p.noise 1
  rw [Complex.ofReal_one, stepCharPolyR_one p h] at this
  rw [this]; push_cast; ring

/-- (S7) Easy direction of stability: if `1 ≤ totalLoad`, `w > 0`, `-1 < beta < 1`, then
`1 ≤ stepRadius` (sec:helps-rate). -/
theorem one_le_stepRadius_of_one_le_totalLoad (p : Params) (hw : 0 < p.w)
    (hb1 : p.beta < 1) (hb2 : -1 < p.beta) (hu : 1 ≤ p.totalLoad) :
    1 ≤ stepRadius p := by
  apply le_stepRadius_of_stepCharPolyR_nonpos p zero_le_one
  rw [stepCharPolyR_one p (by linarith)]
  have h1 : 0 < 1 - p.beta := by linarith
  have h2 : 0 < 1 + p.beta := by linarith
  have : 0 < 2 * p.w * (1 - p.beta) * (1 + p.beta) := by positivity
  nlinarith

/-! ### Retention-clock substitution -/

/-- The limiting cubic `chi(mu; Delta, u) = mu^3+3mu^2+(2+4Delta)mu+4Delta(1-u)`
(lem:L3, lem:helps-transfer). -/
def chiC {K : Type*} [CommRing K] (mu Delta u : K) : K :=
  mu ^ 3 + 3 * mu ^ 2 + (2 + 4 * Delta) * mu + 4 * Delta * (1 - u)

/-- The remainder in the retention-clock substitution (it has no `mu^3` term). -/
def transferRemainder {K : Type*} [CommRing K] (eps Delta un mu : K) : K :=
  -Delta ^ 2 * eps ^ 2 * mu ^ 2 - Delta ^ 2 * eps ^ 2 * mu - Delta ^ 2 * eps * mu
    - Delta ^ 2 * eps - 2 * Delta * eps * mu ^ 2 * un - 2 * Delta * eps * mu ^ 2
    + 2 * Delta * eps * mu * un - 2 * Delta * eps * mu + 4 * Delta * mu ^ 2
    - 6 * Delta * mu * un + 2 * Delta * mu + 2 * Delta * un - 2 * Delta
    - mu ^ 2 - mu

/-- `chiC` agrees with `spectrumPolynomial` on reals. -/
theorem chiC_eq_spectrumPolynomial (mu Delta u : ℝ) :
    chiC mu Delta u = spectrumPolynomial Delta u mu := by
  simp [chiC, spectrumPolynomial]

/-- (S8) Retention-clock substitution, real variable (lem:helps-transfer, Step 2):
`stepCharPoly (1-eps) (eps^2 Delta) un (1+eps mu) = eps^3 (chi + eps R)`. -/
theorem stepCharPolyR_retention_clock (eps Delta un mu : ℝ) :
    stepCharPolyR (1 - eps) (eps ^ 2 * Delta) un (1 + eps * mu) =
      eps ^ 3 * (chiC mu Delta un + eps * transferRemainder eps Delta un mu) := by
  simp only [stepCharPolyR, chiC, transferRemainder]; ring

/-- (S8) Retention-clock substitution, complex variable `mu` (lem:helps-transfer). -/
theorem stepCharPoly_retention_clock (eps Delta un : ℝ) (mu : ℂ) :
    stepCharPoly (1 - eps) (eps ^ 2 * Delta) un (1 + (eps : ℂ) * mu) =
      (eps : ℂ) ^ 3 * (chiC mu (Delta : ℂ) (un : ℂ)
        + (eps : ℂ) * transferRemainder (eps : ℂ) (Delta : ℂ) (un : ℂ) mu) := by
  simp only [stepCharPoly, chiC, transferRemainder]; push_cast; ring

/-- `Params`-level form of (S8): with `beta = 1 - eps`, `w = eps^2 Delta`. -/
theorem stepCharPoly_retention_clock_params (p : Params) (Delta : ℝ)
    (hw : p.w = p.eps ^ 2 * Delta) (mu : ℂ) :
    stepCharPoly p.beta p.w p.noise (1 + (p.eps : ℂ) * mu) =
      (p.eps : ℂ) ^ 3 * (chiC mu (Delta : ℂ) (p.noise : ℂ)
        + (p.eps : ℂ) * transferRemainder (p.eps : ℂ) (Delta : ℂ) (p.noise : ℂ) mu) := by
  have hb : p.beta = 1 - p.eps := by simp [Params.eps]
  rw [hb, hw]
  exact stepCharPoly_retention_clock p.eps Delta p.noise mu

/-! ### Conjugation to the continuum generator -/

/-- The rescaling `diag(1, (eps Delta)^2, eps Delta)` of `(R,V,C)` coordinates. -/
def retentionScale (eps Delta : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![1, (eps * Delta) ^ 2, eps * Delta]

/-- Its inverse. -/
def retentionScaleInv (eps Delta : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![1, ((eps * Delta) ^ 2)⁻¹, (eps * Delta)⁻¹]

theorem retentionScaleInv_mul (eps Delta : ℝ) (he : eps ≠ 0) (hD : Delta ≠ 0) :
    retentionScaleInv eps Delta * retentionScale eps Delta = 1 := by
  have : eps * Delta ≠ 0 := mul_ne_zero he hD
  unfold retentionScaleInv retentionScale
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i; fin_cases i <;> simp [this] <;> field_simp

/-- The matrix `G` of the tex (Step 1 of lem:helps-transfer); it depends on `eps`. -/
def transferG (eps Delta un : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Delta * (eps ^ 2 * Delta + 2 * eps * un - 2), (1 - eps) ^ 2 * Delta ^ 2,
      2 * Delta * (1 + eps * Delta - eps ^ 2 * Delta);
     1, 1, -2;
     -eps * Delta - 2 * un, (2 - eps) * Delta, -2 * (1 - eps) * Delta]

/-- (S9) Step 1 of lem:helps-transfer: if `beta = 1 - eps` and `w = eps^2 Delta`, then
`D^{-1} L D = 1 + eps A + eps^2 G` with `A = continuumGenerator Delta u_n`
(`D = diag(1, (eps Delta)^2, eps Delta)`). -/
theorem stepLinearMatrix_conj (p : Params) (Delta : ℝ) (he : p.eps ≠ 0) (hD : Delta ≠ 0)
    (hw : p.w = p.eps ^ 2 * Delta) :
    retentionScaleInv p.eps Delta * stepLinearMatrix p * retentionScale p.eps Delta =
      1 + p.eps • continuumGenerator Delta p.noise
        + p.eps ^ 2 • transferG p.eps Delta p.noise := by
  rcases p with ⟨b, w, un, a⟩
  simp only [Params.eps] at he hw ⊢
  subst hw
  have he' : (1 - b) * Delta ≠ 0 := mul_ne_zero he hD
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [retentionScaleInv, retentionScale, stepLinearMatrix, continuumGenerator, transferG,
      Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ, Params.eps] <;>
    field_simp <;> ring

end

end SparseSGD.Scaling.Helps
