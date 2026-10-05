import SparseSGD.Logistic.V2.WindowMapAlgebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic

/-! # v2: unit-circle spectrum below `w_c` and period doubling at `w_c` (prop:W2 (ii),(iii))

Builds on `WindowMapAlgebra`.  The characteristic polynomial of the undamped window
Jacobian `J0` is `(z-1) (z^4 + b z^3 + c z^2 + b z + 1)`; the palindromic quartic factors
as `(z^2 - m1 z + 1)(z^2 - m2 z + 1)` with `m1 + m2 = -b`, `m1 m2 = c - 2`, i.e. `m1, m2`
are the roots of `p(m) = m^2 + b m + c - 2`.

* `window_roots_inside`: for `0 < w < w_c` both roots lie in `(-2, 2)`.
* `prop_W2_ii`: hence all eigenvalues of `J0` lie on the unit circle, and they are simple.
* `prop_W2_iii_critical`, `prop_W2_iii_above`: `-1` is an eigenvalue at `w_c`, and a real
  eigenvalue `< -1` appears just above `w_c`.
* `real_eigenvalue_persistence`: a real eigenvalue `< -1` at which the characteristic
  polynomial changes sign persists under entrywise-small perturbation (the drift-recursion
  Jacobian converging to `J0` is a hypothesis, not formalized).
-/
namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic
noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-! ### Generic algebra -/

/-- v2 prop:W2 (ii): the palindromic quartic factors through the roots of `p`. -/
theorem palindromic_factor {R : Type*} [CommRing R] (b c m1 m2 z : R)
    (hs : m1 + m2 = -b) (hp : m1 * m2 = c - 2) :
    z ^ 4 + b * z ^ 3 + c * z ^ 2 + b * z + 1 = (z ^ 2 - m1 * z + 1) * (z ^ 2 - m2 * z + 1) := by
  have hb : b = -(m1 + m2) := by rw [hs]; ring
  have hc : c = m1 * m2 + 2 := by rw [hp]; ring
  subst hb hc
  ring

/-- The upper-half-plane unit-circle point with real part `m/2`. -/
def unitRoot (m : ℝ) : ℂ := ⟨m / 2, Real.sqrt (1 - m ^ 2 / 4)⟩

theorem unitRoot_re (m : ℝ) : (unitRoot m).re = m / 2 := rfl

theorem unitRoot_im_pos {m : ℝ} (hm : |m| < 2) : 0 < (unitRoot m).im := by
  have : m ^ 2 < 4 := by
    have := sq_lt_sq' (by linarith [abs_lt.1 hm]) (abs_lt.1 hm).2
    nlinarith [abs_lt.1 hm]
  show 0 < Real.sqrt (1 - m ^ 2 / 4)
  apply Real.sqrt_pos.2; linarith

theorem unitRoot_add_conj (m : ℝ) : unitRoot m + (starRingEnd ℂ) (unitRoot m) = (m : ℂ) := by
  apply Complex.ext <;> simp [unitRoot]

theorem unitRoot_mul_conj {m : ℝ} (hm : |m| < 2) :
    unitRoot m * (starRingEnd ℂ) (unitRoot m) = 1 := by
  have h4 : m ^ 2 < 4 := by nlinarith [abs_lt.1 hm]
  have hs : Real.sqrt (1 - m ^ 2 / 4) ^ 2 = 1 - m ^ 2 / 4 :=
    Real.sq_sqrt (by linarith)
  apply Complex.ext
  · simp [unitRoot]; nlinarith [hs]
  · simp [unitRoot]; ring

theorem unitRoot_factor {m : ℝ} (hm : |m| < 2) (z : ℂ) :
    z ^ 2 - (m : ℂ) * z + 1 = (z - unitRoot m) * (z - (starRingEnd ℂ) (unitRoot m)) := by
  have h1 := unitRoot_add_conj m
  have h2 := unitRoot_mul_conj hm
  linear_combination z * h1 - h2

theorem unitRoot_norm {m : ℝ} (hm : |m| < 2) : ‖unitRoot m‖ = 1 := by
  have h2 := unitRoot_mul_conj hm
  rw [Complex.mul_conj] at h2
  have h3 : Complex.normSq (unitRoot m) = 1 := by exact_mod_cast h2
  have : ‖unitRoot m‖ ^ 2 = 1 := by rw [Complex.sq_norm]; exact h3
  nlinarith [norm_nonneg (unitRoot m)]

/-- v2 prop:W2 (ii): for real `m` with `|m| < 2`, every complex root of `z^2 - m z + 1` is
non-real with `|z| = 1`. -/
theorem quadratic_unit_roots (m : ℝ) (hm : |m| < 2) (z : ℂ)
    (hz : z ^ 2 - (m : ℂ) * z + 1 = 0) : z.im ≠ 0 ∧ ‖z‖ = 1 := by
  rw [unitRoot_factor hm] at hz
  have hu := unitRoot_im_pos hm
  have hn := unitRoot_norm hm
  rcases mul_eq_zero.1 hz with h | h
  · have : z = unitRoot m := sub_eq_zero.1 h
    subst this
    exact ⟨hu.ne', hn⟩
  · have : z = (starRingEnd ℂ) (unitRoot m) := sub_eq_zero.1 h
    subst this
    refine ⟨by simpa using hu.ne', by simpa using hn⟩

/-- v2 prop:W2 (iii): for real `m < -2`, `z^2 - m z + 1` has a real root `z < -1`
(namely `z = (m - sqrt (m^2 - 4))/2`, and its inverse lies in `(-1, 0)`). -/
theorem quadratic_neg_real_root (m : ℝ) (hm : m < -2) :
    ∃ z : ℝ, z < -1 ∧ z ^ 2 - m * z + 1 = 0 := by
  have h4 : 0 ≤ m ^ 2 - 4 := by nlinarith
  have ht := Real.sq_sqrt h4
  have ht0 := Real.sqrt_nonneg (m ^ 2 - 4)
  refine ⟨(m - Real.sqrt (m ^ 2 - 4)) / 2, by linarith, ?_⟩
  linear_combination (1 / 4 : ℝ) * ht

/-! ### Window roots -/

/-- `b < 4` on `(0, w_c)`, proved by the intermediate value theorem on the polynomial `b`:
if `b(w1) >= 4` there is `w2 <= w1` with `b(w2) = 4`; at `w2` the vertex of `p` is `-2`,
so `p(-2) = -disc/4 < 0`, contradicting `p(-2) > 0`. -/
theorem windowCoefB_lt_four (theta R w : ℝ) (hR : 0 < R) (hw0 : 0 < w)
    (hwc : w < windowCritical theta R) : windowCoefB theta R w < 4 := by
  by_contra hcon
  have hcon := not_lt.1 hcon
  have hcont : Continuous (fun x : ℝ => windowCoefB theta R x) := by
    unfold windowCoefB; fun_prop
  have hb0 : windowCoefB theta R 0 = -4 := by simp [windowCoefB]; norm_num
  have hmem : (4 : ℝ) ∈ Set.Icc (windowCoefB theta R 0) (windowCoefB theta R w) := by
    rw [hb0]; exact ⟨by norm_num, hcon⟩
  obtain ⟨w2, ⟨hw2a, hw2b⟩, hw2⟩ :=
    intermediate_value_Icc hw0.le hcont.continuousOn hmem
  have hw2 : windowCoefB theta R w2 = 4 := hw2
  have hw2pos : 0 < w2 := by
    rcases hw2a.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, hb0] at hw2; norm_num at hw2
  have hw2c : w2 < windowCritical theta R := lt_of_le_of_lt hw2b hwc
  have hQ := windowQ_pos_of_lt theta R w2 hR hw2c
  have hlt2 : w2 < 2 := lt_trans hw2c (windowCritical_lt_two theta R hR)
  have hp := windowP_neg_two theta R w2
  have hD := windowD_pos theta R w2 hR hlt2
  have hdisc := window_discriminant theta R w2
  have hpp : 0 < windowP theta R w2 (-2) := by rw [hp]; nlinarith
  unfold windowP at hpp
  rw [hw2] at hpp hdisc
  have : 0 < w2 ^ 2 * windowD theta R w2 / 4 := by positivity
  nlinarith

/-- `D(w) > 0` and the discriminant is positive on `(0, w_c)`. -/
theorem window_disc_pos (theta R w : ℝ) (hR : 0 < R) (hw0 : 0 < w) (hw2 : w < 2) :
    0 < windowCoefB theta R w ^ 2 - 4 * (windowCoefC theta R w - 2) := by
  rw [window_discriminant]
  have := windowD_pos theta R w hR hw2
  positivity

/-- v2 prop:W2 (ii) core: for `R > 0`, `0 < w < w_c`, the quadratic `p` has two distinct
real roots `m1 < m2`, both in `(-2, 2)` (given as `m1 + m2 = -b`, `m1 m2 = c - 2`). -/
theorem window_roots_inside (theta R w : ℝ) (hR : 0 < R) (hw0 : 0 < w)
    (hwc : w < windowCritical theta R) :
    ∃ m1 m2 : ℝ, m1 < m2 ∧ -2 < m1 ∧ m2 < 2 ∧
      m1 + m2 = -windowCoefB theta R w ∧ m1 * m2 = windowCoefC theta R w - 2 := by
  have hw2 : w < 2 := lt_trans hwc (windowCritical_lt_two theta R hR)
  have hb4 := windowCoefB_lt_four theta R w hR hw0 hwc
  have hb4' := windowCoefB_add_four_pos theta R w hR hw0 hw2
  have hp2 := windowP_two_pos theta R w hR hw0 hw2
  have hpm2 : 0 < windowP theta R w (-2) := by
    rw [windowP_neg_two]
    have := windowQ_pos_of_lt theta R w hR hwc
    have : 0 < 2 - w := by linarith
    positivity
  have hdisc := window_disc_pos theta R w hR hw0 hw2
  unfold windowP at hp2 hpm2
  generalize windowCoefB theta R w = b at *
  generalize windowCoefC theta R w = c at *
  have hs := Real.sq_sqrt hdisc.le
  have hs0 := Real.sqrt_pos.2 hdisc
  set s := Real.sqrt (b ^ 2 - 4 * (c - 2)) with hsdef
  refine ⟨(-b - s) / 2, (-b + s) / 2, by linarith, ?_, ?_, by ring, ?_⟩
  · have : s < 4 - b := by
      rw [hsdef, Real.sqrt_lt' (by linarith)]; nlinarith
    linarith
  · have : s < b + 4 := by
      rw [hsdef, Real.sqrt_lt' (by linarith)]; nlinarith
    linarith
  · linear_combination (-1 / 4 : ℝ) * hs

/-! ### Characteristic polynomial and spectrum -/

/-- The complex characteristic polynomial of `J0`, factored through `p`'s roots. -/
theorem window_charpoly_factored (theta R w : ℝ) (m1 m2 : ℝ)
    (hs : m1 + m2 = -windowCoefB theta R w) (hp : m1 * m2 = windowCoefC theta R w - 2)
    (z : ℂ) :
    (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) - (windowJacobian theta R w).map Complex.ofReal).det =
      (z - 1) * ((z ^ 2 - (m1 : ℂ) * z + 1) * (z ^ 2 - (m2 : ℂ) * z + 1)) := by
  rw [window_charpoly]
  congr 1
  apply palindromic_factor
  · exact_mod_cast hs
  · exact_mod_cast hp

/-- v2 prop:W2 (ii) [hypothesis `R* > 0`]: for `0 < w < w_c`, every eigenvalue of `J0` has
modulus one, and the spectrum is simple: the characteristic polynomial equals
`(X-1)(X-z1)(X-conj z1)(X-z2)(X-conj z2)` with these five numbers pairwise distinct. -/
theorem prop_W2_ii (theta R w : ℝ) (hR : 0 < R) (hw0 : 0 < w)
    (hwc : w < windowCritical theta R) :
    (∀ z : ℂ, (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
        (windowJacobian theta R w).map Complex.ofReal).det = 0 → ‖z‖ = 1) ∧
    ∃ z1 z2 : ℂ, ‖z1‖ = 1 ∧ ‖z2‖ = 1 ∧ 0 < z1.im ∧ 0 < z2.im ∧
      (∀ z : ℂ, (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
          (windowJacobian theta R w).map Complex.ofReal).det =
        (z - 1) * (z - z1) * (z - (starRingEnd ℂ) z1) * (z - z2) * (z - (starRingEnd ℂ) z2)) ∧
      [(1 : ℂ), z1, (starRingEnd ℂ) z1, z2, (starRingEnd ℂ) z2].Nodup := by
  obtain ⟨m1, m2, h12, h1, h2, hs, hp⟩ := window_roots_inside theta R w hR hw0 hwc
  have hm1 : |m1| < 2 := abs_lt.2 ⟨h1, by linarith⟩
  have hm2 : |m2| < 2 := abs_lt.2 ⟨by linarith, h2⟩
  refine ⟨?_, unitRoot m1, unitRoot m2, unitRoot_norm hm1, unitRoot_norm hm2,
    unitRoot_im_pos hm1, unitRoot_im_pos hm2, ?_, ?_⟩
  · intro z hz
    rw [window_charpoly_factored theta R w m1 m2 hs hp z] at hz
    rcases mul_eq_zero.1 hz with h | h
    · have : z = 1 := sub_eq_zero.1 h
      subst this; simp
    · rcases mul_eq_zero.1 h with h | h
      · exact (quadratic_unit_roots m1 hm1 z h).2
      · exact (quadratic_unit_roots m2 hm2 z h).2
  · intro z
    rw [window_charpoly_factored theta R w m1 m2 hs hp z, unitRoot_factor hm1,
      unitRoot_factor hm2]
    ring
  · have i1 := unitRoot_im_pos hm1
    have i2 := unitRoot_im_pos hm2
    have r1 := unitRoot_re m1
    have r2 := unitRoot_re m2
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> intro h <;>
      first
      | (have := congrArg Complex.im h; simp at this; linarith)
      | (have := congrArg Complex.re h; simp [r1, r2] at this; linarith)

/-! ### Period doubling -/

/-- `x ↦ det (x - J0)` equals `(x - 1) (x^4 + b x^3 + c x^2 + b x + 1)`. -/
theorem window_det_x_sub (theta R w x : ℝ) :
    (x • (1 : Matrix (Fin 5) (Fin 5) ℝ) - windowJacobian theta R w).det =
      (x - 1) * (x ^ 4 + windowCoefB theta R w * x ^ 3 + windowCoefC theta R w * x ^ 2
        + windowCoefB theta R w * x + 1) := by
  have e : x • (1 : Matrix (Fin 5) (Fin 5) ℝ) - windowJacobian theta R w =
      -(windowJacobian theta R w - x • (1 : Matrix (Fin 5) (Fin 5) ℝ)) := by
    rw [neg_sub]
  rw [e, Matrix.det_neg, windowJacobian_det_sub_smul_one]
  simp
  ring

/-- A real root of the characteristic polynomial is an eigenvalue with an eigenvector. -/
theorem exists_eigenvector_of_det_eq_zero (M : Matrix (Fin 5) (Fin 5) ℝ) (z : ℝ)
    (h : (z • (1 : Matrix (Fin 5) (Fin 5) ℝ) - M).det = 0) :
    ∃ v : Fin 5 → ℝ, v ≠ 0 ∧ M.mulVec v = z • v := by
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv0
  exact hv0.symm

/-- v2 prop:W2 (iii), fixed map: at `w = w_c`, `-1` is an eigenvalue of `J0`
(`det (J0 + 1) = 0`, with a null eigenvector). -/
theorem prop_W2_iii_critical (theta R : ℝ) (hR : 0 < R) :
    (windowJacobian theta R (windowCritical theta R) + 1).det = 0 ∧
    ∃ v : Fin 5 → ℝ, v ≠ 0 ∧
      (windowJacobian theta R (windowCritical theta R)).mulVec v = (-1 : ℝ) • v := by
  have hdet : (windowJacobian theta R (windowCritical theta R) + 1).det = 0 := by
    rw [windowJacobian_det_add_one, windowQ_critical theta R hR]; ring
  refine ⟨hdet, ?_⟩
  apply exists_eigenvector_of_det_eq_zero
  have e : (-1 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ) - windowJacobian theta R (windowCritical theta R)
      = -(windowJacobian theta R (windowCritical theta R) + 1) := by
    rw [neg_add]; simp; abel
  rw [e, Matrix.det_neg, hdet]; simp

/-- v2 prop:W2 (iii), fixed map: there is `eta > 0` such that for `w` in `(w_c, w_c + eta)`
the Jacobian `J0` has a real eigenvalue `z < -1` (with eigenvector).  Moreover the
characteristic polynomial changes sign at `z`, in the form
`∀ delta > 0, ∃ x1 x2` within `delta` of `z` with `det (x1 - J0) * det (x2 - J0) < 0`. -/
theorem prop_W2_iii_above (theta R : ℝ) (hR : 0 < R) :
    ∃ eta > 0, ∀ w, windowCritical theta R < w → w < windowCritical theta R + eta →
      ∃ z : ℝ, z < -1 ∧
        (z • (1 : Matrix (Fin 5) (Fin 5) ℝ) - windowJacobian theta R w).det = 0 ∧
        (∃ v : Fin 5 → ℝ, v ≠ 0 ∧ (windowJacobian theta R w).mulVec v = z • v) ∧
        ∀ δ > 0, ∃ x1 x2 : ℝ, |x1 - z| < δ ∧ |x2 - z| < δ ∧
          (x1 • (1 : Matrix (Fin 5) (Fin 5) ℝ) - windowJacobian theta R w).det *
          (x2 • (1 : Matrix (Fin 5) (Fin 5) ℝ) - windowJacobian theta R w).det < 0 := by
  obtain ⟨eta0, heta0, hQ⟩ := windowQ_neg_above theta R hR
  have hc2 := windowCritical_lt_two theta R hR
  refine ⟨min eta0 (2 - windowCritical theta R), lt_min heta0 (by linarith), ?_⟩
  intro w hw1 hw2
  have hw2a : w < windowCritical theta R + eta0 := lt_of_lt_of_le hw2 (by
    have := min_le_left eta0 (2 - windowCritical theta R); linarith)
  have hw2b : w < 2 := lt_of_lt_of_le hw2 (by
    have := min_le_right eta0 (2 - windowCritical theta R); linarith)
  have hQw := hQ w hw1 hw2a
  have hpm2 : windowP theta R w (-2) < 0 := by
    rw [windowP_neg_two]
    have : 0 < 2 - w := by linarith
    nlinarith
  have hw0 : 0 < w := lt_trans (windowCritical_pos theta R hR) hw1
  have hdisc := window_disc_pos theta R w hR hw0 hw2b
  unfold windowP at hpm2
  have hdet : ∀ x : ℝ, (x • (1 : Matrix (Fin 5) (Fin 5) ℝ) - windowJacobian theta R w).det =
      (x - 1) * (x ^ 4 + windowCoefB theta R w * x ^ 3 + windowCoefC theta R w * x ^ 2
        + windowCoefB theta R w * x + 1) := window_det_x_sub theta R w
  generalize windowCoefB theta R w = b at hpm2 hdisc hdet
  generalize windowCoefC theta R w = c at hpm2 hdisc hdet
  -- roots of p
  have hs := Real.sq_sqrt hdisc.le
  have hs0 := Real.sqrt_nonneg (b ^ 2 - 4 * (c - 2))
  set s := Real.sqrt (b ^ 2 - 4 * (c - 2)) with hsdef
  have hs1 : 4 - b < s := Real.lt_sqrt_of_sq_lt (by nlinarith)
  have hs2 : b - 4 < s := Real.lt_sqrt_of_sq_lt (by nlinarith)
  set m1 : ℝ := (-b - s) / 2 with hm1
  set m2 : ℝ := (-b + s) / 2 with hm2
  have hm1lt : m1 < -2 := by rw [hm1]; linarith
  have hm2gt : -2 < m2 := by rw [hm2]; linarith
  have hsum : m1 + m2 = -b := by rw [hm1, hm2]; ring
  have hprod : m1 * m2 = c - 2 := by rw [hm1, hm2]; linear_combination (-1 / 4 : ℝ) * hs
  -- the real root z
  have h4 : 0 ≤ m1 ^ 2 - 4 := by nlinarith
  have ht := Real.sq_sqrt h4
  have ht0 := Real.sqrt_nonneg (m1 ^ 2 - 4)
  set t := Real.sqrt (m1 ^ 2 - 4) with htdef
  set z : ℝ := (m1 - t) / 2 with hzdef
  set z' : ℝ := (m1 + t) / 2 with hz'def
  have hz1 : z < -1 := by rw [hzdef]; linarith
  have hzz' : z * z' = 1 := by rw [hzdef, hz'def]; linear_combination (-1 / 4 : ℝ) * ht
  have hzsum : z + z' = m1 := by rw [hzdef, hz'def]; ring
  have hz'gt : -1 < z' := by
    by_contra hcon
    have hcon := not_lt.1 hcon
    nlinarith
  have hfac : ∀ x : ℝ, (x • (1 : Matrix (Fin 5) (Fin 5) ℝ) - windowJacobian theta R w).det =
      (x - z) * ((x - 1) * (x - z') * (x ^ 2 - m2 * x + 1)) := by
    intro x
    rw [hdet x]
    have := palindromic_factor b c m1 m2 x hsum hprod
    rw [this]
    have e : x ^ 2 - m1 * x + 1 = (x - z) * (x - z') := by
      rw [← hzsum]; linear_combination (-1) * hzz'
    rw [e]; ring
  have hg : ∀ x : ℝ, x < -1 → 0 < (x - 1) * (x - z') * (x ^ 2 - m2 * x + 1) := by
    intro x hx
    have a1 : x - 1 < 0 := by linarith
    have a2 : x - z' < 0 := by linarith
    have a3 : 0 < x ^ 2 - m2 * x + 1 := by nlinarith [sq_nonneg (x + 1)]
    exact mul_pos (mul_pos_of_neg_of_neg a1 a2) a3
  have hroot : (z • (1 : Matrix (Fin 5) (Fin 5) ℝ) - windowJacobian theta R w).det = 0 := by
    rw [hfac]; ring
  refine ⟨z, hz1, hroot, exists_eigenvector_of_det_eq_zero _ z hroot, ?_⟩
  intro δ hδ
  set τ := min (δ / 2) ((-1 - z) / 2) with hτ
  have hτ0 : 0 < τ := lt_min (by linarith) (by linarith)
  have hτ1 : τ ≤ δ / 2 := min_le_left _ _
  have hτ2 : τ ≤ (-1 - z) / 2 := min_le_right _ _
  refine ⟨z - τ, z + τ, ?_, ?_, ?_⟩
  · rw [show z - τ - z = -τ by ring, abs_neg, abs_of_pos hτ0]; linarith
  · rw [show z + τ - z = τ by ring, abs_of_pos hτ0]; linarith
  · obtain ⟨g1, hg1, hf1⟩ : ∃ g, 0 < g ∧ ((z - τ) • (1 : Matrix (Fin 5) (Fin 5) ℝ) -
        windowJacobian theta R w).det = (z - τ - z) * g :=
      ⟨_, hg (z - τ) (by linarith), hfac (z - τ)⟩
    obtain ⟨g2, hg2, hf2⟩ : ∃ g, 0 < g ∧ ((z + τ) • (1 : Matrix (Fin 5) (Fin 5) ℝ) -
        windowJacobian theta R w).det = (z + τ - z) * g :=
      ⟨_, hg (z + τ) (by linarith), hfac (z + τ)⟩
    rw [hf1, hf2]
    have e : (z - τ - z) * g1 * ((z + τ - z) * g2) = -(τ ^ 2 * (g1 * g2)) := by ring
    rw [e]
    have := mul_pos (pow_pos hτ0 2) (mul_pos hg1 hg2)
    linarith

/-! ### Persistence under perturbation -/

/-- The characteristic polynomial `x ↦ det (x - M)` is continuous. -/
theorem continuous_det_x_sub (M : Matrix (Fin 5) (Fin 5) ℝ) :
    Continuous (fun x : ℝ => (x • (1 : Matrix (Fin 5) (Fin 5) ℝ) - M).det) := by
  apply Continuous.matrix_det
  exact (continuous_id.smul continuous_const).sub continuous_const

/-- Core of v2 prop:W2 (iii) for the drift recursion: if `J ε → J0` entrywise along a filter
`l` (e.g. `𝓝[>] 0`) and `x ↦ det (x - J0)` is nonzero with opposite signs at two points
`x1, x2 ≤ -1`, then eventually `J ε` has a real eigenvalue `< -1`; in particular an
eigenvalue of modulus `> 1`.  The convergence of the drift-recursion Jacobian to `J0` is a
hypothesis here, not formalized. -/
theorem real_eigenvalue_persistence_of_sign_change
    {l : Filter ℝ} (J : ℝ → Matrix (Fin 5) (Fin 5) ℝ) (J0 : Matrix (Fin 5) (Fin 5) ℝ)
    (hJ : ∀ i j, Filter.Tendsto (fun ε => J ε i j) l (nhds (J0 i j)))
    (x1 x2 : ℝ) (hx1 : x1 ≤ -1) (hx2 : x2 ≤ -1)
    (hsign : (x1 • (1 : Matrix (Fin 5) (Fin 5) ℝ) - J0).det *
      (x2 • (1 : Matrix (Fin 5) (Fin 5) ℝ) - J0).det < 0) :
    ∀ᶠ ε in l, ∃ z : ℝ, z < -1 ∧
      (z • (1 : Matrix (Fin 5) (Fin 5) ℝ) - J ε).det = 0 ∧
      ∃ z' : ℂ, (z' • (1 : Matrix (Fin 5) (Fin 5) ℂ) - (J ε).map Complex.ofReal).det = 0 ∧
        1 < ‖z'‖ := by
  have hJt : Filter.Tendsto J l (nhds J0) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hJ i j
  have hdet : ∀ x : ℝ, Filter.Tendsto
      (fun ε => (x • (1 : Matrix (Fin 5) (Fin 5) ℝ) - J ε).det) l
      (nhds ((x • (1 : Matrix (Fin 5) (Fin 5) ℝ) - J0).det)) := by
    intro x
    have hc : Continuous (fun M : Matrix (Fin 5) (Fin 5) ℝ =>
        (x • (1 : Matrix (Fin 5) (Fin 5) ℝ) - M).det) := by
      apply Continuous.matrix_det
      exact continuous_const.sub continuous_id
    exact (hc.tendsto J0).comp hJt
  have hprod := (hdet x1).mul (hdet x2)
  have hev : ∀ᶠ ε in l, (x1 • (1 : Matrix (Fin 5) (Fin 5) ℝ) - J ε).det *
      (x2 • (1 : Matrix (Fin 5) (Fin 5) ℝ) - J ε).det < 0 :=
    hprod.eventually (gt_mem_nhds hsign)
  filter_upwards [hev] with ε hε
  have hcont := continuous_det_x_sub (J ε)
  set f := fun x : ℝ => (x • (1 : Matrix (Fin 5) (Fin 5) ℝ) - J ε).det with hf
  have hne1 : f x1 ≠ 0 := by intro h; simp only [hf] at h; rw [h] at hε; simp at hε
  have hne2 : f x2 ≠ 0 := by intro h; simp only [hf] at h; rw [h] at hε; simp at hε
  have h0mem : (0 : ℝ) ∈ Set.uIcc (f x1) (f x2) := by
    rcases mul_neg_iff.1 hε with ⟨a, b⟩ | ⟨a, b⟩
    · exact Set.mem_uIcc.2 (Or.inr ⟨b.le, a.le⟩)
    · exact Set.mem_uIcc.2 (Or.inl ⟨a.le, b.le⟩)
  obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc hcont.continuousOn h0mem
  have hzle : z ≤ max x1 x2 := (Set.mem_uIcc.1 hz).elim (fun h => le_trans h.2 (le_max_right _ _))
      (fun h => le_trans h.2 (le_max_left _ _)) |>.trans le_rfl
  have hz1 : z ≠ x1 := by rintro rfl; exact hne1 hz0
  have hz2 : z ≠ x2 := by rintro rfl; exact hne2 hz0
  have hzlt : z < -1 := by
    rcases le_total x1 x2 with h | h
    · rw [max_eq_right h] at hzle
      exact lt_of_le_of_ne hzle hz2 |>.trans_le hx2
    · rw [max_eq_left h] at hzle
      exact lt_of_le_of_ne hzle hz1 |>.trans_le hx1
  refine ⟨z, hzlt, hz0, (z : ℂ), ?_, ?_⟩
  · have e : (z : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ) - (J ε).map Complex.ofReal =
        (z • (1 : Matrix (Fin 5) (Fin 5) ℝ) - J ε).map Complex.ofReal := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [e]
    have := RingHom.map_det Complex.ofRealHom (z • (1 : Matrix (Fin 5) (Fin 5) ℝ) - J ε)
    have h2 : (Complex.ofRealHom.mapMatrix (z • (1 : Matrix (Fin 5) (Fin 5) ℝ) - J ε)) =
        (z • (1 : Matrix (Fin 5) (Fin 5) ℝ) - J ε).map Complex.ofReal := rfl
    rw [h2] at this
    rw [← this]
    simp
    exact hz0
  · rw [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_neg (by linarith)]; linarith

/-- v2 prop:W2 (iii), drift recursion (generic): if `J ε → J0` entrywise and `J0` has a real
eigenvalue `z0 < -1` at which `x ↦ det (x - J0)` changes sign (in the form: for every `δ > 0`
there are `x1, x2` within `δ` of `z0` where the values have opposite signs), then for all
small `ε`, `J ε` has a real eigenvalue `< -1`, hence an eigenvalue of modulus `> 1`.
The hypothesis that the drift-recursion Jacobian converges entrywise to `J0` is not
formalized. -/
theorem real_eigenvalue_persistence
    {l : Filter ℝ} (J : ℝ → Matrix (Fin 5) (Fin 5) ℝ) (J0 : Matrix (Fin 5) (Fin 5) ℝ)
    (hJ : ∀ i j, Filter.Tendsto (fun ε => J ε i j) l (nhds (J0 i j)))
    (z0 : ℝ) (hz0 : z0 < -1)
    (hsign : ∀ δ > 0, ∃ x1 x2 : ℝ, |x1 - z0| < δ ∧ |x2 - z0| < δ ∧
      (x1 • (1 : Matrix (Fin 5) (Fin 5) ℝ) - J0).det *
        (x2 • (1 : Matrix (Fin 5) (Fin 5) ℝ) - J0).det < 0) :
    ∀ᶠ ε in l, ∃ z : ℝ, z < -1 ∧
      (z • (1 : Matrix (Fin 5) (Fin 5) ℝ) - J ε).det = 0 ∧
      ∃ z' : ℂ, (z' • (1 : Matrix (Fin 5) (Fin 5) ℂ) - (J ε).map Complex.ofReal).det = 0 ∧
        1 < ‖z'‖ := by
  obtain ⟨x1, x2, h1, h2, hp⟩ := hsign (-1 - z0) (by linarith)
  have a1 := (abs_lt.1 h1).2
  have a2 := (abs_lt.1 h2).2
  exact real_eigenvalue_persistence_of_sign_change J J0 hJ x1 x2 (by linarith) (by linarith) hp

/-- v2 prop:W2 (iii): the two halves combined.  For `w` slightly above `w_c`, any perturbation
`J ε → J0 = windowJacobian theta R w` (entrywise) has, for small `ε`, an eigenvalue of modulus
`> 1`. -/
theorem prop_W2_iii (theta R : ℝ) (hR : 0 < R) :
    ∃ eta > 0, ∀ w, windowCritical theta R < w → w < windowCritical theta R + eta →
      ∀ {l : Filter ℝ} (J : ℝ → Matrix (Fin 5) (Fin 5) ℝ),
        (∀ i j, Filter.Tendsto (fun ε => J ε i j) l (nhds (windowJacobian theta R w i j))) →
        ∀ᶠ ε in l, ∃ z' : ℂ,
          (z' • (1 : Matrix (Fin 5) (Fin 5) ℂ) - (J ε).map Complex.ofReal).det = 0 ∧ 1 < ‖z'‖ := by
  obtain ⟨eta, heta, h⟩ := prop_W2_iii_above theta R hR
  refine ⟨eta, heta, fun w hw1 hw2 l J hJ => ?_⟩
  obtain ⟨z, hz, -, -, hsign⟩ := h w hw1 hw2
  filter_upwards [real_eigenvalue_persistence J _ hJ z hz hsign] with ε hε
  obtain ⟨_, _, _, z', h1, h2⟩ := hε
  exact ⟨z', h1, h2⟩

end
end SparseSGD.Logistic.V2
