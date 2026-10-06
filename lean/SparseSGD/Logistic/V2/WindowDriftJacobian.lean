import SparseSGD.Logistic.V2.WindowDrift
import SparseSGD.Logistic.V2.WindowUnitCircle

/-! # v2 `prop:W2` (iii) for the drift recursion: the Jacobian and its limit

The drift window map `windowDriftMap r h eps Phi` is differentiable everywhere with explicit
Jacobian `windowDriftJacobian r h eps x` (the temperature `Phi` enters only through an additive
constant, so it does not appear).  At `eps = 0` and at the window fixed point this is the
undamped Jacobian `windowJacobian`, and it depends continuously on `(eps, x)`.  Together with
`windowDrift_fixedPoint_tendsto` and `real_eigenvalue_persistence` this gives
`prop_W2_iii_drift`: for `w = h * exp ((theta^2 + R - r^2)/2)` in `(w_c, 2)`, fixed points of the
drift recursion are linearly unstable for small `eps`.
-/
namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic Filter Topology
noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-- Entries of the Jacobian of the drift window map, in terms of `a = alpha` and the
coordinates `x0, x2, x4` (using `d alpha / d x0 = a x0`, `d alpha / d x2 = a / 2`). -/
def windowDriftJacobianCore (h eps a x0 x2 x4 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1 - h * (a * (x0 ^ 2 + 1)), -(1 - eps), -(h * (a * x0 / 2)), 0, 0;
     h * (a * (x0 ^ 2 + 1)), 1 - eps, h * (a * x0 / 2), 0, 0;
     -2 * (h * x2 * (a * x0)) + (2 * (1 - eps) * h * x4 * (a * x0) + 2 * h ^ 2 * a * x2 * (a * x0)),
     0,
     1 - 2 * (h * (x2 * (a / 2) + a)) + ((1 - eps) * h * x4 * a + h ^ 2 * a ^ 2 * x2 + h ^ 2 * a ^ 2),
     (1 - eps) ^ 2,
     -2 * (1 - eps) + 2 * (1 - eps) * h * a;
     2 * (1 - eps) * h * x4 * (a * x0) + 2 * h ^ 2 * a * x2 * (a * x0), 0,
     (1 - eps) * h * x4 * a + h ^ 2 * a ^ 2 * x2 + h ^ 2 * a ^ 2, (1 - eps) ^ 2,
     2 * (1 - eps) * h * a;
     h * x2 * (a * x0) - (2 * (1 - eps) * h * x4 * (a * x0) + 2 * h ^ 2 * a * x2 * (a * x0)), 0,
     h * (x2 * (a / 2) + a) - ((1 - eps) * h * x4 * a + h ^ 2 * a ^ 2 * x2 + h ^ 2 * a ^ 2),
     -(1 - eps) ^ 2, (1 - eps) - 2 * (1 - eps) * h * a]

/-- The Jacobian of `windowDriftMap r h eps Phi` at `x`. -/
def windowDriftJacobian (r h eps : ℝ) (x : DynamicState) : Matrix (Fin 5) (Fin 5) ℝ :=
  windowDriftJacobianCore h eps (dynamicAlpha r x) (x 0) (x 2) (x 4)

/-- The drift window map is differentiable at every point, with derivative
`windowDriftJacobian r h eps x`. -/
theorem hasFDerivAt_windowDriftMap (r h eps Phi : ℝ) (x : DynamicState) :
    HasFDerivAt (windowDriftMap r h eps Phi)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (windowDriftJacobian r h eps x))) x := by
  have hA := hasFDerivAt_dynamicAlpha_window r x
  have hP : ∀ i : Fin 5, HasFDerivAt (fun y : DynamicState => y i)
      (ContinuousLinearMap.proj i : DynamicState →L[ℝ] ℝ) x :=
    fun i => hasFDerivAt_apply i _
  have hg := (hA.mul (hP 0)).sub_const r
  have hU := ((hP 1).const_mul (1 - eps)).add (hg.const_mul h)
  have hC := ((hP 4).const_mul (1 - eps)).add ((hA.const_mul h).mul (hP 2))
  have hV := ((((hP 3).const_mul ((1 - eps) ^ 2)).add
    ((hA.const_mul (2 * (1 - eps) * h)).mul (hP 4))).add
    (((hA.pow 2).const_mul (h ^ 2)).mul (hP 2))).add_const (2 * eps * h * Phi)
  refine hasFDerivAt_pi'.2 fun i => ?_
  fin_cases i
  · exact ((hP 0).sub hU).congr_fderiv (by
      ext v; simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
        windowDriftJacobian, windowDriftJacobianCore]; ring)
  · exact hU.congr_fderiv (by
      ext v; simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
        windowDriftJacobian, windowDriftJacobianCore]; ring)
  · exact (((hP 2).sub (hC.const_mul 2)).add hV).congr_fderiv (by
      ext v; simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
        windowDriftJacobian, windowDriftJacobianCore]; ring)
  · exact hV.congr_fderiv (by
      ext v; simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
        windowDriftJacobian, windowDriftJacobianCore]; ring)
  · exact (hC.sub hV).congr_fderiv (by
      ext v; simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
        windowDriftJacobian, windowDriftJacobianCore]; ring)

/-- At `eps = 0` and at the window fixed point the drift Jacobian is `windowJacobian`
(by uniqueness of the derivative). -/
theorem windowDriftJacobian_zero_fixed (r h θ R a w : ℝ)
    (ha : dynamicAlpha r (windowFixedPoint θ R w) = a) (hr : a * θ = r) (hw : w = h * a) :
    windowDriftJacobian r h 0 (windowFixedPoint θ R w) = windowJacobian θ R w := by
  have h1 := hasFDerivAt_windowDriftMap r h 0 0 (windowFixedPoint θ R w)
  rw [windowDriftMap_zero] at h1
  have h2 := hasFDerivAt_windowMap r h θ R a w ha hr hw
  have h3 := h1.unique h2
  have h4 : Matrix.toLin' (windowDriftJacobian r h 0 (windowFixedPoint θ R w)) =
      Matrix.toLin' (windowJacobian θ R w) := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun f : DynamicState →L[ℝ] DynamicState => f v) h3
  exact Matrix.toLin'.injective h4

/-- Joint continuity of the entries of the drift Jacobian in `(eps, x)`. -/
theorem continuous_windowDriftJacobian_entry (r h : ℝ) (i j : Fin 5) :
    Continuous (fun p : ℝ × DynamicState => windowDriftJacobian r h p.1 p.2 i j) := by
  have hα : Continuous (fun p : ℝ × DynamicState => dynamicAlpha r p.2) := by
    unfold dynamicAlpha; fun_prop
  have h0 : Continuous (fun p : ℝ × DynamicState => p.2 0) := by fun_prop
  have h2 : Continuous (fun p : ℝ × DynamicState => p.2 2) := by fun_prop
  have h4 : Continuous (fun p : ℝ × DynamicState => p.2 4) := by fun_prop
  have he : Continuous (fun p : ℝ × DynamicState => p.1) := by fun_prop
  have hq : Continuous (fun p : ℝ × DynamicState =>
      ((p.1, dynamicAlpha r p.2, p.2 0, p.2 2, p.2 4) : ℝ × ℝ × ℝ × ℝ × ℝ)) := by
    refine he.prodMk (hα.prodMk (h0.prodMk (h2.prodMk h4)))
  have hc : Continuous (fun q : ℝ × ℝ × ℝ × ℝ × ℝ =>
      windowDriftJacobianCore h q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 i j) := by
    fin_cases i <;> fin_cases j <;>
      simp only [windowDriftJacobianCore, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> fun_prop
  exact hc.comp hq

/-- If `eps -> 0` and `x eps -> x0` along `l`, the drift Jacobians converge entrywise to
`windowDriftJacobian r h 0 x0`. -/
theorem windowDriftJacobian_tendsto (r h : ℝ) {l : Filter ℝ} (hl : l ≤ 𝓝 0)
    (x : ℝ → DynamicState) (x0 : DynamicState) (hx : Tendsto x l (𝓝 x0)) :
    ∀ i j, Tendsto (fun eps => windowDriftJacobian r h eps (x eps) i j) l
      (𝓝 (windowDriftJacobian r h 0 x0 i j)) := by
  intro i j
  have hp : Tendsto (fun eps => (eps, x eps)) l (𝓝 ((0 : ℝ), x0)) :=
    Tendsto.prodMk_nhds hl hx
  have hc := ((continuous_windowDriftJacobian_entry r h i j).tendsto ((0 : ℝ), x0)).comp hp
  rw [Function.comp_def] at hc
  exact hc

/-- `2 < w_+` for `R > 0`. -/
theorem two_lt_windowUpper (θ R : ℝ) (hR : 0 < R) : 2 < windowUpper θ R := by
  have hA := windowA_pos θ R hR.le
  have hc := windowCritical_lt_two θ R hR
  by_contra hcon
  have hcon := not_lt.1 hcon
  have hQ := windowQ_factor θ R 2 hR
  rw [windowQ_two] at hQ
  have h1 : 0 ≤ 2 - windowUpper θ R := by linarith
  have h2 : 0 < 2 - windowCritical θ R := by linarith
  have h3 : 0 ≤ windowA θ R * (2 - windowCritical θ R) * (2 - windowUpper θ R) := by positivity
  nlinarith

/-- v2 prop:W2 (iii) on the full interval `w_c < w < 2` (fixed map): `J0` has a real eigenvalue
`z < -1` at which the characteristic polynomial changes sign. -/
theorem prop_W2_iii_above_interval (θ R : ℝ) (hR : 0 < R) :
    ∀ w, windowCritical θ R < w → w < 2 →
      ∃ z : ℝ, z < -1 ∧
        (z • (1 : Matrix (Fin 5) (Fin 5) ℝ) - windowJacobian θ R w).det = 0 ∧
        (∃ v : Fin 5 → ℝ, v ≠ 0 ∧ (windowJacobian θ R w).mulVec v = z • v) ∧
        ∀ δ > 0, ∃ x1 x2 : ℝ, |x1 - z| < δ ∧ |x2 - z| < δ ∧
          (x1 • (1 : Matrix (Fin 5) (Fin 5) ℝ) - windowJacobian θ R w).det *
          (x2 • (1 : Matrix (Fin 5) (Fin 5) ℝ) - windowJacobian θ R w).det < 0 := by
  intro w hw1 hw2b
  have hQw : windowQ θ R w < 0 := by
    rw [windowQ_factor θ R w hR]
    have hA := windowA_pos θ R hR.le
    have h1' : 0 < w - windowCritical θ R := by linarith
    have h2' : w - windowUpper θ R < 0 := by linarith [two_lt_windowUpper θ R hR]
    have := mul_neg_of_pos_of_neg h1' h2'
    rw [mul_assoc]
    exact mul_neg_of_pos_of_neg hA this
  have hpm2 : windowP θ R w (-2) < 0 := by
    rw [windowP_neg_two]
    have : 0 < 2 - w := by linarith
    nlinarith
  have hw0 : 0 < w := lt_trans (windowCritical_pos θ R hR) hw1
  have hdisc := window_disc_pos θ R w hR hw0 hw2b
  unfold windowP at hpm2
  have hdet : ∀ x : ℝ, (x • (1 : Matrix (Fin 5) (Fin 5) ℝ) - windowJacobian θ R w).det =
      (x - 1) * (x ^ 4 + windowCoefB θ R w * x ^ 3 + windowCoefC θ R w * x ^ 2
        + windowCoefB θ R w * x + 1) := window_det_x_sub θ R w
  generalize windowCoefB θ R w = b at hpm2 hdisc hdet
  generalize windowCoefC θ R w = c at hpm2 hdisc hdet
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
  have hfac : ∀ x : ℝ, (x • (1 : Matrix (Fin 5) (Fin 5) ℝ) - windowJacobian θ R w).det =
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
  have hroot : (z • (1 : Matrix (Fin 5) (Fin 5) ℝ) - windowJacobian θ R w).det = 0 := by
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
        windowJacobian θ R w).det = (z - τ - z) * g :=
      ⟨_, hg (z - τ) (by linarith), hfac (z - τ)⟩
    obtain ⟨g2, hg2, hf2⟩ : ∃ g, 0 < g ∧ ((z + τ) • (1 : Matrix (Fin 5) (Fin 5) ℝ) -
        windowJacobian θ R w).det = (z + τ - z) * g :=
      ⟨_, hg (z + τ) (by linarith), hfac (z + τ)⟩
    rw [hf1, hf2]
    have e : (z - τ - z) * g1 * ((z + τ - z) * g2) = -(τ ^ 2 * (g1 * g2)) := by ring
    rw [e]
    have := mul_pos (pow_pos hτ0 2) (mul_pos hg1 hg2)
    linarith

/-- v2 `prop:W2` (iii) for the drift recursion: if fixed points `x eps` of the drift window map
have signal and bulk components converging to `(θ, R)` with `R > 0` and
`λ = h exp ((θ^2 + R - r^2)/2) ∈ (λ_c, 2)`, then for small `eps` the derivative of the drift map
at `x eps` exists and has an eigenvalue of modulus `> 1` (the fixed point is linearly unstable). -/
theorem prop_W2_iii_drift (r h θ R : ℝ) (hh : h ≠ 0) (hR : 0 < R)
    (hw1 : windowCritical θ R < h * Real.exp ((θ ^ 2 + R - r ^ 2) / 2))
    (hw2 : h * Real.exp ((θ ^ 2 + R - r ^ 2) / 2) < 2)
    (l : Filter ℝ) [l.NeBot] (hl : l ≤ nhds 0) (Phi : ℝ → ℝ) (x : ℝ → DynamicState)
    (hfix : ∀ᶠ eps in l, windowDriftMap r h eps (Phi eps) (x eps) = x eps)
    (h0 : Tendsto (fun eps => x eps 0) l (nhds θ))
    (h2 : Tendsto (fun eps => x eps 2) l (nhds R)) :
    ∀ᶠ eps in l,
      HasFDerivAt (windowDriftMap r h eps (Phi eps))
        (LinearMap.toContinuousLinearMap (Matrix.toLin' (windowDriftJacobian r h eps (x eps))))
        (x eps) ∧
      ∃ z : ℂ, (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
        (windowDriftJacobian r h eps (x eps)).map Complex.ofReal).det = 0 ∧ 1 < ‖z‖ := by
  set a := Real.exp ((θ ^ 2 + R - r ^ 2) / 2) with ha
  set w := h * a with hw
  have hxt := windowDrift_fixedPoint_tendsto r h θ R l hl Phi x hh hfix h0 h2
  have hsig := windowDrift_fixedPoint_signal r h θ R l hl Phi x hh hfix h0 h2
  have hα : dynamicAlpha r (windowFixedPoint θ R w) = a :=
    dynamicAlpha_windowFixedPoint r θ R w
  have hJ0 := windowDriftJacobian_zero_fixed r h θ R a w hα hsig hw
  have hJ := windowDriftJacobian_tendsto r h hl x _ hxt
  rw [hJ0] at hJ
  obtain ⟨z0, hz0, -, -, hsign⟩ := prop_W2_iii_above_interval θ R hR w hw1 hw2
  filter_upwards [real_eigenvalue_persistence (fun eps => windowDriftJacobian r h eps (x eps))
    (windowJacobian θ R w) hJ z0 hz0 hsign] with eps hε
  obtain ⟨_, _, _, z', h1, h2'⟩ := hε
  exact ⟨hasFDerivAt_windowDriftMap r h eps (Phi eps) (x eps), z', h1, h2'⟩

end
end SparseSGD.Logistic.V2
