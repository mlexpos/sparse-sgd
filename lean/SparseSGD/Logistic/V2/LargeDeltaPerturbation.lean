import SparseSGD.Logistic.V2.LargeDeltaAlgebra
import SparseSGD.Logistic.V2.Hurwitz
import SparseSGD.Logistic.EquilibriumAnalysis

open Polynomial

/-!
# v2 prop:W1, analytic part (large-Delta eigenvalue asymptotics)

Throughout `a = alpha*`, `theta = theta*`, `R = R*` are fixed and `Delta -> infinity`; write
`eps = Delta^{-1/2}`.  Mathlib has no analytic perturbation theory, so everything is reduced to
scalar polynomials:

* `det_jacobian_real`, `det_jacobian_complex`: the characteristic polynomial of the Jacobian of
  eq:LR5 at `y*`, explicitly, as a polynomial in `(Delta, lambda)`;
* `jacPoly_scale`: with `kappa = eps * lambda`, `eps^5 * jacPoly = chi(eps, kappa)`, where
  `chi(eps, kappa) = det(kappa - Omega - eps D)`;
* `exists_root_near`: a monic complex polynomial has a root within `2 n |p|/|p'|` of any point
  where `p' != 0` (from `p = prod (X - w_i)` and the logarithmic-derivative bound);
* real eigenvalue (T2): intermediate value theorem for `chi(eps, eps lambda)/eps`;
* oscillatory eigenvalues (T3): `exists_root_near` applied in the `kappa` scale at
  `kappa_0 = i nu + eps mu`, using that the first-order condition `chi_kappa mu + chi_eps = 0`
  is exactly the Rayleigh formula `mu = -N/(2D)` of `LargeDeltaAlgebra`.

Both are in fact `O(Delta^{-1})` resp. `O(Delta^{-1/2})` as claimed; the real eigenvalue is
sharper than the paper's statement.
-/

namespace SparseSGD.Logistic.V2
noncomputable section


/-- v2 prop:W1 (fast_conjugation): the change of variables `T : (theta,Y,R,V,C) -> (theta, sqrt(Delta) Y, R, sqrt(Delta) C, Delta V)`, a diagonal scaling composed with the swap of the last two coordinates, into the fast ordering `(theta, ytilde, R, Ctilde, Vtilde)`. -/
def fastT (Δ : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
     0, Real.sqrt Δ, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 0, Real.sqrt Δ;
     0, 0, 0, Δ, 0]

/-- v2 prop:W1: the explicit inverse of `fastT` (see `fastT_mul_inv`). -/
def fastTInv (Δ : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
     0, 1 / Real.sqrt Δ, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 0, 1 / Δ;
     0, 0, 0, 1 / Real.sqrt Δ, 0]

/-- v2 prop:W1: `fastT * fastTInv = 1` for `Delta > 0`. -/
theorem fastT_mul_inv (Δ : ℝ) (hΔ : 0 < Δ) : fastT Δ * fastTInv Δ = 1 := by
  have hs : Real.sqrt Δ ≠ 0 := (Real.sqrt_pos.2 hΔ).ne'
  have hss : Real.sqrt Δ * Real.sqrt Δ = Δ := Real.mul_self_sqrt hΔ.le
  have hΔ' : Δ ≠ 0 := hΔ.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fastT, fastTInv, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp

/-- v2 prop:W1: `fastTInv * fastT = 1` for `Delta > 0`. -/
theorem fastTInv_mul (Δ : ℝ) (hΔ : 0 < Δ) : fastTInv Δ * fastT Δ = 1 := by
  have hs : Real.sqrt Δ ≠ 0 := (Real.sqrt_pos.2 hΔ).ne'
  have hss : Real.sqrt Δ * Real.sqrt Δ = Δ := Real.mul_self_sqrt hΔ.le
  have hΔ' : Δ ≠ 0 := hΔ.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fastT, fastTInv, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp

/-- v2 prop:W1 (T1): `T A T^{-1} = sqrt(Delta) Omega + D`, where `A = jacobianMatrix a theta R Delta`, `Omega = fastOmega a theta R` and `D = fastDamping`. -/
theorem fast_conjugation (a θ R Δ : ℝ) (hΔ : 0 < Δ) :
    fastT Δ * jacobianMatrix a θ R Δ * (fastT Δ)⁻¹ =
      Real.sqrt Δ • fastOmega a θ R + fastDamping := by
  have hinv : (fastT Δ)⁻¹ = fastTInv Δ := Matrix.inv_eq_right_inv (fastT_mul_inv Δ hΔ)
  rw [hinv]
  have hs : Real.sqrt Δ ≠ 0 := (Real.sqrt_pos.2 hΔ).ne'
  have hss : Real.sqrt Δ * Real.sqrt Δ = Δ := Real.mul_self_sqrt hΔ.le
  have hΔ' : Δ ≠ 0 := hΔ.ne'
  have hsq : Real.sqrt Δ ^ 2 = Δ := Real.sq_sqrt hΔ.le
  rw [fastDamping_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fastT, fastTInv, jacobianMatrix, fastOmega, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp
  all_goals (try rw [hsq])
  all_goals (try ring)


/-- v2 prop:W1: the characteristic polynomial of `jacobianMatrix a theta R Delta`, explicitly, in the variables `(Delta, lambda)`. -/
def jacPoly {K : Type*} [CommRing K] (a θ R Δ l : K) : K :=
  l ^ 5 + 4 * l ^ 4 + (a * Δ * (5 + θ ^ 2 + R) + 5) * l ^ 3 +
    (a * Δ * (3 * R + 3 * θ ^ 2 + 11) + 2) * l ^ 2 +
    a * Δ * (a * Δ * (R + 4 * θ ^ 2 + 4) + 2 * R + 2 * θ ^ 2 + 6) * l +
    2 * a ^ 2 * Δ ^ 2 * (R + 2 * θ ^ 2 + 2)

/-- v2 prop:W1: `det(l 1 - A) = jacPoly a theta R Delta l` for real `l` (direct determinant expansion). -/
theorem det_jacobian_real (a θ R Δ l : ℝ) :
    Matrix.det (l • (1 : Matrix (Fin 5) (Fin 5) ℝ) - jacobianMatrix a θ R Δ) =
      jacPoly a θ R Δ l := by
  rw [Matrix.det_succ_row_zero]
  simp [jacobianMatrix, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove,
    Matrix.one_apply, jacPoly]
  ring

/-- v2 prop:W1: `det(z 1 - A) = jacPoly` over `C`, for the complexified Jacobian. -/
theorem det_jacobian_complex (a θ R Δ : ℝ) (z : ℂ) :
    Matrix.det (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
        (jacobianMatrix a θ R Δ).map Complex.ofReal) =
      jacPoly (a : ℂ) (θ : ℂ) (R : ℂ) (Δ : ℂ) z := by
  rw [Matrix.det_succ_row_zero]
  simp [jacobianMatrix, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove,
    Matrix.one_apply, jacPoly]
  ring


/-- v2 prop:W1: `chi(eps, kappa) = det(kappa 1 - Omega - eps D)`, the characteristic polynomial of the scaled Jacobian `A / sqrt(Delta) = Omega + eps D`, `eps = Delta^{-1/2}`, written explicitly (`jacPoly_scale` identifies it with `jacPoly`). -/
def chi {K : Type*} [CommRing K] (a θ R ε κ : K) : K :=
  κ ^ 5 + 4 * ε * κ ^ 4 + (a * (5 + θ ^ 2 + R) + 5 * ε ^ 2) * κ ^ 3 +
    ε * (a * (3 * R + 3 * θ ^ 2 + 11) + 2 * ε ^ 2) * κ ^ 2 +
    a * (a * (R + 4 * θ ^ 2 + 4) + 2 * ε ^ 2 * (R + θ ^ 2 + 3)) * κ +
    2 * a ^ 2 * ε * (R + 2 * θ ^ 2 + 2)

/-- v2 prop:W1: the `kappa`-derivative of `chi`. -/
def dchi {K : Type*} [CommRing K] (a θ R ε κ : K) : K :=
  5 * κ ^ 4 + 16 * ε * κ ^ 3 + 3 * (a * (5 + θ ^ 2 + R) + 5 * ε ^ 2) * κ ^ 2 +
    2 * ε * (a * (3 * R + 3 * θ ^ 2 + 11) + 2 * ε ^ 2) * κ +
    a * (a * (R + 4 * θ ^ 2 + 4) + 2 * ε ^ 2 * (R + θ ^ 2 + 3))

/-- v2 prop:W1: `chi(eps, .)` as a monic polynomial in `kappa` over `C`. -/
def chiPoly (a θ R ε : ℂ) : ℂ[X] :=
  X ^ 5 + C (4 * ε) * X ^ 4 + C (a * (5 + θ ^ 2 + R) + 5 * ε ^ 2) * X ^ 3 +
    C (ε * (a * (3 * R + 3 * θ ^ 2 + 11) + 2 * ε ^ 2)) * X ^ 2 +
    C (a * (a * (R + 4 * θ ^ 2 + 4) + 2 * ε ^ 2 * (R + θ ^ 2 + 3))) * X +
    C (2 * a ^ 2 * ε * (R + 2 * θ ^ 2 + 2))

/-- v2 prop:W1: evaluation of `chiPoly`. -/
theorem chiPoly_eval (a θ R ε κ : ℂ) : (chiPoly a θ R ε).eval κ = chi a θ R ε κ := by
  simp [chiPoly, chi]

/-- v2 prop:W1: evaluation of the derivative of `chiPoly`. -/
theorem chiPoly_deriv_eval (a θ R ε κ : ℂ) :
    (derivative (chiPoly a θ R ε)).eval κ = dchi a θ R ε κ := by
  simp [chiPoly, dchi, derivative_pow, derivative_mul]
  ring

/-- v2 prop:W1: `chiPoly` is monic. -/
theorem chiPoly_monic (a θ R ε : ℂ) : (chiPoly a θ R ε).Monic := by
  unfold chiPoly
  monicity!

/-- v2 prop:W1: `chiPoly` has degree at most `5`. -/
theorem chiPoly_natDegree (a θ R ε : ℂ) : (chiPoly a θ R ε).natDegree ≤ 5 := by
  unfold chiPoly
  compute_degree


/-- Logarithmic-derivative bound: for `P = prod (X - w_i)` with `|z - w_i| >= d > 0`, `|P'(z)| d <= n |P(z)|`. -/
theorem prod_derivative_bound (z : ℂ) (d : ℝ) (hd : 0 < d) (s : Multiset ℂ)
    (hs : ∀ w ∈ s, d ≤ ‖z - w‖) :
    ‖eval z (derivative (s.map (fun w => X - C w)).prod)‖ * d ≤
      (Multiset.card s : ℝ) * ‖eval z (s.map (fun w => X - C w)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w t ih =>
    have hw : d ≤ ‖z - w‖ := hs w (Multiset.mem_cons_self w t)
    have iht := ih (fun v hv => hs v (Multiset.mem_cons_of_mem hv))
    have e : eval z (derivative ((Multiset.map (fun w => X - C w) (w ::ₘ t)).prod)) =
        eval z (derivative (t.map (fun w => X - C w)).prod) * (z - w) +
          eval z (t.map (fun w => X - C w)).prod := by
      simp [derivative_mul]
      ring
    have e2 : eval z ((Multiset.map (fun w => X - C w) (w ::ₘ t)).prod) =
        (z - w) * eval z (t.map (fun w => X - C w)).prod := by
      simp
    rw [e, e2]
    generalize eval z (derivative (t.map (fun w => X - C w)).prod) = u at *
    generalize eval z (t.map (fun w => X - C w)).prod = v at *
    rw [Multiset.card_cons, Nat.cast_add, Nat.cast_one, norm_mul]
    have h1 : ‖u * (z - w) + v‖ ≤ ‖u‖ * ‖z - w‖ + ‖v‖ :=
      (norm_add_le _ _).trans (by rw [norm_mul])
    have hv : 0 ≤ ‖v‖ := norm_nonneg _
    have hu : 0 ≤ ‖u‖ := norm_nonneg _
    have hz : 0 ≤ ‖z - w‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hw hv, mul_le_mul_of_nonneg_left iht hz,
      mul_le_mul_of_nonneg_right h1 hd.le]

/-- A monic complex polynomial with nonvanishing derivative at `z` has a root within
`2 n |p(z)|/|p'(z)|` of `z`. -/
theorem exists_root_near (p : ℂ[X]) (hm : p.Monic) (z : ℂ)
    (hz : eval z (derivative p) ≠ 0) :
    ∃ w, p.eval w = 0 ∧ ‖z - w‖ ≤ 2 * p.natDegree * ‖eval z p‖ / ‖eval z (derivative p)‖ := by
  have hsp := IsAlgClosed.splits p
  have hprod := hsp.eq_prod_roots_of_monic hm
  have hcard := hsp.natDegree_eq_card_roots
  by_cases hp0 : eval z p = 0
  · exact ⟨z, hp0, by simp only [sub_self, norm_zero]; positivity⟩
  have hn : 0 < Multiset.card p.roots := by
    rcases Nat.eq_zero_or_pos (Multiset.card p.roots) with h | h
    · rw [Multiset.card_eq_zero] at h
      rw [h] at hprod
      rw [hprod] at hz
      simp at hz
    · exact h
  by_contra hcon
  push Not at hcon
  have hP : 0 < ‖eval z p‖ := norm_pos_iff.mpr hp0
  have hP' : 0 < ‖eval z (derivative p)‖ := norm_pos_iff.mpr hz
  have hn' : (0:ℝ) < (p.natDegree : ℝ) := by
    rw [hcard]; exact_mod_cast hn
  set d := 2 * p.natDegree * ‖eval z p‖ / ‖eval z (derivative p)‖ with hd
  have hdpos : 0 < d := by positivity
  have hs : ∀ w ∈ p.roots, d ≤ ‖z - w‖ := by
    intro w hw
    exact (hcon w ((mem_roots hm.ne_zero).1 hw)).le
  have key := prod_derivative_bound z d hdpos p.roots hs
  rw [← hprod, ← hcard] at key
  have : ‖eval z (derivative p)‖ * d = 2 * p.natDegree * ‖eval z p‖ := by
    rw [hd]; field_simp
  rw [this] at key
  nlinarith


/-! ### expansion coefficients of `chi` along `kappa = z0 + eps mu` -/

/-- v2 prop:W1: the `eps^0` coefficient of `chi(eps, k0 + eps mu)`. -/
def cf0 (a θ R k0 : ℂ) : ℂ :=
  k0 * (k0 ^ 4 + a * (5 + θ ^ 2 + R) * k0 ^ 2 + a ^ 2 * (R + 4 * θ ^ 2 + 4))

/-- v2 prop:W1: the `eps^1` coefficient of `chi(eps, k0 + eps mu)`: `chi_eps(0,k0) + mu chi_kappa(0,k0)`, the first-order (Rayleigh) condition. -/
def cf1 (a θ R k0 μ : ℂ) : ℂ :=
  (4 * k0 ^ 4 + a * (3 * R + 3 * θ ^ 2 + 11) * k0 ^ 2 + 2 * a ^ 2 * (R + 2 * θ ^ 2 + 2)) +
    μ * (5 * k0 ^ 4 + 3 * a * (5 + θ ^ 2 + R) * k0 ^ 2 + a ^ 2 * (R + 4 * θ ^ 2 + 4))

/-- v2 prop:W1: the quotient `(chi(eps, k0 + eps mu) - cf0 - eps cf1)/eps^2`, a polynomial in `eps`. -/
def cQ (a θ R k0 μ ε : ℂ) : ℂ :=
  (2 * R * a * k0 + 2 * a * k0 * θ ^ 2 + 6 * a * k0 + 5 * k0 ^ 3 +
      μ ^ 2 * (3 * R * a * k0 + 3 * a * k0 * θ ^ 2 + 15 * a * k0 + 10 * k0 ^ 3) +
      μ * (6 * R * a * k0 + 6 * a * k0 * θ ^ 2 + 22 * a * k0 + 16 * k0 ^ 3)) +
  ε * (2 * k0 ^ 2 + μ ^ 3 * (R * a + a * θ ^ 2 + 5 * a + 10 * k0 ^ 2) +
      μ ^ 2 * (3 * R * a + 3 * a * θ ^ 2 + 11 * a + 24 * k0 ^ 2) +
      μ * (2 * R * a + 2 * a * θ ^ 2 + 6 * a + 15 * k0 ^ 2)) +
  ε ^ 2 * (5 * k0 * μ ^ 4 + 16 * k0 * μ ^ 3 + 15 * k0 * μ ^ 2 + 4 * k0 * μ) +
  ε ^ 3 * (μ ^ 5 + 4 * μ ^ 4 + 5 * μ ^ 3 + 2 * μ ^ 2)

/-- v2 prop:W1: expansion of `chi(eps, k0 + eps mu)` in powers of `eps`. -/
theorem chi_expansion (a θ R k0 μ ε : ℂ) :
    chi a θ R ε (k0 + ε * μ) = cf0 a θ R k0 + ε * cf1 a θ R k0 μ + ε ^ 2 * cQ a θ R k0 μ ε := by
  unfold chi cf0 cf1 cQ
  ring

/-- v2 prop:W1: continuity of the second-order remainder in `eps`. -/
theorem cQ_continuous (a θ R k0 μ : ℂ) : Continuous (fun ε : ℝ => cQ a θ R k0 μ (ε : ℂ)) := by
  unfold cQ
  fun_prop

/-- v2 prop:W1: continuity of `eps -> chi_kappa(eps, k0 + eps mu)`. -/
theorem dchi_continuous (a θ R k0 μ : ℂ) :
    Continuous (fun ε : ℝ => dchi a θ R (ε : ℂ) (k0 + (ε : ℂ) * μ)) := by
  unfold dchi
  fun_prop

/-- chi-level perturbation: a simple root of the `eps = 0` polynomial that satisfies the
first-order condition is the limit of roots, at rate `eps^2`. -/
theorem chi_root_near (a θ R ν μ : ℝ)
    (h0 : (ν ^ 2) ^ 2 - a * (5 + θ ^ 2 + R) * ν ^ 2 + a ^ 2 * (R + 4 * θ ^ 2 + 4) = 0)
    (h1 : (4 * (ν ^ 2) ^ 2 - a * (3 * R + 3 * θ ^ 2 + 11) * ν ^ 2 +
        2 * a ^ 2 * (R + 2 * θ ^ 2 + 2)) +
      μ * (5 * (ν ^ 2) ^ 2 - 3 * a * (5 + θ ^ 2 + R) * ν ^ 2 +
        a ^ 2 * (R + 4 * θ ^ 2 + 4)) = 0)
    (hm : 5 * (ν ^ 2) ^ 2 - 3 * a * (5 + θ ^ 2 + R) * ν ^ 2 + a ^ 2 * (R + 4 * θ ^ 2 + 4) ≠ 0) :
    ∃ ε1 K : ℝ, 0 < ε1 ∧ 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε1 →
      ∃ w : ℂ, chi (a : ℂ) (θ : ℂ) (R : ℂ) (ε : ℂ) w = 0 ∧
        ‖((Complex.I * ν + ε * μ : ℂ)) - w‖ ≤ K * ε ^ 2 := by
  set z0 : ℂ := Complex.I * ν with hz0
  have hz2 : z0 ^ 2 = -((ν : ℂ) ^ 2) := by
    rw [hz0, mul_pow, Complex.I_sq]; ring
  have hz4 : z0 ^ 4 = ((ν : ℂ) ^ 2) ^ 2 := by
    have : z0 ^ 4 = (z0 ^ 2) ^ 2 := by ring
    rw [this, hz2]; ring
  have e0 : cf0 (a : ℂ) θ R z0 = 0 := by
    unfold cf0
    rw [hz2, hz4]
    have : (((ν ^ 2) ^ 2 - a * (5 + θ ^ 2 + R) * ν ^ 2 + a ^ 2 * (R + 4 * θ ^ 2 + 4) : ℝ) : ℂ) = 0 := by
      rw [h0]; simp
    push_cast at this
    rw [show ((ν : ℂ) ^ 2) ^ 2 + (a : ℂ) * (5 + θ ^ 2 + R) * -((ν : ℂ) ^ 2) + (a : ℂ) ^ 2 * (R + 4 * θ ^ 2 + 4)
      = ((ν : ℂ) ^ 2) ^ 2 - a * (5 + θ ^ 2 + R) * (ν : ℂ) ^ 2 + (a : ℂ) ^ 2 * (R + 4 * θ ^ 2 + 4) by ring, this]
    simp
  have e1 : cf1 (a : ℂ) θ R z0 (μ : ℂ) = 0 := by
    unfold cf1
    rw [hz2, hz4]
    have : (((4 * (ν ^ 2) ^ 2 - a * (3 * R + 3 * θ ^ 2 + 11) * ν ^ 2 +
        2 * a ^ 2 * (R + 2 * θ ^ 2 + 2)) +
      μ * (5 * (ν ^ 2) ^ 2 - 3 * a * (5 + θ ^ 2 + R) * ν ^ 2 +
        a ^ 2 * (R + 4 * θ ^ 2 + 4)) : ℝ) : ℂ) = 0 := by
      rw [h1]; simp
    push_cast at this
    linear_combination this
  -- the derivative at eps = 0
  set m0 : ℂ := dchi (a : ℂ) θ R 0 z0 with hm0
  have hm0eq : m0 = ((5 * (ν ^ 2) ^ 2 - 3 * a * (5 + θ ^ 2 + R) * ν ^ 2 +
        a ^ 2 * (R + 4 * θ ^ 2 + 4) : ℝ) : ℂ) := by
    rw [hm0]
    unfold dchi
    rw [hz2, hz4]
    push_cast
    ring
  have hm0ne : m0 ≠ 0 := by
    rw [hm0eq]; exact_mod_cast hm
  have hm0pos : 0 < ‖m0‖ := norm_pos_iff.mpr hm0ne
  -- bound on Q
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (cQ_continuous (a : ℂ) θ R z0 (μ : ℂ)).continuousOn
  -- continuity of the derivative
  have hcont := (dchi_continuous (a : ℂ) θ R z0 (μ : ℂ)).continuousAt (x := 0)
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hδ'⟩ := hcont (‖m0‖ / 2) (by positivity)
  refine ⟨min 1 (δ / 2), 20 * max M 0 / ‖m0‖, by positivity, by positivity, ?_⟩
  intro ε hε hεle
  have hε1 : ε ≤ 1 := hεle.trans (min_le_left _ _)
  have hεδ : ε < δ := by
    have := hεle.trans (min_le_right _ _)
    linarith
  set z : ℂ := z0 + (ε : ℂ) * μ with hz
  have hD : ‖m0‖ / 2 ≤ ‖dchi (a : ℂ) θ R (ε : ℂ) z‖ := by
    have h := hδ' (x := ε) (by rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact hεδ)
    have h2 : dchi (a : ℂ) θ R ((0 : ℝ) : ℂ) (z0 + ((0 : ℝ) : ℂ) * μ) = m0 := by
      rw [hm0]; simp
    rw [h2, dist_eq_norm] at h
    have := norm_sub_norm_le m0 (dchi (a : ℂ) θ R (ε : ℂ) z)
    rw [norm_sub_rev] at h
    linarith [norm_sub_norm_le m0 (dchi (a : ℂ) θ R (ε : ℂ) z), norm_sub_rev m0 (dchi (a : ℂ) θ R (ε : ℂ) z)]
  have hDne : eval z (derivative (chiPoly (a : ℂ) θ R (ε : ℂ))) ≠ 0 := by
    rw [chiPoly_deriv_eval]
    intro h
    rw [h, norm_zero] at hD
    linarith
  obtain ⟨w, hw, hdist⟩ := exists_root_near (chiPoly (a : ℂ) θ R (ε : ℂ))
    (chiPoly_monic _ _ _ _) z hDne
  rw [chiPoly_eval] at hw
  refine ⟨w, hw, ?_⟩
  rw [chiPoly_deriv_eval, chiPoly_eval, hz, chi_expansion, e0, e1] at hdist
  simp only [mul_zero, zero_add] at hdist
  have hQ : ‖cQ (a : ℂ) θ R z0 (μ : ℂ) (ε : ℂ)‖ ≤ max M 0 :=
    (hM ε ⟨hε.le, hε1⟩).trans (le_max_left _ _)
  have hnd : ((chiPoly (a : ℂ) θ R (ε : ℂ)).natDegree : ℝ) ≤ 5 := by
    exact_mod_cast chiPoly_natDegree _ _ _ _
  have hP : ‖(ε : ℂ) ^ 2 * cQ (a : ℂ) θ R z0 (μ : ℂ) (ε : ℂ)‖ ≤ max M 0 * ε ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hε.le]
    nlinarith [sq_nonneg ε]
  refine hdist.trans ?_
  have hDpos : 0 < ‖dchi (a : ℂ) θ R (ε : ℂ) z‖ := lt_of_lt_of_le (by positivity) hD
  rw [div_le_iff₀ hDpos]
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hn0 : (0:ℝ) ≤ ((chiPoly (a : ℂ) θ R (ε : ℂ)).natDegree : ℝ) := Nat.cast_nonneg _
  have hstep : 2 * ((chiPoly (a : ℂ) θ R (ε : ℂ)).natDegree : ℝ) *
      ‖(ε : ℂ) ^ 2 * cQ (a : ℂ) θ R z0 (μ : ℂ) (ε : ℂ)‖ ≤ 10 * (max M 0 * ε ^ 2) := by
    have := mul_le_mul hnd hP (norm_nonneg _) (by norm_num)
    nlinarith
  have hK : 20 * max M 0 / ‖m0‖ * ε ^ 2 * ‖dchi (a : ℂ) θ R (ε : ℂ) z‖ ≥
      20 * max M 0 / ‖m0‖ * ε ^ 2 * (‖m0‖ / 2) := by
    apply mul_le_mul_of_nonneg_left hD
    positivity
  have hval : 20 * max M 0 / ‖m0‖ * ε ^ 2 * (‖m0‖ / 2) = 10 * (max M 0 * ε ^ 2) := by
    field_simp
    ring
  linarith


/-! ### Scaling `lambda = kappa / eps` and the real eigenvalue -/

/-- v2 prop:W1: with `Delta eps^2 = 1` and `kappa = eps lambda`,
`eps^5 jacPoly(Delta, lambda) = chi(eps, kappa)`. -/
theorem jacPoly_scale {K : Type*} [Field K] (a θ R Δ ε l : K) (hε : ε ≠ 0)
    (hΔ : Δ * ε ^ 2 = 1) :
    ε ^ 5 * jacPoly a θ R Δ l = chi a θ R ε (ε * l) := by
  have hΔ' : Δ = 1 / ε ^ 2 := eq_div_of_mul_eq (pow_ne_zero 2 hε) hΔ
  subst hΔ'
  unfold jacPoly chi
  field_simp
  ring

/-- The remainder in `chi(eps, eps lambda)/eps`. -/
def gRem (a θ R ε l : ℝ) : ℝ :=
  ε ^ 2 * l ^ 5 + 4 * ε ^ 2 * l ^ 4 + (a * (5 + θ ^ 2 + R) + 5 * ε ^ 2) * l ^ 3 +
    (a * (3 * R + 3 * θ ^ 2 + 11) + 2 * ε ^ 2) * l ^ 2 + 2 * a * (R + θ ^ 2 + 3) * l

/-- v2 prop:W1: `chi(eps, eps lambda) = eps (a^2 (q lambda + 2 c) + eps^2 G)` with `q = R+4theta^2+4`, `c = R+2theta^2+2`. -/
theorem chi_real_scale (a θ R ε l : ℝ) :
    chi a θ R ε (ε * l) = ε * (a ^ 2 * ((R + 4 * θ ^ 2 + 4) * l + 2 * (R + 2 * θ ^ 2 + 2)) +
      ε ^ 2 * gRem a θ R ε l) := by
  unfold chi gRem
  ring

/-- v2 prop:W1: continuity of `G` in `(eps, lambda)`. -/
theorem gRem_continuous (a θ R : ℝ) : Continuous (fun p : ℝ × ℝ => gRem a θ R p.1 p.2) := by
  unfold gRem
  fun_prop

/-- the real root, at the level of the scaled polynomial. -/
theorem real_root_near (a θ R : ℝ) (ha : a ≠ 0) (hq : 0 < R + 4 * θ ^ 2 + 4) :
    ∃ ε1 K : ℝ, 0 < ε1 ∧ 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε1 →
      ∃ l : ℝ, |l - (-(2 * (R + 2 * θ ^ 2 + 2)) / (R + 4 * θ ^ 2 + 4))| ≤ K * ε ^ 2 ∧
        a ^ 2 * ((R + 4 * θ ^ 2 + 4) * l + 2 * (R + 2 * θ ^ 2 + 2)) +
          ε ^ 2 * gRem a θ R ε l = 0 := by
  set q := R + 4 * θ ^ 2 + 4 with hqdef
  set c := R + 2 * θ ^ 2 + 2 with hcdef
  set l0 := -(2 * c) / q with hl0
  have hq' : 0 < a ^ 2 * q := by positivity
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_Icc (a := l0 - 1) (b := l0 + 1)) |>.exists_bound_of_continuousOn
    (gRem_continuous a θ R).continuousOn
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set K := (M' + 1) / (a ^ 2 * q) with hK
  have hK0 : 0 ≤ K := by positivity
  have hKq : K * (a ^ 2 * q) = M' + 1 := by rw [hK]; field_simp
  refine ⟨min 1 (1 / (K + 1)), K, by positivity, hK0, ?_⟩
  intro ε hε hεle
  have hε1 : ε ≤ 1 := hεle.trans (min_le_left _ _)
  have hε2 : ε ≤ 1 / (K + 1) := hεle.trans (min_le_right _ _)
  have ht : K * ε ^ 2 ≤ 1 := by
    have h1 : ε ^ 2 ≤ ε := by nlinarith
    have h2 : K * ε ^ 2 ≤ K * (1 / (K + 1)) :=
      calc K * ε ^ 2 ≤ K * ε := mul_le_mul_of_nonneg_left h1 hK0
        _ ≤ K * (1 / (K + 1)) := mul_le_mul_of_nonneg_left hε2 hK0
    have h3 : K * (1 / (K + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]; linarith
    linarith
  set t := K * ε ^ 2 with htdef
  have ht0 : 0 ≤ t := by positivity
  have hlin : ∀ l, a ^ 2 * (q * l + 2 * c) = a ^ 2 * q * (l - l0) := by
    intro l
    rw [hl0]
    field_simp
    ring
  have hbound : ∀ l ∈ Set.Icc (l0 - t) (l0 + t), |gRem a θ R ε l| ≤ M' := by
    intro l hl
    have hmem : (ε, l) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (l0 - 1) (l0 + 1) :=
      ⟨⟨hε.le, hε1⟩, ⟨by linarith [hl.1], by linarith [hl.2]⟩⟩
    have := hM (ε, l) hmem
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  set f : ℝ → ℝ := fun l => a ^ 2 * (q * l + 2 * c) + ε ^ 2 * gRem a θ R ε l with hf
  have hfc : Continuous f := by
    rw [hf]
    unfold gRem
    fun_prop
  have hlo : f (l0 - t) < 0 := by
    have h1 := hbound (l0 - t) ⟨le_refl _, by linarith⟩
    have h2 := abs_le.mp h1
    show a ^ 2 * (q * (l0 - t) + 2 * c) + ε ^ 2 * gRem a θ R ε (l0 - t) < 0
    rw [hlin]
    have : a ^ 2 * q * (l0 - t - l0) = -(M' + 1) * ε ^ 2 := by
      rw [show l0 - t - l0 = -t by ring, htdef]
      nlinarith [hKq]
    rw [this]
    nlinarith [sq_pos_of_pos hε, mul_le_mul_of_nonneg_left h2.2 (sq_nonneg ε)]
  have hhi : 0 < f (l0 + t) := by
    have h1 := hbound (l0 + t) ⟨by linarith, le_refl _⟩
    have h2 := abs_le.mp h1
    show 0 < a ^ 2 * (q * (l0 + t) + 2 * c) + ε ^ 2 * gRem a θ R ε (l0 + t)
    rw [hlin]
    have : a ^ 2 * q * (l0 + t - l0) = (M' + 1) * ε ^ 2 := by
      rw [show l0 + t - l0 = t by ring, htdef]
      nlinarith [hKq]
    rw [this]
    nlinarith [sq_pos_of_pos hε, mul_le_mul_of_nonneg_left h2.1 (sq_nonneg ε)]
  have hivt := intermediate_value_Icc (show l0 - t ≤ l0 + t by linarith) hfc.continuousOn
  obtain ⟨l, hl, hl0'⟩ := hivt ⟨hlo.le, hhi.le⟩
  refine ⟨l, ?_, hl0'⟩
  rw [abs_le]
  constructor <;> linarith [hl.1, hl.2]

/-- `lambdaZero` in the form `-2 (R + 2 theta^2 + 2) / (R + 4 theta^2 + 4)`. -/
theorem lambdaZero_eq' (θ R : ℝ) (hR : 0 ≤ R) :
    lambdaZero θ R = -(2 * (R + 2 * θ ^ 2 + 2)) / (R + 4 * θ ^ 2 + 4) := by
  unfold lambdaZero
  have h1 : (1 + θ ^ 2) ≠ 0 := by positivity
  have h2 : (2 + R / (2 * (1 + θ ^ 2))) ≠ 0 := by positivity
  have h3 : R + 4 * θ ^ 2 + 4 ≠ 0 := by positivity
  field_simp
  ring

/-- v2 prop:W1, sharp form of the real eigenvalue: the Jacobian has a real eigenvalue
within `K/Delta` of `lambda_0`.  The paper claims `O(Delta^{-1/2})`. -/
theorem real_eigenvalue_asymptotics_sharp (a θ R : ℝ) (ha : a ≠ 0) (hR : 0 ≤ R) :
    ∃ Δ0 K : ℝ, 0 < Δ0 ∧ 0 ≤ K ∧ ∀ Δ : ℝ, Δ0 ≤ Δ → ∃ l : ℝ,
      Matrix.det (l • (1 : Matrix (Fin 5) (Fin 5) ℝ) - jacobianMatrix a θ R Δ) = 0 ∧
        |l - lambdaZero θ R| ≤ K / Δ := by
  have hq : 0 < R + 4 * θ ^ 2 + 4 := by positivity
  obtain ⟨ε1, K, hε1, hK, hroot⟩ := real_root_near a θ R ha hq
  refine ⟨1 / ε1 ^ 2, K, by positivity, hK, ?_⟩
  intro Δ hΔ
  have hΔpos : 0 < Δ := lt_of_lt_of_le (by positivity) hΔ
  set ε : ℝ := 1 / Real.sqrt Δ with hε
  have hsq : 0 < Real.sqrt Δ := Real.sqrt_pos.2 hΔpos
  have hεpos : 0 < ε := by positivity
  have hεsq : Δ * ε ^ 2 = 1 := by
    rw [hε, div_pow, Real.sq_sqrt hΔpos.le]; field_simp
  have hεle : ε ≤ ε1 := by
    by_contra hcon
    push Not at hcon
    have h1 : ε1 ^ 2 < ε ^ 2 := by nlinarith
    have h2 : 1 / ε1 ^ 2 * ε ^ 2 ≤ Δ * ε ^ 2 := mul_le_mul_of_nonneg_right hΔ (sq_nonneg _)
    have h3 : 1 < 1 / ε1 ^ 2 * ε ^ 2 := by
      rw [one_div, inv_mul_eq_div, lt_div_iff₀ (by positivity)]; linarith
    linarith
  obtain ⟨l, hl, hz⟩ := hroot ε hεpos hεle
  refine ⟨l, ?_, ?_⟩
  · rw [det_jacobian_real]
    have h := jacPoly_scale a θ R Δ ε l hεpos.ne' hεsq
    rw [chi_real_scale, hz, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 5 hεpos.ne')
  · rw [lambdaZero_eq' θ R hR]
    have : K * ε ^ 2 = K / Δ := by
      have : ε ^ 2 = 1 / Δ := by
        rw [hε, div_pow, Real.sq_sqrt hΔpos.le, one_pow]
      rw [this]; ring
    rw [← this]
    exact hl

/-- v2 prop:W1 (lambda_0), as stated in the paper: for `Delta` large the Jacobian has a real
eigenvalue `lambda(Delta)` with `|lambda + (2 + 2 rho)/(2 + rho)| <= K / sqrt Delta`,
`rho = R/(2(1+theta^2))`. -/
theorem real_eigenvalue_asymptotics (a θ R : ℝ) (ha : a ≠ 0) (hR : 0 ≤ R) :
    ∃ Δ0 K : ℝ, 0 < Δ0 ∧ 0 ≤ K ∧ ∀ Δ : ℝ, Δ0 ≤ Δ → ∃ l : ℝ,
      Matrix.det (l • (1 : Matrix (Fin 5) (Fin 5) ℝ) - jacobianMatrix a θ R Δ) = 0 ∧
        |l + (2 + 2 * (R / (2 * (1 + θ ^ 2)))) / (2 + R / (2 * (1 + θ ^ 2)))| ≤
          K / Real.sqrt Δ := by
  obtain ⟨Δ0, K, hΔ0, hK, h⟩ := real_eigenvalue_asymptotics_sharp a θ R ha hR
  refine ⟨max Δ0 1, K, lt_max_of_lt_left hΔ0, hK, ?_⟩
  intro Δ hΔ
  have hΔ1 : 1 ≤ Δ := (le_max_right _ _).trans hΔ
  obtain ⟨l, hl, hb⟩ := h Δ ((le_max_left _ _).trans hΔ)
  refine ⟨l, hl, ?_⟩
  have e : l + (2 + 2 * (R / (2 * (1 + θ ^ 2)))) / (2 + R / (2 * (1 + θ ^ 2))) =
      l - lambdaZero θ R := by
    unfold lambdaZero
    rw [neg_div, sub_neg_eq_add]
  rw [e]
  refine hb.trans ?_
  have hs : 1 ≤ Real.sqrt Δ := by rw [Real.one_le_sqrt]; exact hΔ1
  have hss : Real.sqrt Δ ≤ Δ := by
    nlinarith [Real.sq_sqrt (by linarith : (0:ℝ) ≤ Δ)]
  exact div_le_div_of_nonneg_left hK (by linarith) hss

/-! ### The first-order condition and the Rayleigh shift -/

/-- the Rayleigh shift `mu = -N/(2D)` for `nu`. -/
def raylMu (a θ R ν : ℝ) : ℝ :=
  -(raylN a R ν (oscS a θ ν)) / (2 * raylD a θ R ν (oscS a θ ν))

/-- v2 prop:W1: `mu = -(a U + V nu^2)/(2 a K)` on a root of the quartic. -/
theorem raylMu_eq (a θ R ν : ℝ) (ha : 0 < a) (hθ : θ ≠ 0) (hR : 0 < R)
    (hq : freqQuartic a θ R (ν ^ 2) = 0) :
    raylMu a θ R ν = -(a * traceU θ R + traceV θ R * ν ^ 2) / (2 * (a * traceK θ R)) := by
  have e := rayl_ratio_root a θ R ν ha hθ hR hq
  have hD := raylD_pos a θ R ν (oscS a θ ν) ha hR
  have hK : 0 < traceK θ R := by
    unfold traceK; have := freqDisc_pos θ R hR; positivity
  unfold raylMu
  have : -(raylN a R ν (oscS a θ ν)) / (2 * raylD a θ R ν (oscS a θ ν)) =
      -(raylN a R ν (oscS a θ ν) / raylD a θ R ν (oscS a θ ν)) / 2 := by
    field_simp
  rw [this, e]
  field_simp

/-- v2 prop:W1: the Rayleigh shift `mu = -N/(2D)` satisfies the first-order condition `chi_eps(0, i nu) + mu chi_kappa(0, i nu) = 0` (real part, after `kappa^2 = -nu^2`). -/
theorem osc_first_order (a θ R ν : ℝ) (ha : 0 < a) (hθ : θ ≠ 0) (hR : 0 < R)
    (hq : freqQuartic a θ R (ν ^ 2) = 0) :
    (4 * (ν ^ 2) ^ 2 - a * (3 * R + 3 * θ ^ 2 + 11) * ν ^ 2 +
        2 * a ^ 2 * (R + 2 * θ ^ 2 + 2)) +
      raylMu a θ R ν * (5 * (ν ^ 2) ^ 2 - 3 * a * (5 + θ ^ 2 + R) * ν ^ 2 +
        a ^ 2 * (R + 4 * θ ^ 2 + 4)) = 0 := by
  rw [raylMu_eq a θ R ν ha hθ hR hq]
  have hK : 0 < traceK θ R := by
    unfold traceK; have := freqDisc_pos θ R hR; positivity
  have hq' : (ν ^ 2) ^ 2 - a * (5 + θ ^ 2 + R) * ν ^ 2 + a ^ 2 * (4 + 4 * θ ^ 2 + R) = 0 := by
    unfold freqQuartic at hq; linear_combination hq
  have haK : a * traceK θ R ≠ 0 := by positivity
  field_simp
  unfold traceK traceU traceV freqDisc
  linear_combination (3*R^3*a + 6*R^2*a*θ^2 + 22*R^2*a + 3*R*a*θ^4 - 6*R*a*θ^2 + 55*R*a -
    16*a*θ^4 + 32*a*θ^2 + 48*a + ν ^ 2 * (20*R*θ^2 - 20*R + 20*θ^4 - 40*θ^2 - 60)) * hq'

/-- v2 prop:W1: `chi_kappa(0, i nu) = 2 a (B nu^2 - 2 a q) != 0`, i.e. the roots `i nu_j` of `chi(0, .)` are simple (the quartic discriminant `(theta^2-3)^2 + R(R+6+2theta^2)` is positive). -/
theorem osc_simple (a θ R ν : ℝ) (ha : 0 < a) (hR : 0 < R)
    (hq : freqQuartic a θ R (ν ^ 2) = 0) :
    5 * (ν ^ 2) ^ 2 - 3 * a * (5 + θ ^ 2 + R) * ν ^ 2 + a ^ 2 * (R + 4 * θ ^ 2 + 4) ≠ 0 := by
  intro h
  have hq' : (ν ^ 2) ^ 2 - a * (5 + θ ^ 2 + R) * ν ^ 2 + a ^ 2 * (4 + 4 * θ ^ 2 + R) = 0 := by
    unfold freqQuartic at hq; linear_combination hq
  have h2 : (5 + θ ^ 2 + R) * ν ^ 2 - 2 * a * (4 + 4 * θ ^ 2 + R) = 0 := by
    have : 2 * a * ((5 + θ ^ 2 + R) * ν ^ 2 - 2 * a * (4 + 4 * θ ^ 2 + R)) = 0 := by
      linear_combination h - 5 * hq'
    exact (mul_eq_zero.mp this).resolve_left (by positivity)
  have hdisc := freqDisc_pos θ R hR
  have : a ^ 2 * (4 + 4 * θ ^ 2 + R) * freqDisc θ R = 0 := by
    unfold freqDisc
    linear_combination (-(5 + θ ^ 2 + R) ^ 2) * hq' +
      ((5 + θ ^ 2 + R) * ν ^ 2 + 2 * a * (4 + 4 * θ ^ 2 + R) - a * (5 + θ ^ 2 + R) ^ 2) * h2
  have hpos : 0 < a ^ 2 * (4 + 4 * θ ^ 2 + R) * freqDisc θ R := by positivity
  linarith

/-- v2 prop:W1 (oscillatory eigenvalues), one frequency: if `nu^2` is a root of the frequency
quartic, then for `Delta` large the Jacobian has a complex eigenvalue within `K/sqrt Delta` of
`i nu sqrt Delta + mu`, `mu = -N/(2D)`. -/
theorem oscillatory_eigenvalue_one (a θ R ν : ℝ) (ha : 0 < a) (hθ : θ ≠ 0) (hR : 0 < R)
    (hq : freqQuartic a θ R (ν ^ 2) = 0) :
    ∃ Δ0 K : ℝ, 0 < Δ0 ∧ 0 ≤ K ∧ ∀ Δ : ℝ, Δ0 ≤ Δ → ∃ z : ℂ,
      Matrix.det (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
        (jacobianMatrix a θ R Δ).map Complex.ofReal) = 0 ∧
      ‖z - (Complex.I * ν * (Real.sqrt Δ : ℂ) + (raylMu a θ R ν : ℂ))‖ ≤ K / Real.sqrt Δ := by
  have h0 : (ν ^ 2) ^ 2 - a * (5 + θ ^ 2 + R) * ν ^ 2 + a ^ 2 * (R + 4 * θ ^ 2 + 4) = 0 := by
    unfold freqQuartic at hq; linear_combination hq
  obtain ⟨ε1, K, hε1, hK, hroot⟩ := chi_root_near a θ R ν (raylMu a θ R ν) h0
    (osc_first_order a θ R ν ha hθ hR hq) (osc_simple a θ R ν ha hR hq)
  refine ⟨1 / ε1 ^ 2, K, by positivity, hK, ?_⟩
  intro Δ hΔ
  have hΔpos : 0 < Δ := lt_of_lt_of_le (by positivity) hΔ
  set ε : ℝ := 1 / Real.sqrt Δ with hε
  have hsq : 0 < Real.sqrt Δ := Real.sqrt_pos.2 hΔpos
  have hεpos : 0 < ε := by positivity
  have hεsq : Δ * ε ^ 2 = 1 := by
    rw [hε, div_pow, Real.sq_sqrt hΔpos.le]; field_simp
  have hεs : ε * Real.sqrt Δ = 1 := by rw [hε]; field_simp
  have hεle : ε ≤ ε1 := by
    by_contra hcon
    push Not at hcon
    have h1 : ε1 ^ 2 < ε ^ 2 := by nlinarith
    have h2 : 1 / ε1 ^ 2 * ε ^ 2 ≤ Δ * ε ^ 2 := mul_le_mul_of_nonneg_right hΔ (sq_nonneg _)
    have h3 : 1 < 1 / ε1 ^ 2 * ε ^ 2 := by
      rw [one_div, inv_mul_eq_div, lt_div_iff₀ (by positivity)]; linarith
    linarith
  obtain ⟨w, hw, hdist⟩ := hroot ε hεpos hεle
  refine ⟨w * (Real.sqrt Δ : ℂ), ?_, ?_⟩
  · rw [det_jacobian_complex]
    have hεsC : (ε : ℂ) * (Real.sqrt Δ : ℂ) = 1 := by exact_mod_cast hεs
    have hεsqC : (Δ : ℂ) * (ε : ℂ) ^ 2 = 1 := by exact_mod_cast hεsq
    have h := jacPoly_scale (a : ℂ) (θ : ℂ) (R : ℂ) (Δ : ℂ) (ε : ℂ) (w * (Real.sqrt Δ : ℂ))
      (by exact_mod_cast hεpos.ne') hεsqC
    rw [show (ε : ℂ) * (w * (Real.sqrt Δ : ℂ)) = w by linear_combination w * hεsC, hw] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 5 (by exact_mod_cast hεpos.ne'))
  · have hεsC : (ε : ℂ) * (Real.sqrt Δ : ℂ) = 1 := by exact_mod_cast hεs
    have key : w * (Real.sqrt Δ : ℂ) - (Complex.I * ν * (Real.sqrt Δ : ℂ) + (raylMu a θ R ν : ℂ)) =
        -((Complex.I * ν + (ε : ℂ) * (raylMu a θ R ν : ℂ) - w) * (Real.sqrt Δ : ℂ)) := by
      linear_combination (raylMu a θ R ν : ℂ) * hεsC
    rw [key, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hsq.le]
    have h1 : ‖Complex.I * ν + (ε : ℂ) * (raylMu a θ R ν : ℂ) - w‖ * Real.sqrt Δ ≤
        K * ε ^ 2 * Real.sqrt Δ := mul_le_mul_of_nonneg_right hdist hsq.le
    have h2 : K * ε ^ 2 * Real.sqrt Δ = K / Real.sqrt Δ := by
      rw [hε]; field_simp
    linarith

/-- v2 prop:W1: `mu` is even in `nu`. -/
theorem raylMu_neg (a θ R ν : ℝ) : raylMu a θ R (-ν) = raylMu a θ R ν := by
  simp [raylMu, raylN, raylD, oscS]

/-- v2 prop:W1 (lambda_j^{+-}), both signs: the Jacobian has eigenvalues within `K/sqrt Delta`
of `+- i nu sqrt Delta + mu` (the second is the complex conjugate of the first, up to the
same error). -/
theorem oscillatory_eigenvalue_asymptotics (a θ R ν : ℝ) (ha : 0 < a) (hθ : θ ≠ 0)
    (hR : 0 < R) (hq : freqQuartic a θ R (ν ^ 2) = 0) :
    ∃ Δ0 K : ℝ, 0 < Δ0 ∧ 0 ≤ K ∧ ∀ Δ : ℝ, Δ0 ≤ Δ →
      (∃ z : ℂ, Matrix.det (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
          (jacobianMatrix a θ R Δ).map Complex.ofReal) = 0 ∧
        ‖z - (Complex.I * ν * (Real.sqrt Δ : ℂ) + (raylMu a θ R ν : ℂ))‖ ≤ K / Real.sqrt Δ) ∧
      (∃ z : ℂ, Matrix.det (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
          (jacobianMatrix a θ R Δ).map Complex.ofReal) = 0 ∧
        ‖z - (-(Complex.I * ν * (Real.sqrt Δ : ℂ)) + (raylMu a θ R ν : ℂ))‖ ≤
          K / Real.sqrt Δ) := by
  obtain ⟨Δ1, K1, h1, k1, H1⟩ := oscillatory_eigenvalue_one a θ R ν ha hθ hR hq
  obtain ⟨Δ2, K2, h2, k2, H2⟩ := oscillatory_eigenvalue_one a θ R (-ν) ha hθ hR
    (by rw [neg_sq]; exact hq)
  refine ⟨max Δ1 Δ2, max K1 K2, lt_max_of_lt_left h1, le_max_of_le_left k1, ?_⟩
  intro Δ hΔ
  have hΔ1 : Δ1 ≤ Δ := (le_max_left _ _).trans hΔ
  have hΔ2 : Δ2 ≤ Δ := (le_max_right _ _).trans hΔ
  have hsq : 0 ≤ Real.sqrt Δ := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz, hb⟩ := H1 Δ hΔ1
    refine ⟨z, hz, hb.trans ?_⟩
    exact div_le_div_of_nonneg_right (le_max_left _ _) hsq
  · obtain ⟨z, hz, hb⟩ := H2 Δ hΔ2
    refine ⟨z, hz, ?_⟩
    rw [raylMu_neg] at hb
    have e : ((-ν : ℝ) : ℂ) = -(ν : ℂ) := by push_cast; ring
    rw [e] at hb
    have e2 : -(ν : ℂ) = -(ν : ℂ) := rfl
    refine le_trans (le_of_eq_of_le (by congr 2; ring) hb) ?_
    exact div_le_div_of_nonneg_right (le_max_right _ _) hsq

/-! ### Completeness of the five roots, and the trace -/

/-- v2 prop:W1: the trace of the Jacobian is `-4` exactly. -/
theorem trace_jacobian (a θ R Δ : ℝ) : Matrix.trace (jacobianMatrix a θ R Δ) = -4 := by
  simp [Matrix.trace, jacobianMatrix, Fin.sum_univ_succ]
  norm_num

/-- v2 prop:W1: for real `l` the complex and the real characteristic determinants agree. -/
theorem det_real_to_complex (a θ R Δ l : ℝ) :
    Matrix.det ((l : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
        (jacobianMatrix a θ R Δ).map Complex.ofReal) =
      ((Matrix.det (l • (1 : Matrix (Fin 5) (Fin 5) ℝ) - jacobianMatrix a θ R Δ) : ℝ) : ℂ) := by
  rw [det_jacobian_complex, det_jacobian_real]
  unfold jacPoly
  push_cast
  ring

/-- Five distinct roots of a `5 x 5` complex characteristic polynomial are all of its roots,
and their sum is the trace. -/
theorem eigenvalue_sum_of_injective (A : Matrix (Fin 5) (Fin 5) ℂ) (r : Fin 5 → ℂ)
    (hinj : Function.Injective r)
    (hr : ∀ i, Matrix.det ((r i) • (1 : Matrix (Fin 5) (Fin 5) ℂ) - A) = 0) :
    (∑ i, r i = A.trace) ∧
      ∀ z : ℂ, Matrix.det (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) - A) = 0 → ∃ i, z = r i := by
  classical
  have hroot : ∀ z : ℂ, A.charpoly.eval z = Matrix.det (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) - A) := by
    intro z
    rw [Matrix.eval_charpoly, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hne : A.charpoly ≠ 0 := A.charpoly_monic.ne_zero
  have hmem : ∀ z : ℂ, z ∈ A.charpoly.roots ↔
      Matrix.det (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) - A) = 0 := by
    intro z
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, hroot]
  set s : Finset ℂ := Finset.univ.image r with hs
  have hscard : s.card = 5 := by
    rw [hs, Finset.card_image_of_injective _ hinj]; simp
  have hrcard : Multiset.card A.charpoly.roots = 5 := by
    have h1 := (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots
    rw [Matrix.charpoly_natDegree_eq_dim] at h1
    simpa using h1.symm
  have hsub : s.val ⊆ A.charpoly.roots := by
    intro z hz
    have : z ∈ s := hz
    rw [hs, Finset.mem_image] at this
    obtain ⟨i, -, rfl⟩ := this
    exact (hmem _).2 (hr i)
  have hle : s.val ≤ A.charpoly.roots := (Multiset.le_iff_subset s.nodup).2 hsub
  have heq : s.val = A.charpoly.roots :=
    Multiset.eq_of_le_of_card_le hle (by
      show Multiset.card A.charpoly.roots ≤ s.card
      omega)
  refine ⟨?_, ?_⟩
  · have := Matrix.trace_eq_sum_roots_charpoly A
    rw [this, ← heq]
    have h2 : s.val.sum = ∑ x ∈ s, x := by
      rw [Finset.sum_eq_multiset_sum, Multiset.map_id']
    rw [h2, hs, Finset.sum_image (fun i _ j _ h => hinj h)]
  · intro z hz
    have : z ∈ A.charpoly.roots := (hmem z).2 hz
    rw [← heq] at this
    have h2 : z ∈ s := this
    rw [hs, Finset.mem_image] at h2
    obtain ⟨i, -, hi⟩ := h2
    exact ⟨i, hi.symm⟩

/-- v2 prop:W1: the trace of the complexified Jacobian is `-4`. -/
theorem trace_jacobian_complex (a θ R Δ : ℝ) :
    Matrix.trace ((jacobianMatrix a θ R Δ).map Complex.ofReal) = -4 := by
  simp [Matrix.trace, jacobianMatrix, Fin.sum_univ_succ]
  norm_num

/-- The imaginary part moves by at most the distance. -/
theorem im_le_of_dist (z t : ℂ) (r : ℝ) (h : ‖z - t‖ ≤ r) : |z.im - t.im| ≤ r := by
  have := Complex.abs_im_le_norm (z - t)
  simp only [Complex.sub_im] at this
  exact this.trans h

/-- v2 prop:W1 (completeness and trace): with `nu_1^2 < nu_2^2` the roots of the frequency
quartic, for `Delta` large the Jacobian has five distinct eigenvalues `lambda_0`,
`lambda_j^+-`, within `K/sqrt Delta` of the predicted values; they are all of the eigenvalues, and
they sum to the trace `-4`. -/
def FiveEigenvalues (a θ R : ℝ) : Prop :=
    ∃ Δ0 K : ℝ, 0 < Δ0 ∧ 0 ≤ K ∧ ∀ Δ : ℝ, Δ0 ≤ Δ → ∃ (l : ℝ) (z1 z1' z2 z2' : ℂ),
      Matrix.det (l • (1 : Matrix (Fin 5) (Fin 5) ℝ) - jacobianMatrix a θ R Δ) = 0 ∧
      |l - lambdaZero θ R| ≤ K / Real.sqrt Δ ∧
      Matrix.det (z1 • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
        (jacobianMatrix a θ R Δ).map Complex.ofReal) = 0 ∧
      ‖z1 - (Complex.I * (Real.sqrt (freqSq1 a θ R) : ℝ) * (Real.sqrt Δ : ℂ) +
        (raylMu a θ R (Real.sqrt (freqSq1 a θ R)) : ℂ))‖ ≤ K / Real.sqrt Δ ∧
      Matrix.det (z1' • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
        (jacobianMatrix a θ R Δ).map Complex.ofReal) = 0 ∧
      ‖z1' - (-(Complex.I * (Real.sqrt (freqSq1 a θ R) : ℝ) * (Real.sqrt Δ : ℂ)) +
        (raylMu a θ R (Real.sqrt (freqSq1 a θ R)) : ℂ))‖ ≤ K / Real.sqrt Δ ∧
      Matrix.det (z2 • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
        (jacobianMatrix a θ R Δ).map Complex.ofReal) = 0 ∧
      ‖z2 - (Complex.I * (Real.sqrt (freqSq2 a θ R) : ℝ) * (Real.sqrt Δ : ℂ) +
        (raylMu a θ R (Real.sqrt (freqSq2 a θ R)) : ℂ))‖ ≤ K / Real.sqrt Δ ∧
      Matrix.det (z2' • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
        (jacobianMatrix a θ R Δ).map Complex.ofReal) = 0 ∧
      ‖z2' - (-(Complex.I * (Real.sqrt (freqSq2 a θ R) : ℝ) * (Real.sqrt Δ : ℂ)) +
        (raylMu a θ R (Real.sqrt (freqSq2 a θ R)) : ℂ))‖ ≤ K / Real.sqrt Δ ∧
      Function.Injective ![z2', z1', (l : ℂ), z1, z2] ∧
      (l : ℂ) + z1 + z1' + z2 + z2' = -4 ∧
      ∀ z : ℂ, Matrix.det (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
          (jacobianMatrix a θ R Δ).map Complex.ofReal) = 0 →
        z = l ∨ z = z1 ∨ z = z1' ∨ z = z2 ∨ z = z2'

/-- v2 prop:W1 (completeness and trace), see `FiveEigenvalues`. -/
theorem five_eigenvalues (a θ R : ℝ) (ha : 0 < a) (hθ : θ ≠ 0) (hR : 0 < R) :
    FiveEigenvalues a θ R := by
  unfold FiveEigenvalues
  obtain ⟨hx1, hx12, hq1, hq2, -⟩ := frequency_roots a θ R ha hR
  set ν1 := Real.sqrt (freqSq1 a θ R) with hν1
  set ν2 := Real.sqrt (freqSq2 a θ R) with hν2
  have hν1pos : 0 < ν1 := Real.sqrt_pos.2 hx1
  have hν12 : ν1 < ν2 := Real.sqrt_lt_sqrt hx1.le hx12
  have hν1sq : ν1 ^ 2 = freqSq1 a θ R := Real.sq_sqrt hx1.le
  have hν2sq : ν2 ^ 2 = freqSq2 a θ R := Real.sq_sqrt (hx1.trans hx12).le
  have hq1' : freqQuartic a θ R (ν1 ^ 2) = 0 := by rw [hν1sq]; exact hq1
  have hq2' : freqQuartic a θ R (ν2 ^ 2) = 0 := by rw [hν2sq]; exact hq2
  obtain ⟨Δa, Ka, ha0, ka, Ha⟩ := real_eigenvalue_asymptotics_sharp a θ R ha.ne' hR.le
  obtain ⟨Δb, Kb, hb0, kb, Hb⟩ := oscillatory_eigenvalue_asymptotics a θ R ν1 ha hθ hR hq1'
  obtain ⟨Δc, Kc, hc0, kc, Hc⟩ := oscillatory_eigenvalue_asymptotics a θ R ν2 ha hθ hR hq2'
  set K := max Ka (max Kb Kc) with hK
  have hK0 : 0 ≤ K := le_max_of_le_left ka
  set δ := min ν1 (ν2 - ν1) with hδ
  have hδpos : 0 < δ := lt_min hν1pos (by linarith)
  refine ⟨max (max Δa (max Δb Δc)) (max 1 (2 * K / δ + 1)), K, by positivity, hK0, ?_⟩
  intro Δ hΔ
  have hΔa : Δa ≤ Δ := ((le_max_left _ _).trans (le_max_left _ _)).trans hΔ
  have hΔb : Δb ≤ Δ := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hΔ
  have hΔc : Δc ≤ Δ := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hΔ
  have hΔ1 : 1 ≤ Δ := ((le_max_left _ _).trans (le_max_right _ _)).trans hΔ
  have hΔδ : 2 * K / δ + 1 ≤ Δ := ((le_max_right _ _).trans (le_max_right _ _)).trans hΔ
  have hΔpos : 0 < Δ := by linarith
  have hS : 0 < Real.sqrt Δ := Real.sqrt_pos.2 hΔpos
  have hSS : Real.sqrt Δ * Real.sqrt Δ = Δ := Real.mul_self_sqrt hΔpos.le
  have hS1 : 1 ≤ Real.sqrt Δ := by rw [Real.one_le_sqrt]; exact hΔ1
  have hSΔ : Real.sqrt Δ ≤ Δ := by nlinarith
  have hKδ : 2 * K < δ * Δ := by
    have : 2 * K / δ < Δ := by linarith
    rw [div_lt_iff₀ hδpos] at this
    linarith
  have hKδ1 : δ ≤ ν1 := min_le_left _ _
  have hKδ2 : δ ≤ ν2 - ν1 := min_le_right _ _
  have hdiv : ∀ K' : ℝ, 0 ≤ K' → K' ≤ K → K' / Real.sqrt Δ ≤ K / Real.sqrt Δ :=
    fun K' _ h => div_le_div_of_nonneg_right h hS.le
  -- the roots
  obtain ⟨l, hl, hlb⟩ := Ha Δ hΔa
  obtain ⟨⟨z1, hz1, hz1b⟩, ⟨z1', hz1', hz1'b⟩⟩ := Hb Δ hΔb
  obtain ⟨⟨z2, hz2, hz2b⟩, ⟨z2', hz2', hz2'b⟩⟩ := Hc Δ hΔc
  have hlb' : |l - lambdaZero θ R| ≤ K / Real.sqrt Δ :=
    hlb.trans ((div_le_div_of_nonneg_left ka hS hSΔ).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) hS.le))
  have hz1b' := hz1b.trans (div_le_div_of_nonneg_right
    ((le_max_left _ _).trans (le_max_right _ _) : Kb ≤ K) hS.le)
  have hz1'b' := hz1'b.trans (div_le_div_of_nonneg_right
    ((le_max_left _ _).trans (le_max_right _ _) : Kb ≤ K) hS.le)
  have hz2b' := hz2b.trans (div_le_div_of_nonneg_right
    ((le_max_right _ _).trans (le_max_right _ _) : Kc ≤ K) hS.le)
  have hz2'b' := hz2'b.trans (div_le_div_of_nonneg_right
    ((le_max_right _ _).trans (le_max_right _ _) : Kc ≤ K) hS.le)
  -- imaginary parts
  set e := K / Real.sqrt Δ with he
  have heS : e * Real.sqrt Δ = K := by rw [he]; field_simp
  have i1 : |z1.im - ν1 * Real.sqrt Δ| ≤ e := by
    have := im_le_of_dist _ _ _ hz1b'
    simpa using this
  have i1' : |z1'.im - -(ν1 * Real.sqrt Δ)| ≤ e := by
    have := im_le_of_dist _ _ _ hz1'b'
    simpa using this
  have i2 : |z2.im - ν2 * Real.sqrt Δ| ≤ e := by
    have := im_le_of_dist _ _ _ hz2b'
    simpa using this
  have i2' : |z2'.im - -(ν2 * Real.sqrt Δ)| ≤ e := by
    have := im_le_of_dist _ _ _ hz2'b'
    simpa using this
  rw [abs_le] at i1 i1' i2 i2'
  have ea : e < ν1 * Real.sqrt Δ := by
    rw [he, div_lt_iff₀ hS, mul_assoc, hSS]
    have := mul_le_mul_of_nonneg_right hKδ1 hΔpos.le
    linarith
  have eb : 2 * e < (ν2 - ν1) * Real.sqrt Δ := by
    rw [he, ← mul_div_assoc, div_lt_iff₀ hS, mul_assoc, hSS]
    have := mul_le_mul_of_nonneg_right hKδ2 hΔpos.le
    linarith
  have c1 : z2'.im < z1'.im := by linarith [i1'.1, i1'.2, i2'.1, i2'.2]
  have c2 : z1'.im < (l : ℂ).im := by
    rw [Complex.ofReal_im]; linarith [i1'.1, i1'.2]
  have c3 : (l : ℂ).im < z1.im := by
    rw [Complex.ofReal_im]; linarith [i1.1, i1.2]
  have c4 : z1.im < z2.im := by linarith [i1.1, i1.2, i2.1, i2.2]
  have hinj : Function.Injective ![z2', z1', (l : ℂ), z1, z2] := by
    have hmono : StrictMono (fun i => (![z2', z1', (l : ℂ), z1, z2] i).im) := by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      fin_cases i
      · exact c1
      · exact c2
      · exact c3
      · exact c4
    exact Function.Injective.of_comp hmono.injective
  have hroots : ∀ i, Matrix.det ((![z2', z1', (l : ℂ), z1, z2] i) • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
      (jacobianMatrix a θ R Δ).map Complex.ofReal) = 0 := by
    intro i
    fin_cases i
    · exact hz2'
    · exact hz1'
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      rw [det_real_to_complex, hl]; simp
    · exact hz1
    · exact hz2
  obtain ⟨hsum, hall⟩ := eigenvalue_sum_of_injective _ _ hinj hroots
  refine ⟨l, z1, z1', z2, z2', hl, hlb', hz1, hz1b', hz1', hz1'b', hz2, hz2b', hz2', hz2'b', hinj,
    ?_, ?_⟩
  · rw [trace_jacobian_complex, Fin.sum_univ_five] at hsum
    simp at hsum
    linear_combination hsum
  · intro z hz
    obtain ⟨i, hi⟩ := hall z hz
    fin_cases i <;> simp at hi <;> tauto

/-- v2 prop:W1 (trace corollary): the real parts of the five eigenvalues sum to `-4` (the
trace), so `lambda_0 + 2 mu_1 + 2 mu_2 = -4 + O(Delta^{-1/2})`.  (The limiting identity holds
with no error term, see `lambda_mu_trace`.) -/
theorem trace_corollary (a θ R : ℝ) (ha : 0 < a) (hθ : θ ≠ 0) (hR : 0 < R) :
    ∃ Δ0 K : ℝ, 0 < Δ0 ∧ 0 ≤ K ∧ ∀ Δ : ℝ, Δ0 ≤ Δ →
      |lambdaZero θ R + 2 * raylMu a θ R (Real.sqrt (freqSq1 a θ R)) +
          2 * raylMu a θ R (Real.sqrt (freqSq2 a θ R)) + 4| ≤ 5 * K / Real.sqrt Δ := by
  obtain ⟨Δ0, K, hΔ0, hK, H⟩ := five_eigenvalues a θ R ha hθ hR
  refine ⟨Δ0, K, hΔ0, hK, ?_⟩
  intro Δ hΔ
  obtain ⟨l, z1, z1', z2, z2', -, hl, -, h1, -, h1', -, h2, -, h2', -, hsum, -⟩ := H Δ hΔ
  set e := K / Real.sqrt Δ with he
  have hre : ∀ (z t : ℂ), ‖z - t‖ ≤ e → |z.re - t.re| ≤ e := by
    intro z t h
    have := Complex.abs_re_le_norm (z - t)
    simp only [Complex.sub_re] at this
    exact this.trans h
  have r1 := hre _ _ h1
  have r1' := hre _ _ h1'
  have r2 := hre _ _ h2
  have r2' := hre _ _ h2'
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, zero_mul, zero_add, mul_zero,
    sub_zero, neg_zero] at r1 r1' r2 r2'
  have hs := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.ofReal_re] at hs
  have hs' : l + z1.re + z1'.re + z2.re + z2'.re = -4 := by
    have h4 : ((-4 : ℂ)).re = -4 := by simp
    rw [h4] at hs
    linarith
  rw [abs_le] at r1 r1' r2 r2' hl ⊢
  have : 5 * K / Real.sqrt Δ = 5 * e := by rw [he]; ring
  rw [this]
  constructor <;> linarith [r1.1, r1.2, r1'.1, r1'.2, r2.1, r2.2, r2'.1, r2'.2, hl.1, hl.2]

/-! ### Specialization to the equilibrium of eq:LR5 -/

/-- `alpha*` at the equilibrium (it does not depend on `Delta`). -/
def eqAlpha (r Phi : ℝ) : ℝ := dynamicAlpha r (dynamicCanonicalEquilibrium r 1 Phi)

/-- v2 prop:W1: `alpha*` does not depend on `Delta`. -/
theorem eqAlpha_eq (r δ Phi : ℝ) :
    dynamicAlpha r (dynamicCanonicalEquilibrium r δ Phi) = eqAlpha r Phi := rfl

/-- v2 prop:W1: `alpha* > 0`. -/
theorem eqAlpha_pos (r Phi : ℝ) : 0 < eqAlpha r Phi := Real.exp_pos _

/-- v2 prop:W1: the matrix `jacobianMatrix (alpha*) theta* R* Delta` is the Frechet derivative
of eq:LR5 at `y*` (restatement of `hasFDerivAt_dynamicField_equilibrium` with `alpha*`
exposed as a `Delta`-independent constant). -/
theorem prop_W1_jacobian (r delta Phi : ℝ) :
    HasFDerivAt (dynamicField r delta Phi)
      (LinearMap.toContinuousLinearMap
        (Matrix.toLin' (jacobianMatrix (eqAlpha r Phi) (positiveRoot r Phi)
          (equilibriumBulk r Phi) delta)))
      (dynamicCanonicalEquilibrium r delta Phi) :=
  hasFDerivAt_dynamicField_equilibrium r delta Phi

/-- v2 prop:W1: for `Phi > 0` the equilibrium parameters satisfy `alpha* > 0`, `theta* != 0`, `R* > 0`. -/
theorem equilibrium_params_pos (r Phi : ℝ) (hr : 0 < r) (hPhi : 0 < Phi) :
    0 < eqAlpha r Phi ∧ positiveRoot r Phi ≠ 0 ∧ 0 < equilibriumBulk r Phi := by
  have hθ : 0 < positiveRoot r Phi := (positiveRoot_spec r Phi hr hPhi.le).1
  refine ⟨eqAlpha_pos r Phi, hθ.ne', ?_⟩
  unfold equilibriumBulk
  positivity

/-- v2 prop:W1 (lambda_0) at the equilibrium of eq:LR5, `Phi > 0`. -/
theorem equilibrium_real_eigenvalue (r Phi : ℝ) (hr : 0 < r) (hPhi : 0 < Phi) :
    ∃ Δ0 K : ℝ, 0 < Δ0 ∧ 0 ≤ K ∧ ∀ Δ : ℝ, Δ0 ≤ Δ → ∃ l : ℝ,
      Matrix.det (l • (1 : Matrix (Fin 5) (Fin 5) ℝ) -
        jacobianMatrix (eqAlpha r Phi) (positiveRoot r Phi) (equilibriumBulk r Phi) Δ) = 0 ∧
      |l + (2 + 2 * (equilibriumBulk r Phi / (2 * (1 + positiveRoot r Phi ^ 2)))) /
          (2 + equilibriumBulk r Phi / (2 * (1 + positiveRoot r Phi ^ 2)))| ≤
        K / Real.sqrt Δ := by
  obtain ⟨ha, -, hR⟩ := equilibrium_params_pos r Phi hr hPhi
  exact real_eigenvalue_asymptotics _ _ _ ha.ne' hR.le

/-- v2 prop:W1 (all five eigenvalues) at the equilibrium of eq:LR5, `Phi > 0`: for `Delta`
large there are five distinct eigenvalues `lambda_0`, `lambda_j^{+-}` of the stated asymptotic
form, these are all the eigenvalues, and they sum to the trace `-4`. -/
theorem equilibrium_five_eigenvalues (r Phi : ℝ) (hr : 0 < r) (hPhi : 0 < Phi) :
    FiveEigenvalues (eqAlpha r Phi) (positiveRoot r Phi) (equilibriumBulk r Phi) := by
  obtain ⟨ha, hθ, hR⟩ := equilibrium_params_pos r Phi hr hPhi
  exact five_eigenvalues _ _ _ ha hθ hR

end
end SparseSGD.Logistic.V2
