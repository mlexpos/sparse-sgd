import Mathlib

/-!
# Drift recursion: local contraction, fixed point, tracking, Jacobian products (v2)

Abstract form of `cor:recursion` of `lr_windows.tex` (v2 results; nothing here replaces a v1
declaration).  The one-step map is `Psi eps y = y + eps • (b y + e eps y)` (`driftMap`) with `b`
strictly differentiable at `ystar` with derivative `A`, and `e eps` an `O(rho eps)` perturbation
which is `rho eps`-bounded and `rho eps`-Lipschitz on a ball (`RecursionSetup`).  The Lyapunov
certificate `(P, c)` of `A` is a hypothesis (`x ⬝ x ≤ x ⬝ P x`, `x ⬝ (Aᵀ P + P A) x ≤ -c x ⬝ x`),
so this file does not depend on the proof that the Jacobian is Hurwitz.

* `local_fixed_point` (`cor:recursion`, "Fixed point"): a `P`-ball `N` around `ystar`, invariance,
  unique fixed point `y_eps` with `‖y_eps - ystar‖ ≤ C rho eps`, contraction at rate `1 - κ eps`.
* `drift_recursion_converges` (`cor:recursion`, entry + uniform-in-time tracking): from every start
  in `K`, `‖Psi^k y0 - y_eps‖ ≤ C exp(-c eps k)` and `sup_k ‖Psi^k y0 - y(k eps)‖ ≤ C rho eps`.
* `jacobian_products` (`cor:recursion`, "Products"): `‖J_{j+m-1} ∘ ⋯ ∘ J_j‖ ≤ Γ exp(-c eps m)`.

All estimates use the quadratic form `q x = x ⬝ P x` and the sup norm, with the equivalence
`‖x‖² ≤ q x ≤ S ‖x‖²`, so no triangle inequality for the `P`-norm is needed.  The error term in the
anchor estimate is `eps C2 rho²` (quadratic), which is what gives a fixed point at distance
`O(rho eps)` rather than `O(sqrt eps)`.

Hypotheses added to the tex statement (recorded as tex corrections in the report): existence of a
solution from every start in `K`; a uniform a priori bound for solutions from `K` on finite
horizons; one-step consistency of the recursion along solutions near `ystar`; differentiability of
`b`, `e eps` on the ball and a finite-horizon a priori bound `1 + L eps` on the Jacobians.
-/

open Filter Topology Set Metric

namespace SparseSGD.Logistic.V2

open Matrix

/-- The one-step drift map `Psi eps y = y + eps • (b y + e eps y)`, with `e eps` the
`O(rho eps)` error (v2 `cor:recursion`, decomposition `Psi = y + eps(b + e)`). -/
def driftMap {n : ℕ} (b : (Fin n → ℝ) → (Fin n → ℝ))
    (e : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (ε : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  y + ε • (b y + e ε y)

/-- `y` is a solution of `y' = f y` on `[0, ∞)` started at `y0`. -/
def IsODESol {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E) (y0 : E)
    (y : ℝ → E) : Prop :=
  y 0 = y0 ∧ ∀ t : ℝ, 0 ≤ t → HasDerivAt y (f (y t)) t

/-- v2 `cor:recursion` (entry): every solution of `y' = f y` started in `K` is within `ρ` of
`ystar` at all times after a time `T0` that depends only on `ρ` and `K`. -/
def UniformEntry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E) (ystar : E)
    (K : Set E) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ T0 : ℝ, 0 ≤ T0 ∧ ∀ y0 ∈ K, ∀ y : ℝ → E, IsODESol f y0 y →
    ∀ t : ℝ, T0 ≤ t → ‖y t - ystar‖ ≤ ρ

/-- Products of Jacobians along an orbit: `jacProd Ψ x m = J_{m-1} ∘ ⋯ ∘ J_0` with
`J_t = fderiv Ψ (Ψ^[t] x)`. -/
noncomputable def jacProd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ψ : E → E)
    (x : E) : ℕ → (E →L[ℝ] E)
  | 0 => ContinuousLinearMap.id ℝ E
  | m + 1 => (fderiv ℝ Ψ (Ψ^[m] x)).comp (jacProd Ψ x m)

/-- Setting of v2 `cor:recursion`: a Lyapunov certificate `(P, c)` of the matrix `A`, a field
`b` with `b ystar = 0` and strict derivative `A` at `ystar`, and an error family `e` of size
`ρ ε ≥ ε` which is `ρ ε`-bounded and `ρ ε`-Lipschitz on `closedBall ystar r0`.  The
certificate is a hypothesis (`P` symmetric, `x ⬝ x ≤ x ⬝ P x`,
`x ⬝ (Aᵀ P + P A) x ≤ -c x ⬝ x`) so that this file is independent of the proof that the
Jacobian is Hurwitz. -/
structure RecursionSetup (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  P : Matrix (Fin n) (Fin n) ℝ
  c : ℝ
  hc : 0 < c
  hPs : Pᵀ = P
  hge : ∀ x : Fin n → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ (P *ᵥ x)
  hdec : ∀ x : Fin n → ℝ, x ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x) ≤ -c * (x ⬝ᵥ x)
  b : (Fin n → ℝ) → (Fin n → ℝ)
  ystar : Fin n → ℝ
  hb0 : b ystar = 0
  hb : HasStrictFDerivAt b (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)) ystar
  e : ℝ → (Fin n → ℝ) → (Fin n → ℝ)
  ρ : ℝ → ℝ
  r0 : ℝ
  hr0 : 0 < r0
  hρε : ∀ ε : ℝ, 0 < ε → ε ≤ ρ ε
  he0 : ∀ ε : ℝ, 0 < ε → ∀ y : Fin n → ℝ, ‖y - ystar‖ ≤ r0 → ‖e ε y‖ ≤ ρ ε
  he1 : ∀ ε : ℝ, 0 < ε → ∀ y z : Fin n → ℝ, ‖y - ystar‖ ≤ r0 → ‖z - ystar‖ ≤ r0 →
    ‖e ε y - e ε z‖ ≤ ρ ε * ‖y - z‖

namespace RecursionContraction

/-- State space of the abstract recursion (sup norm). -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- The quadratic form `x ⬝ P x`. -/
def qf {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) : ℝ := x ⬝ᵥ (P *ᵥ x)

/-- Sum of the absolute values of the entries. -/
def absSum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, |M i j|

section Algebra

variable {n : ℕ}

lemma absSum_nonneg (M : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ absSum M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma norm_sq_le_dot (x : Vec n) : ‖x‖ ^ 2 ≤ x ⬝ᵥ x := by
  have hnn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have h : ‖x‖ ≤ Real.sqrt (x ⬝ᵥ x) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    have := Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
    simpa [dotProduct, sq] using this
  calc ‖x‖ ^ 2 ≤ (Real.sqrt (x ⬝ᵥ x)) ^ 2 := by gcongr
    _ = x ⬝ᵥ x := Real.sq_sqrt hnn

lemma abs_bil_le (P : Matrix (Fin n) (Fin n) ℝ) (u w : Vec n) :
    |u ⬝ᵥ (P *ᵥ w)| ≤ absSum P * ‖u‖ * ‖w‖ := by
  have h1 : u ⬝ᵥ (P *ᵥ w) = ∑ i, ∑ j, u i * (P i j * w j) := by
    simp [dotProduct, mulVec, Finset.mul_sum]
  rw [h1]
  calc |∑ i, ∑ j, u i * (P i j * w j)|
      ≤ ∑ i, |∑ j, u i * (P i j * w j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |u i * (P i j * w j)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, (|P i j| * ‖u‖ * ‖w‖) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have hu : |u i| ≤ ‖u‖ := by simpa using norm_le_pi_norm u i
        have hw : |w j| ≤ ‖w‖ := by simpa using norm_le_pi_norm w j
        rw [abs_mul, abs_mul]
        calc |u i| * (|P i j| * |w j|) = |P i j| * (|u i| * |w j|) := by ring
          _ ≤ |P i j| * (‖u‖ * ‖w‖) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hu hw (abs_nonneg _) (norm_nonneg _)) (abs_nonneg _)
          _ = |P i j| * ‖u‖ * ‖w‖ := by ring
    _ = absSum P * ‖u‖ * ‖w‖ := by
        simp only [absSum, Finset.sum_mul]

lemma norm_mulVec_le (A : Matrix (Fin n) (Fin n) ℝ) (v : Vec n) :
    ‖A *ᵥ v‖ ≤ absSum A * ‖v‖ := by
  have hnn : 0 ≤ absSum A * ‖v‖ := mul_nonneg (absSum_nonneg A) (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have h1 : (A *ᵥ v) i = ∑ j, A i j * v j := rfl
  rw [h1]
  calc |∑ j, A i j * v j| ≤ ∑ j, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |A i j| * ‖v‖ := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm v j) (abs_nonneg _)
    _ = (∑ j, |A i j|) * ‖v‖ := by rw [Finset.sum_mul]
    _ ≤ absSum A * ‖v‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ j, |A i j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

lemma qf_add (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (u w : Vec n) :
    qf P (u + w) = qf P u + 2 * (u ⬝ᵥ (P *ᵥ w)) + qf P w := by
  have hsw : w ⬝ᵥ (P *ᵥ u) = u ⬝ᵥ (P *ᵥ w) := by
    rw [dotProduct_mulVec, ← hP, vecMul_transpose, hP, dotProduct_comm]
  simp only [qf, mulVec_add, dotProduct_add, add_dotProduct]
  rw [hsw]; ring

lemma qf_smul (P : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (w : Vec n) :
    qf P (t • w) = t ^ 2 * qf P w := by
  simp only [qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring

lemma qf_le_abs (P : Matrix (Fin n) (Fin n) ℝ) (S : ℝ) (hS : absSum P ≤ S) (x : Vec n) :
    qf P x ≤ S * ‖x‖ ^ 2 := by
  have h := (le_abs_self _).trans (abs_bil_le P x x)
  have : absSum P * ‖x‖ * ‖x‖ ≤ S * ‖x‖ ^ 2 := by
    have : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
    nlinarith
  exact h.trans this

lemma quad_form_eq (A P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (d : Vec n) :
    d ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ d) = 2 * (d ⬝ᵥ (P *ᵥ (A *ᵥ d))) := by
  have hsw : (A *ᵥ d) ⬝ᵥ (P *ᵥ d) = d ⬝ᵥ (P *ᵥ (A *ᵥ d)) := by
    rw [dotProduct_mulVec, ← hP, vecMul_transpose, hP, dotProduct_comm]
  rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose, hsw]
  ring

/-- One-step estimate for the quadratic form: the core algebraic inequality. -/
lemma qf_step_le (A P : Matrix (Fin n) (Fin n) ℝ) (hPs : Pᵀ = P) (c : ℝ) (hc : 0 ≤ c)
    (hdec : ∀ x : Vec n, x ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x) ≤ -c * (x ⬝ᵥ x))
    (S : ℝ) (hS : absSum P ≤ S) (ε : ℝ) (hε : 0 ≤ ε) (hεa : ε * absSum A ≤ 1)
    (d w : Vec n) :
    qf P (d + ε • (A *ᵥ d + w)) ≤ qf P d - ε * c * ‖d‖ ^ 2
      + ε ^ 2 * S * absSum A ^ 2 * ‖d‖ ^ 2 + 4 * ε * S * ‖d‖ * ‖w‖ + ε ^ 2 * S * ‖w‖ ^ 2 := by
  set a := absSum A with ha
  have ha0 : 0 ≤ a := absSum_nonneg A
  have hS0 : 0 ≤ S := (absSum_nonneg P).trans hS
  have hAd : ‖A *ᵥ d‖ ≤ a * ‖d‖ := norm_mulVec_le A d
  set u : Vec n := d + ε • (A *ᵥ d) with hu
  have hsplit : d + ε • (A *ᵥ d + w) = u + ε • w := by
    rw [hu, smul_add]; abel
  have hnu : ‖u‖ ≤ 2 * ‖d‖ := by
    calc ‖u‖ ≤ ‖d‖ + ‖ε • (A *ᵥ d)‖ := norm_add_le _ _
      _ = ‖d‖ + ε * ‖A *ᵥ d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
      _ ≤ ‖d‖ + ε * (a * ‖d‖) := by gcongr
      _ = ‖d‖ + (ε * a) * ‖d‖ := by ring
      _ ≤ ‖d‖ + 1 * ‖d‖ := by gcongr
      _ = 2 * ‖d‖ := by ring
  have hqu : qf P u = qf P d + ε * (d ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ d)) + ε ^ 2 * qf P (A *ᵥ d) := by
    rw [hu, qf_add P hPs, qf_smul, quad_form_eq A P hPs, mulVec_smul, dotProduct_smul,
      smul_eq_mul]
    ring
  have hdd : ‖d‖ ^ 2 ≤ d ⬝ᵥ d := norm_sq_le_dot d
  have h1 : ε * (d ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ d)) ≤ -(ε * c * ‖d‖ ^ 2) := by
    have := hdec d
    have h2 : -c * (d ⬝ᵥ d) ≤ -c * ‖d‖ ^ 2 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left (this.trans h2) hε
    linarith
  have h4 : qf P (A *ᵥ d) ≤ S * (a * ‖d‖) ^ 2 := by
    refine (qf_le_abs P S hS _).trans ?_
    have : ‖A *ᵥ d‖ ^ 2 ≤ (a * ‖d‖) ^ 2 := by gcongr
    exact mul_le_mul_of_nonneg_left this hS0
  have h5 : 2 * ε * (u ⬝ᵥ (P *ᵥ w)) ≤ 4 * ε * S * ‖d‖ * ‖w‖ := by
    have h6 := (le_abs_self _).trans (abs_bil_le P u w)
    have h7 : absSum P * ‖u‖ * ‖w‖ ≤ S * (2 * ‖d‖) * ‖w‖ := by
      gcongr
    have : u ⬝ᵥ (P *ᵥ w) ≤ S * (2 * ‖d‖) * ‖w‖ := h6.trans h7
    nlinarith [mul_le_mul_of_nonneg_left this hε]
  have h8 : qf P w ≤ S * ‖w‖ ^ 2 := qf_le_abs P S hS w
  rw [hsplit, qf_add P hPs, qf_smul, hqu, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h9 : ε ^ 2 * qf P (A *ᵥ d) ≤ ε ^ 2 * (S * (a * ‖d‖) ^ 2) :=
    mul_le_mul_of_nonneg_left h4 (sq_nonneg ε)
  have h10 : ε ^ 2 * qf P w ≤ ε ^ 2 * (S * ‖w‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h8 (sq_nonneg ε)
  nlinarith [h1, h5, h9, h10]

lemma real_ineq_V (ε S a c η X W : ℝ) (hε : 0 < ε) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hη : 8 * S * η ≤ c / 4) (hS : 1 ≤ S) (h1 : ε * S * (a ^ 2 + 4) ≤ c / 4)
    (hX : 0 ≤ X) (hW : 0 ≤ W) (hWX : W ≤ 2 * η * X) :
    -(ε * c * X ^ 2) + ε ^ 2 * S * a ^ 2 * X ^ 2 + 4 * ε * S * X * W + ε ^ 2 * S * W ^ 2
      ≤ -(ε * c / 4) * X ^ 2 := by
  have hS0 : 0 ≤ S := by linarith
  have hεS : 0 ≤ ε * S := by positivity
  have ha2 : ε * S * a ^ 2 ≤ c / 4 := by nlinarith [mul_nonneg hεS (by norm_num : (0:ℝ) ≤ 4)]
  have h4 : 4 * ε * S ≤ c / 4 := by nlinarith [mul_nonneg hεS (sq_nonneg a)]
  have t1 : ε ^ 2 * S * a ^ 2 * X ^ 2 ≤ ε * (c / 4) * X ^ 2 := by
    have : ε ^ 2 * S * a ^ 2 * X ^ 2 = ε * X ^ 2 * (ε * S * a ^ 2) := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left ha2 (mul_nonneg hε.le (sq_nonneg X))]
  have t2 : 4 * ε * S * X * W ≤ ε * (c / 4) * X ^ 2 := by
    have h5 : 4 * ε * S * X * W ≤ 4 * ε * S * X * (2 * η * X) :=
      mul_le_mul_of_nonneg_left hWX (by positivity)
    have h6 : 4 * ε * S * X * (2 * η * X) = ε * X ^ 2 * (8 * S * η) := by ring
    have h7 := mul_le_mul_of_nonneg_left hη (mul_nonneg hε.le (sq_nonneg X))
    nlinarith
  have t3 : ε ^ 2 * S * W ^ 2 ≤ ε * (c / 4) * X ^ 2 := by
    have h5 : W ^ 2 ≤ (2 * η * X) ^ 2 := by gcongr
    have h6 : (2 * η * X) ^ 2 ≤ 4 * X ^ 2 := by
      have : (2 * η * X) ^ 2 = 4 * η ^ 2 * X ^ 2 := by ring
      rw [this]
      have : η ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg X]
    have h7 : ε ^ 2 * S * W ^ 2 ≤ ε ^ 2 * S * (4 * X ^ 2) :=
      mul_le_mul_of_nonneg_left (h5.trans h6) (by positivity)
    have h8 : ε ^ 2 * S * (4 * X ^ 2) = ε * X ^ 2 * (4 * ε * S) := by ring
    have h9 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hε.le (sq_nonneg X))
    nlinarith
  nlinarith

lemma real_ineq_U (ε S a c η X W ρ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 < c)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hη : 4 * S * η ≤ c / 8) (hS : 1 ≤ S)
    (h1 : ε * S * (a ^ 2 + 4) ≤ c / 4)
    (hX : 0 ≤ X) (hW : 0 ≤ W) (hWX : W ≤ η * X + ρ) :
    -(ε * c * X ^ 2) + ε ^ 2 * S * a ^ 2 * X ^ 2 + 4 * ε * S * X * W + ε ^ 2 * S * W ^ 2
      ≤ -(ε * c / 2) * X ^ 2 + ε * (32 * S ^ 2 / c + 2 * S) * ρ ^ 2 := by
  have hS0 : 0 ≤ S := by linarith
  have hεS : 0 ≤ ε * S := by positivity
  have ha2 : ε * S * (a ^ 2 + 2 * η ^ 2) ≤ c / 4 := by
    have : η ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg hεS (by nlinarith : (0:ℝ) ≤ 4 - 2 * η ^ 2)]
  -- Young's inequality: 4 S X ρ ≤ (c/8) X² + (32 S²/c) ρ²
  have young : 4 * S * X * ρ ≤ c / 8 * X ^ 2 + 32 * S ^ 2 / c * ρ ^ 2 := by
    have : 32 * S ^ 2 / c * ρ ^ 2 = (32 * S ^ 2 * ρ ^ 2) / c := by ring
    rw [this]
    have hh : 0 ≤ (c / 8 * X ^ 2 + (32 * S ^ 2 * ρ ^ 2) / c - 4 * S * X * ρ) := by
      have e : c / 8 * X ^ 2 + (32 * S ^ 2 * ρ ^ 2) / c - 4 * S * X * ρ
          = (c / 8) * (X - 16 * S * ρ / c) ^ 2 + 0 := by
        field_simp
        ring
      rw [e]
      positivity
    linarith
  have hW2 : W ^ 2 ≤ 2 * η ^ 2 * X ^ 2 + 2 * ρ ^ 2 := by
    nlinarith [sq_nonneg (η * X - ρ), mul_nonneg hη0 hX]
  have t1 : 4 * ε * S * X * W ≤ 4 * ε * S * η * X ^ 2 + ε * (4 * S * X * ρ) := by
    have : 4 * ε * S * X * W ≤ 4 * ε * S * X * (η * X + ρ) :=
      mul_le_mul_of_nonneg_left hWX (by positivity)
    nlinarith
  have t2 : ε ^ 2 * S * W ^ 2 ≤ ε ^ 2 * S * (2 * η ^ 2 * X ^ 2 + 2 * ρ ^ 2) :=
    mul_le_mul_of_nonneg_left hW2 (by positivity)
  have t3 : ε * (4 * S * X * ρ) ≤ ε * (c / 8 * X ^ 2 + 32 * S ^ 2 / c * ρ ^ 2) :=
    mul_le_mul_of_nonneg_left young hε.le
  have t4 : 4 * ε * S * η * X ^ 2 ≤ ε * (c / 8) * X ^ 2 := by
    have := mul_le_mul_of_nonneg_left hη (mul_nonneg hε.le (sq_nonneg X))
    nlinarith
  have t5 : ε ^ 2 * S * (2 * ρ ^ 2) ≤ ε * (2 * S) * ρ ^ 2 := by
    have : ε ^ 2 * S * (2 * ρ ^ 2) = ε * (2 * S) * ρ ^ 2 * ε := by ring
    rw [this]
    have : 0 ≤ ε * (2 * S) * ρ ^ 2 := by positivity
    nlinarith
  have t6 : ε ^ 2 * S * a ^ 2 * X ^ 2 + ε ^ 2 * S * (2 * η ^ 2 * X ^ 2) ≤ ε * (c / 4) * X ^ 2 := by
    have : ε ^ 2 * S * a ^ 2 * X ^ 2 + ε ^ 2 * S * (2 * η ^ 2 * X ^ 2)
        = ε * X ^ 2 * (ε * S * (a ^ 2 + 2 * η ^ 2)) := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left ha2 (mul_nonneg hε.le (sq_nonneg X))]
  nlinarith

/-- Constants of the local contraction.  For a certificate `(P, c)` of `A` there are
`S ≥ 1`, a contraction rate `κ0`, a tolerance `η` for the nonlinear remainder and a step
threshold `ε0` such that the Euler step `d ↦ d + ε (A d + w)` contracts the quadratic form
`q = x ⬝ P x` by `1 - ε κ0` whenever `‖w‖ ≤ 2 η ‖d‖` (two-point form), and by
`1 - ε κ0` up to an additive `ε C2 ρ²` whenever `‖w‖ ≤ η ‖d‖ + ρ` (anchor form). -/
theorem contraction_constants (A P : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 < c)
    (hPs : Pᵀ = P) (hge : ∀ x : Vec n, x ⬝ᵥ x ≤ x ⬝ᵥ (P *ᵥ x))
    (hdec : ∀ x : Vec n, x ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x) ≤ -c * (x ⬝ᵥ x)) :
    ∃ S κ0 η ε0 C2 : ℝ, 1 ≤ S ∧ 0 < κ0 ∧ 0 < η ∧ η ≤ 1 ∧ 0 < ε0 ∧ ε0 ≤ 1 ∧
      ε0 * κ0 ≤ 1 ∧ 0 < C2 ∧
      (∀ x : Vec n, ‖x‖ ^ 2 ≤ qf P x ∧ qf P x ≤ S * ‖x‖ ^ 2) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ ε0 → ∀ d w : Vec n, ‖w‖ ≤ 2 * η * ‖d‖ →
        qf P (d + ε • (A *ᵥ d + w)) ≤ (1 - ε * κ0) * qf P d) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ ε0 → ∀ (d w : Vec n) (ρ : ℝ), ‖w‖ ≤ η * ‖d‖ + ρ →
        qf P (d + ε • (A *ᵥ d + w)) ≤ (1 - ε * κ0) * qf P d + ε * C2 * ρ ^ 2) ∧
      (∀ u w : Vec n, |u ⬝ᵥ (P *ᵥ w)| ≤ S * ‖u‖ * ‖w‖) := by
  set a := absSum A with ha
  have ha0 : 0 ≤ a := absSum_nonneg A
  set S : ℝ := absSum P + 1 with hSdef
  have hS1 : 1 ≤ S := by have := absSum_nonneg P; linarith
  have hS0 : 0 < S := by linarith
  have hSP : absSum P ≤ S := by linarith
  set κ0 : ℝ := c / (8 * S) with hκ0
  have hκ0pos : 0 < κ0 := by positivity
  set η : ℝ := min 1 (c / (32 * S)) with hηdef
  have hηpos : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηc : η ≤ c / (32 * S) := min_le_right _ _
  have hηS : 4 * S * η ≤ c / 8 := by
    have : 4 * S * η ≤ 4 * S * (c / (32 * S)) := mul_le_mul_of_nonneg_left hηc (by positivity)
    have e : 4 * S * (c / (32 * S)) = c / 8 := by field_simp; ring
    linarith
  have hηS2 : 8 * S * η ≤ c / 4 := by linarith
  set ε0 : ℝ := min (min 1 (1 / (a + 1))) (min (c / (4 * S * (a ^ 2 + 4))) (8 * S / c)) with hε0
  have hε0pos : 0 < ε0 := lt_min (lt_min one_pos (by positivity)) (lt_min (by positivity) (by positivity))
  have hε01 : ε0 ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hε0a : ε0 ≤ 1 / (a + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have hε0c : ε0 ≤ c / (4 * S * (a ^ 2 + 4)) := (min_le_right _ _).trans (min_le_left _ _)
  have hε0k : ε0 ≤ 8 * S / c := (min_le_right _ _).trans (min_le_right _ _)
  have hε0κ : ε0 * κ0 ≤ 1 := by
    have : ε0 * κ0 ≤ 8 * S / c * (c / (8 * S)) :=
      mul_le_mul hε0k le_rfl hκ0pos.le (by positivity)
    have e : 8 * S / c * (c / (8 * S)) = 1 := by field_simp
    linarith
  set C2 : ℝ := 32 * S ^ 2 / c + 2 * S with hC2
  have hC2pos : 0 < C2 := by positivity
  have hnorm : ∀ x : Vec n, ‖x‖ ^ 2 ≤ qf P x ∧ qf P x ≤ S * ‖x‖ ^ 2 := fun x =>
    ⟨(norm_sq_le_dot x).trans (hge x), qf_le_abs P S hSP x⟩
  -- facts about ε
  have hεfacts : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → ε * absSum A ≤ 1 ∧ ε * S * (a ^ 2 + 4) ≤ c / 4 := by
    intro ε hε hεle
    constructor
    · have h1 : ε ≤ 1 / (a + 1) := hεle.trans hε0a
      have h2 : ε * (a + 1) ≤ 1 := by
        have := mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ a + 1)
        have e : 1 / (a + 1) * (a + 1) = 1 := by field_simp
        linarith
      show ε * a ≤ 1
      nlinarith
    · have h1 : ε ≤ c / (4 * S * (a ^ 2 + 4)) := hεle.trans hε0c
      have hp : 0 < 4 * S * (a ^ 2 + 4) := by positivity
      rw [le_div_iff₀ hp] at h1
      nlinarith
  refine ⟨S, κ0, η, ε0, C2, hS1, hκ0pos, hηpos, hη1, hε0pos, hε01, hε0κ, hC2pos, hnorm, ?_, ?_, ?_⟩
  · intro ε hε hεle d w hw
    obtain ⟨hεa, h1⟩ := hεfacts ε hε hεle
    have key := qf_step_le A P hPs c hc.le hdec S hSP ε hε.le hεa d w
    have hv := real_ineq_V ε S a c η ‖d‖ ‖w‖ hε hηpos.le hη1 hηS2 hS1 h1 (norm_nonneg _)
      (norm_nonneg _) hw
    have hq := (hnorm d).2
    -- q' ≤ q - (ε c / 4) X² ≤ (1 - ε κ0) q
    have hXq : (ε * c / 4) * ‖d‖ ^ 2 ≥ ε * κ0 * qf P d := by
      have h2 : qf P d ≤ S * ‖d‖ ^ 2 := hq
      have e : ε * κ0 * S = ε * c / 8 := by rw [hκ0]; field_simp
      have h3 : ε * κ0 * qf P d ≤ ε * κ0 * (S * ‖d‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have : ε * κ0 * (S * ‖d‖ ^ 2) = (ε * c / 8) * ‖d‖ ^ 2 := by rw [← e]; ring
      have h4 := mul_nonneg (mul_nonneg hε.le hc.le) (sq_nonneg ‖d‖)
      linarith
    linarith
  · intro ε hε hεle d w ρ hw
    obtain ⟨hεa, h1⟩ := hεfacts ε hε hεle
    have key := qf_step_le A P hPs c hc.le hdec S hSP ε hε.le hεa d w
    have hv := real_ineq_U ε S a c η ‖d‖ ‖w‖ ρ hε (hεle.trans hε01) hc hηpos.le hη1 hηS hS1 h1
      (norm_nonneg _) (norm_nonneg _) hw
    have hq := (hnorm d).2
    have hXq : (ε * c / 2) * ‖d‖ ^ 2 ≥ ε * κ0 * qf P d := by
      have h2 : qf P d ≤ S * ‖d‖ ^ 2 := hq
      have e : ε * κ0 * S = ε * c / 8 := by rw [hκ0]; field_simp
      have h3 : ε * κ0 * qf P d ≤ ε * κ0 * (S * ‖d‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have : ε * κ0 * (S * ‖d‖ ^ 2) = (ε * c / 8) * ‖d‖ ^ 2 := by rw [← e]; ring
      have h4 := mul_nonneg (mul_nonneg hε.le hc.le) (sq_nonneg ‖d‖)
      linarith
    linarith
  · intro u w
    have := abs_bil_le P u w
    have h2 : absSum P * ‖u‖ * ‖w‖ ≤ S * ‖u‖ * ‖w‖ := by
      gcongr
    exact this.trans h2

lemma strict_ball (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n → Vec n) (ystar : Vec n)
    (hb : HasStrictFDerivAt b (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)) ystar)
    (η : ℝ) (hη : 0 < η) :
    ∃ s : ℝ, 0 < s ∧ ∀ y z : Vec n, ‖y - ystar‖ < s → ‖z - ystar‖ < s →
      ‖b y - b z - A *ᵥ (y - z)‖ ≤ η * ‖y - z‖ := by
  have h := hb.isLittleO.def hη
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨s, hs, hsp⟩ := h
  refine ⟨s, hs, fun y z hy hz => ?_⟩
  have hd : dist (y, z) (ystar, ystar) < s := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨by simpa [dist_eq_norm] using hy, by simpa [dist_eq_norm] using hz⟩
  have := hsp hd
  simpa using this

end Algebra

section Core

variable {n : ℕ} (H : RecursionSetup n)

/-- Data of the local contraction: all the constants and one-step estimates on the
`P`-ball `{y | q (y - ystar) ≤ R²}`. -/
theorem core_data :
    ∃ R κ0 ε0 ρ0 S η C2 : ℝ, 0 < R ∧ R ≤ H.r0 ∧ 0 < κ0 ∧ 0 < ε0 ∧ ε0 ≤ 1 ∧ ε0 * κ0 ≤ 1 ∧
      0 < ρ0 ∧ ρ0 ≤ η ∧ 1 ≤ S ∧ 0 < η ∧ 0 < C2 ∧
      (∀ x : Vec n, ‖x‖ ^ 2 ≤ qf H.P x ∧ qf H.P x ≤ S * ‖x‖ ^ 2) ∧
      (∃ s : ℝ, R < s ∧ ∀ y z : Vec n, ‖y - H.ystar‖ < s → ‖z - H.ystar‖ < s →
        ‖H.b y - H.b z - H.A *ᵥ (y - z)‖ ≤ η * ‖y - z‖) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ ε0 → ∀ d w : Vec n, ‖w‖ ≤ 2 * η * ‖d‖ →
        qf H.P (d + ε • (H.A *ᵥ d + w)) ≤ (1 - ε * κ0) * qf H.P d) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ ε0 → H.ρ ε ≤ ρ0 → ∀ y : Vec n,
        qf H.P (y - H.ystar) ≤ R ^ 2 →
        qf H.P (driftMap H.b H.e ε y - H.ystar) ≤
          (1 - ε * κ0) * qf H.P (y - H.ystar) + ε * C2 * H.ρ ε ^ 2) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ ε0 → H.ρ ε ≤ ρ0 → ∀ y z : Vec n,
        qf H.P (y - H.ystar) ≤ R ^ 2 → qf H.P (z - H.ystar) ≤ R ^ 2 →
        qf H.P (driftMap H.b H.e ε y - driftMap H.b H.e ε z) ≤
          (1 - ε * κ0) * qf H.P (y - z)) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ ε0 → H.ρ ε ≤ ρ0 → ∀ y : Vec n,
        qf H.P (y - H.ystar) ≤ R ^ 2 → qf H.P (driftMap H.b H.e ε y - H.ystar) ≤ R ^ 2) ∧
      (∀ u w : Vec n, |u ⬝ᵥ (H.P *ᵥ w)| ≤ S * ‖u‖ * ‖w‖) := by
  obtain ⟨S, κ0, η, ε0, C2, hS1, hκ0, hη, hη1, hε0, hε01, hε0κ, hC2, hnorm, hV, hU, hbil⟩ :=
    contraction_constants H.A H.P H.c H.hc H.hPs H.hge H.hdec
  obtain ⟨s, hs, hstrict⟩ := strict_ball H.A H.b H.ystar H.hb η hη
  set R : ℝ := min H.r0 (s / 2) with hRdef
  have hR : 0 < R := lt_min H.hr0 (by linarith)
  have hRr : R ≤ H.r0 := min_le_left _ _
  have hRs : R ≤ s / 2 := min_le_right _ _
  set t : ℝ := min 1 (κ0 / C2) with ht
  have htpos : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htk : t ≤ κ0 / C2 := min_le_right _ _
  set ρ0 : ℝ := min η (R * t) with hρ0
  have hρ0pos : 0 < ρ0 := lt_min hη (by positivity)
  have hρ0η : ρ0 ≤ η := min_le_left _ _
  have hρ0R : ρ0 ≤ R * t := min_le_right _ _
  have hsR : ∀ y : Vec n, ‖y - H.ystar‖ ≤ R → ‖y - H.ystar‖ < s := fun y hy => by linarith
  have hqR : ∀ y : Vec n, qf H.P (y - H.ystar) ≤ R ^ 2 → ‖y - H.ystar‖ ≤ R := by
    intro y hy
    have h1 := (hnorm (y - H.ystar)).1
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (y - H.ystar)]
  have hρnn : ∀ ε : ℝ, 0 < ε → 0 ≤ H.ρ ε := fun ε hε =>
    le_trans (norm_nonneg _) (H.he0 ε hε H.ystar (by simpa using H.hr0.le))
  -- strict estimate at the anchor
  have hanchor : ∀ y : Vec n, ‖y - H.ystar‖ ≤ R →
      ‖H.b y - H.A *ᵥ (y - H.ystar)‖ ≤ η * ‖y - H.ystar‖ := by
    intro y hy
    have := hstrict y H.ystar (hsR y hy) (by simpa using hs)
    simpa [H.hb0] using this
  have hstrict' : ∀ y z : Vec n, ‖y - H.ystar‖ ≤ R → ‖z - H.ystar‖ ≤ R →
      ‖H.b y - H.b z - H.A *ᵥ (y - z)‖ ≤ η * ‖y - z‖ := fun y z hy hz =>
    hstrict y z (hsR y hy) (hsR z hz)
  have hUfull : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → ∀ y : Vec n, ‖y - H.ystar‖ ≤ R →
      qf H.P (driftMap H.b H.e ε y - H.ystar) ≤
        (1 - ε * κ0) * qf H.P (y - H.ystar) + ε * C2 * H.ρ ε ^ 2 := by
    intro ε hε hεle y hy
    have hdec : driftMap H.b H.e ε y - H.ystar = (y - H.ystar) + ε •
        (H.A *ᵥ (y - H.ystar) + ((H.b y - H.A *ᵥ (y - H.ystar)) + H.e ε y)) := by
      simp only [driftMap]
      module
    rw [hdec]
    refine hU ε hε hεle _ _ (H.ρ ε) ?_
    calc ‖(H.b y - H.A *ᵥ (y - H.ystar)) + H.e ε y‖
        ≤ ‖H.b y - H.A *ᵥ (y - H.ystar)‖ + ‖H.e ε y‖ := norm_add_le _ _
      _ ≤ η * ‖y - H.ystar‖ + H.ρ ε :=
        add_le_add (hanchor y hy) (H.he0 ε hε y (hy.trans hRr))
  have hVfull : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → H.ρ ε ≤ ρ0 → ∀ y z : Vec n,
      ‖y - H.ystar‖ ≤ R → ‖z - H.ystar‖ ≤ R →
      qf H.P (driftMap H.b H.e ε y - driftMap H.b H.e ε z) ≤
        (1 - ε * κ0) * qf H.P (y - z) := by
    intro ε hε hεle hρ y z hy hz
    have hdec : driftMap H.b H.e ε y - driftMap H.b H.e ε z = (y - z) + ε •
        (H.A *ᵥ (y - z) + ((H.b y - H.b z - H.A *ᵥ (y - z)) + (H.e ε y - H.e ε z))) := by
      simp only [driftMap]
      module
    rw [hdec]
    refine hV ε hε hεle _ _ ?_
    calc ‖(H.b y - H.b z - H.A *ᵥ (y - z)) + (H.e ε y - H.e ε z)‖
        ≤ ‖H.b y - H.b z - H.A *ᵥ (y - z)‖ + ‖H.e ε y - H.e ε z‖ := norm_add_le _ _
      _ ≤ η * ‖y - z‖ + H.ρ ε * ‖y - z‖ :=
        add_le_add (hstrict' y z hy hz) (H.he1 ε hε y z (hy.trans hRr) (hz.trans hRr))
      _ ≤ η * ‖y - z‖ + η * ‖y - z‖ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right (hρ.trans hρ0η) (norm_nonneg _))
      _ = 2 * η * ‖y - z‖ := by ring
  refine ⟨R, κ0, ε0, ρ0, S, η, C2, hR, hRr, hκ0, hε0, hε01, hε0κ, hρ0pos, hρ0η, hS1, hη, hC2,
    hnorm, ⟨s, by linarith, hstrict⟩, hV, ?_, ?_, ?_, hbil⟩
  · intro ε hε hεle hρ y hy
    exact hUfull ε hε hεle y (hqR y hy)
  · intro ε hε hεle hρ y z hy hz
    exact hVfull ε hε hεle hρ y z (hqR y hy) (hqR z hz)
  · intro ε hε hεle hρ y hy
    have h1 := hUfull ε hε hεle y (hqR y hy)
    have hq0 : 0 ≤ qf H.P (y - H.ystar) := (sq_nonneg _).trans (hnorm _).1
    have hρ2 : C2 * H.ρ ε ^ 2 ≤ κ0 * R ^ 2 := by
      have h2 : H.ρ ε ≤ R * t := hρ.trans hρ0R
      have h3 : H.ρ ε ^ 2 ≤ (R * t) ^ 2 := by gcongr; exact hρnn ε hε
      have h4 : (R * t) ^ 2 ≤ R ^ 2 * t := by
        have : (R * t) ^ 2 = R ^ 2 * t * t := by ring
        rw [this]
        nlinarith [mul_nonneg (sq_nonneg R) htpos.le]
      have h5 : C2 * t ≤ κ0 := by
        have := mul_le_mul_of_nonneg_left htk hC2.le
        have e : C2 * (κ0 / C2) = κ0 := by field_simp
        linarith
      calc C2 * H.ρ ε ^ 2 ≤ C2 * (R ^ 2 * t) := mul_le_mul_of_nonneg_left (h3.trans h4) hC2.le
        _ = (C2 * t) * R ^ 2 := by ring
        _ ≤ κ0 * R ^ 2 := mul_le_mul_of_nonneg_right h5 (sq_nonneg R)
    have h6 : ε * C2 * H.ρ ε ^ 2 ≤ ε * (κ0 * R ^ 2) := by
      have := mul_le_mul_of_nonneg_left hρ2 hε.le
      linarith
    have h7 : (1 - ε * κ0) * qf H.P (y - H.ystar) ≤ (1 - ε * κ0) * R ^ 2 :=
      mul_le_mul_of_nonneg_left hy (by nlinarith)
    nlinarith

end Core

section Abstract

variable {n : ℕ}

lemma le_of_sq_le' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hc
  push Not at hc
  nlinarith

lemma continuous_qf_shift (P : Matrix (Fin n) (Fin n) ℝ) (ystar : Vec n) :
    Continuous fun y : Vec n => qf P (y - ystar) := by
  unfold qf
  simp only [dotProduct, mulVec]
  fun_prop

/-- Abstract contraction on a `q`-ball: iterates stay in the ball, contract the quadratic
form, and the orbit of `ystar` converges to the unique fixed point. -/
theorem abstract_fixed_point (P : Matrix (Fin n) (Fin n) ℝ) (S : ℝ) (hS : 1 ≤ S)
    (hnorm : ∀ x : Vec n, ‖x‖ ^ 2 ≤ qf P x ∧ qf P x ≤ S * ‖x‖ ^ 2)
    (Ψ : Vec n → Vec n) (ystar : Vec n) (R θ D : ℝ) (hR : 0 < R) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hmaps : ∀ y : Vec n, qf P (y - ystar) ≤ R ^ 2 → qf P (Ψ y - ystar) ≤ R ^ 2)
    (hV : ∀ y z : Vec n, qf P (y - ystar) ≤ R ^ 2 → qf P (z - ystar) ≤ R ^ 2 →
      qf P (Ψ y - Ψ z) ≤ θ * qf P (y - z))
    (hU : ∀ y : Vec n, qf P (y - ystar) ≤ R ^ 2 →
      qf P (Ψ y - ystar) ≤ θ * qf P (y - ystar) + D) :
    ∃ L : Vec n, qf P (L - ystar) ≤ R ^ 2 ∧ Ψ L = L ∧
      (∀ z : Vec n, qf P (z - ystar) ≤ R ^ 2 → Ψ z = z → z = L) ∧
      (1 - θ) * qf P (L - ystar) ≤ D := by
  set N : Set (Vec n) := {y | qf P (y - ystar) ≤ R ^ 2} with hN
  have hmapsN : Set.MapsTo Ψ N N := fun y hy => hmaps y hy
  have hystar : ystar ∈ N := by
    show qf P (ystar - ystar) ≤ R ^ 2
    simp [qf]; positivity
  have hiterN : ∀ k : ℕ, Set.MapsTo Ψ^[k] N N := fun k => hmapsN.iterate k
  have hq0 : ∀ x : Vec n, 0 ≤ qf P x := fun x => (sq_nonneg _).trans (hnorm x).1
  have hcontr : ∀ k : ℕ, ∀ y z : Vec n, y ∈ N → z ∈ N →
      qf P (Ψ^[k] y - Ψ^[k] z) ≤ θ ^ k * qf P (y - z) := by
    intro k
    induction k with
    | zero => intro y z _ _; simp
    | succ k ih =>
      intro y z hy hz
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ]
      refine (hV _ _ (hiterN k hy) (hiterN k hz)).trans ?_
      have := mul_le_mul_of_nonneg_left (ih y z hy hz) hθ0
      nlinarith
  -- Lipschitz bound
  have hlip : ∀ y z : Vec n, y ∈ N → z ∈ N → ‖Ψ y - Ψ z‖ ≤ S * ‖y - z‖ := by
    intro y z hy hz
    apply le_of_sq_le' (by positivity)
    have h1 := (hnorm (Ψ y - Ψ z)).1
    have h2 := hV y z hy hz
    have h3 := (hnorm (y - z)).2
    have h4 : θ * qf P (y - z) ≤ qf P (y - z) := by nlinarith [hq0 (y - z)]
    have h5 : S * ‖y - z‖ ^ 2 ≤ (S * ‖y - z‖) ^ 2 := by nlinarith [sq_nonneg ‖y - z‖]
    nlinarith
  -- Cauchy sequence
  set x : ℕ → Vec n := fun k => Ψ^[k] ystar with hx
  set r : ℝ := Real.sqrt θ with hr
  have hr1 : r < 1 := by
    rw [hr, Real.sqrt_lt' one_pos]; simpa using hθ1
  have hdist : ∀ k : ℕ, dist (x k) (x (k + 1)) ≤ R * r ^ k := by
    intro k
    rw [dist_eq_norm]
    have h1 : x (k + 1) = Ψ^[k] (Ψ ystar) := by
      simp only [hx]; rw [← Function.iterate_succ_apply]
    have hmem : Ψ ystar ∈ N := hmapsN hystar
    have h2 := hcontr k (Ψ ystar) ystar hmem hystar
    have h3 : qf P (Ψ ystar - ystar) ≤ R ^ 2 := hmaps ystar hystar
    have h4 := (hnorm (x k - x (k + 1))).1
    have h5 : x k - x (k + 1) = -(Ψ^[k] (Ψ ystar) - Ψ^[k] ystar) := by
      rw [h1]; simp [hx]
    rw [h5] at h4 ⊢
    rw [norm_neg]
    rw [norm_neg] at h4
    apply le_of_sq_le' (by positivity)
    have h6 : qf P (-(Ψ^[k] (Ψ ystar) - Ψ^[k] ystar)) = qf P (Ψ^[k] (Ψ ystar) - Ψ^[k] ystar) := by
      simp only [qf, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
    rw [h6] at h4
    have h7 : (R * r ^ k) ^ 2 = R ^ 2 * θ ^ k := by
      rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, hr, Real.sq_sqrt hθ0]
    rw [h7]
    have := mul_le_mul_of_nonneg_left h3 (pow_nonneg hθ0 k)
    nlinarith
  have hcs : CauchySeq x := cauchySeq_of_le_geometric r R hr1 hdist
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  have hxN : ∀ k, x k ∈ N := fun k => hiterN k hystar
  have hclosed : IsClosed N := isClosed_le (continuous_qf_shift P ystar) continuous_const
  have hLN : L ∈ N := hclosed.mem_of_tendsto hL (Eventually.of_forall hxN)
  have hfix : Ψ L = L := by
    have h1 : Tendsto (fun k => x (k + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun k => Ψ (x k)) atTop (𝓝 (Ψ L)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_)
        (by simpa using (tendsto_iff_dist_tendsto_zero.mp hL).const_mul S)
      rw [dist_eq_norm, dist_eq_norm]
      exact hlip _ _ (hxN k) hLN
    have h3 : (fun k => x (k + 1)) = fun k => Ψ (x k) := by
      funext k; simp only [hx]; rw [Function.iterate_succ_apply']
    rw [h3] at h1
    exact tendsto_nhds_unique h2 h1
  refine ⟨L, hLN, hfix, ?_, ?_⟩
  · intro z hz hzf
    have h1 := hV z L hz hLN
    rw [hzf, hfix] at h1
    have h2 : qf P (z - L) = 0 := by nlinarith [hq0 (z - L)]
    have h3 : ‖z - L‖ ^ 2 ≤ 0 := h2 ▸ (hnorm (z - L)).1
    have : ‖z - L‖ = 0 := by nlinarith [norm_nonneg (z - L)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  · have h1 := hU L hLN
    rw [hfix] at h1
    linarith

lemma iterate_qf_contract (P : Matrix (Fin n) (Fin n) ℝ)
    (Ψ : Vec n → Vec n) (ystar : Vec n) (R θ : ℝ)
    (hθ0 : 0 ≤ θ)
    (hmaps : ∀ y : Vec n, qf P (y - ystar) ≤ R ^ 2 → qf P (Ψ y - ystar) ≤ R ^ 2)
    (hV : ∀ y z : Vec n, qf P (y - ystar) ≤ R ^ 2 → qf P (z - ystar) ≤ R ^ 2 →
      qf P (Ψ y - Ψ z) ≤ θ * qf P (y - z)) (k : ℕ) (y z : Vec n)
    (hy : qf P (y - ystar) ≤ R ^ 2) (hz : qf P (z - ystar) ≤ R ^ 2) :
    qf P (Ψ^[k] y - Ψ^[k] z) ≤ θ ^ k * qf P (y - z) ∧ qf P (Ψ^[k] y - ystar) ≤ R ^ 2 := by
  have hmapsN : Set.MapsTo Ψ {y | qf P (y - ystar) ≤ R ^ 2} {y | qf P (y - ystar) ≤ R ^ 2} :=
    fun y hy => hmaps y hy
  have hiterN : ∀ k : ℕ, Set.MapsTo Ψ^[k] {y | qf P (y - ystar) ≤ R ^ 2}
      {y | qf P (y - ystar) ≤ R ^ 2} := fun k => hmapsN.iterate k
  refine ⟨?_, hiterN k hy⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ]
    refine (hV _ _ (hiterN k hy) (hiterN k hz)).trans ?_
    have := mul_le_mul_of_nonneg_left ih hθ0
    nlinarith

/-- Entry step of `cor:recursion`: after the time `T0` of `UniformEntry` the solution is in a
small ball, the recursion tracks it on `[0, T0 + 1]`, hence it is in the `P`-ball `N` at step
`⌈T0/ε⌉` and stays there. -/
theorem entry_abstract (P : Matrix (Fin n) (Fin n) ℝ) (S R ε0 ρ0 rc : ℝ) (hS1 : 1 ≤ S)
    (hR : 0 < R) (hε0 : 0 < ε0) (hρ0 : 0 < ρ0) (hrc : 0 < rc)
    (hup : ∀ x : Vec n, qf P x ≤ S * ‖x‖ ^ 2)
    (b : Vec n → Vec n) (ystar : Vec n) (K : Set (Vec n)) (Ψ : ℝ → Vec n → Vec n)
    (ρ : ℝ → ℝ)
    (hent : UniformEntry b ystar K)
    (htrack : ∀ T : ℝ, 0 ≤ T → ∃ CT εT : ℝ, 0 < CT ∧ 0 < εT ∧ ∀ ε : ℝ, 0 < ε → ε ≤ εT →
      ∀ y0 ∈ K, ∀ y : ℝ → Vec n, IsODESol b y0 y → ∀ k : ℕ, (k : ℝ) * ε ≤ T →
        ‖(Ψ ε)^[k] y0 - y (k * ε)‖ ≤ CT * ρ ε)
    (hinv : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → ρ ε ≤ ρ0 → ∀ y : Vec n, qf P (y - ystar) ≤ R ^ 2 →
      qf P (Ψ ε y - ystar) ≤ R ^ 2) :
    ∃ T0 CT ε1 ρ1 : ℝ, 0 ≤ T0 ∧ 0 < CT ∧ 0 < ε1 ∧ 0 < ρ1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε1 → ρ ε ≤ ρ1 →
        ε ≤ ε0 ∧ ρ ε ≤ ρ0 ∧ ε ≤ 1 ∧ ∀ y0 ∈ K, ∀ y : ℝ → Vec n, IsODESol b y0 y →
          ((⌈T0 / ε⌉₊ : ℕ) : ℝ) * ε ≤ T0 + 1 ∧
          (∀ k : ℕ, ⌈T0 / ε⌉₊ ≤ k → ‖y (k * ε) - ystar‖ ≤ min (R / (2 * S)) rc) ∧
          (∀ k : ℕ, (k : ℝ) * ε ≤ T0 + 1 → ‖(Ψ ε)^[k] y0 - y (k * ε)‖ ≤ CT * ρ ε) ∧
          (∀ k : ℕ, ⌈T0 / ε⌉₊ ≤ k → qf P ((Ψ ε)^[k] y0 - ystar) ≤ R ^ 2) := by
  have hS0 : 0 < S := by linarith
  set r' : ℝ := min (R / (2 * S)) rc with hr'
  have hr'pos : 0 < r' := lt_min (by positivity) hrc
  have hr'1 : r' ≤ R / (2 * S) := min_le_left _ _
  obtain ⟨T0, hT0, hT0prop⟩ := hent r' hr'pos
  obtain ⟨CT, εT, hCT, hεT, htr⟩ := htrack (T0 + 1) (by linarith)
  refine ⟨T0, CT, min (min ε0 εT) 1, min ρ0 (R / (2 * S * CT)), hT0, hCT,
    lt_min (lt_min hε0 hεT) one_pos, lt_min hρ0 (by positivity), ?_⟩
  intro ε hε hεle hρle
  have hεε0 : ε ≤ ε0 := hεle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεεT : ε ≤ εT := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := hεle.trans (min_le_right _ _)
  have hρρ0 : ρ ε ≤ ρ0 := hρle.trans (min_le_left _ _)
  have hρρ1 : ρ ε ≤ R / (2 * S * CT) := hρle.trans (min_le_right _ _)
  refine ⟨hεε0, hρρ0, hε1, fun y0 hy0 y hy => ?_⟩
  set k0 : ℕ := ⌈T0 / ε⌉₊ with hk0
  have hk0le : (k0 : ℝ) * ε ≤ T0 + 1 := by
    have h1 : (k0 : ℝ) < T0 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (k0 : ℝ) * ε < (T0 / ε + 1) * ε := mul_lt_mul_of_pos_right h1 hε
    have h3 : (T0 / ε + 1) * ε = T0 + ε := by field_simp
    linarith
  have hk0ge : T0 ≤ (k0 : ℝ) * ε := by
    have h1 : T0 / ε ≤ (k0 : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hε] at h1
    exact h1
  have hball : ∀ k : ℕ, k0 ≤ k → ‖y (k * ε) - ystar‖ ≤ r' := by
    intro k hk
    apply hT0prop y0 hy0 y hy
    have : (k0 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have htk : ∀ k : ℕ, (k : ℝ) * ε ≤ T0 + 1 → ‖(Ψ ε)^[k] y0 - y (k * ε)‖ ≤ CT * ρ ε :=
    fun k hk => htr ε hε hεεT y0 hy0 y hy k hk
  have hN0 : qf P ((Ψ ε)^[k0] y0 - ystar) ≤ R ^ 2 := by
    have h1 := htk k0 hk0le
    have h2 := hball k0 le_rfl
    have h3 : CT * ρ ε ≤ R / (2 * S) := by
      have := mul_le_mul_of_nonneg_left hρρ1 hCT.le
      have e : CT * (R / (2 * S * CT)) = R / (2 * S) := by field_simp
      linarith
    have h4 : ‖(Ψ ε)^[k0] y0 - ystar‖ ≤ R / S := by
      calc ‖(Ψ ε)^[k0] y0 - ystar‖
          = ‖((Ψ ε)^[k0] y0 - y (k0 * ε)) + (y (k0 * ε) - ystar)‖ := by congr 1; abel
        _ ≤ ‖(Ψ ε)^[k0] y0 - y (k0 * ε)‖ + ‖y (k0 * ε) - ystar‖ := norm_add_le _ _
        _ ≤ R / (2 * S) + R / (2 * S) := add_le_add (h1.trans h3) (h2.trans hr'1)
        _ = R / S := by field_simp; ring
    have h5 : ‖(Ψ ε)^[k0] y0 - ystar‖ ^ 2 ≤ (R / S) ^ 2 := by gcongr
    have h6 : S * (R / S) ^ 2 = R ^ 2 / S := by field_simp
    have h7 : R ^ 2 / S ≤ R ^ 2 := div_le_self (sq_nonneg R) hS1
    have h8 := hup ((Ψ ε)^[k0] y0 - ystar)
    nlinarith
  refine ⟨hk0le, hball, htk, fun k hk => ?_⟩
  have hmapsN : Set.MapsTo (Ψ ε) {y | qf P (y - ystar) ≤ R ^ 2} {y | qf P (y - ystar) ≤ R ^ 2} :=
    fun y hy => hinv ε hε hεε0 hρρ0 y hy
  have := (hmapsN.iterate (k - k0)) hN0
  have e : (Ψ ε)^[k - k0] ((Ψ ε)^[k0] y0) = (Ψ ε)^[k] y0 := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hk]
  rw [e] at this
  exact this

/-- Perturbation of the quadratic form (Young's inequality, no triangle inequality for the
`P`-norm needed). -/
lemma perturbed_step (P : Matrix (Fin n) (Fin n) ℝ) (hPs : Pᵀ = P) (S : ℝ)
    (hbil : ∀ u w : Vec n, |u ⬝ᵥ (P *ᵥ w)| ≤ S * ‖u‖ * ‖w‖)
    (hnorm : ∀ x : Vec n, ‖x‖ ^ 2 ≤ qf P x ∧ qf P x ≤ S * ‖x‖ ^ 2)
    (u v : Vec n) (t : ℝ) (ht : 0 < t) :
    qf P (u + v) ≤ (1 + t) * qf P u + (S ^ 2 / t + S) * ‖v‖ ^ 2 := by
  have h1 : u ⬝ᵥ (P *ᵥ v) ≤ S * ‖u‖ * ‖v‖ := (le_abs_self _).trans (hbil u v)
  have h2 : 2 * (S * ‖u‖ * ‖v‖) ≤ t * ‖u‖ ^ 2 + S ^ 2 / t * ‖v‖ ^ 2 := by
    have : 0 ≤ (t * ‖u‖ - S * ‖v‖) ^ 2 / t := by positivity
    have e : (t * ‖u‖ - S * ‖v‖) ^ 2 / t
        = t * ‖u‖ ^ 2 + S ^ 2 / t * ‖v‖ ^ 2 - 2 * (S * ‖u‖ * ‖v‖) := by
      field_simp; ring
    linarith
  have h3 : t * ‖u‖ ^ 2 ≤ t * qf P u := mul_le_mul_of_nonneg_left (hnorm u).1 ht.le
  have h4 := (hnorm v).2
  rw [qf_add P hPs]
  nlinarith

/-- Discrete comparison: a recursion `q_{k+1} ≤ (1 - t) q_k + t B` keeps `q_k ≤ q_{k0} + B`. -/
lemma bounded_recursion (q : ℕ → ℝ) (t B : ℝ) (k0 : ℕ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hB : 0 ≤ B)
    (hq0 : 0 ≤ q k0) (hstep : ∀ k, k0 ≤ k → q (k + 1) ≤ (1 - t) * q k + t * B) :
    ∀ k, k0 ≤ k → q k ≤ q k0 + B := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => linarith
  | succ k hk ih =>
    have := hstep k hk
    nlinarith

lemma mem_of_norm_le (P : Matrix (Fin n) (Fin n) ℝ) (S R : ℝ) (hS : 1 ≤ S) (hR : 0 < R)
    (hup : ∀ x : Vec n, qf P x ≤ S * ‖x‖ ^ 2) (d : Vec n) (hd : ‖d‖ ≤ R / S) :
    qf P d ≤ R ^ 2 := by
  have h2 : ‖d‖ ^ 2 ≤ (R / S) ^ 2 := by gcongr
  have h3 : S * (R / S) ^ 2 = R ^ 2 / S := by field_simp
  have h4 : R ^ 2 / S ≤ R ^ 2 := div_le_self (sq_nonneg R) hS
  have h8 := hup d
  nlinarith

/-- Post-entry comparison of two sequences, one following `F` and one an `O(ε r)`-consistent
approximate orbit: the quadratic form of the gap stays below its initial value plus `B r²`. -/
lemma post_entry_bound (P : Matrix (Fin n) (Fin n) ℝ) (hPs : Pᵀ = P) (S κ0 ε C1 r : ℝ)
    (hbil : ∀ u w : Vec n, |u ⬝ᵥ (P *ᵥ w)| ≤ S * ‖u‖ * ‖w‖)
    (hnorm : ∀ x : Vec n, ‖x‖ ^ 2 ≤ qf P x ∧ qf P x ≤ S * ‖x‖ ^ 2)
    (hS0 : 0 < S) (hκ0 : 0 < κ0) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεκ : ε * κ0 ≤ 1)
    (x z : ℕ → Vec n) (F : Vec n → Vec n) (k0 : ℕ)
    (hxs : ∀ k, x (k + 1) = F (x k))
    (hVk : ∀ k, k0 ≤ k → qf P (F (x k) - F (z k)) ≤ (1 - ε * κ0) * qf P (x k - z k))
    (hcs : ∀ k, k0 ≤ k → ‖z (k + 1) - F (z k)‖ ≤ C1 * ε * r) :
    ∀ k, k0 ≤ k → qf P (x k - z k) ≤ qf P (x k0 - z k0) +
      (4 * S ^ 2 * C1 ^ 2 / κ0 ^ 2 + 2 * S * C1 ^ 2 / κ0) * r ^ 2 := by
  have hq0 : ∀ x : Vec n, 0 ≤ qf P x := fun x => (sq_nonneg _).trans (hnorm x).1
  set B : ℝ := 4 * S ^ 2 * C1 ^ 2 / κ0 ^ 2 + 2 * S * C1 ^ 2 / κ0 with hB
  have hB0 : 0 ≤ B := by positivity
  set t : ℝ := ε * κ0 / 2 with ht
  have htpos : 0 < t := by positivity
  have ht1 : t ≤ 1 := by nlinarith
  have hstep : ∀ k, k0 ≤ k →
      qf P (x (k + 1) - z (k + 1)) ≤ (1 - t) * qf P (x k - z k) + t * (B * r ^ 2) := by
    intro k hk
    set u : Vec n := F (x k) - F (z k) with hu
    set v : Vec n := F (z k) - z (k + 1) with hv
    have hsplit : x (k + 1) - z (k + 1) = u + v := by
      rw [hxs, hu, hv]; abel
    have hvn : ‖v‖ ≤ C1 * ε * r := by
      rw [hv, norm_sub_rev]; exact hcs k hk
    have hquv := perturbed_step P hPs S hbil hnorm u v t htpos
    have hqu := hVk k hk
    have hqk0 : 0 ≤ qf P (x k - z k) := hq0 _
    have hv2 : ‖v‖ ^ 2 ≤ (C1 * ε * r) ^ 2 := by gcongr
    have hA : (1 + t) * qf P u ≤ (1 - t) * qf P (x k - z k) := by
      have h1 : (1 + t) * qf P u ≤ (1 + t) * ((1 - ε * κ0) * qf P (x k - z k)) :=
        mul_le_mul_of_nonneg_left hqu (by linarith)
      have h2 : (1 + t) * ((1 - ε * κ0) * qf P (x k - z k)) ≤ (1 - t) * qf P (x k - z k) := by
        have : (1 + t) * (1 - ε * κ0) = 1 - t - 2 * t ^ 2 := by rw [ht]; ring
        nlinarith [mul_nonneg (sq_nonneg t) hqk0]
      linarith
    have hBd : (S ^ 2 / t + S) * ‖v‖ ^ 2 ≤ t * (B * r ^ 2) := by
      have h1 : (S ^ 2 / t + S) * ‖v‖ ^ 2 ≤ (S ^ 2 / t + S) * (C1 * ε * r) ^ 2 :=
        mul_le_mul_of_nonneg_left hv2 (by positivity)
      have h2 : (S ^ 2 / t + S) * (C1 * ε * r) ^ 2 =
          2 * S ^ 2 * C1 ^ 2 * ε * r ^ 2 / κ0 + S * C1 ^ 2 * ε ^ 2 * r ^ 2 := by
        rw [ht]; field_simp
      have h3 : t * (B * r ^ 2) =
          2 * S ^ 2 * C1 ^ 2 * ε * r ^ 2 / κ0 + S * C1 ^ 2 * ε * r ^ 2 := by
        rw [ht, hB]; field_simp; ring
      have h4 : S * C1 ^ 2 * ε ^ 2 * r ^ 2 ≤ S * C1 ^ 2 * ε * r ^ 2 := by
        have : 0 ≤ S * C1 ^ 2 * r ^ 2 := by positivity
        nlinarith [mul_nonneg this (mul_nonneg hε.le (sub_nonneg.2 hε1))]
      linarith
    rw [hsplit]
    linarith
  intro k hk
  have := bounded_recursion (fun k => qf P (x k - z k)) t (B * r ^ 2) k0 htpos.le ht1
    (by positivity) (hq0 _) hstep k hk
  simpa [hB] using this

lemma lt_ceil_mul_le (T0 ε : ℝ) (k : ℕ) (hε : 0 < ε) (hk : k < ⌈T0 / ε⌉₊)
    (h : ((⌈T0 / ε⌉₊ : ℕ) : ℝ) * ε ≤ T0 + 1) : (k : ℝ) * ε ≤ T0 + 1 := by
  have h1 : (k : ℝ) ≤ ((⌈T0 / ε⌉₊ : ℕ) : ℝ) := by exact_mod_cast hk.le
  have h2 := mul_le_mul_of_nonneg_right h1 hε.le
  linarith only [h2, h]

/-- Real-variable bound turning a geometric decay after step `k0` into an exponential bound. -/
lemma after_entry_real (S R κ0 ε T0 X : ℝ) (k k0 : ℕ) (hS : 1 ≤ S) (hR : 0 < R) (hκ0 : 0 < κ0)
    (hεκ : ε * κ0 ≤ 1) (hk : k0 ≤ k)
    (hXsq : X ^ 2 ≤ S * (2 * R) ^ 2 * (1 - ε * κ0) ^ (k - k0))
    (hk0 : (k0 : ℝ) * ε ≤ T0 + 1) :
    X ≤ (2 * S * R * Real.exp (κ0 * (T0 + 1) / 2)) * Real.exp (-(κ0 / 2 * ε * k)) := by
  have hθ0 : 0 ≤ 1 - ε * κ0 := by linarith
  have h1 : 1 - ε * κ0 ≤ Real.exp (-(ε * κ0)) := by
    have := Real.add_one_le_exp (-(ε * κ0)); linarith
  have h2 : (1 - ε * κ0) ^ (k - k0) ≤ Real.exp (-(ε * κ0) * ((k - k0 : ℕ) : ℝ)) := by
    rw [show -(ε * κ0) * ((k - k0 : ℕ) : ℝ) = ((k - k0 : ℕ) : ℝ) * (-(ε * κ0)) from mul_comm _ _,
      Real.exp_nat_mul]
    exact pow_le_pow_left₀ hθ0 h1 _
  have hkk : ((k - k0 : ℕ) : ℝ) = (k : ℝ) - k0 := by
    rw [Nat.cast_sub hk]
  rw [hkk] at h2
  have h3 : Real.exp (-(ε * κ0) * ((k : ℝ) - k0)) =
      Real.exp (-(ε * κ0 * k)) * Real.exp (ε * κ0 * k0) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (ε * κ0 * k0) ≤ Real.exp (κ0 * (T0 + 1)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hE : 0 ≤ Real.exp (-(ε * κ0 * k)) := (Real.exp_pos _).le
  have hS0 : 0 < S := by linarith
  apply le_of_sq_le' (by positivity)
  have e1 : ((2 * S * R * Real.exp (κ0 * (T0 + 1) / 2)) * Real.exp (-(κ0 / 2 * ε * k))) ^ 2 =
      4 * S ^ 2 * R ^ 2 * Real.exp (κ0 * (T0 + 1)) * Real.exp (-(ε * κ0 * k)) := by
    have a1 : Real.exp (κ0 * (T0 + 1) / 2) ^ 2 = Real.exp (κ0 * (T0 + 1)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have a2 : Real.exp (-(κ0 / 2 * ε * k)) ^ 2 = Real.exp (-(ε * κ0 * k)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    calc _ = 4 * S ^ 2 * R ^ 2 * (Real.exp (κ0 * (T0 + 1) / 2) ^ 2) *
          (Real.exp (-(κ0 / 2 * ε * k)) ^ 2) := by ring
      _ = _ := by rw [a1, a2]
  rw [e1]
  have h5 : S * (2 * R) ^ 2 * (1 - ε * κ0) ^ (k - k0) ≤
      S * (2 * R) ^ 2 * (Real.exp (-(ε * κ0 * k)) * Real.exp (κ0 * (T0 + 1))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [h3] at h2
    calc (1 - ε * κ0) ^ (k - k0) ≤ Real.exp (-(ε * κ0 * k)) * Real.exp (ε * κ0 * k0) := h2
      _ ≤ Real.exp (-(ε * κ0 * k)) * Real.exp (κ0 * (T0 + 1)) :=
          mul_le_mul_of_nonneg_left h4 hE
  refine hXsq.trans (h5.trans ?_)
  have hpos : 0 ≤ Real.exp (-(ε * κ0 * k)) * Real.exp (κ0 * (T0 + 1)) := by positivity
  nlinarith [mul_nonneg hpos (sq_nonneg R), mul_nonneg (mul_nonneg hpos (sq_nonneg R)) (by linarith : (0:ℝ) ≤ S - 1), mul_nonneg hS0.le hS0.le]

/-- The fixed point of the drift map in the `P`-ball, with its distance to `ystar`. -/
theorem fixed_point_pkg {n : ℕ} (H : RecursionSetup n) (R κ0 ε0 ρ0 S C2 : ℝ) (hR : 0 < R)
    (hκ0 : 0 < κ0) (hC2 : 0 < C2) (hS1 : 1 ≤ S) (hε0κ : ε0 * κ0 ≤ 1)
    (hnorm : ∀ x : Vec n, ‖x‖ ^ 2 ≤ qf H.P x ∧ qf H.P x ≤ S * ‖x‖ ^ 2)
    (hU : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → H.ρ ε ≤ ρ0 → ∀ y : Vec n,
        qf H.P (y - H.ystar) ≤ R ^ 2 →
        qf H.P (driftMap H.b H.e ε y - H.ystar) ≤
          (1 - ε * κ0) * qf H.P (y - H.ystar) + ε * C2 * H.ρ ε ^ 2)
    (hV : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → H.ρ ε ≤ ρ0 → ∀ y z : Vec n,
        qf H.P (y - H.ystar) ≤ R ^ 2 → qf H.P (z - H.ystar) ≤ R ^ 2 →
        qf H.P (driftMap H.b H.e ε y - driftMap H.b H.e ε z) ≤
          (1 - ε * κ0) * qf H.P (y - z))
    (hinv : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → H.ρ ε ≤ ρ0 → ∀ y : Vec n,
        qf H.P (y - H.ystar) ≤ R ^ 2 → qf H.P (driftMap H.b H.e ε y - H.ystar) ≤ R ^ 2)
    (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ ε0) (hρ : H.ρ ε ≤ ρ0) :
    ∃ L : Vec n, qf H.P (L - H.ystar) ≤ R ^ 2 ∧ driftMap H.b H.e ε L = L ∧
      (∀ z : Vec n, qf H.P (z - H.ystar) ≤ R ^ 2 → driftMap H.b H.e ε z = z → z = L) ∧
      ‖L - H.ystar‖ ≤ Real.sqrt (C2 / κ0) * H.ρ ε := by
  have hρnn : 0 ≤ H.ρ ε :=
    le_trans (norm_nonneg _) (H.he0 ε hε H.ystar (by simpa using H.hr0.le))
  have hεκ : ε * κ0 ≤ 1 := (mul_le_mul_of_nonneg_right hεle hκ0.le).trans hε0κ
  have hθ0 : 0 ≤ 1 - ε * κ0 := by linarith
  have hθ1 : 1 - ε * κ0 < 1 := by have := mul_pos hε hκ0; linarith
  obtain ⟨L, hLN, hLfix, hLuniq, hLbd⟩ := abstract_fixed_point H.P S hS1 hnorm
    (driftMap H.b H.e ε) H.ystar R (1 - ε * κ0) (ε * C2 * H.ρ ε ^ 2) hR hθ0 hθ1
    (fun y hy => hinv ε hε hεle hρ y hy) (fun y z hy hz => hV ε hε hεle hρ y z hy hz)
    (fun y hy => hU ε hε hεle hρ y hy)
  refine ⟨L, hLN, hLfix, hLuniq, ?_⟩
  have hCf0 : 0 ≤ Real.sqrt (C2 / κ0) := Real.sqrt_nonneg _
  have hCf2 : Real.sqrt (C2 / κ0) ^ 2 = C2 / κ0 := Real.sq_sqrt (by positivity)
  have h1 : ε * κ0 * qf H.P (L - H.ystar) ≤ ε * C2 * H.ρ ε ^ 2 := by
    have : 1 - (1 - ε * κ0) = ε * κ0 := by ring
    rw [this] at hLbd; exact hLbd
  have h2 : κ0 * qf H.P (L - H.ystar) ≤ C2 * H.ρ ε ^ 2 := by
    have : ε * (κ0 * qf H.P (L - H.ystar)) ≤ ε * (C2 * H.ρ ε ^ 2) := by linarith
    exact le_of_mul_le_mul_left this hε
  have h3 : qf H.P (L - H.ystar) ≤ Real.sqrt (C2 / κ0) ^ 2 * H.ρ ε ^ 2 := by
    rw [hCf2, div_mul_eq_mul_div, le_div_iff₀ hκ0]
    linarith
  apply le_of_sq_le' (mul_nonneg hCf0 hρnn)
  calc ‖L - H.ystar‖ ^ 2 ≤ qf H.P (L - H.ystar) := (hnorm _).1
    _ ≤ Real.sqrt (C2 / κ0) ^ 2 * H.ρ ε ^ 2 := h3
    _ = (Real.sqrt (C2 / κ0) * H.ρ ε) ^ 2 := by ring

lemma ball_props {n : ℕ} (H : RecursionSetup n) (R S : ℝ) (hR : 0 < R) (hRr : R ≤ H.r0)
    (hS1 : 1 ≤ S) (hnorm : ∀ x : Vec n, ‖x‖ ^ 2 ≤ qf H.P x ∧ qf H.P x ≤ S * ‖x‖ ^ 2) :
    (∃ s : ℝ, 0 < s ∧ closedBall H.ystar s ⊆ {y | qf H.P (y - H.ystar) ≤ R ^ 2}) ∧
      {y | qf H.P (y - H.ystar) ≤ R ^ 2} ⊆ closedBall H.ystar H.r0 := by
  have hS0 : 0 < S := by linarith
  refine ⟨⟨R / S, by positivity, fun y hy => ?_⟩, fun y hy => ?_⟩
  · have hy' : ‖y - H.ystar‖ ≤ R / S := by simpa [dist_eq_norm] using hy
    exact mem_of_norm_le H.P S R hS1 hR (fun x => (hnorm x).2) _ hy'
  · have : ‖y - H.ystar‖ ≤ R := by
      apply le_of_sq_le' hR.le
      exact (hnorm _).1.trans hy
    simpa [dist_eq_norm] using this.trans hRr

end Abstract

end RecursionContraction

open RecursionContraction

/-- v2 `cor:recursion` ("Fixed point").  Under the setting `H` there are a `P`-ball `N` around
`ystar` (containing a sup-ball and contained in `closedBall ystar r0`) and constants such that
for `0 < ε ≤ ε0` and `ρ ε ≤ ρ0` the map `Ψ_ε` sends `N` into itself, has a unique fixed point
`y_ε ∈ N` with `‖y_ε - ystar‖ ≤ C ρ ε`, and contracts `N` to it at the rate `(1 - κ ε)` per
step. -/
theorem local_fixed_point {n : ℕ} (H : RecursionSetup n) :
    ∃ ε0 ρ0 C κ : ℝ, 0 < ε0 ∧ 0 < ρ0 ∧ 0 < C ∧ 0 < κ ∧
      ∃ N : Set (Fin n → ℝ),
        (∃ s : ℝ, 0 < s ∧ closedBall H.ystar s ⊆ N) ∧ N ⊆ closedBall H.ystar H.r0 ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → H.ρ ε ≤ ρ0 →
          Set.MapsTo (driftMap H.b H.e ε) N N ∧
          ∃ yε ∈ N, driftMap H.b H.e ε yε = yε ∧
            (∀ z ∈ N, driftMap H.b H.e ε z = z → z = yε) ∧
            ‖yε - H.ystar‖ ≤ C * H.ρ ε ∧
            ∀ y ∈ N, ∀ k : ℕ,
              ‖(driftMap H.b H.e ε)^[k] y - yε‖ ≤ C * (1 - κ * ε) ^ k * ‖y - yε‖ := by
  classical
  obtain ⟨R, κ0, ε0, ρ0, S, η, C2, hR, hRr, hκ0, hε0, hε01, hε0κ, hρ0, hρ0η, hS1, hη, hC2,
    hnorm, -, -, hU, hV, hinv, -⟩ := RecursionContraction.core_data H
  set Cf : ℝ := Real.sqrt (C2 / κ0) with hCf
  have hCf0 : 0 ≤ Cf := Real.sqrt_nonneg _
  have hCf2 : Cf ^ 2 = C2 / κ0 := Real.sq_sqrt (by positivity)
  refine ⟨ε0, ρ0, S + Cf, κ0 / 2, hε0, hρ0, by linarith, by positivity, ?_⟩
  set N : Set (Fin n → ℝ) := {y | qf H.P (y - H.ystar) ≤ R ^ 2} with hN
  have hqR : ∀ y : Fin n → ℝ, y ∈ N → ‖y - H.ystar‖ ≤ R := by
    intro y hy
    apply le_of_sq_le' hR.le
    exact (hnorm _).1.trans hy
  refine ⟨N, ⟨R / S, by positivity, fun y hy => ?_⟩, fun y hy => ?_, ?_⟩
  · have hy' : ‖y - H.ystar‖ ≤ R / S := by simpa [dist_eq_norm] using hy
    show qf H.P (y - H.ystar) ≤ R ^ 2
    have h1 := (hnorm (y - H.ystar)).2
    have h2 : ‖y - H.ystar‖ ^ 2 ≤ (R / S) ^ 2 := by gcongr
    have h3 : S * (R / S) ^ 2 = R ^ 2 / S := by field_simp
    have h4 : R ^ 2 / S ≤ R ^ 2 := div_le_self (sq_nonneg R) hS1
    nlinarith
  · simpa [dist_eq_norm] using (hqR y hy).trans hRr
  · intro ε hε hεle hρ
    have hρnn : 0 ≤ H.ρ ε :=
      le_trans (norm_nonneg _) (H.he0 ε hε H.ystar (by simpa using H.hr0.le))
    have hεκ : ε * κ0 ≤ 1 := (mul_le_mul_of_nonneg_right hεle hκ0.le).trans hε0κ
    have hθ0 : 0 ≤ 1 - ε * κ0 := by linarith
    have hθ1 : 1 - ε * κ0 < 1 := by have := mul_pos hε hκ0; linarith
    have hmaps : Set.MapsTo (driftMap H.b H.e ε) N N := fun y hy => hinv ε hε hεle hρ y hy
    refine ⟨hmaps, ?_⟩
    obtain ⟨L, hLN, hLfix, hLuniq, hLbd⟩ := abstract_fixed_point H.P S hS1 hnorm
      (driftMap H.b H.e ε) H.ystar R (1 - ε * κ0) (ε * C2 * H.ρ ε ^ 2) hR hθ0 hθ1
      (fun y hy => hinv ε hε hεle hρ y hy) (fun y z hy hz => hV ε hε hεle hρ y z hy hz)
      (fun y hy => hU ε hε hεle hρ y hy)
    refine ⟨L, hLN, hLfix, fun z hz hzf => hLuniq z hz hzf, ?_, ?_⟩
    · -- distance of the fixed point
      have h1 : ε * κ0 * qf H.P (L - H.ystar) ≤ ε * C2 * H.ρ ε ^ 2 := by
        have : 1 - (1 - ε * κ0) = ε * κ0 := by ring
        rw [this] at hLbd; exact hLbd
      have h2 : κ0 * qf H.P (L - H.ystar) ≤ C2 * H.ρ ε ^ 2 := by
        have : ε * (κ0 * qf H.P (L - H.ystar)) ≤ ε * (C2 * H.ρ ε ^ 2) := by linarith
        exact le_of_mul_le_mul_left this hε
      have h3 : qf H.P (L - H.ystar) ≤ Cf ^ 2 * H.ρ ε ^ 2 := by
        rw [hCf2, div_mul_eq_mul_div, le_div_iff₀ hκ0]
        linarith
      have h4 : ‖L - H.ystar‖ ≤ Cf * H.ρ ε := by
        apply le_of_sq_le' (mul_nonneg hCf0 hρnn)
        calc ‖L - H.ystar‖ ^ 2 ≤ qf H.P (L - H.ystar) := (hnorm _).1
          _ ≤ Cf ^ 2 * H.ρ ε ^ 2 := h3
          _ = (Cf * H.ρ ε) ^ 2 := by ring
      calc ‖L - H.ystar‖ ≤ Cf * H.ρ ε := h4
        _ ≤ (S + Cf) * H.ρ ε := by nlinarith
    · intro y hy k
      have hq0 : ∀ x : Fin n → ℝ, 0 ≤ qf H.P x := fun x => (sq_nonneg _).trans (hnorm x).1
      obtain ⟨hc1, -⟩ := iterate_qf_contract H.P (driftMap H.b H.e ε) H.ystar R
        (1 - ε * κ0) hθ0 (fun y hy => hinv ε hε hεle hρ y hy)
        (fun y z hy hz => hV ε hε hεle hρ y z hy hz) k y L hy hLN
      have hLk : (driftMap H.b H.e ε)^[k] L = L := (Function.IsFixedPt.iterate hLfix k).eq
      rw [hLk] at hc1
      have hκε : κ0 / 2 * ε ≤ 1 / 2 := by nlinarith
      have hb0 : 0 ≤ 1 - κ0 / 2 * ε := by linarith
      have hθle : 1 - ε * κ0 ≤ (1 - κ0 / 2 * ε) ^ 2 := by nlinarith [sq_nonneg (κ0 / 2 * ε)]
      have hpow : (1 - ε * κ0) ^ k ≤ ((1 - κ0 / 2 * ε) ^ k) ^ 2 := by
        calc (1 - ε * κ0) ^ k ≤ ((1 - κ0 / 2 * ε) ^ 2) ^ k := pow_le_pow_left₀ hθ0 hθle k
          _ = ((1 - κ0 / 2 * ε) ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      have hbk : 0 ≤ (1 - κ0 / 2 * ε) ^ k := pow_nonneg hb0 k
      have hnk := (hnorm ((driftMap H.b H.e ε)^[k] y - L)).1
      have hyL := (hnorm (y - L)).2
      have hmain : ‖(driftMap H.b H.e ε)^[k] y - L‖ ^ 2 ≤
          (S * (1 - κ0 / 2 * ε) ^ k * ‖y - L‖) ^ 2 := by
        have h1 : (1 - ε * κ0) ^ k * qf H.P (y - L) ≤
            ((1 - κ0 / 2 * ε) ^ k) ^ 2 * (S * ‖y - L‖ ^ 2) := by
          apply mul_le_mul hpow hyL (hq0 _) (by positivity)
        have h2 : ((1 - κ0 / 2 * ε) ^ k) ^ 2 * (S * ‖y - L‖ ^ 2) ≤
            (S * (1 - κ0 / 2 * ε) ^ k * ‖y - L‖) ^ 2 := by
          have : (S * (1 - κ0 / 2 * ε) ^ k * ‖y - L‖) ^ 2 =
              ((1 - κ0 / 2 * ε) ^ k) ^ 2 * (S ^ 2 * ‖y - L‖ ^ 2) := by ring
          rw [this]
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ S) (by linarith : (0:ℝ) ≤ S - 1)) (sq_nonneg ‖y - L‖)]
        linarith
      have := le_of_sq_le' (by positivity) hmain
      calc _ ≤ S * (1 - κ0 / 2 * ε) ^ k * ‖y - L‖ := this
        _ ≤ (S + Cf) * (1 - κ0 / 2 * ε) ^ k * ‖y - L‖ := by
          have : 0 ≤ (1 - κ0 / 2 * ε) ^ k * ‖y - L‖ := mul_nonneg hbk (norm_nonneg _)
          nlinarith




namespace RecursionContraction

section Jac

variable {n : ℕ}

lemma jacProd_add (Ψ : Vec n → Vec n) (x : Vec n) (a b : ℕ) :
    jacProd Ψ x (a + b) = (jacProd Ψ (Ψ^[a] x) b).comp (jacProd Ψ x a) := by
  induction b with
  | zero => ext v; simp [jacProd]
  | succ b ih =>
    show (fderiv ℝ Ψ (Ψ^[a + b] x)).comp (jacProd Ψ x (a + b)) =
      ((fderiv ℝ Ψ (Ψ^[b] (Ψ^[a] x))).comp (jacProd Ψ (Ψ^[a] x) b)).comp (jacProd Ψ x a)
    rw [ih, ← Function.iterate_add_apply, Nat.add_comm b a, ContinuousLinearMap.comp_assoc]

lemma jacProd_early (Ψ : Vec n → Vec n) (x : Vec n) (B : ℝ) (a : ℕ)
    (h : ∀ t < a, ‖fderiv ℝ Ψ (Ψ^[t] x)‖ ≤ B) : ‖jacProd Ψ x a‖ ≤ B ^ a := by
  induction a with
  | zero => simpa [jacProd] using ContinuousLinearMap.norm_id_le
  | succ a ih =>
    have h1 := ih (fun t ht => h t (Nat.lt_succ_of_lt ht))
    have h2 := h a (Nat.lt_succ_self a)
    calc ‖jacProd Ψ x (a + 1)‖ = ‖(fderiv ℝ Ψ (Ψ^[a] x)).comp (jacProd Ψ x a)‖ := rfl
      _ ≤ ‖fderiv ℝ Ψ (Ψ^[a] x)‖ * ‖jacProd Ψ x a‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ B * B ^ a := mul_le_mul h2 h1 (norm_nonneg _) ((norm_nonneg _).trans h2)
      _ = B ^ (a + 1) := by ring

lemma jacProd_late (P : Matrix (Fin n) (Fin n) ℝ) (Ψ : Vec n → Vec n) (x : Vec n) (θ : ℝ)
    (hθ : 0 ≤ θ) (Nset : Set (Vec n)) (hmem : ∀ t, Ψ^[t] x ∈ Nset)
    (hstep : ∀ z ∈ Nset, ∀ v, qf P (fderiv ℝ Ψ z v) ≤ θ * qf P v) :
    ∀ b : ℕ, ∀ v, qf P (jacProd Ψ x b v) ≤ θ ^ b * qf P v := by
  intro b
  induction b with
  | zero => intro v; simp [jacProd]
  | succ b ih =>
    intro v
    have e : jacProd Ψ x (b + 1) v = fderiv ℝ Ψ (Ψ^[b] x) (jacProd Ψ x b v) := rfl
    rw [e, pow_succ]
    refine (hstep _ (hmem b) _).trans ?_
    have := mul_le_mul_of_nonneg_left (ih v) hθ
    nlinarith

lemma fderiv_close (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n → Vec n) (ystar : Vec n) (s η : ℝ)
    (hstrict : ∀ y z : Vec n, ‖y - ystar‖ < s → ‖z - ystar‖ < s →
      ‖b y - b z - A *ᵥ (y - z)‖ ≤ η * ‖y - z‖)
    (y : Vec n) (hy : ‖y - ystar‖ < s) (D : Vec n →L[ℝ] Vec n) (hD : HasFDerivAt b D y)
    (v : Vec n) : ‖D v - A *ᵥ v‖ ≤ η * ‖v‖ := by
  have hd : HasDerivAt (fun t : ℝ => b (y + t • v)) (D v) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y
    have h2 : HasFDerivAt b D (y + (0:ℝ) • v) := by simpa using hD
    exact h2.comp_hasDerivAt (0:ℝ) h1
  have hlim := hd.tendsto_slope_zero_right
  have hcont : Continuous fun t : ℝ => ‖y + t • v - ystar‖ := by fun_prop
  have hopen : ∀ᶠ t in 𝓝 (0:ℝ), ‖y + t • v - ystar‖ < s := by
    have := hcont.continuousAt (x := 0)
    have h0 : ‖y + (0:ℝ) • v - ystar‖ < s := by simpa using hy
    exact this.eventually (gt_mem_nhds h0)
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ),
      ‖t⁻¹ • (b (y + (0 + t) • v) - b (y + (0:ℝ) • v)) - A *ᵥ v‖ ≤ η * ‖v‖ := by
    filter_upwards [hopen.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htpos
    have htp : 0 < t := htpos
    have h1 := hstrict (y + t • v) y (by simpa using ht) hy
    have e : t⁻¹ • (b (y + (0 + t) • v) - b (y + (0:ℝ) • v)) - A *ᵥ v =
        t⁻¹ • (b (y + t • v) - b y - A *ᵥ (y + t • v - y)) := by
      have : A *ᵥ (y + t • v - y) = t • (A *ᵥ v) := by
        rw [add_sub_cancel_left, mulVec_smul]
      rw [this]
      simp only [zero_add, zero_smul, add_zero]
      rw [smul_sub t⁻¹ (b (y + t • v) - b y) (t • A *ᵥ v), smul_smul, inv_mul_cancel₀ htp.ne',
        one_smul]
    rw [e, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos htp]
    have h2 : ‖y + t • v - y‖ = t * ‖v‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htp]
    rw [h2] at h1
    calc t⁻¹ * ‖b (y + t • v) - b y - A *ᵥ (y + t • v - y)‖ ≤ t⁻¹ * (η * (t * ‖v‖)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr htp.le)
      _ = η * ‖v‖ := by field_simp
  have hlim' := (hlim.sub_const (A *ᵥ v)).norm
  exact le_of_tendsto hlim' hev

lemma jac_step_contract (H : RecursionSetup n) (R κ0 ε0 ρ0 η s : ℝ) (hRs : R < s)
    (hRr : R ≤ H.r0) (hρη : ρ0 ≤ η)
    (hstrict : ∀ y z : Vec n, ‖y - H.ystar‖ < s → ‖z - H.ystar‖ < s →
      ‖H.b y - H.b z - H.A *ᵥ (y - z)‖ ≤ η * ‖y - z‖)
    (hVj : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → ∀ d w : Vec n, ‖w‖ ≤ 2 * η * ‖d‖ →
      qf H.P (d + ε • (H.A *ᵥ d + w)) ≤ (1 - ε * κ0) * qf H.P d)
    (hdb : ∀ y : Vec n, ‖y - H.ystar‖ ≤ H.r0 → DifferentiableAt ℝ H.b y)
    (hde : ∀ ε : ℝ, 0 < ε → ∀ y : Vec n, ‖y - H.ystar‖ ≤ H.r0 →
      DifferentiableAt ℝ (H.e ε) y ∧ ‖fderiv ℝ (H.e ε) y‖ ≤ H.ρ ε)
    (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ ε0) (hρ : H.ρ ε ≤ ρ0)
    (z : Vec n) (hz : ‖z - H.ystar‖ ≤ R) (v : Vec n) :
    qf H.P (fderiv ℝ (driftMap H.b H.e ε) z v) ≤ (1 - ε * κ0) * qf H.P v := by
  have hzr : ‖z - H.ystar‖ ≤ H.r0 := hz.trans hRr
  have hbd := hdb z hzr
  obtain ⟨hed, hen⟩ := hde ε hε z hzr
  set D : Vec n →L[ℝ] Vec n := fderiv ℝ H.b z with hD
  set E : Vec n →L[ℝ] Vec n := fderiv ℝ (H.e ε) z with hE
  have hDd : HasFDerivAt H.b D z := hbd.hasFDerivAt
  have hEd : HasFDerivAt (H.e ε) E z := hed.hasFDerivAt
  have hΨ : HasFDerivAt (driftMap H.b H.e ε)
      (ContinuousLinearMap.id ℝ (Vec n) + ε • (D + E)) z := by
    have := (hasFDerivAt_id z).add ((hDd.add hEd).const_smul ε)
    exact this
  rw [hΨ.fderiv]
  have hcl := fderiv_close H.A H.b H.ystar s η hstrict z (by linarith) D hDd v
  have hρη' : H.ρ ε ≤ η := hρ.trans hρη
  have hw : ‖(D v - H.A *ᵥ v) + E v‖ ≤ 2 * η * ‖v‖ := by
    calc ‖(D v - H.A *ᵥ v) + E v‖ ≤ ‖D v - H.A *ᵥ v‖ + ‖E v‖ := norm_add_le _ _
      _ ≤ η * ‖v‖ + H.ρ ε * ‖v‖ :=
        add_le_add hcl ((E.le_opNorm v).trans (mul_le_mul_of_nonneg_right hen (norm_nonneg _)))
      _ ≤ η * ‖v‖ + η * ‖v‖ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hρη' (norm_nonneg _))
      _ = 2 * η * ‖v‖ := by ring
  have := hVj ε hε hεle v _ hw
  have e : (ContinuousLinearMap.id ℝ (Vec n) + ε • (D + E)) v =
      v + ε • (H.A *ᵥ v + ((D v - H.A *ᵥ v) + E v)) := by
    simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.id_apply]
    congr 2
    abel
  rw [e]
  exact this

lemma jac_real (S Lj κ0 ε T0 X Y : ℝ) (m a : ℕ) (hS : 1 ≤ S) (hLj : 0 ≤ Lj) (hκ0 : 0 < κ0)
    (hε : 0 < ε) (hεκ : ε * κ0 ≤ 1) (ha : a ≤ m) (haε : (a : ℝ) * ε ≤ T0 + 1) (hY : 0 ≤ Y)
    (hX : X ^ 2 ≤ (1 - ε * κ0) ^ (m - a) * S * ((1 + Lj * ε) ^ a * Y) ^ 2) :
    X ≤ (S * Real.exp (Lj * (T0 + 1)) * Real.exp (κ0 * (T0 + 1) / 2)) *
      Real.exp (-(κ0 / 2 * ε * m)) * Y := by
  have hθ0 : 0 ≤ 1 - ε * κ0 := by linarith
  have hS0 : 0 < S := by linarith
  have h1 : 1 - ε * κ0 ≤ Real.exp (-(ε * κ0)) := by
    have := Real.add_one_le_exp (-(ε * κ0)); linarith
  have h2 : (1 - ε * κ0) ^ (m - a) ≤ Real.exp (-(ε * κ0) * ((m - a : ℕ) : ℝ)) := by
    rw [show -(ε * κ0) * ((m - a : ℕ) : ℝ) = ((m - a : ℕ) : ℝ) * (-(ε * κ0)) from mul_comm _ _,
      Real.exp_nat_mul]
    exact pow_le_pow_left₀ hθ0 h1 _
  have hma : ((m - a : ℕ) : ℝ) = (m : ℝ) - a := by rw [Nat.cast_sub ha]
  rw [hma] at h2
  have h3 : Real.exp (-(ε * κ0) * ((m : ℝ) - a)) =
      Real.exp (-(ε * κ0 * m)) * Real.exp (ε * κ0 * a) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (ε * κ0 * a) ≤ Real.exp (κ0 * (T0 + 1)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h5 : (1 + Lj * ε) ^ a ≤ Real.exp (Lj * (T0 + 1)) := by
    have h6 : 1 + Lj * ε ≤ Real.exp (Lj * ε) := by
      have := Real.add_one_le_exp (Lj * ε); linarith
    calc (1 + Lj * ε) ^ a ≤ Real.exp (Lj * ε) ^ a :=
          pow_le_pow_left₀ (by positivity) h6 a
      _ = Real.exp (a * (Lj * ε)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (Lj * (T0 + 1)) := by
          apply Real.exp_le_exp.mpr
          nlinarith
  have hE : 0 ≤ Real.exp (-(ε * κ0 * m)) := (Real.exp_pos _).le
  have hq0 : 0 ≤ (1 + Lj * ε) ^ a := by positivity
  apply le_of_sq_le' (by positivity)
  have e1 : ((S * Real.exp (Lj * (T0 + 1)) * Real.exp (κ0 * (T0 + 1) / 2)) *
      Real.exp (-(κ0 / 2 * ε * m)) * Y) ^ 2 =
      S ^ 2 * Real.exp (Lj * (T0 + 1)) ^ 2 * Real.exp (κ0 * (T0 + 1)) *
        Real.exp (-(ε * κ0 * m)) * Y ^ 2 := by
    have a1 : Real.exp (κ0 * (T0 + 1) / 2) ^ 2 = Real.exp (κ0 * (T0 + 1)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have a2 : Real.exp (-(κ0 / 2 * ε * m)) ^ 2 = Real.exp (-(ε * κ0 * m)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    calc _ = S ^ 2 * Real.exp (Lj * (T0 + 1)) ^ 2 * (Real.exp (κ0 * (T0 + 1) / 2) ^ 2) *
          (Real.exp (-(κ0 / 2 * ε * m)) ^ 2) * Y ^ 2 := by ring
      _ = _ := by rw [a1, a2]
  rw [e1]
  have h7 : (1 - ε * κ0) ^ (m - a) ≤
      Real.exp (-(ε * κ0 * m)) * Real.exp (κ0 * (T0 + 1)) := by
    rw [h3] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left h4 hE)
  have h8 : ((1 + Lj * ε) ^ a * Y) ^ 2 ≤ Real.exp (Lj * (T0 + 1)) ^ 2 * Y ^ 2 := by
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg Y)
    exact pow_le_pow_left₀ hq0 h5 2
  have h9 : (1 - ε * κ0) ^ (m - a) * S * ((1 + Lj * ε) ^ a * Y) ^ 2 ≤
      (Real.exp (-(ε * κ0 * m)) * Real.exp (κ0 * (T0 + 1))) * S *
        (Real.exp (Lj * (T0 + 1)) ^ 2 * Y ^ 2) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right h7 hS0.le) h8 (sq_nonneg _) (by positivity)
  refine hX.trans (h9.trans ?_)
  have hpos : 0 ≤ Real.exp (-(ε * κ0 * m)) * Real.exp (κ0 * (T0 + 1)) *
      Real.exp (Lj * (T0 + 1)) ^ 2 * Y ^ 2 := by positivity
  have : (Real.exp (-(ε * κ0 * m)) * Real.exp (κ0 * (T0 + 1))) * S *
        (Real.exp (Lj * (T0 + 1)) ^ 2 * Y ^ 2) =
      S * (Real.exp (-(ε * κ0 * m)) * Real.exp (κ0 * (T0 + 1)) *
        Real.exp (Lj * (T0 + 1)) ^ 2 * Y ^ 2) := by ring
  rw [this]
  have : S ^ 2 * Real.exp (Lj * (T0 + 1)) ^ 2 * Real.exp (κ0 * (T0 + 1)) *
        Real.exp (-(ε * κ0 * m)) * Y ^ 2 =
      S ^ 2 * (Real.exp (-(ε * κ0 * m)) * Real.exp (κ0 * (T0 + 1)) *
        Real.exp (Lj * (T0 + 1)) ^ 2 * Y ^ 2) := by ring
  rw [this]
  nlinarith [mul_nonneg hpos (by linarith : (0:ℝ) ≤ S - 1), mul_nonneg hpos hS0.le]

end Jac

end RecursionContraction


/-- v2 `cor:recursion` (abstract form: entry, exponential convergence and uniform tracking).

Hypotheses beyond the setting `H`: `K` is a compact set of starts, every start in `K` has a
solution of `y' = b y` on `[0, ∞)` (`hex`; supplied by Proposition `prop:S`), `UniformEntry`,
a uniform a priori bound for solutions from `K` on finite horizons (`hbdd`; supplied by the
Lyapunov sublevel bound), the finite-horizon tracking estimate (`htrack`; Proposition
`prop:LR34`) and one-step consistency along solutions close to `ystar` (`hcons`).  Conclusion:
for `ε ≤ ε1` and `ρ ε ≤ ρ1` the fixed point `y_ε` of `local_fixed_point` attracts every
orbit from `K` at the rate `C exp (-c ε k)`, and every orbit stays within `C ρ ε` of the
solution it tracks, uniformly in `k`. -/
theorem drift_recursion_converges {n : ℕ} (H : RecursionSetup n) (K : Set (Fin n → ℝ))
    (_hK : IsCompact K)
    (hex : ∀ y0 ∈ K, ∃ y : ℝ → Fin n → ℝ, IsODESol H.b y0 y)
    (hent : UniformEntry H.b H.ystar K)
    (hbdd : ∀ T : ℝ, 0 ≤ T → ∃ M : ℝ, 0 ≤ M ∧ ∀ y0 ∈ K, ∀ y : ℝ → Fin n → ℝ,
      IsODESol H.b y0 y → ∀ t : ℝ, 0 ≤ t → t ≤ T → ‖y t - H.ystar‖ ≤ M)
    (htrack : ∀ T : ℝ, 0 ≤ T → ∃ CT εT : ℝ, 0 < CT ∧ 0 < εT ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εT → ∀ y0 ∈ K, ∀ y : ℝ → Fin n → ℝ, IsODESol H.b y0 y →
        ∀ k : ℕ, (k : ℝ) * ε ≤ T →
          ‖(driftMap H.b H.e ε)^[k] y0 - y (k * ε)‖ ≤ CT * H.ρ ε)
    (hcons : ∃ rc C1 εc : ℝ, 0 < rc ∧ 0 < C1 ∧ 0 < εc ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εc → ∀ y0 ∈ K, ∀ y : ℝ → Fin n → ℝ, IsODESol H.b y0 y →
        ∀ k : ℕ, ‖y (k * ε) - H.ystar‖ ≤ rc →
          ‖y (((k + 1 : ℕ) : ℝ) * ε) - driftMap H.b H.e ε (y (k * ε))‖ ≤ C1 * ε * H.ρ ε) :
    ∃ ε1 ρ1 C c : ℝ, 0 < ε1 ∧ 0 < ρ1 ∧ 0 < C ∧ 0 < c ∧
      ∃ N : Set (Fin n → ℝ),
        (∃ s : ℝ, 0 < s ∧ closedBall H.ystar s ⊆ N) ∧ N ⊆ closedBall H.ystar H.r0 ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ ε1 → H.ρ ε ≤ ρ1 →
          ∃ yε ∈ N, driftMap H.b H.e ε yε = yε ∧
            (∀ z ∈ N, driftMap H.b H.e ε z = z → z = yε) ∧
            ‖yε - H.ystar‖ ≤ C * H.ρ ε ∧
            ∀ y0 ∈ K,
              (∀ k : ℕ, ‖(driftMap H.b H.e ε)^[k] y0 - yε‖ ≤ C * Real.exp (-(c * ε * k))) ∧
              ∀ y : ℝ → Fin n → ℝ, IsODESol H.b y0 y → ∀ k : ℕ,
                ‖(driftMap H.b H.e ε)^[k] y0 - y (k * ε)‖ ≤ C * H.ρ ε := by
  classical
  obtain ⟨R, κ0, ε0, ρ0, S, η, C2, hR, hRr, hκ0, hε0, hε01, hε0κ, hρ0, hρ0η, hS1, hη, hC2,
    hnorm, -, -, hU, hV, hinv, hbil⟩ := RecursionContraction.core_data H
  obtain ⟨rc, C1, εc, hrc, hC1, hεc, hcons⟩ := hcons
  have hS0 : 0 < S := by linarith
  have hup : ∀ x : Vec n, qf H.P x ≤ S * ‖x‖ ^ 2 := fun x => (hnorm x).2
  obtain ⟨T0, CT, ε1', ρ1', hT0, hCT, hε1', hρ1', hent'⟩ := entry_abstract H.P S R ε0 ρ0 rc
    hS1 hR hε0 hρ0 hrc hup H.b H.ystar K (driftMap H.b H.e) H.ρ hent htrack hinv
  obtain ⟨M, hM0, hMb⟩ := hbdd (T0 + 1) (by linarith)
  set Cf : ℝ := Real.sqrt (C2 / κ0) with hCf
  have hCf0 : 0 ≤ Cf := Real.sqrt_nonneg _
  set B : ℝ := 4 * S ^ 2 * C1 ^ 2 / κ0 ^ 2 + 2 * S * C1 ^ 2 / κ0 with hB
  have hB0 : 0 ≤ B := by positivity
  set Cs : ℝ := Real.sqrt (S * CT ^ 2 + B) with hCs
  have hCs0 : 0 ≤ Cs := Real.sqrt_nonneg _
  have hCs2 : Cs ^ 2 = S * CT ^ 2 + B := Real.sq_sqrt (by positivity)
  set Γ : ℝ := 2 * S * R * Real.exp (κ0 * (T0 + 1) / 2) with hΓ
  have hΓ0 : 0 ≤ Γ := by positivity
  set Γ1 : ℝ := (CT * ρ1' + R + M) * Real.exp (κ0 * (T0 + 1) / 2) with hΓ1
  have hΓ10 : 0 ≤ Γ1 := by positivity
  obtain ⟨hNball, hNsub⟩ := ball_props H R S hR hRr hS1 hnorm
  refine ⟨min ε1' εc, ρ1', Cf + Γ + Γ1 + CT + Cs + 1, κ0 / 2, lt_min hε1' hεc, hρ1', by positivity,
    by positivity, {y | qf H.P (y - H.ystar) ≤ R ^ 2}, hNball, hNsub, ?_⟩
  intro ε hε hεle hρle
  have hεε1' : ε ≤ ε1' := hεle.trans (min_le_left _ _)
  have hεεc : ε ≤ εc := hεle.trans (min_le_right _ _)
  obtain ⟨hεε0, hρρ0, hε1, hfacts⟩ := hent' ε hε hεε1' hρle
  have hρnn : 0 ≤ H.ρ ε :=
    le_trans (norm_nonneg _) (H.he0 ε hε H.ystar (by simpa using H.hr0.le))
  obtain ⟨L, hLN, hLfix, hLuniq, hLbd⟩ := fixed_point_pkg H R κ0 ε0 ρ0 S C2 hR hκ0 hC2 hS1 hε0κ
    hnorm hU hV hinv ε hε hεε0 hρρ0
  have hq0 : ∀ x : Vec n, 0 ≤ qf H.P x := fun x => (sq_nonneg _).trans (hnorm x).1
  have hLR : ‖L - H.ystar‖ ≤ R := by
    apply le_of_sq_le' hR.le
    exact (hnorm _).1.trans hLN
  -- uniform tracking
  have hsup : ∀ y0 ∈ K, ∀ y : ℝ → Fin n → ℝ, IsODESol H.b y0 y → ∀ k : ℕ,
      ‖(driftMap H.b H.e ε)^[k] y0 - y (k * ε)‖ ≤ (CT + Cs) * H.ρ ε := by
    intro y0 hy0 y hy k
    obtain ⟨hk0le, hball, htk, hxN⟩ := hfacts y0 hy0 y hy
    by_cases hk : ⌈T0 / ε⌉₊ ≤ k
    · -- after entry
      set k0 : ℕ := ⌈T0 / ε⌉₊ with hk0
      set x : ℕ → Vec n := fun k => (driftMap H.b H.e ε)^[k] y0 with hx
      set z : ℕ → Vec n := fun k => y (k * ε) with hz
      have hzN : ∀ k, k0 ≤ k → qf H.P (z k - H.ystar) ≤ R ^ 2 := by
        intro k hk
        refine mem_of_norm_le H.P S R hS1 hR hup _ ?_
        have := (hball k hk).trans (min_le_left _ _)
        refine this.trans ?_
        exact div_le_div_of_nonneg_left hR.le hS0 (by linarith)
      have hxs : ∀ k, x (k + 1) = driftMap H.b H.e ε (x k) := by
        intro k; simp only [hx]; rw [Function.iterate_succ_apply']
      have hbound := post_entry_bound H.P H.hPs S κ0 ε C1 (H.ρ ε) hbil hnorm hS0 hκ0 hε hε1
        ((mul_le_mul_of_nonneg_right (hεε0) hκ0.le).trans hε0κ) x z (driftMap H.b H.e ε) k0 hxs
        (fun k hk => hV ε hε hεε0 hρρ0 (x k) (z k) (hxN k hk) (hzN k hk))
        (fun k hk => by
          have := hcons ε hε hεεc y0 hy0 y hy k ((hball k hk).trans (min_le_right _ _))
          simpa [hz] using this) k hk
      have hqk0 : qf H.P (x k0 - z k0) ≤ S * (CT * H.ρ ε) ^ 2 := by
        refine (hup _).trans ?_
        exact mul_le_mul_of_nonneg_left (by gcongr; exact htk k0 hk0le) hS0.le
      have hfin : ‖x k - z k‖ ^ 2 ≤ (Cs * H.ρ ε) ^ 2 := by
        have h1 := (hnorm (x k - z k)).1
        have : (Cs * H.ρ ε) ^ 2 = S * (CT * H.ρ ε) ^ 2 + B * H.ρ ε ^ 2 := by
          rw [mul_pow, hCs2]; ring
        rw [this]
        have h2 : B * H.ρ ε ^ 2 = (4 * S ^ 2 * C1 ^ 2 / κ0 ^ 2 + 2 * S * C1 ^ 2 / κ0) * H.ρ ε ^ 2 := rfl
        linarith
      have h5 := le_of_sq_le' (mul_nonneg hCs0 hρnn) hfin
      show ‖x k - z k‖ ≤ _
      exact h5.trans (mul_le_mul_of_nonneg_right (by linarith only [hCT]) hρnn)
    · push Not at hk
      have hkε : (k : ℝ) * ε ≤ T0 + 1 := lt_ceil_mul_le T0 ε k hε hk hk0le
      exact (htk k hkε).trans (mul_le_mul_of_nonneg_right (by linarith only [hCs0]) hρnn)
  have hεκ : ε * κ0 ≤ 1 := (mul_le_mul_of_nonneg_right hεε0 hκ0.le).trans hε0κ
  have hθ0 : 0 ≤ 1 - ε * κ0 := by linarith
  have hCge : Cf + Γ + Γ1 + CT + Cs + 1 ≥ Γ + Γ1 + (CT + Cs) + Cf := by linarith
  refine ⟨L, hLN, hLfix, hLuniq, ?_, ?_⟩
  · calc ‖L - H.ystar‖ ≤ Cf * H.ρ ε := hLbd
      _ ≤ (Cf + Γ + Γ1 + CT + Cs + 1) * H.ρ ε := by
        apply mul_le_mul_of_nonneg_right _ hρnn; linarith
  · intro y0 hy0
    refine ⟨?_, fun y hy k => ?_⟩
    · intro k
      obtain ⟨y, hy⟩ := hex y0 hy0
      obtain ⟨hk0le, hball, htk, hxN⟩ := hfacts y0 hy0 y hy
      have hEpos : 0 < Real.exp (-(κ0 / 2 * ε * k)) := Real.exp_pos _
      by_cases hk : ⌈T0 / ε⌉₊ ≤ k
      · set k0 : ℕ := ⌈T0 / ε⌉₊ with hk0
        have hxk0 := hxN k0 le_rfl
        obtain ⟨hc1, -⟩ := iterate_qf_contract H.P (driftMap H.b H.e ε) H.ystar R (1 - ε * κ0)
          hθ0 (fun y hy => hinv ε hε hεε0 hρρ0 y hy)
          (fun y z hy hz => hV ε hε hεε0 hρρ0 y z hy hz) (k - k0)
          ((driftMap H.b H.e ε)^[k0] y0) L hxk0 hLN
        have e1 : (driftMap H.b H.e ε)^[k - k0] ((driftMap H.b H.e ε)^[k0] y0) =
            (driftMap H.b H.e ε)^[k] y0 := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel hk]
        have e2 : (driftMap H.b H.e ε)^[k - k0] L = L :=
          (Function.IsFixedPt.iterate hLfix _).eq
        rw [e1, e2] at hc1
        have hd1 : ‖(driftMap H.b H.e ε)^[k0] y0 - H.ystar‖ ≤ R := by
          apply le_of_sq_le' hR.le
          exact (hnorm _).1.trans hxk0
        have hd : ‖(driftMap H.b H.e ε)^[k0] y0 - L‖ ≤ 2 * R := by
          calc ‖(driftMap H.b H.e ε)^[k0] y0 - L‖
              = ‖((driftMap H.b H.e ε)^[k0] y0 - H.ystar) - (L - H.ystar)‖ := by congr 1; abel
            _ ≤ ‖(driftMap H.b H.e ε)^[k0] y0 - H.ystar‖ + ‖L - H.ystar‖ := norm_sub_le _ _
            _ ≤ R + R := add_le_add hd1 hLR
            _ = 2 * R := by ring
        have hXsq : ‖(driftMap H.b H.e ε)^[k] y0 - L‖ ^ 2 ≤
            S * (2 * R) ^ 2 * (1 - ε * κ0) ^ (k - k0) := by
          have h1 := (hnorm ((driftMap H.b H.e ε)^[k] y0 - L)).1
          have h2 := hup ((driftMap H.b H.e ε)^[k0] y0 - L)
          have h3 : ‖(driftMap H.b H.e ε)^[k0] y0 - L‖ ^ 2 ≤ (2 * R) ^ 2 := by gcongr
          have h4 : (1 - ε * κ0) ^ (k - k0) * qf H.P ((driftMap H.b H.e ε)^[k0] y0 - L) ≤
              (1 - ε * κ0) ^ (k - k0) * (S * (2 * R) ^ 2) :=
            mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hS0.le))
              (pow_nonneg hθ0 _)
          calc _ ≤ qf H.P ((driftMap H.b H.e ε)^[k] y0 - L) := h1
            _ ≤ (1 - ε * κ0) ^ (k - k0) * qf H.P ((driftMap H.b H.e ε)^[k0] y0 - L) := hc1
            _ ≤ (1 - ε * κ0) ^ (k - k0) * (S * (2 * R) ^ 2) := h4
            _ = S * (2 * R) ^ 2 * (1 - ε * κ0) ^ (k - k0) := by ring
        have := after_entry_real S R κ0 ε T0 _ k k0 hS1 hR hκ0 hεκ hk hXsq hk0le
        calc _ ≤ (2 * S * R * Real.exp (κ0 * (T0 + 1) / 2)) * Real.exp (-(κ0 / 2 * ε * k)) := this
          _ ≤ (Cf + Γ + Γ1 + CT + Cs + 1) * Real.exp (-(κ0 / 2 * ε * k)) := by
            apply mul_le_mul_of_nonneg_right _ hEpos.le
            have : 2 * S * R * Real.exp (κ0 * (T0 + 1) / 2) = Γ := rfl
            linarith only [this, hCf0, hΓ10, hCT, hCs0]
      · push Not at hk
        have hkε : (k : ℝ) * ε ≤ T0 + 1 := lt_ceil_mul_le T0 ε k hε hk hk0le
        have h1 := htk k hkε
        have h2 : ‖y (k * ε) - H.ystar‖ ≤ M := hMb y0 hy0 y hy _ (by positivity) hkε
        have h3 : CT * H.ρ ε ≤ CT * ρ1' := mul_le_mul_of_nonneg_left hρle hCT.le
        have h4 : ‖(driftMap H.b H.e ε)^[k] y0 - L‖ ≤ CT * ρ1' + R + M := by
          calc ‖(driftMap H.b H.e ε)^[k] y0 - L‖
              = ‖((driftMap H.b H.e ε)^[k] y0 - y (k * ε)) + (y (k * ε) - H.ystar)
                  - (L - H.ystar)‖ := by congr 1; abel
            _ ≤ ‖(driftMap H.b H.e ε)^[k] y0 - y (k * ε)‖ + ‖y (k * ε) - H.ystar‖
                  + ‖L - H.ystar‖ := by
                refine (norm_sub_le _ _).trans ?_
                gcongr
                exact norm_add_le _ _
            _ ≤ CT * ρ1' + M + R := by linarith only [h1, h2, h3, hLR]
            _ = CT * ρ1' + R + M := by ring
        have h5 : 1 ≤ Real.exp (κ0 * (T0 + 1) / 2) * Real.exp (-(κ0 / 2 * ε * k)) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          have h7 := mul_le_mul_of_nonneg_left hkε (by positivity : 0 ≤ κ0 / 2)
          linarith only [h7]
        have hA1 : 0 ≤ CT * ρ1' + R + M := by positivity
        calc _ ≤ CT * ρ1' + R + M := h4
          _ ≤ (CT * ρ1' + R + M) * (Real.exp (κ0 * (T0 + 1) / 2) *
              Real.exp (-(κ0 / 2 * ε * k))) := le_mul_of_one_le_right hA1 h5
          _ = Γ1 * Real.exp (-(κ0 / 2 * ε * k)) := by rw [hΓ1]; ring
          _ ≤ (Cf + Γ + Γ1 + CT + Cs + 1) * Real.exp (-(κ0 / 2 * ε * k)) := by
            apply mul_le_mul_of_nonneg_right _ hEpos.le
            linarith only [hCf0, hΓ0, hCT, hCs0]
    · have := hsup y0 hy0 y hy k
      refine this.trans ?_
      apply mul_le_mul_of_nonneg_right _ hρnn
      linarith only [hCf0, hΓ0, hΓ10]

/-- v2 `cor:recursion` ("Products").  If in addition `b` and `e ε` are differentiable on the
ball (so that `D Ψ_ε = id + ε (D b + D e_ε)`), `‖D e_ε‖ ≤ ρ ε`, and the Jacobians are bounded
by `1 + L ε` along the orbit up to every finite horizon (`hJ`), then the products of the
Jacobians along the orbit decay exponentially: `‖J_{j+m-1} ∘ ⋯ ∘ J_j‖ ≤ Γ exp (-c ε m)`, with
`Γ, c` uniform in `ε`, in `j` and in the start `y0 ∈ K`. -/
theorem jacobian_products {n : ℕ} (H : RecursionSetup n) (K : Set (Fin n → ℝ))
    (hex : ∀ y0 ∈ K, ∃ y : ℝ → Fin n → ℝ, IsODESol H.b y0 y)
    (hent : UniformEntry H.b H.ystar K)
    (htrack : ∀ T : ℝ, 0 ≤ T → ∃ CT εT : ℝ, 0 < CT ∧ 0 < εT ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εT → ∀ y0 ∈ K, ∀ y : ℝ → Fin n → ℝ, IsODESol H.b y0 y →
        ∀ k : ℕ, (k : ℝ) * ε ≤ T →
          ‖(driftMap H.b H.e ε)^[k] y0 - y (k * ε)‖ ≤ CT * H.ρ ε)
    (hdb : ∀ y : Fin n → ℝ, ‖y - H.ystar‖ ≤ H.r0 → DifferentiableAt ℝ H.b y)
    (hde : ∀ ε : ℝ, 0 < ε → ∀ y : Fin n → ℝ, ‖y - H.ystar‖ ≤ H.r0 →
      DifferentiableAt ℝ (H.e ε) y ∧ ‖fderiv ℝ (H.e ε) y‖ ≤ H.ρ ε)
    (hJ : ∀ T : ℝ, 0 ≤ T → ∃ L εL : ℝ, 0 ≤ L ∧ 0 < εL ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εL → ∀ y0 ∈ K, ∀ k : ℕ, (k : ℝ) * ε ≤ T →
        ‖fderiv ℝ (driftMap H.b H.e ε) ((driftMap H.b H.e ε)^[k] y0)‖ ≤ 1 + L * ε) :
    ∃ ε1 ρ1 Γ c : ℝ, 0 < ε1 ∧ 0 < ρ1 ∧ 0 < Γ ∧ 0 < c ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε1 → H.ρ ε ≤ ρ1 → ∀ y0 ∈ K, ∀ j m : ℕ,
        ‖jacProd (driftMap H.b H.e ε) ((driftMap H.b H.e ε)^[j] y0) m‖ ≤
          Γ * Real.exp (-(c * ε * m)) := by
  classical
  obtain ⟨R, κ0, ε0, ρ0, S, η, C2, hR, hRr, hκ0, hε0, hε01, hε0κ, hρ0, hρ0η, hS1, hη, hC2,
    hnorm, ⟨s, hRs, hstrict⟩, hVj, hU, hV, hinv, hbil⟩ := RecursionContraction.core_data H
  have hS0 : 0 < S := by linarith
  have hup : ∀ x : Vec n, qf H.P x ≤ S * ‖x‖ ^ 2 := fun x => (hnorm x).2
  obtain ⟨T0, CT, ε1', ρ1', hT0, hCT, hε1', hρ1', hent'⟩ := entry_abstract H.P S R ε0 ρ0 1
    hS1 hR hε0 hρ0 one_pos hup H.b H.ystar K (driftMap H.b H.e) H.ρ hent htrack hinv
  obtain ⟨Lj, εL, hLj0, hεL, hJb⟩ := hJ (T0 + 1) (by linarith)
  refine ⟨min ε1' εL, ρ1', S * Real.exp (Lj * (T0 + 1)) * Real.exp (κ0 * (T0 + 1) / 2), κ0 / 2,
    lt_min hε1' hεL, hρ1', by positivity, by positivity, ?_⟩
  intro ε hε hεle hρle y0 hy0 j m
  have hεε1' : ε ≤ ε1' := hεle.trans (min_le_left _ _)
  have hεεL : ε ≤ εL := hεle.trans (min_le_right _ _)
  obtain ⟨hεε0, hρρ0, hε1, hfacts⟩ := hent' ε hε hεε1' hρle
  obtain ⟨y, hy⟩ := hex y0 hy0
  obtain ⟨hk0le, -, -, hxN⟩ := hfacts y0 hy0 y hy
  have hεκ : ε * κ0 ≤ 1 := (mul_le_mul_of_nonneg_right hεε0 hκ0.le).trans hε0κ
  have hθ0 : 0 ≤ 1 - ε * κ0 := by linarith
  set Ψ := driftMap H.b H.e ε with hΨ
  set k0 : ℕ := ⌈T0 / ε⌉₊ with hk0
  have hstepN : ∀ z : Vec n, qf H.P (z - H.ystar) ≤ R ^ 2 → ∀ v : Vec n,
      qf H.P (fderiv ℝ Ψ z v) ≤ (1 - ε * κ0) * qf H.P v := by
    intro z hz v
    have hzR : ‖z - H.ystar‖ ≤ R := by
      apply le_of_sq_le' hR.le
      exact (hnorm _).1.trans hz
    exact jac_step_contract H R κ0 ε0 ρ0 η s hRs hRr hρ0η hstrict hVj hdb hde ε hε hεε0 hρρ0 z hzR v
  have hmemN : ∀ t j' : ℕ, k0 ≤ j' → qf H.P (Ψ^[t] (Ψ^[j'] y0) - H.ystar) ≤ R ^ 2 := by
    intro t j' hj'
    rw [← Function.iterate_add_apply]
    exact hxN (t + j') (by omega)
  -- decomposition of the product
  have key : ∃ a : ℕ, a ≤ m ∧ (a : ℝ) * ε ≤ T0 + 1 ∧
      ‖jacProd Ψ (Ψ^[j] y0) a‖ ≤ (1 + Lj * ε) ^ a ∧
      ∀ v : Vec n, qf H.P (jacProd Ψ (Ψ^[j] y0) m v) ≤
        (1 - ε * κ0) ^ (m - a) * qf H.P (jacProd Ψ (Ψ^[j] y0) a v) := by
    have hlate : ∀ a : ℕ, a ≤ m → (m - a = 0 ∨ k0 ≤ a + j) → ∀ v : Vec n,
        qf H.P (jacProd Ψ (Ψ^[j] y0) m v) ≤
          (1 - ε * κ0) ^ (m - a) * qf H.P (jacProd Ψ (Ψ^[j] y0) a v) := by
      intro a ham hcase v
      have hsplit : jacProd Ψ (Ψ^[j] y0) m =
          (jacProd Ψ (Ψ^[a] (Ψ^[j] y0)) (m - a)).comp (jacProd Ψ (Ψ^[j] y0) a) := by
        rw [← jacProd_add, Nat.add_sub_cancel' ham]
      rw [hsplit, ContinuousLinearMap.comp_apply]
      rcases hcase with h0 | hk
      · rw [h0]; simp [jacProd]
      · refine jacProd_late H.P Ψ (Ψ^[a] (Ψ^[j] y0)) (1 - ε * κ0) hθ0
          {z | qf H.P (z - H.ystar) ≤ R ^ 2} ?_ (fun z hz v => hstepN z hz v) (m - a) _
        intro t
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
        exact hxN (t + a + j) (by omega)
    by_cases hj : k0 ≤ j
    · refine ⟨0, Nat.zero_le _, by simp; positivity, ?_, hlate 0 (Nat.zero_le _) (Or.inr (by omega))⟩
      simpa [jacProd] using ContinuousLinearMap.norm_id_le
    · push Not at hj
      set a : ℕ := min m (k0 - j) with ha
      have ham : a ≤ m := min_le_left _ _
      have hak : a + j ≤ k0 := by omega
      have haε : (a : ℝ) * ε ≤ T0 + 1 := by
        have : (a : ℝ) ≤ k0 := by exact_mod_cast (by omega : a ≤ k0)
        nlinarith
      refine ⟨a, ham, haε, ?_, hlate a ham ?_⟩
      · apply jacProd_early Ψ (Ψ^[j] y0) (1 + Lj * ε) a
        intro t ht
        rw [← Function.iterate_add_apply]
        apply hJb ε hε hεεL y0 hy0
        have : (t + j : ℕ) ≤ k0 := by omega
        have h2 : ((t + j : ℕ) : ℝ) ≤ k0 := by exact_mod_cast this
        push_cast at h2 ⊢
        nlinarith
      · by_cases hma : m - a = 0
        · exact Or.inl hma
        · right
          have : a = k0 - j := by omega
          omega
  obtain ⟨a, ham, haε, hearly, hlatev⟩ := key
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply jac_real S Lj κ0 ε T0 _ ‖v‖ m a hS1 hLj0 hκ0 hε hεκ ham haε (norm_nonneg _)
  have h1 := (hnorm (jacProd Ψ (Ψ^[j] y0) m v)).1
  have h2 := hlatev v
  have h3 := (hnorm (jacProd Ψ (Ψ^[j] y0) a v)).2
  have h4 : ‖jacProd Ψ (Ψ^[j] y0) a v‖ ≤ (1 + Lj * ε) ^ a * ‖v‖ :=
    ((jacProd Ψ (Ψ^[j] y0) a).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hearly (norm_nonneg _))
  have h5 : ‖jacProd Ψ (Ψ^[j] y0) a v‖ ^ 2 ≤ ((1 + Lj * ε) ^ a * ‖v‖) ^ 2 := by gcongr
  have h6 : 0 ≤ (1 - ε * κ0) ^ (m - a) := pow_nonneg hθ0 _
  calc ‖jacProd Ψ (Ψ^[j] y0) m v‖ ^ 2 ≤ qf H.P (jacProd Ψ (Ψ^[j] y0) m v) := h1
    _ ≤ (1 - ε * κ0) ^ (m - a) * qf H.P (jacProd Ψ (Ψ^[j] y0) a v) := h2
    _ ≤ (1 - ε * κ0) ^ (m - a) * (S * ‖jacProd Ψ (Ψ^[j] y0) a v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 h6
    _ ≤ (1 - ε * κ0) ^ (m - a) * (S * ((1 + Lj * ε) ^ a * ‖v‖) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hS0.le) h6
    _ = (1 - ε * κ0) ^ (m - a) * S * ((1 + Lj * ε) ^ a * ‖v‖) ^ 2 := by ring


end SparseSGD.Logistic.V2
