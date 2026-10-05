import Mathlib
import SparseSGD.Continuum.PerronRate

/-!
# Root perturbation for monic cubics (v2 `lem:helps-roots`) and continuity of `r_c`

Formalizes `lem:helps-roots` of `paper/appendix/momentum_helps.tex` and the continuity of the
continuum Perron rate `r_c = continuumPerronRate` used in Step 6 of `lem:helps-transfer`.

**Deviation from the tex.** The tex states `lem:helps-roots` for monic polynomials of arbitrary
degree `n` (with `δ^(1/n)`).  Every use in the appendix (the continuum cubic `χ`, the
step characteristic polynomial and the transfer cubic) is a monic *cubic*, so the Lean statements
are specialized to `n = 3`; the general-`n` version is not formalized.  The statements are
otherwise exactly those of the tex, with `δ` an arbitrary upper bound for
`max_{|z| ≤ M} |P(z) - Q(z)|` (which is how it is applied).
-/

namespace SparseSGD.Scaling.Helps

noncomputable section

/-- Roots in `ℂ` of the monic cubic `z^3 + a2 z^2 + a1 z + a0`. -/
def cubicRoots (a2 a1 a0 : ℂ) : Set ℂ := {z | z^3 + a2*z^2 + a1*z + a0 = 0}

/-- Largest real part of a set of complex numbers. -/
def maxRe (S : Set ℂ) : ℝ := sSup (Complex.re '' S)

/-- Largest modulus of a set of complex numbers. -/
def maxNorm (S : Set ℂ) : ℝ := sSup ((fun z : ℂ => ‖z‖) '' S)

/-! ### Factorization and the root set -/

/-- Every monic complex cubic factors into linear factors (`lem:helps-roots`, factorization). -/
theorem cubic_factor (a2 a1 a0 : ℂ) :
    ∃ z1 z2 z3 : ℂ, ∀ z : ℂ, z^3 + a2*z^2 + a1*z + a0 = (z-z1)*(z-z2)*(z-z3) := by
  let p : Polynomial ℂ := Polynomial.X^3 + Polynomial.C a2 * Polynomial.X^2
    + Polynomial.C a1 * Polynomial.X + Polynomial.C a0
  have hm : p.Monic := by unfold p; monicity!
  have hd : p.natDegree = 3 := by unfold p; compute_degree!
  have hprod := (IsAlgClosed.splits p).eq_prod_roots_of_monic hm
  have hc : Multiset.card p.roots = 3 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hd]
  obtain ⟨z1, z2, z3, hr⟩ := Multiset.card_eq_three.mp hc
  refine ⟨z1, z2, z3, fun z => ?_⟩
  have h := congrArg (Polynomial.eval z) hprod
  rw [hr] at h
  simp only [p, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons,
    Multiset.map_singleton, Multiset.prod_singleton, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_pow] at h
  rw [h]; ring

/-- The root set of a monic cubic is the set of its three factors' roots. -/
theorem cubicRoots_eq {a2 a1 a0 z1 z2 z3 : ℂ}
    (h : ∀ z : ℂ, z^3 + a2*z^2 + a1*z + a0 = (z-z1)*(z-z2)*(z-z3)) :
    cubicRoots a2 a1 a0 = {z1, z2, z3} := by
  ext z
  simp only [cubicRoots, Set.mem_ofPred_eq, h, mul_eq_zero, sub_eq_zero, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  tauto

theorem cubicRoots_finite (a2 a1 a0 : ℂ) : (cubicRoots a2 a1 a0).Finite := by
  obtain ⟨z1, z2, z3, h⟩ := cubic_factor a2 a1 a0
  rw [cubicRoots_eq h]
  exact Set.toFinite _

theorem cubicRoots_nonempty (a2 a1 a0 : ℂ) : (cubicRoots a2 a1 a0).Nonempty := by
  obtain ⟨z1, z2, z3, h⟩ := cubic_factor a2 a1 a0
  rw [cubicRoots_eq h]
  exact ⟨z1, by simp⟩

/-! ### (P1) Cauchy bound -/

/-- `lem:helps-roots`, first claim (cubic case): every root of the monic cubic lies in the disc
of radius `1 + max |a_i|`. -/
theorem cubicRoots_norm_le {a2 a1 a0 z : ℂ} (hz : z ∈ cubicRoots a2 a1 a0) :
    ‖z‖ ≤ 1 + max ‖a2‖ (max ‖a1‖ ‖a0‖) := by
  by_contra hcon
  push Not at hcon
  set m : ℝ := max ‖a2‖ (max ‖a1‖ ‖a0‖) with hm
  set r : ℝ := ‖z‖ with hr
  have hm0 : 0 ≤ m := le_trans (norm_nonneg _) (le_max_left _ _)
  have h2 : ‖a2‖ ≤ m := le_max_left _ _
  have h1 : ‖a1‖ ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
  have h0 : ‖a0‖ ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
  have hr1 : 1 + m < r := hcon
  have hr0 : 0 ≤ r := norm_nonneg _
  have hz' : z^3 = -(a2*z^2 + a1*z + a0) := by
    have : z^3 + a2*z^2 + a1*z + a0 = 0 := hz
    linear_combination this
  have hn : r^3 = ‖a2*z^2 + a1*z + a0‖ := by
    rw [hr, ← norm_pow, hz', norm_neg]
  have hb : ‖a2*z^2 + a1*z + a0‖ ≤ m*(r^2 + r + 1) := by
    calc ‖a2*z^2 + a1*z + a0‖ ≤ ‖a2*z^2‖ + ‖a1*z‖ + ‖a0‖ := norm_add₃_le
      _ = ‖a2‖*r^2 + ‖a1‖*r + ‖a0‖ := by simp [norm_pow, hr]
      _ ≤ m*r^2 + m*r + m := by gcongr
      _ = m*(r^2 + r + 1) := by ring
  have hpos : 0 < r^2 + r + 1 := by positivity
  have hlt : m*(r^2 + r + 1) < (r-1)*(r^2+r+1) :=
    mul_lt_mul_of_pos_right (by linarith) hpos
  nlinarith

/-- Sum form of the Cauchy bound. -/
theorem cubicRoots_norm_le_sum {a2 a1 a0 z : ℂ} (hz : z ∈ cubicRoots a2 a1 a0) :
    ‖z‖ ≤ 1 + (‖a2‖ + ‖a1‖ + ‖a0‖) := by
  have h := cubicRoots_norm_le hz
  have : max ‖a2‖ (max ‖a1‖ ‖a0‖) ≤ ‖a2‖ + ‖a1‖ + ‖a0‖ := by
    refine max_le (by linarith [norm_nonneg a1, norm_nonneg a0]) (max_le ?_ ?_) <;>
      linarith [norm_nonneg a2, norm_nonneg a1, norm_nonneg a0]
  linarith

/-! ### (P2) Root matching -/

/-- The cube-root step: if `‖(μ-z1)(μ-z2)(μ-z3)‖ ≤ δ` then some `zi` is within `δ^(1/3)` of `μ`. -/
theorem exists_factor_close (μ z1 z2 z3 : ℂ) (δ : ℝ)
    (h : ‖(μ-z1)*(μ-z2)*(μ-z3)‖ ≤ δ) :
    ∃ z ∈ ({z1, z2, z3} : Set ℂ), ‖μ - z‖ ≤ δ ^ ((1:ℝ)/3) := by
  have hδ : 0 ≤ δ := le_trans (norm_nonneg _) h
  set t : ℝ := δ ^ ((1:ℝ)/3) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hδ _
  have ht3 : t^3 = δ := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hδ]; norm_num
  by_contra hcon
  push Not at hcon
  have a1 : t < ‖μ - z1‖ := hcon z1 (by simp)
  have a2 : t < ‖μ - z2‖ := hcon z2 (by simp)
  have a3 : t < ‖μ - z3‖ := hcon z3 (by simp)
  have : t^3 < ‖(μ-z1)*(μ-z2)*(μ-z3)‖ := by
    rw [norm_mul, norm_mul]
    calc t^3 = t*t*t := by ring
      _ < _ := by gcongr
  linarith

/-- The difference of two monic cubics on `‖z‖ ≤ M` is bounded by the coefficient expression. -/
theorem cubic_diff_bound (a2 a1 a0 b2 b1 b0 z : ℂ) (M : ℝ) (hz : ‖z‖ ≤ M) :
    ‖(z^3 + a2*z^2 + a1*z + a0) - (z^3 + b2*z^2 + b1*z + b0)‖
      ≤ ‖a2 - b2‖*M^2 + ‖a1 - b1‖*M + ‖a0 - b0‖ := by
  have e : (z^3 + a2*z^2 + a1*z + a0) - (z^3 + b2*z^2 + b1*z + b0)
      = (a2-b2)*z^2 + (a1-b1)*z + (a0-b0) := by ring
  rw [e]
  have h2 : ‖z‖^2 ≤ M^2 := by gcongr
  calc ‖(a2-b2)*z^2 + (a1-b1)*z + (a0-b0)‖
      ≤ ‖(a2-b2)*z^2‖ + ‖(a1-b1)*z‖ + ‖a0-b0‖ := norm_add₃_le
    _ = ‖a2-b2‖*‖z‖^2 + ‖a1-b1‖*‖z‖ + ‖a0-b0‖ := by simp [norm_pow]
    _ ≤ _ := by gcongr

/-- `lem:helps-roots`, root matching (cubic case, one direction): if all roots of `P` lie in
`‖z‖ ≤ M` and `‖P(z) - Q(z)‖ ≤ δ` for `‖z‖ ≤ M`, then every root `μ` of `Q` with `‖μ‖ ≤ M`
lies within `δ^(1/3)` of a root of `P`. -/
theorem cubicRoots_match_aux {a2 a1 a0 b2 b1 b0 : ℂ} {M δ : ℝ}
    (hd : ∀ z : ℂ, ‖z‖ ≤ M →
      ‖(z^3 + a2*z^2 + a1*z + a0) - (z^3 + b2*z^2 + b1*z + b0)‖ ≤ δ)
    {μ : ℂ} (hμ : μ ∈ cubicRoots b2 b1 b0) (hμM : ‖μ‖ ≤ M) :
    ∃ z ∈ cubicRoots a2 a1 a0, ‖μ - z‖ ≤ δ ^ ((1:ℝ)/3) := by
  obtain ⟨z1, z2, z3, h⟩ := cubic_factor a2 a1 a0
  have hQ : μ^3 + b2*μ^2 + b1*μ + b0 = 0 := hμ
  have h1 := hd μ hμM
  rw [hQ, sub_zero, h] at h1
  obtain ⟨z, hz, hle⟩ := exists_factor_close μ z1 z2 z3 δ h1
  exact ⟨z, by rw [cubicRoots_eq h]; exact hz, hle⟩

/-- `lem:helps-roots`, root matching (cubic case).  Let `P`, `Q` be monic cubics all of whose roots
lie in `‖z‖ ≤ M`, and `‖P(z) - Q(z)‖ ≤ δ` for `‖z‖ ≤ M`.  Then every root of `Q` is within
`δ^(1/3)` of a root of `P`, and every root of `P` is within `δ^(1/3)` of a root of `Q`. -/
theorem cubicRoots_match {a2 a1 a0 b2 b1 b0 : ℂ} {M δ : ℝ}
    (hP : ∀ z ∈ cubicRoots a2 a1 a0, ‖z‖ ≤ M)
    (hQ : ∀ z ∈ cubicRoots b2 b1 b0, ‖z‖ ≤ M)
    (hd : ∀ z : ℂ, ‖z‖ ≤ M →
      ‖(z^3 + a2*z^2 + a1*z + a0) - (z^3 + b2*z^2 + b1*z + b0)‖ ≤ δ) :
    (∀ μ ∈ cubicRoots b2 b1 b0, ∃ z ∈ cubicRoots a2 a1 a0, ‖μ - z‖ ≤ δ ^ ((1:ℝ)/3)) ∧
    (∀ μ ∈ cubicRoots a2 a1 a0, ∃ z ∈ cubicRoots b2 b1 b0, ‖μ - z‖ ≤ δ ^ ((1:ℝ)/3)) := by
  refine ⟨fun μ hμ => cubicRoots_match_aux hd hμ (hQ μ hμ), fun μ hμ => ?_⟩
  refine cubicRoots_match_aux (a2 := b2) (a1 := b1) (a0 := b0) (b2 := a2) (b1 := a1)
    (b0 := a0) (fun z hz => ?_) hμ (hP μ hμ)
  rw [norm_sub_rev]; exact hd z hz

/-- Coefficient form of the root matching: take
`δ = ‖a2-b2‖ M² + ‖a1-b1‖ M + ‖a0-b0‖`. -/
theorem cubicRoots_match_coeff {a2 a1 a0 b2 b1 b0 : ℂ} {M : ℝ}
    (hP : ∀ z ∈ cubicRoots a2 a1 a0, ‖z‖ ≤ M)
    (hQ : ∀ z ∈ cubicRoots b2 b1 b0, ‖z‖ ≤ M) :
    (∀ μ ∈ cubicRoots b2 b1 b0, ∃ z ∈ cubicRoots a2 a1 a0,
      ‖μ - z‖ ≤ (‖a2 - b2‖*M^2 + ‖a1 - b1‖*M + ‖a0 - b0‖) ^ ((1:ℝ)/3)) ∧
    (∀ μ ∈ cubicRoots a2 a1 a0, ∃ z ∈ cubicRoots b2 b1 b0,
      ‖μ - z‖ ≤ (‖a2 - b2‖*M^2 + ‖a1 - b1‖*M + ‖a0 - b0‖) ^ ((1:ℝ)/3)) :=
  cubicRoots_match hP hQ (fun z hz => cubic_diff_bound a2 a1 a0 b2 b1 b0 z M hz)

/-! ### (P3) Largest real part and largest modulus -/

/-- Generic comparison of suprema over two finite nonempty sets that are `t`-matched, for a
function `f` that is 1-Lipschitz. -/
theorem sSup_image_close {S T : Set ℂ} (hS : S.Finite) (hSn : S.Nonempty)
    (hT : T.Finite) (hTn : T.Nonempty) (f : ℂ → ℝ) (hf : ∀ x y, |f x - f y| ≤ ‖x - y‖) {t : ℝ}
    (hTS : ∀ μ ∈ T, ∃ z ∈ S, ‖μ - z‖ ≤ t) (hST : ∀ μ ∈ S, ∃ z ∈ T, ‖μ - z‖ ≤ t) :
    |sSup (f '' S) - sSup (f '' T)| ≤ t := by
  have key : ∀ {S T : Set ℂ}, S.Finite → S.Nonempty → T.Finite → T.Nonempty →
      (∀ μ ∈ T, ∃ z ∈ S, ‖μ - z‖ ≤ t) → sSup (f '' T) ≤ sSup (f '' S) + t := by
    intro S T hS hSn hT hTn h
    obtain ⟨μ, hμ, hμe⟩ := (hTn.image f).csSup_mem (hT.image f)
    obtain ⟨z, hz, hzt⟩ := h μ hμ
    have h1 : f z ≤ sSup (f '' S) := le_csSup (hS.image f).bddAbove ⟨z, hz, rfl⟩
    have h2 : f μ - f z ≤ t := le_trans (le_abs_self _) (le_trans (hf μ z) hzt)
    rw [← hμe]; linarith
  have a := key hS hSn hT hTn hTS
  have b := key hT hTn hS hSn hST
  rw [abs_le]; constructor <;> linarith

theorem sSup_re_close {S T : Set ℂ} (hS : S.Finite) (hSn : S.Nonempty)
    (hT : T.Finite) (hTn : T.Nonempty) {t : ℝ}
    (hTS : ∀ μ ∈ T, ∃ z ∈ S, ‖μ - z‖ ≤ t) (hST : ∀ μ ∈ S, ∃ z ∈ T, ‖μ - z‖ ≤ t) :
    |maxRe S - maxRe T| ≤ t := by
  refine sSup_image_close hS hSn hT hTn Complex.re (fun x y => ?_) hTS hST
  rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _

theorem sSup_norm_close {S T : Set ℂ} (hS : S.Finite) (hSn : S.Nonempty)
    (hT : T.Finite) (hTn : T.Nonempty) {t : ℝ}
    (hTS : ∀ μ ∈ T, ∃ z ∈ S, ‖μ - z‖ ≤ t) (hST : ∀ μ ∈ S, ∃ z ∈ T, ‖μ - z‖ ≤ t) :
    |maxNorm S - maxNorm T| ≤ t :=
  sSup_image_close hS hSn hT hTn (fun z => ‖z‖) (fun x y => abs_norm_sub_norm_le x y) hTS hST

/-- `lem:helps-roots`, last claim (cubic case), largest real part: under the hypotheses of the
matching statement, the largest real parts of the roots differ by at most `δ^(1/3)`. -/
theorem maxRe_cubicRoots_close {a2 a1 a0 b2 b1 b0 : ℂ} {M δ : ℝ}
    (hP : ∀ z ∈ cubicRoots a2 a1 a0, ‖z‖ ≤ M)
    (hQ : ∀ z ∈ cubicRoots b2 b1 b0, ‖z‖ ≤ M)
    (hd : ∀ z : ℂ, ‖z‖ ≤ M →
      ‖(z^3 + a2*z^2 + a1*z + a0) - (z^3 + b2*z^2 + b1*z + b0)‖ ≤ δ) :
    |maxRe (cubicRoots a2 a1 a0) - maxRe (cubicRoots b2 b1 b0)| ≤ δ ^ ((1:ℝ)/3) := by
  obtain ⟨h1, h2⟩ := cubicRoots_match hP hQ hd
  exact sSup_re_close (cubicRoots_finite _ _ _) (cubicRoots_nonempty _ _ _)
    (cubicRoots_finite _ _ _) (cubicRoots_nonempty _ _ _) h1 h2

/-- `lem:helps-roots`, last claim (cubic case), largest modulus. -/
theorem maxNorm_cubicRoots_close {a2 a1 a0 b2 b1 b0 : ℂ} {M δ : ℝ}
    (hP : ∀ z ∈ cubicRoots a2 a1 a0, ‖z‖ ≤ M)
    (hQ : ∀ z ∈ cubicRoots b2 b1 b0, ‖z‖ ≤ M)
    (hd : ∀ z : ℂ, ‖z‖ ≤ M →
      ‖(z^3 + a2*z^2 + a1*z + a0) - (z^3 + b2*z^2 + b1*z + b0)‖ ≤ δ) :
    |maxNorm (cubicRoots a2 a1 a0) - maxNorm (cubicRoots b2 b1 b0)| ≤ δ ^ ((1:ℝ)/3) := by
  obtain ⟨h1, h2⟩ := cubicRoots_match hP hQ hd
  exact sSup_norm_close (cubicRoots_finite _ _ _) (cubicRoots_nonempty _ _ _)
    (cubicRoots_finite _ _ _) (cubicRoots_nonempty _ _ _) h1 h2

/-- Coefficient form of the largest-real-part bound. -/
theorem maxRe_cubicRoots_close_coeff {a2 a1 a0 b2 b1 b0 : ℂ} {M : ℝ}
    (hP : ∀ z ∈ cubicRoots a2 a1 a0, ‖z‖ ≤ M)
    (hQ : ∀ z ∈ cubicRoots b2 b1 b0, ‖z‖ ≤ M) :
    |maxRe (cubicRoots a2 a1 a0) - maxRe (cubicRoots b2 b1 b0)|
      ≤ (‖a2 - b2‖*M^2 + ‖a1 - b1‖*M + ‖a0 - b0‖) ^ ((1:ℝ)/3) :=
  maxRe_cubicRoots_close hP hQ (fun z hz => cubic_diff_bound a2 a1 a0 b2 b1 b0 z M hz)

/-- Coefficient form of the largest-modulus bound. -/
theorem maxNorm_cubicRoots_close_coeff {a2 a1 a0 b2 b1 b0 : ℂ} {M : ℝ}
    (hP : ∀ z ∈ cubicRoots a2 a1 a0, ‖z‖ ≤ M)
    (hQ : ∀ z ∈ cubicRoots b2 b1 b0, ‖z‖ ≤ M) :
    |maxNorm (cubicRoots a2 a1 a0) - maxNorm (cubicRoots b2 b1 b0)|
      ≤ (‖a2 - b2‖*M^2 + ‖a1 - b1‖*M + ‖a0 - b0‖) ^ ((1:ℝ)/3) :=
  maxNorm_cubicRoots_close hP hQ (fun z hz => cubic_diff_bound a2 a1 a0 b2 b1 b0 z M hz)

/-! ### (P4) Continuity of the continuum Perron rate -/

section Continuity

open Filter Topology

/-- The continuum characteristic roots are the roots of a monic cubic. -/
theorem continuumCharacteristicRoots_eq_cubicRoots (δ u : ℝ) :
    continuumCharacteristicRoots δ u =
      cubicRoots 3 (2 + 4*(δ:ℂ)) (4*(δ:ℂ)*(1-(u:ℂ))) := rfl

/-- `r_c = - max Re` of the cubic roots. -/
theorem continuumPerronRate_eq (δ u : ℝ) :
    continuumPerronRate δ u = -maxRe (cubicRoots 3 (2 + 4*(δ:ℂ)) (4*(δ:ℂ)*(1-(u:ℂ)))) := rfl

/-- A radius containing all continuum characteristic roots when `|δ| ≤ D`, `|u| ≤ U`. -/
def rateRadius (D U : ℝ) : ℝ := 1 + (3 + (2 + 4*D) + 4*D*(1+U))

theorem continuumRoots_norm_le {δ u D U : ℝ} (hδ : |δ| ≤ D) (hu : |u| ≤ U) {z : ℂ}
    (hz : z ∈ continuumCharacteristicRoots δ u) : ‖z‖ ≤ rateRadius D U := by
  have h := cubicRoots_norm_le_sum (a2 := 3) (a1 := 2 + 4*(δ:ℂ)) (a0 := 4*(δ:ℂ)*(1-(u:ℂ))) hz
  have hD : 0 ≤ D := le_trans (abs_nonneg _) hδ
  have hU : 0 ≤ U := le_trans (abs_nonneg _) hu
  have e1 : (2 + 4*(δ:ℂ)) = ((2 + 4*δ : ℝ) : ℂ) := by push_cast; ring
  have e2 : (4*(δ:ℂ)*(1-(u:ℂ))) = ((4*δ*(1-u) : ℝ) : ℂ) := by push_cast; ring
  have n1 : ‖(2 + 4*(δ:ℂ))‖ ≤ 2 + 4*D := by
    rw [e1, Complex.norm_real, Real.norm_eq_abs]
    obtain ⟨l, r⟩ := abs_le.mp hδ
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have n2 : ‖(4*(δ:ℂ)*(1-(u:ℂ)))‖ ≤ 4*D*(1+U) := by
    rw [e2, Complex.norm_real, Real.norm_eq_abs]
    have h1u : |1 - u| ≤ 1 + U := by
      obtain ⟨l, r⟩ := abs_le.mp hu
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    calc |4*δ*(1-u)| = 4*|δ| *|1-u| := by rw [abs_mul, abs_mul]; norm_num
      _ ≤ 4*D*(1+U) := by gcongr
  have n3 : ‖(3:ℂ)‖ = 3 := by norm_num
  unfold rateRadius
  linarith

/-- Quantitative local modulus for `r_c`: for `|δ-δ₀| ≤ 1`, `|u-u₀| ≤ 1`,
`|r_c(δ,u) - r_c(δ₀,u₀)| ≤ (4|δ-δ₀| M + 4|δ(1-u) - δ₀(1-u₀)| M²)^(1/3)` with
`M = rateRadius (|δ₀|+1) (|u₀|+1)`.  This is `lem:helps-roots` applied to the continuum cubic. -/
theorem continuumPerronRate_close (δ u δ0 u0 : ℝ) (h1 : |δ - δ0| ≤ 1) (h2 : |u - u0| ≤ 1) :
    |continuumPerronRate δ u - continuumPerronRate δ0 u0|
      ≤ (4*|δ-δ0| *rateRadius (|δ0|+1) (|u0|+1)
          + 4*|δ*(1-u) - δ0*(1-u0)|) ^ ((1:ℝ)/3) := by
  set M := rateRadius (|δ0|+1) (|u0|+1) with hM
  have hδ : |δ| ≤ |δ0| + 1 := by
    have := abs_sub_abs_le_abs_sub δ δ0; linarith
  have hu : |u| ≤ |u0| + 1 := by
    have := abs_sub_abs_le_abs_sub u u0; linarith
  have hδ0 : |δ0| ≤ |δ0| + 1 := by linarith
  have hu0 : |u0| ≤ |u0| + 1 := by linarith
  have hP : ∀ z ∈ cubicRoots 3 (2 + 4*(δ:ℂ)) (4*(δ:ℂ)*(1-(u:ℂ))), ‖z‖ ≤ M :=
    fun z hz => continuumRoots_norm_le hδ hu hz
  have hQ : ∀ z ∈ cubicRoots 3 (2 + 4*(δ0:ℂ)) (4*(δ0:ℂ)*(1-(u0:ℂ))), ‖z‖ ≤ M :=
    fun z hz => continuumRoots_norm_le hδ0 hu0 hz
  have h := maxRe_cubicRoots_close_coeff hP hQ
  have e1 : (2 + 4*(δ:ℂ)) - (2 + 4*(δ0:ℂ)) = ((4*(δ-δ0) : ℝ) : ℂ) := by push_cast; ring
  have e2 : (4*(δ:ℂ)*(1-(u:ℂ))) - (4*(δ0:ℂ)*(1-(u0:ℂ)))
      = ((4*(δ*(1-u) - δ0*(1-u0)) : ℝ) : ℂ) := by push_cast; ring
  have n1 : ‖(2 + 4*(δ:ℂ)) - (2 + 4*(δ0:ℂ))‖ = 4*|δ-δ0| := by
    rw [e1, Complex.norm_real, Real.norm_eq_abs, abs_mul]; norm_num
  have n2 : ‖(4*(δ:ℂ)*(1-(u:ℂ))) - (4*(δ0:ℂ)*(1-(u0:ℂ)))‖ = 4*|δ*(1-u) - δ0*(1-u0)| := by
    rw [e2, Complex.norm_real, Real.norm_eq_abs, abs_mul]; norm_num
  rw [n1, n2, sub_self, norm_zero, zero_mul, zero_add] at h
  rw [continuumPerronRate_eq, continuumPerronRate_eq]
  have : -maxRe (cubicRoots 3 (2 + 4*(δ:ℂ)) (4*(δ:ℂ)*(1-(u:ℂ))))
      - -maxRe (cubicRoots 3 (2 + 4*(δ0:ℂ)) (4*(δ0:ℂ)*(1-(u0:ℂ))))
      = -(maxRe (cubicRoots 3 (2 + 4*(δ:ℂ)) (4*(δ:ℂ)*(1-(u:ℂ))))
        - maxRe (cubicRoots 3 (2 + 4*(δ0:ℂ)) (4*(δ0:ℂ)*(1-(u0:ℂ))))) := by ring
  rw [this, abs_neg]
  exact h

/-- Continuity of `r_c` on all of `ℝ × ℝ` (`lem:helps-transfer`, Step 6).  The cubic always has a
root, so no hypotheses on `(δ,u)` are needed. -/
theorem continuous_continuumPerronRate :
    Continuous (fun p : ℝ × ℝ => continuumPerronRate p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨δ0, u0⟩
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  set M := rateRadius (|δ0|+1) (|u0|+1) with hM
  let g : ℝ × ℝ → ℝ := fun p =>
    (4*|p.1-δ0| *M + 4*|p.1*(1-p.2) - δ0*(1-u0)|) ^ ((1:ℝ)/3)
  have hgc : Continuous g := by
    refine Continuous.rpow_const ?_ (fun _ => Or.inr (by norm_num))
    fun_prop
  have hg : Tendsto g (𝓝 (δ0, u0)) (𝓝 0) := by
    have := hgc.tendsto (δ0, u0)
    have hz : g (δ0, u0) = 0 := by
      simp only [g, sub_self, abs_zero, mul_zero, zero_mul, add_zero]
      exact Real.zero_rpow (by norm_num)
    rwa [hz] at this
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hg
  filter_upwards [Metric.ball_mem_nhds (δ0, u0) one_pos] with p hp
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hp
  simp only [Real.dist_eq] at hp ⊢
  exact continuumPerronRate_close p.1 p.2 δ0 u0 hp.1.le hp.2.le

/-- On a compact subset of `(0,∞) × [0,1)`, `r_c` is bounded below by a positive constant
(`lem:helps-transfer`, Step 6). -/
theorem continuumPerronRate_pos_lower_bound {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hsub : K ⊆ Set.Ioi 0 ×ˢ Set.Ico 0 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ K, c ≤ continuumPerronRate p.1 p.2 := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, by simp [he]⟩
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne continuous_continuumPerronRate.continuousOn
  have hs := hsub hp
  refine ⟨continuumPerronRate p.1 p.2, ?_, fun q hq => hmin hq⟩
  exact continuumPerronRate_pos p.1 p.2 hs.1 hs.2.1 hs.2.2

end Continuity

end

end SparseSGD.Scaling.Helps
