import Mathlib
import SparseSGD.Scaling.Helps.RootPerturbation
import SparseSGD.Scaling.Helps.StepMatrix

/-!
# Per-step rate as `ε → 0` (v2 `lem:helps-transfer`)

Formalizes `lem:helps-transfer` of `paper/appendix/momentum_helps.tex`:
for `β = 1 - ε`, `w = ε² Δ` and noise feedback `u_n`, the per-step rate `Λ = perStepRate p`
satisfies `Λ = ε r_c(Δ, u_n) + O(ε^{4/3})` and `Λ = ε r_c(Δ, u_n + u_c) + O(ε^{4/3})`,
uniformly on `{ε ≤ ε₀, Δ ≤ D, u_n ≤ cΔ}`.

**Route.**  We do not use the matrices `A`, `G` of the tex.  The retention-clock substitution
`z = 1 + ε μ` (S8, `StepMatrix.lean`) turns the closed-form characteristic polynomial of the
step map into `ε³ (χ(μ;Δ,u_n) + ε R(μ))`, a monic cubic in `μ` whose coefficients differ from those
of `χ` by `ε` times quantities bounded on the parameter box.  The root-perturbation bound
(`RootPerturbation.lean`, v2 `lem:helps-roots`) and a logarithm estimate finish.

**Deviation from the tex (a simplification).**  The closed-form route only needs
`u_n ≤ U` on the parameter box (`helps_transfer_box`), not `u_n ≤ cΔ`: the tex hypothesis
`u_n ≤ cΔ` is used there only to bound the entry `2u_n/Δ` of the matrix `A`, which does not
occur here.  The tex statement is the special case `U = cD` (`helps_transfer`).  For the compact
form we nevertheless pass through `u_n ≤ cΔ`, `c = 1/Δ_min`, exactly as in the tex, although
`U = 1` would also do.
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD

noncomputable section

/-! ### The transfer cubic (Tr1) -/

/-- Coefficient of `μ²` in the remainder `R` of the retention-clock substitution. -/
def transferR2 (eps Delta un : ℝ) : ℝ :=
  -Delta ^ 2 * eps ^ 2 - 2 * Delta * eps * un - 2 * Delta * eps + 4 * Delta - 1

/-- Coefficient of `μ` in the remainder `R` of the retention-clock substitution. -/
def transferR1 (eps Delta un : ℝ) : ℝ :=
  -Delta ^ 2 * eps ^ 2 - Delta ^ 2 * eps + 2 * Delta * eps * un - 2 * Delta * eps
    - 6 * Delta * un + 2 * Delta - 1

/-- Constant coefficient of the remainder `R` of the retention-clock substitution. -/
def transferR0 (eps Delta un : ℝ) : ℝ :=
  -Delta ^ 2 * eps + 2 * Delta * un - 2 * Delta

/-- `lem:helps-transfer`: the remainder `R` is the quadratic `r2 μ² + r1 μ + r0`. -/
theorem transferRemainder_eq (eps Delta un : ℝ) (mu : ℂ) :
    transferRemainder (eps : ℂ) (Delta : ℂ) (un : ℂ) mu =
      (transferR2 eps Delta un : ℂ) * mu ^ 2 + (transferR1 eps Delta un : ℂ) * mu
        + (transferR0 eps Delta un : ℂ) := by
  simp only [transferRemainder, transferR2, transferR1, transferR0]
  push_cast; ring

/-- The coefficients of the transfer cubic `Q_ε = χ + ε R`. -/
def transferQ2 (eps Delta un : ℝ) : ℝ := 3 + eps * transferR2 eps Delta un
def transferQ1 (eps Delta un : ℝ) : ℝ := 2 + 4 * Delta + eps * transferR1 eps Delta un
def transferQ0 (eps Delta un : ℝ) : ℝ := 4 * Delta * (1 - un) + eps * transferR0 eps Delta un

/-- The step parameters `β = 1 - ε`, `w = ε² Δ`, noise feedback `u_n`, no additive noise. -/
abbrev transferParams (eps Delta un : ℝ) : Params := ⟨1 - eps, eps ^ 2 * Delta, un, 0⟩

/-- `lem:helps-transfer`: `stepCharPoly (1-ε) (ε²Δ) u_n (1 + ε μ) = ε³ · Q_ε(μ)`. -/
theorem stepCharPoly_transfer (eps Delta un : ℝ) (mu : ℂ) :
    stepCharPoly (1 - eps) (eps ^ 2 * Delta) un (1 + (eps : ℂ) * mu) =
      (eps : ℂ) ^ 3 * (mu ^ 3 + (transferQ2 eps Delta un : ℂ) * mu ^ 2
        + (transferQ1 eps Delta un : ℂ) * mu + (transferQ0 eps Delta un : ℂ)) := by
  rw [stepCharPoly_retention_clock, transferRemainder_eq]
  simp only [chiC, transferQ2, transferQ1, transferQ0]
  push_cast; ring

/-- (Tr1) `lem:helps-transfer`, transfer cubic: for `β = 1-ε`, `w = ε²Δ` (`ε ≠ 0`),
`z` is an eigenvalue of the step map iff `z = 1 + ε μ` with `μ` a root of the monic cubic
`μ³ + (3+ε r2) μ² + (2+4Δ+ε r1) μ + (4Δ(1-u_n)+ε r0)`, whose coefficients are those of
`χ(·;Δ,u_n)` plus `ε` times the coefficients `r2, r1, r0` of `transferRemainder`. -/
theorem mem_stepRoots_transfer_iff (eps Delta un : ℝ) (he : eps ≠ 0) (z : ℂ) :
    z ∈ stepRoots (transferParams eps Delta un) ↔
      ∃ mu ∈ cubicRoots (transferQ2 eps Delta un : ℂ) (transferQ1 eps Delta un : ℂ)
        (transferQ0 eps Delta un : ℂ), z = 1 + (eps : ℂ) * mu := by
  have he' : (eps : ℂ) ≠ 0 := by exact_mod_cast he
  have he3 : (eps : ℂ) ^ 3 ≠ 0 := pow_ne_zero 3 he'
  constructor
  · intro hz
    refine ⟨(z - 1) / eps, ?_, ?_⟩
    · have hz' : stepCharPoly (1 - eps) (eps ^ 2 * Delta) un z = 0 := hz
      have hz1 : z = 1 + (eps : ℂ) * ((z - 1) / eps) := by field_simp; ring
      rw [hz1, stepCharPoly_transfer] at hz'
      exact (mul_eq_zero.1 hz').resolve_left he3
    · field_simp; ring
  · rintro ⟨mu, hmu, rfl⟩
    have hmu' : mu ^ 3 + (transferQ2 eps Delta un : ℂ) * mu ^ 2
        + (transferQ1 eps Delta un : ℂ) * mu + (transferQ0 eps Delta un : ℂ) = 0 := hmu
    show stepCharPoly (1 - eps) (eps ^ 2 * Delta) un (1 + (eps : ℂ) * mu) = 0
    rw [stepCharPoly_transfer, hmu', mul_zero]

/-! ### Logarithm estimate -/

/-- `|log(1+x) - x| ≤ 2 x²` for `|x| ≤ 1/2`. -/
theorem abs_log_one_add_sub_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have hx1 : |-x| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 1
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one, sub_neg_eq_add,
    abs_neg] at h
  have h2 : |Real.log (1 + x) - x| = |-x + Real.log (1 + x)| := by
    rw [show Real.log (1 + x) - x = -x + Real.log (1 + x) by ring]
  rw [h2]
  refine h.trans ?_
  have hxa : 0 ≤ |x| := abs_nonneg x
  have hden : (1 : ℝ) / 2 ≤ 1 - |x| := by linarith
  have hsq : |x| ^ (1 + 1) = x ^ 2 := sq_abs x
  rw [hsq, div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg x]

/-- The logarithm of the modulus of `1 + ε μ` is `ε Re μ` up to `6 M² ε²`, when
`‖μ‖ ≤ M` and `ε M ≤ 1/8`. -/
theorem abs_log_norm_one_add_le {eps M : ℝ} {mu : ℂ} (he : 0 ≤ eps) (hM : ‖mu‖ ≤ M)
    (h8 : eps * M ≤ 1 / 8) :
    |Real.log ‖1 + (eps : ℂ) * mu‖ - eps * mu.re| ≤ 6 * M ^ 2 * eps ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM
  set t : ℝ := eps * M with ht
  have ht0 : 0 ≤ t := mul_nonneg he hM0
  have hre : |mu.re| ≤ M := le_trans (Complex.abs_re_le_norm mu) hM
  have hnsq : ‖mu‖ ^ 2 = mu.re ^ 2 + mu.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsq : ‖1 + (eps : ℂ) * mu‖ ^ 2 = 1 + (2 * eps * mu.re + eps ^ 2 * ‖mu‖ ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply, hnsq]
    simp
    ring
  set x : ℝ := 2 * eps * mu.re + eps ^ 2 * ‖mu‖ ^ 2 with hx
  have hxa : |2 * eps * mu.re| ≤ 2 * t := by
    rw [abs_mul, abs_mul, abs_of_nonneg he, abs_two]
    have := mul_le_mul_of_nonneg_left hre he
    rw [ht]; linarith
  have hx2 : eps ^ 2 * ‖mu‖ ^ 2 ≤ t ^ 2 := by
    rw [ht, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hM 2) (sq_nonneg _)
  have hx2' : 0 ≤ eps ^ 2 * ‖mu‖ ^ 2 := by positivity
  have hxabs : |x| ≤ 2 * t + t ^ 2 := by
    rw [hx]
    calc |2 * eps * mu.re + eps ^ 2 * ‖mu‖ ^ 2|
        ≤ |2 * eps * mu.re| + |eps ^ 2 * ‖mu‖ ^ 2| := abs_add_le _ _
      _ ≤ 2 * t + t ^ 2 := by rw [abs_of_nonneg hx2']; linarith
  have hxh : |x| ≤ 1 / 2 := by nlinarith
  have hx_sq : x ^ 2 ≤ 5 * t ^ 2 := by
    have h1 : x ^ 2 ≤ (2 * t + t ^ 2) ^ 2 := by
      have := abs_le.1 hxabs
      exact sq_le_sq' this.1 this.2
    have h2 : (2 + t) ^ 2 ≤ 5 := by nlinarith
    have h3 : (2 * t + t ^ 2) ^ 2 = t ^ 2 * (2 + t) ^ 2 := by ring
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg t)
    nlinarith
  have hlog : Real.log ‖1 + (eps : ℂ) * mu‖ = Real.log (1 + x) / 2 := by
    have h2 : Real.log (‖1 + (eps : ℂ) * mu‖ ^ 2) = 2 * Real.log ‖1 + (eps : ℂ) * mu‖ := by
      simp
    rw [hsq] at h2
    linarith
  have hb := abs_log_one_add_sub_le hxh
  have hkey : Real.log ‖1 + (eps : ℂ) * mu‖ - eps * mu.re
      = (Real.log (1 + x) - x) / 2 + eps ^ 2 * ‖mu‖ ^ 2 / 2 := by
    rw [hlog, hx]; ring
  rw [hkey]
  have hb' := abs_le.1 hb
  rw [abs_le]
  have hMt : M ^ 2 * eps ^ 2 = t ^ 2 := by rw [ht]; ring
  constructor <;> nlinarith

/-! ### From roots to the rate -/

/-- If the eigenvalues of the step map are `1 + ε μ`, `μ` ranging over a monic cubic's roots with
`‖μ‖ ≤ M` and `ε M ≤ 1/8`, then `perStepRate = -ε · maxRe` up to `6 M² ε²`. -/
theorem perStepRate_close_maxRe (p : Params) {eps M : ℝ} {a2 a1 a0 : ℂ} (he : 0 < eps)
    (h8 : eps * M ≤ 1 / 8)
    (hM : ∀ mu ∈ cubicRoots a2 a1 a0, ‖mu‖ ≤ M)
    (hiff : ∀ z, z ∈ stepRoots p ↔ ∃ mu ∈ cubicRoots a2 a1 a0, z = 1 + (eps : ℂ) * mu) :
    |perStepRate p + eps * maxRe (cubicRoots a2 a1 a0)| ≤ 6 * M ^ 2 * eps ^ 2 := by
  have hfin := (cubicRoots_finite a2 a1 a0).image Complex.re
  have hne := (cubicRoots_nonempty a2 a1 a0).image Complex.re
  obtain ⟨z1, hz1, hz1e⟩ := stepRadius_attained p
  obtain ⟨mu1, hmu1, rfl⟩ := (hiff z1).1 hz1
  obtain ⟨mu0', hmu0', hmu0e⟩ := hne.csSup_mem hfin
  have hmaxRe : maxRe (cubicRoots a2 a1 a0) = mu0'.re := hmu0e.symm
  have hle1 : mu1.re ≤ maxRe (cubicRoots a2 a1 a0) :=
    le_csSup hfin.bddAbove ⟨mu1, hmu1, rfl⟩
  have hM1 := hM mu1 hmu1
  have hM0 := hM mu0' hmu0'
  have b1 := abs_log_norm_one_add_le he.le hM1 h8
  have b0 := abs_log_norm_one_add_le he.le hM0 h8
  have hMn : 0 ≤ M := le_trans (norm_nonneg _) hM1
  have hpos0 : 0 < ‖1 + (eps : ℂ) * mu0'‖ := by
    have h1 : ‖(eps : ℂ) * mu0'‖ ≤ 1 / 8 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
      calc eps * ‖mu0'‖ ≤ eps * M := by gcongr
        _ ≤ 1 / 8 := h8
    have := norm_sub_norm_le (1 : ℂ) (-((eps : ℂ) * mu0'))
    have h2 : ‖(1 : ℂ) - -((eps : ℂ) * mu0')‖ ≤ ‖(1 : ℂ)‖ + ‖-((eps : ℂ) * mu0')‖ := norm_sub_le _ _
    have h3 : ‖(1 : ℂ)‖ - ‖(eps : ℂ) * mu0'‖ ≤ ‖1 + (eps : ℂ) * mu0'‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-((eps : ℂ) * mu0'))
      rw [norm_neg, sub_neg_eq_add] at this
      exact this
    rw [norm_one] at h3
    linarith
  have hmem0 : (1 + (eps : ℂ) * mu0') ∈ stepRoots p := (hiff _).2 ⟨mu0', hmu0', rfl⟩
  have hle0 := norm_le_stepRadius p hmem0
  rw [hz1e] at b1
  have hlogle := Real.log_le_log hpos0 hle0
  unfold perStepRate
  rw [hz1e] at *
  rw [hmaxRe]
  have b1' := abs_le.1 b1
  have b0' := abs_le.1 b0
  rw [abs_le]
  have : eps * mu1.re ≤ eps * mu0'.re := mul_le_mul_of_nonneg_left (hmaxRe ▸ hle1) he.le
  constructor <;> nlinarith

/-! ### Real-power bookkeeping -/

/-- `ε · δ^(1/3) ≤ K^(1/3) ε^(4/3)` if `0 ≤ δ ≤ K ε`. -/
theorem eps_mul_rpow_third_le {K delta eps : ℝ} (hK : 0 ≤ K) (he : 0 < eps) (hδ0 : 0 ≤ delta)
    (hδ : delta ≤ K * eps) :
    eps * delta ^ ((1 : ℝ) / 3) ≤ K ^ ((1 : ℝ) / 3) * eps ^ ((4 : ℝ) / 3) := by
  have h1 : delta ^ ((1 : ℝ) / 3) ≤ (K * eps) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hδ0 hδ (by norm_num)
  rw [Real.mul_rpow hK he.le] at h1
  have h2 : eps ^ ((4 : ℝ) / 3) = eps * eps ^ ((1 : ℝ) / 3) := by
    rw [show (4 : ℝ) / 3 = 1 + 1 / 3 by norm_num, Real.rpow_add he, Real.rpow_one]
  rw [h2]
  have := mul_le_mul_of_nonneg_left h1 he.le
  nlinarith

/-- `ε² ≤ ε^(4/3)` for `0 < ε ≤ 1`. -/
theorem sq_le_rpow_four_thirds {eps : ℝ} (he : 0 < eps) (he1 : eps ≤ 1) :
    eps ^ 2 ≤ eps ^ ((4 : ℝ) / 3) := by
  have h2 : eps ^ ((4 : ℝ) / 3) = eps * eps ^ ((1 : ℝ) / 3) := by
    rw [show (4 : ℝ) / 3 = 1 + 1 / 3 by norm_num, Real.rpow_add he, Real.rpow_one]
  have h3 : eps ^ (1 : ℝ) ≤ eps ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_ge he he1 (by norm_num)
  rw [Real.rpow_one] at h3
  rw [h2, pow_two]
  exact mul_le_mul_of_nonneg_left h3 he.le

/-- (Tr2, second bound) The total feedback `u = u_n + u_c` changes the Perron rate by at most
`(4 D² ε)^(1/3)` for `Δ ≤ D`, `ε (1+D) ≤ 1` (`lem:helps-transfer`, Step 5). -/
theorem transfer_total_load_close {D Lam eps Delta un C0 : ℝ} (hD : 0 < D) (he : 0 < eps)
    (heD' : eps * (1 + D) ≤ 1) (hΔ0 : 0 < Delta) (hΔD : Delta ≤ D)
    (hfirst : |Lam - eps * continuumPerronRate Delta un| ≤ C0 * eps ^ ((4 : ℝ) / 3)) :
    |Lam - eps * continuumPerronRate Delta (un + (transferParams eps Delta un).curvature)|
      ≤ (C0 + (4 * D ^ 2) ^ ((1 : ℝ) / 3)) * eps ^ ((4 : ℝ) / 3) := by
  have he1 : eps ≤ 1 := by nlinarith [mul_nonneg he.le hD.le]
  set uc : ℝ := (transferParams eps Delta un).curvature with huc
  have huc_eq : uc = eps ^ 2 * Delta / (2 * (1 + (1 - eps))) := rfl
  have hden : 0 < 2 * (1 + (1 - eps)) := by linarith
  have huc0 : 0 ≤ uc := by rw [huc_eq]; positivity
  have huc1 : uc ≤ eps ^ 2 * D := by
    rw [huc_eq, div_le_iff₀ hden]
    have : eps ^ 2 * Delta ≤ eps ^ 2 * D := by gcongr
    nlinarith [sq_nonneg eps, mul_nonneg (sq_nonneg eps) hD.le]
  have hucle : uc ≤ 1 := by
    have : eps ^ 2 * D ≤ 1 := by nlinarith [mul_nonneg he.le hD.le]
    linarith
  have hcl := continuumPerronRate_close Delta (un + uc) Delta un (by simp)
    (by rw [add_sub_cancel_left, abs_of_nonneg huc0]; exact hucle)
  have hexp : 4 * |Delta - Delta| * rateRadius (|Delta| + 1) (|un| + 1)
      + 4 * |Delta * (1 - (un + uc)) - Delta * (1 - un)| = 4 * Delta * uc := by
    rw [sub_self, abs_zero,
      show Delta * (1 - (un + uc)) - Delta * (1 - un) = -(Delta * uc) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg hΔ0.le huc0)]
    ring
  rw [hexp] at hcl
  have h4 : 4 * Delta * uc ≤ (4 * D ^ 2) * eps := by
    have h1 : Delta * uc ≤ D * (eps ^ 2 * D) := mul_le_mul hΔD huc1 huc0 hD.le
    have h2 : eps ^ 2 ≤ eps := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg D)
    nlinarith
  have h40 : 0 ≤ 4 * Delta * uc := by positivity
  have e1 := eps_mul_rpow_third_le (by positivity : (0 : ℝ) ≤ 4 * D ^ 2) he h40 h4
  have hc2 := abs_le.1 hcl
  have hf := abs_le.1 hfirst
  rw [abs_le]
  have m1 := mul_le_mul_of_nonneg_left hc2.1 he.le
  have m2 := mul_le_mul_of_nonneg_left hc2.2 he.le
  constructor <;> linarith

/-! ### Uniform bound on the parameter box (Tr2, strengthened) -/

/-- (Tr2, strengthened) `lem:helps-transfer` on the box `{ε ≤ ε₀, Δ ≤ D, u_n ≤ U}`.
The tex hypothesis `u_n ≤ c Δ` is not needed: the closed-form characteristic polynomial has no
entry `2u_n/Δ`.  Here `p = ⟨1-ε, ε²Δ, u_n, 0⟩`, `Λ = perStepRate p`. -/
theorem helps_transfer_box (D U : ℝ) (hD : 0 < D) (hU : 0 ≤ U) :
    ∃ eps0 : ℝ, eps0 ∈ Set.Ioc (0 : ℝ) (1 / 2) ∧ ∃ C : ℝ,
      ∀ eps ∈ Set.Ioc (0 : ℝ) eps0, ∀ Delta ∈ Set.Ioc (0 : ℝ) D, ∀ un ∈ Set.Icc (0 : ℝ) U,
        |perStepRate (transferParams eps Delta un) - eps * continuumPerronRate Delta un|
            ≤ C * eps ^ ((4 : ℝ) / 3) ∧
        |perStepRate (transferParams eps Delta un)
            - eps * continuumPerronRate Delta (un + (transferParams eps Delta un).curvature)|
            ≤ C * eps ^ ((4 : ℝ) / 3) := by
  -- bound on the remainder coefficients (continuous on a compact box)
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ eps ∈ Set.Icc (0 : ℝ) (1 / 2),
      ∀ Delta ∈ Set.Icc (0 : ℝ) D, ∀ un ∈ Set.Icc (0 : ℝ) U,
        |transferR2 eps Delta un| ≤ B ∧ |transferR1 eps Delta un| ≤ B
          ∧ |transferR0 eps Delta un| ≤ B := by
    have hc : IsCompact (Set.Icc (0 : ℝ) (1 / 2) ×ˢ Set.Icc (0 : ℝ) D ×ˢ Set.Icc (0 : ℝ) U) :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    have hcont : Continuous (fun q : ℝ × ℝ × ℝ =>
        |transferR2 q.1 q.2.1 q.2.2| + |transferR1 q.1 q.2.1 q.2.2|
          + |transferR0 q.1 q.2.1 q.2.2|) := by
      unfold transferR2 transferR1 transferR0; fun_prop
    obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro eps he Delta hΔ un hu
    have h := hB (eps, Delta, un) ⟨he, hΔ, hu⟩
    simp only [Real.norm_eq_abs] at h
    have h' := le_trans (le_abs_self _) h
    have a2 := abs_nonneg (transferR2 eps Delta un)
    have a1 := abs_nonneg (transferR1 eps Delta un)
    have a0 := abs_nonneg (transferR0 eps Delta un)
    have hm : B ≤ max B 0 := le_max_left _ _
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  -- a common radius for the roots of `χ(·;Δ,u_n)` and of the transfer cubic
  set M : ℝ := rateRadius D U + (1 + (3 + B) + (2 + 4 * D + B) + (4 * D * (1 + U) + B)) with hM
  have hrr : 0 ≤ rateRadius D U := by unfold rateRadius; positivity
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith [mul_nonneg hD.le hU]
  have hMpos : 0 < M := by linarith
  set K : ℝ := B * (M ^ 2 + M + 1) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨min (1 / 2) (min (1 / (8 * M)) (1 / (1 + D))), ⟨?_, min_le_left _ _⟩,
    6 * M ^ 2 + K ^ ((1 : ℝ) / 3) + (4 * D ^ 2) ^ ((1 : ℝ) / 3), ?_⟩
  · refine lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  rintro eps ⟨he, heb⟩ Delta ⟨hΔ0, hΔD⟩ un ⟨hun0, hunU⟩
  have he2 : eps ≤ 1 / 2 := heb.trans (min_le_left _ _)
  have he8 : eps ≤ 1 / (8 * M) := heb.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heD : eps ≤ 1 / (1 + D) := heb.trans ((min_le_right _ _).trans (min_le_right _ _))
  have heM : eps * M ≤ 1 / 8 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * M)).1 he8
    linarith
  have heD' : eps * (1 + D) ≤ 1 := (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + D)).1 heD
  have he1 : eps ≤ 1 := by linarith
  obtain ⟨hr2, hr1, hr0⟩ := hB eps ⟨he.le, he2⟩ Delta ⟨hΔ0.le, hΔD⟩ un ⟨hun0, hunU⟩
  -- norm bounds for the coefficients of the transfer cubic
  have hmul : ∀ r : ℝ, |r| ≤ B → |eps * r| ≤ B := by
    intro r hr
    rw [abs_mul, abs_of_pos he]
    nlinarith [abs_nonneg r]
  have hq2 : ‖(transferQ2 eps Delta un : ℂ)‖ ≤ 3 + B := by
    rw [Complex.norm_real, Real.norm_eq_abs, transferQ2]
    calc |3 + eps * transferR2 eps Delta un| ≤ |(3 : ℝ)| + |eps * transferR2 eps Delta un| :=
          abs_add_le _ _
      _ ≤ 3 + B := by
        have := hmul _ hr2
        have h3 : |(3 : ℝ)| = 3 := abs_of_pos (by norm_num)
        linarith
  have hq1 : ‖(transferQ1 eps Delta un : ℂ)‖ ≤ 2 + 4 * D + B := by
    rw [Complex.norm_real, Real.norm_eq_abs, transferQ1]
    calc |2 + 4 * Delta + eps * transferR1 eps Delta un|
        ≤ |2 + 4 * Delta| + |eps * transferR1 eps Delta un| := abs_add_le _ _
      _ ≤ 2 + 4 * D + B := by
        have := hmul _ hr1
        have h3 : |2 + 4 * Delta| = 2 + 4 * Delta := abs_of_pos (by linarith)
        linarith
  have hq0 : ‖(transferQ0 eps Delta un : ℂ)‖ ≤ 4 * D * (1 + U) + B := by
    rw [Complex.norm_real, Real.norm_eq_abs, transferQ0]
    calc |4 * Delta * (1 - un) + eps * transferR0 eps Delta un|
        ≤ |4 * Delta * (1 - un)| + |eps * transferR0 eps Delta un| := abs_add_le _ _
      _ ≤ 4 * D * (1 + U) + B := by
        have := hmul _ hr0
        have h3 : |4 * Delta * (1 - un)| ≤ 4 * D * (1 + U) := by
          rw [abs_mul, abs_of_pos (by linarith : 0 < 4 * Delta)]
          have h1u : |1 - un| ≤ 1 + U := abs_le.2 ⟨by linarith, by linarith⟩
          exact mul_le_mul (by linarith) h1u (abs_nonneg _) (by linarith)
        linarith
  have hQM : ∀ mu ∈ cubicRoots (transferQ2 eps Delta un : ℂ) (transferQ1 eps Delta un : ℂ)
      (transferQ0 eps Delta un : ℂ), ‖mu‖ ≤ M := by
    intro mu hmu
    have := cubicRoots_norm_le_sum hmu
    rw [hM]; linarith
  have hχM : ∀ mu ∈ cubicRoots 3 (2 + 4 * (Delta : ℂ)) (4 * (Delta : ℂ) * (1 - (un : ℂ))),
      ‖mu‖ ≤ M := by
    intro mu hmu
    have h := continuumRoots_norm_le (δ := Delta) (u := un) (D := D) (U := U)
      (by rw [abs_of_pos hΔ0]; exact hΔD) (by rw [abs_of_nonneg hun0]; exact hunU) hmu
    have h4 : 0 ≤ 4 * D * (1 + U) := by positivity
    rw [hM]; linarith
  -- root perturbation: `χ` versus the transfer cubic
  have hclose := maxRe_cubicRoots_close_coeff hχM hQM
  have hd2 : ‖(3 : ℂ) - (transferQ2 eps Delta un : ℂ)‖ = eps * |transferR2 eps Delta un| := by
    have : (3 : ℂ) - (transferQ2 eps Delta un : ℂ) = ((-(eps * transferR2 eps Delta un) : ℝ) : ℂ) := by
      simp only [transferQ2]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos he]
  have hd1 : ‖(2 + 4 * (Delta : ℂ)) - (transferQ1 eps Delta un : ℂ)‖
      = eps * |transferR1 eps Delta un| := by
    have : (2 + 4 * (Delta : ℂ)) - (transferQ1 eps Delta un : ℂ)
        = ((-(eps * transferR1 eps Delta un) : ℝ) : ℂ) := by
      simp only [transferQ1]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos he]
  have hd0 : ‖(4 * (Delta : ℂ) * (1 - (un : ℂ))) - (transferQ0 eps Delta un : ℂ)‖
      = eps * |transferR0 eps Delta un| := by
    have : (4 * (Delta : ℂ) * (1 - (un : ℂ))) - (transferQ0 eps Delta un : ℂ)
        = ((-(eps * transferR0 eps Delta un) : ℝ) : ℂ) := by
      simp only [transferQ0]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos he]
  rw [hd2, hd1, hd0] at hclose
  set δ : ℝ := eps * |transferR2 eps Delta un| * M ^ 2 + eps * |transferR1 eps Delta un| * M
    + eps * |transferR0 eps Delta un| with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδK : δ ≤ K * eps := by
    rw [hδ, hK]
    have h2 : eps * |transferR2 eps Delta un| * M ^ 2 ≤ eps * B * M ^ 2 := by gcongr
    have h1 : eps * |transferR1 eps Delta un| * M ≤ eps * B * M := by gcongr
    have h0 : eps * |transferR0 eps Delta un| ≤ eps * B := by gcongr
    nlinarith
  have hstep := perStepRate_close_maxRe (transferParams eps Delta un) he heM hQM
    (mem_stepRoots_transfer_iff eps Delta un he.ne')
  -- first bound
  have hrc : continuumPerronRate Delta un
      = -maxRe (cubicRoots 3 (2 + 4 * (Delta : ℂ)) (4 * (Delta : ℂ) * (1 - (un : ℂ)))) :=
    continuumPerronRate_eq Delta un
  have hfirst : |perStepRate (transferParams eps Delta un) - eps * continuumPerronRate Delta un|
      ≤ (6 * M ^ 2 + K ^ ((1 : ℝ) / 3)) * eps ^ ((4 : ℝ) / 3) := by
    have e1 := eps_mul_rpow_third_le hK0 he hδ0 hδK
    have e2 := sq_le_rpow_four_thirds he he1
    have hc := abs_le.1 hclose
    have hs := abs_le.1 hstep
    have hrc' : eps * continuumPerronRate Delta un
        = -(eps * maxRe (cubicRoots 3 (2 + 4 * (Delta : ℂ)) (4 * (Delta : ℂ) * (1 - (un : ℂ))))) := by
      rw [hrc]; ring
    rw [hrc', abs_le]
    have hMsq : 0 ≤ 6 * M ^ 2 := by positivity
    have e3 := mul_le_mul_of_nonneg_left e2 hMsq
    have hce := mul_le_mul_of_nonneg_left hc.2 he.le
    have hce' := mul_le_mul_of_nonneg_left hc.1 he.le
    constructor <;> linarith
  refine ⟨?_, ?_⟩
  · refine hfirst.trans ?_
    have : 0 ≤ (4 * D ^ 2) ^ ((1 : ℝ) / 3) * eps ^ ((4 : ℝ) / 3) := by positivity
    linarith
  · exact transfer_total_load_close hD he heD' hΔ0 hΔD hfirst

/-! ### The tex statement (Tr2) and the compact form (Tr3) -/

/-- (Tr2) `lem:helps-transfer`.  Let `D, c > 0`.  There are `ε₀ ∈ (0, 1/2]` and `C`, depending only
on `D` and `c`, such that for `ε ≤ ε₀`, `Δ ≤ D`, `u_n ≤ cΔ`, with `p = ⟨1-ε, ε²Δ, u_n, 0⟩`
(so `β = 1-ε`, `w = ε²Δ`),
`|Λ - ε r_c(Δ,u_n)| ≤ C ε^(4/3)` and `|Λ - ε r_c(Δ,u_n+u_c)| ≤ C ε^(4/3)`, where
`Λ = perStepRate p` and `u_c = p.curvature`. -/
theorem helps_transfer (D c : ℝ) (hD : 0 < D) (hc : 0 < c) :
    ∃ eps0 : ℝ, eps0 ∈ Set.Ioc (0 : ℝ) (1 / 2) ∧ ∃ C : ℝ,
      ∀ eps ∈ Set.Ioc (0 : ℝ) eps0, ∀ Delta ∈ Set.Ioc (0 : ℝ) D,
        ∀ un ∈ Set.Icc (0 : ℝ) (c * Delta),
        |perStepRate (transferParams eps Delta un) - eps * continuumPerronRate Delta un|
            ≤ C * eps ^ ((4 : ℝ) / 3) ∧
        |perStepRate (transferParams eps Delta un)
            - eps * continuumPerronRate Delta (un + (transferParams eps Delta un).curvature)|
            ≤ C * eps ^ ((4 : ℝ) / 3) := by
  obtain ⟨eps0, h0, C, hC⟩ := helps_transfer_box D (c * D) hD (by positivity)
  refine ⟨eps0, h0, C, fun eps heps Delta hΔ un hun => ?_⟩
  exact hC eps heps Delta hΔ un ⟨hun.1, hun.2.trans (by nlinarith [hΔ.2, hc])⟩

/-- (Tr3) `lem:helps-transfer`, compact form: on a compact `K ⊆ (0,∞) × [0,1)`,
`Λ = ε r_c(Δ,u_n) (1 + O(ε^(1/3)))` uniformly, where `Λ = perStepRate ⟨1-ε, ε²Δ, u_n, 0⟩`. -/
theorem helps_transfer_compact {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hsub : K ⊆ Set.Ioi 0 ×ˢ Set.Ico 0 1) :
    ∃ eps0 : ℝ, eps0 ∈ Set.Ioc (0 : ℝ) (1 / 2) ∧ ∃ C : ℝ,
      ∀ eps ∈ Set.Ioc (0 : ℝ) eps0, ∀ x ∈ K,
        |perStepRate (transferParams eps x.1 x.2) / (eps * continuumPerronRate x.1 x.2) - 1|
          ≤ C * eps ^ ((1 : ℝ) / 3) := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨1 / 2, ⟨by norm_num, le_refl _⟩, 0, by simp [he]⟩
  obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
  obtain ⟨x1, hx1, hmax⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
  have hD0 : 0 < x0.1 := (hsub hx0).1
  have hD1 : 0 < x1.1 := (hsub hx1).1
  obtain ⟨cK, hcK, hcKle⟩ := continuumPerronRate_pos_lower_bound hK hsub
  obtain ⟨eps0, h0, C, hC⟩ := helps_transfer x1.1 (1 / x0.1) hD1 (by positivity)
  refine ⟨eps0, h0, max C 0 / cK, fun eps heps x hx => ?_⟩
  have hxs := hsub hx
  have hΔ : x.1 ∈ Set.Ioc (0 : ℝ) x1.1 := ⟨hxs.1, hmax hx⟩
  have hΔ0 : x0.1 ≤ x.1 := hmin hx
  have hun : x.2 ∈ Set.Icc (0 : ℝ) (1 / x0.1 * x.1) := by
    refine ⟨hxs.2.1, ?_⟩
    have : 1 ≤ 1 / x0.1 * x.1 := by
      rw [one_div_mul_eq_div, le_div_iff₀ hD0]; linarith
    linarith [hxs.2.2]
  have hb := (hC eps heps x.1 hΔ x.2 hun).1
  have he : 0 < eps := heps.1
  have hr : cK ≤ continuumPerronRate x.1 x.2 := hcKle x hx
  have hrpos : 0 < continuumPerronRate x.1 x.2 := lt_of_lt_of_le hcK hr
  have hden : 0 < eps * continuumPerronRate x.1 x.2 := mul_pos he hrpos
  have h2 : eps ^ ((4 : ℝ) / 3) = eps * eps ^ ((1 : ℝ) / 3) := by
    rw [show (4 : ℝ) / 3 = 1 + 1 / 3 by norm_num, Real.rpow_add he, Real.rpow_one]
  have hq : 0 < eps ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos he _
  have hCm : C * eps ^ ((4 : ℝ) / 3) ≤ max C 0 * eps ^ ((4 : ℝ) / 3) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg he.le _)
  rw [div_sub_one hden.ne', abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have hmc : 0 ≤ max C 0 := le_max_right _ _
  have h3 : max C 0 ≤ max C 0 / cK * continuumPerronRate x.1 x.2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcK]
    exact mul_le_mul_of_nonneg_left hr hmc
  have h4 := mul_le_mul_of_nonneg_left h3 (mul_nonneg he.le hq.le)
  calc _ ≤ C * eps ^ ((4 : ℝ) / 3) := hb
    _ ≤ max C 0 * eps ^ ((4 : ℝ) / 3) := hCm
    _ = max C 0 * (eps * eps ^ ((1 : ℝ) / 3)) := by rw [h2]
    _ ≤ _ := by nlinarith

end

end SparseSGD.Scaling.Helps
