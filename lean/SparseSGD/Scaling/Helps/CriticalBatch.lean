import SparseSGD.Scaling.Helps.Vocabulary
import SparseSGD.Scaling.Helps.StepSpeed

/-!
# Critical batch size of a vocabulary (momentum-helps appendix)

Paper labels: `lem:helps-twocurv`, `prop:helps-critical` (draft blocks `helps-two-curvatures`,
`helps-critical-batch`).

Setup as in `Vocabulary.lean`: `ps : Fin (n+1) → unitInterval` antitone with every `ps j > 0`,
copy `j` has parameters `copyParams d B ν beta eta ps j`, `Lmin = -log rhoMax`.

* `admSet d B ν ps K` is `A_O(B)`: the pairs `(eta, beta)` with `eta > 0`, `beta ∈ K` and every copy
  exponentially stable (`stepRadius < 1`).  The class is `K = sgdClass = {0}` or
  `K = momClass = [0,1)`.
* `Sfun` is `S_O(B) = inf 1/Lmin` over `admSet` (`sInf` of a set of reals), `Efun = B * Sfun`,
  `Sinf = inf_{B ≥ 1} S_O(B)`, `Einf = inf_{B ≥ 1} E_O(B)`, `Bcrit = Einf / Sinf`.
  Here `1/Lmin` is `1/Λ_min` of the tex (on `admSet` every radius is in `(0,1)`, so `Lmin = Λ_min`
  is finite and positive; this is proved in `rhoMax_pos_lt_one`).

Map from the tex to the Lean statements:
* `lem:helps-twocurv`: `twocurv_real` (real-variable core), `rhoMax_ge_twocurv`.
* `prop:helps-critical` (i): `helps_critical_i`; steps in `Sfun_sgd_ge`, `Sfun_mom_ge`,
  `Sfun_tendsto_sgd`, `Sfun_tendsto_mom`, `Sinf_sgd`, `Sinf_mom`, `inv_two_log_bounds`.
* (ii): `helps_critical_ii` (SGD, `E_mom ≤ E_SGD`), `helps_critical_ii_mom'` (`κ > 16`, sharp
  constant `c_κ = max(1 - 4/√κ, 1/√5)`; steps `neg_log_one_sub_le_div_sqrt` (`φ(m) ≥ √(1-m)`),
  `Mk_props`, `min_le_Mk` (`m ≤ m_κ = 4/(1+√(1+κ))`), `cK_le_sqrt_one_sub`, `mom_real_aux2`,
  `mom_B_div_Lmin'`, `Efun_mom_ge'`, `Einf_mom_ge'`).  `helps_critical_ii_mom` is the weaker form
  with `1 - 4/√κ` alone.
* (iii): `helps_critical_iii_sgd`, `helps_critical_iii_ratio'` (lower bound with `c_κ`, `κ > 16`,
  and the claim that the left side is `≥ √κ/19`: `Bratio_ge'`, `Bratio_ge_div19`), and
  `Bratio_of_Einf_eq` (the remark "if `E_mom = E_SGD`").  `helps_critical_iii_ratio` is the weaker
  form with `(√κ-4)/8`.
* `prop_helps_critical`: all parts at `κ > 16`; `helps_critical_finiteB`: the finite-`B`
  lower bounds and the limits `S_O(B) → 1/λ_O`.

Differences from, and hypotheses added to, the tex statements:
* `lem:helps-twocurv` is formalized in the form needed: with `s := max_j rho(L_j)` and
  `rho(F_j)^2 ≤ s` (the content of `rem:retention-cap`(a), here `sq_le_stepRadius_of_meanEig`
  for real eigenvalues and `beta_le_stepRadius` for complex ones), `s ≥ ((√κ-1)/(√κ+1))^2` and
  `s ≥ ((κ-1)/(κ+1))^2` if `beta = 0` (`rhoMax_ge_twocurv`).  The spectral radius of `F` itself
  is not defined; the bound already holds at `beta = 0` for the momentum class, so the tex
  comparison `λ_SGD ≤ λ_mom` is not needed.
* The tex's "we may assume `r < 1`" is the admissibility hypothesis (`rhoMax < 1`).
* The tex's monotonicity of `x/log(1+x)` is replaced by Bernoulli's inequality `(1+a)^B ≥ 1+Ba`
  (`bernoulli_aux`), and the monotonicity of `m/(-log(1-m))` is not needed: `φ(m) ≥ √(1-m)` and
  `m ≤ m_κ` give `φ(m) ≥ √(1-m_κ)` directly.  The `d ≥ 1` of the tex is not needed for the
  `√κ/19` claim (`d = 0` already gives `(1/8)(0.447)(255/256)(31/32) > 1/19`).
* No Jury hypothesis is needed anywhere: only the easy direction of stability and the explicit
  admissible point `(1/(d+2), 0)` (`sgd_point_mem`) are used; nonemptiness of `A_O(B)` for every
  `B ≥ 1` follows from it.
* `B` ranges over `ℕ`, `B ≥ 1`; `d : ℕ`; `κ_V > 1` (hence `V ≥ 2`) for all parts except the
  momentum lower bound in (ii) and the lower bound in (iii), which use `κ_V > 16`.
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD SparseSGD.Probability.LeastSquares MeasureTheory Filter
open scoped Topology

noncomputable section

/-! ### Scalar lemmas -/

/-- `log ((1+x)/(1-x)) ≤ 2x/(1-x²)` for `0 ≤ x < 1` (upper series bound, `prop:helps-critical`
Step 2). -/
theorem log_div_le_two_mul_div {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log ((1 + x) / (1 - x)) ≤ 2 * x / (1 - x ^ 2) := by
  have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have h := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hg := (hasSum_geometric_of_lt_one (sq_nonneg x) hx2).mul_left (2 * x)
  have hle := hasSum_le (fun k : ℕ => ?_) h hg
  · have e : Real.log ((1 + x) / (1 - x)) = Real.log (1 + x) - Real.log (1 - x) :=
      Real.log_div (by linarith) (by linarith)
    rw [e]
    have e2 : 2 * x * (1 - x ^ 2)⁻¹ = 2 * x / (1 - x ^ 2) := by rw [div_eq_mul_inv]
    rw [e2] at hle
    exact hle
  · have h1 : (1 : ℝ) / (2 * k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have h2 : x ^ (2 * k + 1) = x * (x ^ 2) ^ k := by
      rw [pow_succ, pow_mul]; ring
    rw [h2]
    have h3 : 0 ≤ x * (x ^ 2) ^ k := by positivity
    nlinarith

/-- For `y > 1`: `4/y ≤ 2 log ((y+1)/(y-1)) ≤ 4y/(y²-1)`. -/
theorem two_log_bounds {y : ℝ} (hy : 1 < y) :
    4 / y ≤ 2 * Real.log ((y + 1) / (y - 1)) ∧
      2 * Real.log ((y + 1) / (y - 1)) ≤ 4 * y / (y ^ 2 - 1) := by
  have hy0 : 0 < y := by linarith
  set x : ℝ := 1 / y with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one hy0]; exact hy
  have e : (y + 1) / (y - 1) = (1 + x) / (1 - x) := by
    rw [hx]
    have : y - 1 ≠ 0 := by linarith
    field_simp
  rw [e]
  have h1 := two_mul_le_log_div hx0.le hx1
  have h2 := log_div_le_two_mul_div hx0.le hx1
  constructor
  · have : 4 / y = 2 * (2 * x) := by rw [hx]; ring
    rw [this]; linarith
  · have e2 : 2 * x / (1 - x ^ 2) = 2 * y / (y ^ 2 - 1) := by
      rw [hx]
      have : y ^ 2 - 1 ≠ 0 := by nlinarith
      have h' : 1 - (1 / y) ^ 2 ≠ 0 := by
        have : (1 : ℝ) - (1 / y) ^ 2 = (y ^ 2 - 1) / y ^ 2 := by field_simp
        rw [this]; exact div_ne_zero ‹_› (by positivity)
      field_simp
    have e3 : 4 * y / (y ^ 2 - 1) = 2 * (2 * y / (y ^ 2 - 1)) := by ring
    rw [e3, ← e2]; linarith

/-- `-log (((s-1)/(s+1))^2) = 2 log ((s+1)/(s-1))` for `s > 1`. -/
theorem neg_log_sq_div {s : ℝ} :
    -Real.log (((s - 1) / (s + 1)) ^ 2) = 2 * Real.log ((s + 1) / (s - 1)) := by
  rw [Real.log_pow, ← inv_div, Real.log_inv]; push_cast; ring

/-! ### `lem:helps-twocurv` -/

/-- Real-variable core of `lem:helps-twocurv`: if every real root `l` of `l² - t l + β` has
`l² ≤ r²`, then `r² ∓ t r + β ≥ 0`. -/
theorem quad_pm_nonneg {t β r : ℝ} (hr0 : 0 ≤ r)
    (h : ∀ l : ℝ, l ^ 2 - t * l + β = 0 → l ^ 2 ≤ r ^ 2) :
    0 ≤ r ^ 2 - t * r + β ∧ 0 ≤ r ^ 2 + t * r + β := by
  by_cases hΔ : t ^ 2 - 4 * β < 0
  · constructor <;> nlinarith [sq_nonneg (2 * r - t), sq_nonneg (2 * r + t)]
  · push Not at hΔ
    set σ : ℝ := Real.sqrt (t ^ 2 - 4 * β) with hσdef
    have hσ : σ ^ 2 = t ^ 2 - 4 * β := Real.sq_sqrt hΔ
    have hl1 : ((t + σ) / 2) ^ 2 - t * ((t + σ) / 2) + β = 0 := by nlinarith
    have hl2 : ((t - σ) / 2) ^ 2 - t * ((t - σ) / 2) + β = 0 := by nlinarith
    obtain ⟨a1, b1⟩ := abs_le_of_sq_le_sq' (h _ hl1) hr0
    obtain ⟨a2, b2⟩ := abs_le_of_sq_le_sq' (h _ hl2) hr0
    constructor
    · have : r ^ 2 - t * r + β = (r - (t + σ) / 2) * (r - (t - σ) / 2) := by nlinarith
      rw [this]; exact mul_nonneg (by linarith) (by linarith)
    · have : r ^ 2 + t * r + β = (r + (t + σ) / 2) * (r + (t - σ) / 2) := by nlinarith
      rw [this]; exact mul_nonneg (by linarith) (by linarith)

/-- Real-variable form of `lem:helps-twocurv`: `p₁ > p_V > 0`, `c > 0`, `0 ≤ β`, `0 ≤ r < 1`,
`β ≤ r²` and every real eigenvalue `l` of `F_j` (root of `l² - (1+β-c p_j) l + β`) has `l² ≤ r²`.
Then `r ≥ (√κ-1)/(√κ+1)`, and `r ≥ (κ-1)/(κ+1)` when `β = 0`. -/
theorem twocurv_real {β c p1 pV r : ℝ} (hβ0 : 0 ≤ β) (hc : 0 < c) (hpV : 0 < pV)
    (hlt : pV < p1) (hr0 : 0 ≤ r) (hr1 : r < 1) (hβr : β ≤ r ^ 2)
    (h1 : ∀ l : ℝ, l ^ 2 - (1 + β - c * p1) * l + β = 0 → l ^ 2 ≤ r ^ 2)
    (hV : ∀ l : ℝ, l ^ 2 - (1 + β - c * pV) * l + β = 0 → l ^ 2 ≤ r ^ 2) :
    (Real.sqrt (p1 / pV) - 1) / (Real.sqrt (p1 / pV) + 1) ≤ r ∧
      (β = 0 → (p1 / pV - 1) / (p1 / pV + 1) ≤ r) := by
  obtain ⟨k1a, k1b⟩ := quad_pm_nonneg hr0 h1
  obtain ⟨kVa, kVb⟩ := quad_pm_nonneg hr0 hV
  set κ : ℝ := p1 / pV with hκ
  have hκ1 : 1 < κ := by rw [hκ, lt_div_iff₀ hpV]; linarith
  have hk : κ * pV = p1 := div_mul_cancel₀ _ hpV.ne'
  -- r > 0
  have hrpos : 0 < r := by
    rcases hr0.lt_or_eq with h | h
    · exact h
    · exfalso
      have hβ : β = 0 := by rw [← h] at hβr; nlinarith
      have e1 := h1 (1 + β - c * p1) (by rw [hβ]; ring)
      have e2 := hV (1 + β - c * pV) (by rw [hβ]; ring)
      rw [← h] at e1 e2
      have a1 : 1 + β - c * p1 = 0 := by nlinarith
      have a2 : 1 + β - c * pV = 0 := by nlinarith
      nlinarith [mul_pos hc (sub_pos.2 hlt)]
  have hκm : (κ - 1) * (c * pV) = c * (p1 - pV) := by rw [← hk]; ring
  -- c (p1 - pV) ≤ 4 r
  have hdiff : c * (p1 - pV) ≤ 4 * r := by
    have a : (1 + β - c * pV) * r ≤ r ^ 2 + β := by nlinarith
    have b : -(1 + β - c * p1) * r ≤ r ^ 2 + β := by nlinarith
    have a' : (1 + β - c * pV) ≤ 2 * r := by
      by_contra hcon; push Not at hcon; nlinarith
    have b' : -(1 + β - c * p1) ≤ 2 * r := by
      by_contra hcon; push Not at hcon; nlinarith
    nlinarith
  -- c pV ≥ (1-r)^2
  have hcp : (1 - r) ^ 2 ≤ c * pV := by
    have a : r * (c * pV) ≥ (1 - r) * (r - β) := by nlinarith
    have b : (1 - r) * (r - β) ≥ (1 - r) * (r - r ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hh : r * (1 - r) ^ 2 ≤ r * (c * pV) := by nlinarith
    exact le_of_mul_le_mul_left hh hrpos
  have hgr : (κ - 1) * (1 - r) ^ 2 ≤ 4 * r := by
    have := mul_le_mul_of_nonneg_left hcp (by linarith : (0 : ℝ) ≤ κ - 1)
    linarith
  refine ⟨?_, fun hβ => ?_⟩
  · set s : ℝ := Real.sqrt κ with hs
    have hs1 : 1 < s := by
      rw [hs, show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) hκ1
    have hs2 : s ^ 2 = κ := Real.sq_sqrt (by linarith)
    set q : ℝ := (s - 1) / (s + 1) with hq
    have hq0 : 0 ≤ q := div_nonneg (by linarith) (by linarith)
    have hq1 : q < 1 := by rw [hq, div_lt_one (by linarith)]; linarith
    have hqe : (κ - 1) * (1 - q) ^ 2 = 4 * q := by
      rw [hq, ← hs2]
      have : s + 1 ≠ 0 := by linarith
      field_simp
      ring
    by_contra hlt'
    push Not at hlt'
    have hpos : 0 < (q - r) * ((κ - 1) * (2 - r - q) + 4) := by
      apply mul_pos (by linarith)
      have : 0 < (κ - 1) * (2 - r - q) := mul_pos (by linarith) (by linarith)
      linarith
    nlinarith
  · -- β = 0: the eigenvalue `t_j` itself is a root
    have ea := hV (1 + β - c * pV) (by rw [hβ]; ring)
    have eb := h1 (1 + β - c * p1) (by rw [hβ]; ring)
    have ea' : (1 + β - c * pV) ≤ r := by
      have := abs_le_of_sq_le_sq' ea hr0; exact this.2
    have eb' : -r ≤ 1 + β - c * p1 := by
      have := abs_le_of_sq_le_sq' eb hr0; exact this.1
    have hcV : 1 - r ≤ c * pV := by rw [hβ] at ea'; linarith
    have h2 : c * (p1 - pV) ≤ 2 * r := by nlinarith
    have h3 : (κ - 1) * (1 - r) ≤ 2 * r := by
      have := mul_le_mul_of_nonneg_left hcV (by linarith : (0 : ℝ) ≤ κ - 1)
      nlinarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith

/-! ### Admissible sets, `S_O(B)`, `E_O(B)`, `S_O`, `E_O`, `B_O` -/

/-- Optimizer class SGD: `beta = 0`. -/
def sgdClass : Set ℝ := {0}

/-- Optimizer class momentum: `beta ∈ [0,1)`. -/
def momClass : Set ℝ := Set.Ico 0 1

/-- `A_O(B)`: pairs `(eta, beta)` with `eta > 0`, `beta ∈ K` and every copy exponentially stable
(`stepRadius < 1`; `v2 prop:helps-critical`). -/
def admSet {n : ℕ} (d B : ℕ) (ν : Measure ℝ) (ps : Fin (n + 1) → unitInterval) (K : Set ℝ) :
    Set (ℝ × ℝ) :=
  {x | 0 < x.1 ∧ x.2 ∈ K ∧ ∀ j, stepRadius (copyParams d B ν x.2 x.1 ps j) < 1}

/-- `S_O(B) = inf_{(eta,beta) ∈ A_O(B)} 1/Λ_min` (`v2 prop:helps-critical`). -/
def Sfun {n : ℕ} (d B : ℕ) (ν : Measure ℝ) (ps : Fin (n + 1) → unitInterval) (K : Set ℝ) : ℝ :=
  sInf ((fun x : ℝ × ℝ => 1 / Lmin d B ν x.2 x.1 ps) '' admSet d B ν ps K)

/-- `E_O(B) = B S_O(B)`. -/
def Efun {n : ℕ} (d B : ℕ) (ν : Measure ℝ) (ps : Fin (n + 1) → unitInterval) (K : Set ℝ) : ℝ :=
  (B : ℝ) * Sfun d B ν ps K

/-- `S_O = inf_{B ≥ 1} S_O(B)`. -/
def Sinf {n : ℕ} (d : ℕ) (ν : Measure ℝ) (ps : Fin (n + 1) → unitInterval) (K : Set ℝ) : ℝ :=
  sInf ((fun B : ℕ => Sfun d B ν ps K) '' Set.Ici 1)

/-- `E_O = inf_{B ≥ 1} E_O(B)`. -/
def Einf {n : ℕ} (d : ℕ) (ν : Measure ℝ) (ps : Fin (n + 1) → unitInterval) (K : Set ℝ) : ℝ :=
  sInf ((fun B : ℕ => Efun d B ν ps K) '' Set.Ici 1)

/-- The critical batch size `B_O = E_O / S_O`. -/
def Bcrit {n : ℕ} (d : ℕ) (ν : Measure ℝ) (ps : Fin (n + 1) → unitInterval) (K : Set ℝ) : ℝ :=
  Einf d ν ps K / Sinf d ν ps K

/-- `λ_SGD = 2 log ((κ+1)/(κ-1))`. -/
def lamSGD {n : ℕ} (ps : Fin (n + 1) → unitInterval) : ℝ :=
  2 * Real.log ((kappaV ps + 1) / (kappaV ps - 1))

/-- `λ_mom = 2 log ((√κ+1)/(√κ-1))`. -/
def lamMom {n : ℕ} (ps : Fin (n + 1) → unitInterval) : ℝ :=
  2 * Real.log ((Real.sqrt (kappaV ps) + 1) / (Real.sqrt (kappaV ps) - 1))

section Basic2

variable {n : ℕ} {d B : ℕ} {ν : Measure ℝ} {ps : Fin (n + 1) → unitInterval}

theorem kappaV_gt_one_lt (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) :
    (ps (Fin.last n) : ℝ) < (ps 0 : ℝ) := by
  unfold kappaV at hκ
  rwa [lt_div_iff₀ (hp _), one_mul] at hκ

theorem sqrt_kappa_gt_one (hκ : 1 < kappaV ps) : 1 < Real.sqrt (kappaV ps) := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) hκ

/-- `lem:helps-twocurv` transferred to the radius of `L`: for every `eta > 0`, `0 ≤ beta < 1` and
stable copies, `rhoMax ≥ ((√κ-1)/(√κ+1))²`, and `rhoMax ≥ ((κ-1)/(κ+1))²` if `beta = 0`.
(Uses `rho(F_j)² ≤ rho(L_j)`, here `sq_le_stepRadius_of_meanEig` and `beta_le_stepRadius`.) -/
theorem rhoMax_ge_twocurv (hp : ∀ j, 0 < (ps j : ℝ)) {beta eta : ℝ} (hη : 0 < eta)
    (hb0 : 0 ≤ beta) (hb1 : beta < 1) (hκ : 1 < kappaV ps)
    (hstab : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) :
    ((Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1)) ^ 2
        ≤ rhoMax d B ν beta eta ps ∧
      (beta = 0 → ((kappaV ps - 1) / (kappaV ps + 1)) ^ 2 ≤ rhoMax d B ν beta eta ps) := by
  have hR0 : 0 ≤ rhoMax d B ν beta eta ps :=
    (stepRadius_nonneg _).trans (le_rhoMax (ps := ps) (d := d) (B := B) (ν := ν)
      (beta := beta) (eta := eta) 0)
  have hR1 : rhoMax d B ν beta eta ps < 1 := rhoMax_lt_one_iff.2 hstab
  set R := rhoMax d B ν beta eta ps with hR
  set r := Real.sqrt R with hr
  have hr2 : r ^ 2 = R := Real.sq_sqrt hR0
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r < 1 := by rw [hr, Real.sqrt_lt' one_pos]; simpa using hR1
  have hc : 0 < eta * (1 - beta) := mul_pos hη (by linarith)
  have hβr : beta ≤ r ^ 2 := by
    rw [hr2]
    have := beta_le_stepRadius (copyParams d B ν beta eta ps 0) hb0 hb1.le
      (by rw [copyParams_w]; have := hp 0; positivity)
      (copyParams_noise_nonneg hp hη.le 0)
    exact this.trans (le_rhoMax 0)
  have hmean : ∀ j : Fin (n + 1), ∀ l : ℝ,
      l ^ 2 - (1 + beta - eta * (1 - beta) * (ps j : ℝ)) * l + beta = 0 → l ^ 2 ≤ r ^ 2 := by
    intro j l hl
    rw [hr2]
    have := sq_le_stepRadius_of_meanEig (copyParams d B ν beta eta ps j) (l := l) hl hb0 hb1.le
      (by rw [copyParams_w]; have := hp j; positivity) (copyParams_noise_nonneg hp hη.le j)
    exact this.trans (le_rhoMax j)
  have key := twocurv_real (β := beta) (c := eta * (1 - beta)) (p1 := (ps 0 : ℝ))
    (pV := (ps (Fin.last n) : ℝ)) hb0 hc (hp _) (kappaV_gt_one_lt hp hκ) hr0 hr1 hβr
    (hmean 0) (hmean (Fin.last n))
  have hk : kappaV ps = (ps 0 : ℝ) / (ps (Fin.last n) : ℝ) := rfl
  rw [← hk] at key
  have hs1 := sqrt_kappa_gt_one hκ
  have hq0 : 0 ≤ (Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1) :=
    div_nonneg (by linarith) (by linarith)
  refine ⟨?_, fun hb => ?_⟩
  · rw [← hr2]; exact pow_le_pow_left₀ hq0 key.1 2
  · rw [← hr2]
    exact pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith)) (key.2 hb) 2

/-- On the admissible set, `rhoMax ∈ (0,1)`. -/
theorem rhoMax_pos_lt_one (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) {K : Set ℝ}
    (hK : K ⊆ Set.Ico 0 1) {x : ℝ × ℝ} (hx : x ∈ admSet d B ν ps K) :
    0 < rhoMax d B ν x.2 x.1 ps ∧ rhoMax d B ν x.2 x.1 ps < 1 := by
  obtain ⟨hη, hβ, hst⟩ := hx
  obtain ⟨hb0, hb1⟩ := hK hβ
  refine ⟨?_, rhoMax_lt_one_iff.2 hst⟩
  have h := (rhoMax_ge_twocurv hp hη hb0 hb1 hκ hst).1
  have hs1 := sqrt_kappa_gt_one hκ
  have : 0 < ((Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1)) ^ 2 := by
    have : 0 < (Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1) :=
      div_pos (by linarith) (by linarith)
    positivity
  linarith

theorem Lmin_pos_of_mem (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) {K : Set ℝ}
    (hK : K ⊆ Set.Ico 0 1) {x : ℝ × ℝ} (hx : x ∈ admSet d B ν ps K) :
    0 < Lmin d B ν x.2 x.1 ps := by
  obtain ⟨h0, h1⟩ := rhoMax_pos_lt_one hp hκ hK hx
  unfold Lmin
  have := Real.log_neg h0 h1
  linarith

/-- `Lmin ≤ λ_mom` on the admissible set of any class inside `[0,1)`. -/
theorem Lmin_le_lamMom (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) {K : Set ℝ}
    (hK : K ⊆ Set.Ico 0 1) {x : ℝ × ℝ} (hx : x ∈ admSet d B ν ps K) :
    Lmin d B ν x.2 x.1 ps ≤ lamMom ps := by
  obtain ⟨hη, hβ, hst⟩ := hx
  obtain ⟨hb0, hb1⟩ := hK hβ
  have h := (rhoMax_ge_twocurv hp hη hb0 hb1 hκ hst).1
  have hs1 := sqrt_kappa_gt_one hκ
  have hq : 0 < ((Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1)) ^ 2 := by
    have : 0 < (Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1) :=
      div_pos (by linarith) (by linarith)
    positivity
  unfold Lmin lamMom
  have := Real.log_le_log hq h
  rw [← neg_log_sq_div (s := Real.sqrt (kappaV ps))]
  linarith

/-- `Lmin ≤ λ_SGD` for `beta = 0`. -/
theorem Lmin_le_lamSGD (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps)
    {x : ℝ × ℝ} (hx : x ∈ admSet d B ν ps sgdClass) :
    Lmin d B ν x.2 x.1 ps ≤ lamSGD ps := by
  obtain ⟨hη, hβ, hst⟩ := hx
  have hb : x.2 = 0 := hβ
  have h := (rhoMax_ge_twocurv hp hη (le_of_eq hb.symm) (by rw [hb]; norm_num) hκ hst).2 hb
  have hk0 : 0 < kappaV ps := by linarith
  have hq : 0 < ((kappaV ps - 1) / (kappaV ps + 1)) ^ 2 := by
    have : 0 < (kappaV ps - 1) / (kappaV ps + 1) := div_pos (by linarith) (by linarith)
    positivity
  unfold Lmin lamSGD
  have := Real.log_le_log hq h
  rw [← neg_log_sq_div (s := kappaV ps)]
  linarith

/-! ### Generic infimum lemmas -/

theorem inv_crit_zero (hB : 0 < B) (p : unitInterval) :
    inverseCriticalRate d B p 0 = ((d : ℝ) + 2 - p + B * p) / (2 * B) := by
  have hB' : (B : ℝ) ≠ 0 := by positivity
  unfold inverseCriticalRate
  field_simp
  ring

theorem crit_zero_eq (hB : 0 < B) (p : unitInterval) :
    criticalRate d B p 0 = 2 * B / ((d : ℝ) + 2 - p + B * p) := by
  unfold criticalRate
  rw [inv_crit_zero hB, inv_div]

/-- The point `(1/(d+2), 0)` is admissible for every class containing `0` and every `B ≥ 1`. -/
theorem sgd_point_mem (hp : ∀ j, 0 < (ps j : ℝ)) (hB : 1 ≤ B) {K : Set ℝ} (h0K : (0 : ℝ) ∈ K) :
    (1 / ((d : ℝ) + 2), (0 : ℝ)) ∈ admSet d B ν ps K := by
  have hB0 : 0 < B := hB
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  refine ⟨by positivity, h0K, fun j => ?_⟩
  show stepRadius (copyParams d B ν 0 (1 / ((d : ℝ) + 2)) ps j) < 1
  have hw : 0 < (copyParams d B ν 0 (1 / ((d : ℝ) + 2)) ps j).w := by
    rw [copyParams_w]; have := hp j; positivity
  rw [stepRadius_lt_one_iff_beta_zero _ rfl hw
    (copyParams_noise_nonneg hp (by positivity) j)]
  have hload : (copyParams d B ν 0 (1 / ((d : ℝ) + 2)) ps j).totalLoad
      = (1 / ((d : ℝ) + 2)) * inverseCriticalRate d B (ps j) 0 :=
    params_totalLoad d B (ps j) (hp j).ne' ν 0 (1 / ((d : ℝ) + 2))
  rw [hload, inv_crit_zero hB0]
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hp1 : (ps j : ℝ) ≤ 1 := (ps j).2.2
  have hp0 := hp j
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [one_div, inv_mul_eq_div, div_div, div_lt_one (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hBr) (sub_nonneg.2 hp1),
    mul_nonneg (sub_nonneg.2 hBr) (by linarith : (0 : ℝ) ≤ (d : ℝ) + 2)]

theorem Sfun_ge (hp : ∀ j, 0 < (ps j : ℝ)) {K : Set ℝ} (h0K : (0 : ℝ) ∈ K) (hB : 1 ≤ B) {c : ℝ}
    (h : ∀ x ∈ admSet d B ν ps K, c ≤ 1 / Lmin d B ν x.2 x.1 ps) : c ≤ Sfun d B ν ps K :=
  le_csInf ((Set.nonempty_of_mem (sgd_point_mem hp hB h0K)).image _)
    (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

theorem Sfun_le (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) {K : Set ℝ}
    (hK : K ⊆ Set.Ico 0 1) {x : ℝ × ℝ} (hx : x ∈ admSet d B ν ps K) :
    Sfun d B ν ps K ≤ 1 / Lmin d B ν x.2 x.1 ps :=
  csInf_le ⟨0, by
    rintro _ ⟨y, hy, rfl⟩
    exact (one_div_pos.2 (Lmin_pos_of_mem hp hκ hK hy)).le⟩ ⟨x, hx, rfl⟩

theorem Sfun_nonneg (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) {K : Set ℝ}
    (hK : K ⊆ Set.Ico 0 1) (h0K : (0 : ℝ) ∈ K) (hB : 1 ≤ B) : 0 ≤ Sfun d B ν ps K :=
  Sfun_ge hp h0K hB (fun _ hx => (one_div_pos.2 (Lmin_pos_of_mem hp hκ hK hx)).le)

theorem Sinf_ge {K : Set ℝ} {c : ℝ}
    (h : ∀ B : ℕ, 1 ≤ B → c ≤ Sfun d B ν ps K) : c ≤ Sinf d ν ps K :=
  le_csInf ⟨_, 1, Set.mem_Ici.2 le_rfl, rfl⟩ (by rintro _ ⟨B, hB, rfl⟩; exact h B hB)

theorem Sinf_le (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) {K : Set ℝ}
    (hK : K ⊆ Set.Ico 0 1) (h0K : (0 : ℝ) ∈ K) (hB : 1 ≤ B) :
    Sinf d ν ps K ≤ Sfun d B ν ps K :=
  csInf_le ⟨0, by rintro _ ⟨B', hB', rfl⟩; exact Sfun_nonneg hp hκ hK h0K hB'⟩ ⟨B, hB, rfl⟩

theorem Efun_nonneg (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) {K : Set ℝ}
    (hK : K ⊆ Set.Ico 0 1) (h0K : (0 : ℝ) ∈ K) (hB : 1 ≤ B) : 0 ≤ Efun d B ν ps K :=
  mul_nonneg (Nat.cast_nonneg B) (Sfun_nonneg hp hκ hK h0K hB)

theorem Einf_ge {K : Set ℝ} {c : ℝ} (h : ∀ B : ℕ, 1 ≤ B → c ≤ Efun d B ν ps K) :
    c ≤ Einf d ν ps K :=
  le_csInf ⟨_, 1, Set.mem_Ici.2 le_rfl, rfl⟩ (by rintro _ ⟨B, hB, rfl⟩; exact h B hB)

theorem Einf_le (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) {K : Set ℝ}
    (hK : K ⊆ Set.Ico 0 1) (h0K : (0 : ℝ) ∈ K) (hB : 1 ≤ B) :
    Einf d ν ps K ≤ Efun d B ν ps K :=
  csInf_le ⟨0, by rintro _ ⟨B', hB', rfl⟩; exact Efun_nonneg hp hκ hK h0K hB'⟩ ⟨B, hB, rfl⟩

theorem sgdClass_sub : sgdClass ⊆ Set.Ico (0 : ℝ) 1 := by
  intro x hx
  have : x = 0 := hx
  subst this; exact ⟨le_rfl, one_pos⟩

theorem momClass_sub : momClass ⊆ Set.Ico (0 : ℝ) 1 := fun _ h => h

theorem zero_mem_sgdClass : (0 : ℝ) ∈ sgdClass := rfl

theorem zero_mem_momClass : (0 : ℝ) ∈ momClass := ⟨le_rfl, one_pos⟩

theorem admSet_sgd_sub_mom : admSet d B ν ps sgdClass ⊆ admSet d B ν ps momClass := by
  rintro x ⟨h1, h2, h3⟩
  have : x.2 = 0 := h2
  exact ⟨h1, by rw [this]; exact zero_mem_momClass, h3⟩

/-- `S_mom(B) ≤ S_SGD(B)` (nested admissible sets). -/
theorem Sfun_mom_le_sgd (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) (hB : 1 ≤ B) :
    Sfun d B ν ps momClass ≤ Sfun d B ν ps sgdClass :=
  csInf_le_csInf ⟨0, by
      rintro _ ⟨y, hy, rfl⟩
      exact (one_div_pos.2 (Lmin_pos_of_mem hp hκ momClass_sub hy)).le⟩
    ((Set.nonempty_of_mem (sgd_point_mem hp hB zero_mem_sgdClass)).image _)
    (Set.image_mono admSet_sgd_sub_mom)

/-! ### SGD: the fewest samples -/

/-- `p_V`, the rarest sparsity. -/
def pLast {n : ℕ} (ps : Fin (n + 1) → unitInterval) : ℝ := (ps (Fin.last n) : ℝ)

/-- `D = d + 2 - p_V`. -/
def Dv {n : ℕ} (d : ℕ) (ps : Fin (n + 1) → unitInterval) : ℝ := (d : ℝ) + 2 - pLast ps

theorem Dv_pos (d : ℕ) (ps : Fin (n + 1) → unitInterval) : 0 < Dv d ps := by
  have h1 : pLast ps ≤ 1 := (ps (Fin.last n)).2.2
  have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  unfold Dv; linarith

/-- The fewest samples of SGD: `1 / log ((d+2)/(d+2-p_V))`. -/
def Esgd1 {n : ℕ} (d : ℕ) (ps : Fin (n + 1) → unitInterval) : ℝ :=
  1 / Real.log (((d : ℝ) + 2) / Dv d ps)

theorem one_add_div_eq (d : ℕ) (ps : Fin (n + 1) → unitInterval) :
    1 + pLast ps / Dv d ps = ((d : ℝ) + 2) / Dv d ps := by
  have := Dv_pos d ps
  unfold Dv at *
  field_simp
  ring

/-- At `B = 1`, `eta = 1/(d+2)`, `beta = 0`, copy `j` has radius `1 - p_j/(d+2)`. -/
theorem sgd_radius_B1 (hp : ∀ j, 0 < (ps j : ℝ)) (j : Fin (n + 1)) :
    stepRadius (copyParams d 1 ν 0 (1 / ((d : ℝ) + 2)) ps j) = 1 - (ps j : ℝ) / ((d : ℝ) + 2) := by
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hload : (copyParams d 1 ν 0 (1 / ((d : ℝ) + 2)) ps j).totalLoad = 1 / 2 := by
    have := params_totalLoad d 1 (ps j) (hp j).ne' ν 0 (1 / ((d : ℝ) + 2))
    show (params d 1 (ps j) ν 0 _).totalLoad = _
    rw [this, inv_crit_zero one_pos]
    push_cast
    field_simp
    ring
  rw [stepRadius_beta_zero _ rfl, hload, copyParams_w]
  have hp1 : (ps j : ℝ) ≤ 1 := (ps j).2.2
  have e : 1 - 2 * (1 / ((d : ℝ) + 2) * (1 - 0) * (ps j : ℝ)) * (1 - 1 / 2)
      = 1 - (ps j : ℝ) / ((d : ℝ) + 2) := by
    field_simp
    ring
  rw [e, abs_of_nonneg]
  rw [sub_nonneg, div_le_one hd2]
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem sgd_rhoMax_B1 (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) :
    rhoMax d 1 ν 0 (1 / ((d : ℝ) + 2)) ps = 1 - pLast ps / ((d : ℝ) + 2) := by
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    show stepRadius (copyParams d 1 ν 0 (1 / ((d : ℝ) + 2)) ps j) ≤ _
    rw [sgd_radius_B1 hp j]
    have := last_le_ps hanti j
    have : pLast ps / ((d : ℝ) + 2) ≤ (ps j : ℝ) / ((d : ℝ) + 2) :=
      div_le_div_of_nonneg_right this hd2.le
    linarith
  · have := le_rhoMax (d := d) (B := 1) (ν := ν) (beta := 0) (eta := 1 / ((d : ℝ) + 2))
      (ps := ps) (Fin.last n)
    rw [sgd_radius_B1 hp] at this
    exact this

/-- Lower bound on the radius from the rarest copy (`prop:helps-critical`, Step 3). -/
theorem sgd_rhoMax_ge_V (hp : ∀ j, 0 < (ps j : ℝ)) (hB : 0 < B) {η : ℝ} (hη : 0 < η)
    (hstab : ∀ j, stepRadius (copyParams d B ν 0 η ps j) < 1) :
    Dv d ps / (Dv d ps + B * pLast ps) ≤ rhoMax d B ν 0 η ps := by
  obtain ⟨x, hx, _, hx2, _⟩ := sgd_radius_eq hB hp hη rfl (hstab (Fin.last n))
  have hcrit := crit_zero_eq (d := d) hB (ps (Fin.last n))
  have hD := Dv_pos d ps
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hpl : 0 < pLast ps := hp _
  have hBp : 0 < Dv d ps + B * pLast ps := by positivity
  have hx3 : x ≤ B * pLast ps / (Dv d ps + B * pLast ps) := by
    calc x ≤ (ps (Fin.last n) : ℝ) * criticalRate d B (ps (Fin.last n)) 0 / 2 := hx2
      _ = B * pLast ps / (Dv d ps + B * pLast ps) := by
        rw [hcrit]
        unfold Dv pLast at *
        field_simp
  have := le_rhoMax (d := d) (B := B) (ν := ν) (beta := 0) (eta := η) (ps := ps) (Fin.last n)
  have e : Dv d ps / (Dv d ps + B * pLast ps) = 1 - B * pLast ps / (Dv d ps + B * pLast ps) := by
    field_simp
    ring
  linarith

theorem sgd_Lmin_le (hp : ∀ j, 0 < (ps j : ℝ)) (hB : 0 < B) {η : ℝ} (hη : 0 < η)
    (hstab : ∀ j, stepRadius (copyParams d B ν 0 η ps j) < 1) :
    Lmin d B ν 0 η ps ≤ Real.log (1 + B * (pLast ps / Dv d ps)) := by
  have hD := Dv_pos d ps
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hpl : 0 < pLast ps := hp _
  have hq : 0 < Dv d ps / (Dv d ps + B * pLast ps) := by positivity
  have h1 := Real.log_le_log hq (sgd_rhoMax_ge_V hp hB hη hstab)
  have e : Real.log (Dv d ps / (Dv d ps + B * pLast ps)) = -Real.log (1 + B * (pLast ps / Dv d ps)) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  unfold Lmin
  linarith

/-- Real core of Step 3: Bernoulli. -/
theorem bernoulli_aux {B : ℕ} (hB : 1 ≤ B) {a Lm : ℝ} (ha : 0 < a) (hLm : 0 < Lm)
    (hLle : Lm ≤ Real.log (1 + B * a)) :
    1 / Real.log (1 + a) ≤ B * (1 / Lm) ∧ 1 / a ≤ B * (1 / Lm) := by
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBb : (0 : ℝ) < B := by linarith
  have hBa : 0 < (B : ℝ) * a := mul_pos hBb ha
  have hpos : 0 < 1 + (B : ℝ) * a := by linarith
  have hL0 : 0 < Real.log (1 + B * a) := Real.log_pos (by linarith)
  have hLa : 0 < Real.log (1 + a) := Real.log_pos (by linarith)
  have h1 : 1 / Real.log (1 + B * a) ≤ 1 / Lm := one_div_le_one_div_of_le hLm hLle
  have hbern : 1 + (B : ℝ) * a ≤ (1 + a) ^ B := one_add_mul_le_pow (by linarith) B
  have hL_le : Real.log (1 + B * a) ≤ B * Real.log (1 + a) := by
    rw [← Real.log_pow]
    exact Real.log_le_log hpos hbern
  have hL_le2 : Real.log (1 + B * a) ≤ B * a := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have h2 : B * (1 / Real.log (1 + B * a)) ≤ B * (1 / Lm) :=
    mul_le_mul_of_nonneg_left h1 hBb.le
  constructor
  · refine le_trans ?_ h2
    rw [mul_one_div, div_le_div_iff₀ hLa hL0]
    linarith
  · refine le_trans ?_ h2
    rw [mul_one_div, div_le_div_iff₀ ha hL0]
    linarith

/-- `B/Λ_min` for SGD: `≥ 1/log(1+a)` and `≥ D/p_V`, with `a = p_V/D` (Step 3). -/
theorem sgd_B_div_Lmin (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) (hB : 1 ≤ B)
    {η : ℝ} (hη : 0 < η) (hstab : ∀ j, stepRadius (copyParams d B ν 0 η ps j) < 1) :
    1 / Real.log (1 + pLast ps / Dv d ps) ≤ B * (1 / Lmin d B ν 0 η ps) ∧
      Dv d ps / pLast ps ≤ B * (1 / Lmin d B ν 0 η ps) := by
  have hB0 : 0 < B := hB
  have hD := Dv_pos d ps
  have hpl : 0 < pLast ps := hp _
  have ha : 0 < pLast ps / Dv d ps := div_pos hpl hD
  have hmem : ((η, (0 : ℝ)) : ℝ × ℝ) ∈ admSet d B ν ps sgdClass :=
    ⟨hη, Set.mem_singleton _, fun j => hstab j⟩
  have hLpos : 0 < Lmin d B ν 0 η ps := by
    have := Lmin_pos_of_mem hp hκ sgdClass_sub hmem
    exact this
  have hLle := sgd_Lmin_le hp hB0 hη hstab
  have := bernoulli_aux hB ha hLpos hLle
  refine ⟨this.1, ?_⟩
  have e : Dv d ps / pLast ps = 1 / (pLast ps / Dv d ps) := by rw [one_div_div]
  rw [e]; exact this.2

theorem Efun_sgd_ge (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) (hB : 1 ≤ B) :
    Esgd1 d ps ≤ Efun d B ν ps sgdClass := by
  have hBb : (0 : ℝ) < B := by exact_mod_cast hB
  have hc : Esgd1 d ps / B ≤ Sfun d B ν ps sgdClass := by
    apply Sfun_ge hp zero_mem_sgdClass hB
    intro x hx
    obtain ⟨η, β⟩ := x
    obtain ⟨hη, hβ, hst⟩ := hx
    have hb : β = 0 := hβ
    subst hb
    have h := (sgd_B_div_Lmin hp hκ hB hη hst).1
    rw [div_le_iff₀ hBb, mul_comm]
    unfold Esgd1
    rw [← one_add_div_eq d ps]
    exact h
  unfold Efun
  calc Esgd1 d ps = B * (Esgd1 d ps / B) := by field_simp
    _ ≤ B * Sfun d B ν ps sgdClass := mul_le_mul_of_nonneg_left hc hBb.le

theorem Efun_sgd_one (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps) :
    Efun d 1 ν ps sgdClass = Esgd1 d ps := by
  apply le_antisymm
  · have h := Sfun_le hp hκ sgdClass_sub
      (sgd_point_mem (d := d) (ν := ν) hp (le_refl 1) zero_mem_sgdClass)
    unfold Efun
    simp only [Nat.cast_one, one_mul]
    refine h.trans (le_of_eq ?_)
    show 1 / Lmin d 1 ν 0 (1 / ((d : ℝ) + 2)) ps = _
    unfold Lmin
    rw [sgd_rhoMax_B1 hp hanti]
    unfold Esgd1
    congr 1
    have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
    have : 1 - pLast ps / ((d : ℝ) + 2) = Dv d ps / ((d : ℝ) + 2) := by
      unfold Dv; field_simp
    rw [this, ← Real.log_inv, inv_div]
  · exact Efun_sgd_ge hp hκ (le_refl 1)

theorem Einf_sgd (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps) :
    Einf d ν ps sgdClass = Esgd1 d ps := by
  apply le_antisymm
  · have := Einf_le hp hκ sgdClass_sub zero_mem_sgdClass (d := d) (ν := ν) (B := 1) (le_refl 1)
    rwa [Efun_sgd_one hp hanti hκ] at this
  · exact Einf_ge (fun B hB => Efun_sgd_ge hp hκ hB)

theorem Esgd1_bounds (d : ℕ) (ps : Fin (n + 1) → unitInterval) (hp : 0 < pLast ps) :
    Dv d ps / pLast ps ≤ Esgd1 d ps ∧ Esgd1 d ps ≤ ((d : ℝ) + 2) / pLast ps := by
  have hD := Dv_pos d ps
  have ha : 0 < pLast ps / Dv d ps := div_pos hp hD
  have hlog0 : 0 < Real.log (1 + pLast ps / Dv d ps) := Real.log_pos (by linarith)
  have e : Esgd1 d ps = 1 / Real.log (1 + pLast ps / Dv d ps) := by
    unfold Esgd1; rw [one_add_div_eq d ps]
  rw [e]
  have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 + pLast ps / Dv d ps by linarith)
  have h2 := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + pLast ps / Dv d ps by linarith)
  constructor
  · have : 1 / (pLast ps / Dv d ps) ≤ 1 / Real.log (1 + pLast ps / Dv d ps) :=
      one_div_le_one_div_of_le hlog0 (by linarith)
    rwa [one_div_div] at this
  · have hq : 0 < 1 - (1 + pLast ps / Dv d ps)⁻¹ := by
      have : (1 + pLast ps / Dv d ps)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
      linarith
    have := one_div_le_one_div_of_le hq h2
    refine this.trans (le_of_eq ?_)
    have key : ∀ a : ℝ, 0 < a → 1 / (1 - (1 + a)⁻¹) = (1 + a) / a := by
      intro a ha
      have : (1 + a) ≠ 0 := by linarith
      have : a ≠ 0 := ha.ne'
      field_simp
      simp [this]
    rw [key _ ha, one_add_div_eq d ps, div_div_div_cancel_right₀ hD.ne']

/-! ### Momentum: the fewest samples -/

theorem first_copy_ceiling (hp : ∀ j, 0 < (ps j : ℝ)) {β η : ℝ} (hη : 0 < η) (hb0 : 0 ≤ β)
    (hb1 : β < 1) (hst0 : stepRadius (copyParams d B ν β η ps 0) < 1) :
    η * (1 - β) * (ps 0 : ℝ) < 2 * (1 + β) := by
  have hl := copy_load_lt_one_of_stable hp hb0 hb1 hη hst0
  have hcurv : (copyParams d B ν β η ps 0).curvature < 1 := by
    have h := copyParams_noise_nonneg (d := d) (B := B) (ν := ν) (beta := β) hp hη.le 0
    have hload : (copyParams d B ν β η ps 0).totalLoad = η * inverseCriticalRate d B (ps 0) β :=
      params_totalLoad d B (ps 0) (hp 0).ne' ν β η
    unfold Params.totalLoad at hload
    linarith
  unfold Params.curvature at hcurv
  rw [div_lt_one (by show 0 < 2 * (1 + β); linarith)] at hcurv
  exact hcurv

/-- Real core of Step 4. -/
theorem mom_real_aux {B D pV η β s Lm R : ℝ} (hB : 0 < B) (hD : 0 < D) (hpV : 0 < pV)
    (hη : 0 < η) (he0 : 0 < 1 - β) (hs4 : 4 < s) (hηD : η * D < 2 * B)
    (hmsq : min (1 - β) (4 * η * pV) ≤ 4 / s)
    (hR : 1 - min (1 - β) (4 * η * pV) ≤ R) (hL : Lm = -Real.log R) (hLpos : 0 < Lm) :
    (1 - 4 / s) * D / (8 * pV) ≤ B * (1 / Lm) := by
  have hm0 : 0 < min (1 - β) (4 * η * pV) := lt_min he0 (by positivity)
  have hm2 : min (1 - β) (4 * η * pV) ≤ 4 * η * pV := min_le_right _ _
  generalize min (1 - β) (4 * η * pV) = m at *
  have hs0 : 0 < s := by linarith
  have h4s : 4 / s < 1 := by rw [div_lt_one hs0]; exact hs4
  have hm1 : m < 1 := lt_of_le_of_lt hmsq h4s
  have h1m : 0 < 1 - m := by linarith
  have hlog := Real.log_le_log h1m hR
  have hle := neg_log_one_sub_le_vocab hm1
  have hLle : Lm ≤ m / (1 - m) := by rw [hL]; linarith
  have hinv : (1 - m) / m ≤ 1 / Lm := by
    have := one_div_le_one_div_of_le hLpos hLle
    rwa [one_div_div] at this
  have hBm : m * D / (8 * pV) ≤ B := by
    rw [div_le_iff₀ (by positivity)]
    have : m * D ≤ 4 * η * pV * D := mul_le_mul_of_nonneg_right hm2 hD.le
    nlinarith [mul_pos hpV hD]
  have h2 : (m * D / (8 * pV)) * ((1 - m) / m) ≤ B * (1 / Lm) :=
    mul_le_mul hBm hinv (div_nonneg h1m.le hm0.le) hB.le
  have e : (m * D / (8 * pV)) * ((1 - m) / m) = D * (1 - m) / (8 * pV) := by
    field_simp
  rw [e] at h2
  refine le_trans ?_ h2
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [mul_nonneg hD.le (sub_nonneg.2 hmsq)]

/-- `φ(m) ≥ √(1-m)` for `0 ≤ m < 1`, with `φ(m) = m/(-log(1-m))`, i.e.
`-log(1-m) ≤ m/√(1-m)`; this is `2 log s ≤ s - 1/s` with `s = (1-m)^{-1/2}` (`prop:helps-critical`
Step 4), derived from `log_div_le_two_mul_div` at `x = (1-t)/(1+t)`, `t = √(1-m)`. -/
theorem neg_log_one_sub_le_div_sqrt {m : ℝ} (h0 : 0 ≤ m) (h1 : m < 1) :
    -Real.log (1 - m) ≤ m / Real.sqrt (1 - m) := by
  have hpos : 0 < 1 - m := by linarith
  set t := Real.sqrt (1 - m) with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 hpos
  have ht2 : t ^ 2 = 1 - m := Real.sq_sqrt hpos.le
  have ht1 : t ≤ 1 := by nlinarith
  have hx0 : 0 ≤ (1 - t) / (1 + t) := div_nonneg (by linarith) (by linarith)
  have hx1 : (1 - t) / (1 + t) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := log_div_le_two_mul_div hx0 hx1
  have ht1' : (1 + t) ≠ 0 := by linarith
  have a1 : 1 + (1 - t) / (1 + t) = 2 / (1 + t) := by field_simp; ring
  have a2 : 1 - (1 - t) / (1 + t) = 2 * t / (1 + t) := by field_simp; ring
  have e1 : (1 + (1 - t) / (1 + t)) / (1 - (1 - t) / (1 + t)) = 1 / t := by
    rw [a1, a2]; field_simp
  have e2 : 2 * ((1 - t) / (1 + t)) / (1 - ((1 - t) / (1 + t)) ^ 2) = m / (2 * t) := by
    have hm : m = 1 - t ^ 2 := by linarith
    rw [hm]
    have : 1 - ((1 - t) / (1 + t)) ^ 2 = 4 * t / (1 + t) ^ 2 := by
      field_simp; ring
    rw [this]
    field_simp
    ring
  rw [e1, e2] at h
  have e3 : -Real.log (1 - m) = 2 * Real.log (1 / t) := by
    rw [← ht2, one_div, Real.log_inv, Real.log_pow]; push_cast; ring
  rw [e3]
  have : m / t = 2 * (m / (2 * t)) := by field_simp
  rw [this]; linarith

/-- Properties of `M = 4/(1+√(1+κ))` (`m_κ` of the tex) for `κ > 16`. -/
theorem Mk_props {κ : ℝ} (hκ : 16 < κ) :
    0 < 4 / (1 + Real.sqrt (1 + κ)) ∧ 4 / (1 + Real.sqrt (1 + κ)) < 4 / 5 ∧
      4 / (1 + Real.sqrt (1 + κ)) < 4 / Real.sqrt κ ∧
      κ * (4 / (1 + Real.sqrt (1 + κ))) ^ 2 + 8 * (4 / (1 + Real.sqrt (1 + κ))) = 16 := by
  have hq4 : 4 < Real.sqrt (1 + κ) := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hq2 : Real.sqrt (1 + κ) ^ 2 = 1 + κ := Real.sq_sqrt (by linarith)
  have hsk : Real.sqrt κ < Real.sqrt (1 + κ) := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hsk0 : 0 < Real.sqrt κ := Real.sqrt_pos.2 (by linarith)
  have h1q : 0 < 1 + Real.sqrt (1 + κ) := by linarith
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [div_lt_div_iff₀ h1q (by norm_num)]; linarith
  · exact div_lt_div_of_pos_left (by norm_num) hsk0 (by linarith)
  · have hk : κ = Real.sqrt (1 + κ) ^ 2 - 1 := by linarith
    set q := Real.sqrt (1 + κ)
    rw [hk]
    field_simp
    ring

/-- `max(1 - 4/√κ, 1/√5) ≤ √(1 - m_κ)` for `κ > 16` (`1 - m_κ > 1/5` and `m_κ < 4/√κ`). -/
theorem cK_le_sqrt_one_sub {κ : ℝ} (hκ : 16 < κ) :
    max (1 - 4 / Real.sqrt κ) (1 / Real.sqrt 5)
      ≤ Real.sqrt (1 - 4 / (1 + Real.sqrt (1 + κ))) := by
  obtain ⟨hM0, hM45, hM4, -⟩ := Mk_props hκ
  set M := 4 / (1 + Real.sqrt (1 + κ)) with hM
  have h1M : 0 < 1 - M := by linarith
  have h1 : 1 - M ≤ Real.sqrt (1 - M) := by
    rw [Real.le_sqrt' h1M]; nlinarith
  have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have h2 : 1 / Real.sqrt 5 ≤ Real.sqrt (1 - M) := by
    rw [Real.le_sqrt' (by positivity), div_pow, Real.sq_sqrt (by norm_num)]
    norm_num; linarith
  exact max_le (by linarith) h2

/-- The case split `min(ε, 4ηp_V) ≤ m_κ` of Step 4: if `q κ e < 8(2-e)` then `min e q ≤ m_κ`. -/
theorem min_le_Mk {e q κ : ℝ} (_he : 0 < e) (_hq : 0 < q) (hκ : 16 < κ)
    (h : q * κ * e < 8 * (2 - e)) : min e q ≤ 4 / (1 + Real.sqrt (1 + κ)) := by
  obtain ⟨hM0, -, -, hMeq⟩ := Mk_props hκ
  set M := 4 / (1 + Real.sqrt (1 + κ))
  by_contra hcon
  rw [not_le, lt_min_iff] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have h3 : M * M < q * e := mul_lt_mul'' h2 h1 hM0.le hM0.le
  nlinarith

/-- Real core of Step 4 with the sharp constant: `max(1 - 4/√κ, 1/√5) · D/(8 p_V) ≤ B/Λ`. -/
theorem mom_real_aux2 {B D pV η β κ Lm R : ℝ} (hB : 0 < B) (hD : 0 < D) (hpV : 0 < pV)
    (hη : 0 < η) (he0 : 0 < 1 - β) (hκ : 16 < κ)
    (hceil : 4 * η * pV * κ * (1 - β) < 8 * (2 - (1 - β))) (hηD : η * D < 2 * B)
    (hR : 1 - min (1 - β) (4 * η * pV) ≤ R) (hL : Lm = -Real.log R) (hLpos : 0 < Lm) :
    max (1 - 4 / Real.sqrt κ) (1 / Real.sqrt 5) * D / (8 * pV) ≤ B * (1 / Lm) := by
  have hm0 : 0 < min (1 - β) (4 * η * pV) := lt_min he0 (by positivity)
  have hm2 : min (1 - β) (4 * η * pV) ≤ 4 * η * pV := min_le_right _ _
  have hmM : min (1 - β) (4 * η * pV) ≤ 4 / (1 + Real.sqrt (1 + κ)) :=
    min_le_Mk he0 (by positivity) hκ hceil
  have hcK := cK_le_sqrt_one_sub hκ
  obtain ⟨hM0, hM45, -, -⟩ := Mk_props hκ
  generalize min (1 - β) (4 * η * pV) = m at *
  generalize 4 / (1 + Real.sqrt (1 + κ)) = M at *
  have hm1 : m < 1 := by linarith
  have h1m : 0 < 1 - m := by linarith
  have hlog := Real.log_le_log h1m hR
  have hA := neg_log_one_sub_le_div_sqrt hm0.le hm1
  have hs0 : 0 < Real.sqrt (1 - m) := Real.sqrt_pos.2 h1m
  have hLle : Lm ≤ m / Real.sqrt (1 - m) := by rw [hL]; linarith
  have hinv : Real.sqrt (1 - m) / m ≤ 1 / Lm := by
    have := one_div_le_one_div_of_le hLpos hLle
    rwa [one_div_div] at this
  have hBm : m * D / (8 * pV) ≤ B := by
    rw [div_le_iff₀ (by positivity)]
    have : m * D ≤ 4 * η * pV * D := mul_le_mul_of_nonneg_right hm2 hD.le
    nlinarith [mul_pos hpV hD]
  have h2 : (m * D / (8 * pV)) * (Real.sqrt (1 - m) / m) ≤ B * (1 / Lm) :=
    mul_le_mul hBm hinv (div_nonneg hs0.le hm0.le) hB.le
  have e : (m * D / (8 * pV)) * (Real.sqrt (1 - m) / m)
      = D * Real.sqrt (1 - m) / (8 * pV) := by
    field_simp
  rw [e] at h2
  refine le_trans ?_ h2
  have hmono : Real.sqrt (1 - M) ≤ Real.sqrt (1 - m) := Real.sqrt_le_sqrt (by linarith)
  have hc : max (1 - 4 / Real.sqrt κ) (1 / Real.sqrt 5) ≤ Real.sqrt (1 - m) := hcK.trans hmono
  rw [mul_comm D, mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hc (by positivity)

theorem mom_B_div_Lmin' (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 16 < kappaV ps) (hB : 1 ≤ B)
    {η β : ℝ} (hη : 0 < η) (hb0 : 0 < β) (hb1 : β < 1)
    (hstab : ∀ j, stepRadius (copyParams d B ν β η ps j) < 1) :
    max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Dv d ps / (8 * pLast ps)
      ≤ B * (1 / Lmin d B ν β η ps) := by
  have hκ1 : 1 < kappaV ps := by linarith
  have hB0 : 0 < B := hB
  have hBb : (0 : ℝ) < B := by exact_mod_cast hB0
  have he0 : 0 < 1 - β := by linarith
  have hD := Dv_pos d ps
  have hpl : 0 < pLast ps := hp _
  have hk0 : 0 < kappaV ps := by linarith
  have hlow : β ≤ stepRadius (copyParams d B ν β η ps (Fin.last n)) ∧
      (4 * η * pLast ps < 1 →
        1 - 4 * η * pLast ps ≤ stepRadius (copyParams d B ν β η ps (Fin.last n))) :=
    momentum_radius_lower (d := d) (B := B) (ν := ν) hp hb0 hb1 hη (Fin.last n)
  have hrad := le_rhoMax (d := d) (B := B) (ν := ν) (beta := β) (eta := η) (ps := ps)
    (Fin.last n)
  have hrho : 1 - min (1 - β) (4 * η * pLast ps) ≤ rhoMax d B ν β η ps := by
    rcases min_choice (1 - β) (4 * η * pLast ps) with h | h
    · rw [h]; have := hlow.1; linarith
    · rw [h]
      have h4 : 4 * η * pLast ps < 1 := by
        have := min_le_left (1 - β) (4 * η * pLast ps); rw [h] at this; linarith
      have := hlow.2 h4
      linarith
  have hceil := first_copy_ceiling hp hη hb0.le hb1 (hstab 0)
  have hk : kappaV ps * pLast ps = (ps 0 : ℝ) := div_mul_cancel₀ _ (hp _).ne'
  have hceil' : 4 * η * pLast ps * kappaV ps * (1 - β) < 8 * (2 - (1 - β)) := by
    have e : 4 * η * pLast ps * kappaV ps * (1 - β) = 4 * (η * (1 - β) * (ps 0 : ℝ)) := by
      rw [← hk]; ring
    rw [e]; linarith
  have hl := copy_load_lt_one_of_stable hp hb0.le hb1 hη (hstab (Fin.last n))
  have hq := noise_part_le_inverseCriticalRate (d := d) (B := B) (ps (Fin.last n)) hb0.le hb1
  have hηD : η * Dv d ps < 2 * B := by
    have h1 : η * (Dv d ps / (2 * B)) < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hq hη.le) hl
    have : η * (Dv d ps / (2 * B)) = η * Dv d ps / (2 * B) := by ring
    rw [this, div_lt_one (by positivity)] at h1
    exact h1
  have hmem : ((η, β) : ℝ × ℝ) ∈ admSet d B ν ps momClass := ⟨hη, ⟨hb0.le, hb1⟩, fun j => hstab j⟩
  have hLpos : 0 < Lmin d B ν β η ps := by
    have := Lmin_pos_of_mem hp hκ1 momClass_sub hmem
    exact this
  exact mom_real_aux2 hBb hD hpl hη he0 hκ hceil' hηD hrho rfl hLpos

theorem mom_B_div_Lmin (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 16 < kappaV ps) (hB : 1 ≤ B)
    {η β : ℝ} (hη : 0 < η) (hb0 : 0 < β) (hb1 : β < 1)
    (hstab : ∀ j, stepRadius (copyParams d B ν β η ps j) < 1) :
    (1 - 4 / Real.sqrt (kappaV ps)) * Dv d ps / (8 * pLast ps)
      ≤ B * (1 / Lmin d B ν β η ps) := by
  have hκ1 : 1 < kappaV ps := by linarith
  have hB0 : 0 < B := hB
  have hBb : (0 : ℝ) < B := by exact_mod_cast hB0
  have he0 : 0 < 1 - β := by linarith
  have hD := Dv_pos d ps
  have hpl : 0 < pLast ps := hp _
  have hk0 : 0 < kappaV ps := by linarith
  have hs0 : 0 < Real.sqrt (kappaV ps) := Real.sqrt_pos.2 hk0
  have hs4 : 4 < Real.sqrt (kappaV ps) := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) hκ
  have hlow : β ≤ stepRadius (copyParams d B ν β η ps (Fin.last n)) ∧
      (4 * η * pLast ps < 1 →
        1 - 4 * η * pLast ps ≤ stepRadius (copyParams d B ν β η ps (Fin.last n))) :=
    momentum_radius_lower (d := d) (B := B) (ν := ν) hp hb0 hb1 hη (Fin.last n)
  have hrad := le_rhoMax (d := d) (B := B) (ν := ν) (beta := β) (eta := η) (ps := ps)
    (Fin.last n)
  have hrho : 1 - min (1 - β) (4 * η * pLast ps) ≤ rhoMax d B ν β η ps := by
    rcases min_choice (1 - β) (4 * η * pLast ps) with h | h
    · rw [h]; have := hlow.1; linarith
    · rw [h]
      have h4 : 4 * η * pLast ps < 1 := by
        have := min_le_left (1 - β) (4 * η * pLast ps); rw [h] at this; linarith
      have := hlow.2 h4
      linarith
  have hceil := first_copy_ceiling hp hη hb0.le hb1 (hstab 0)
  have hk : kappaV ps * pLast ps = (ps 0 : ℝ) := div_mul_cancel₀ _ (hp _).ne'
  have h16 : 4 * η * pLast ps < (16 / kappaV ps) / (1 - β) := by
    rw [lt_div_iff₀ he0, lt_div_iff₀ hk0]
    have e : 4 * η * pLast ps * (1 - β) * kappaV ps = 4 * (η * (1 - β) * (ps 0 : ℝ)) := by
      rw [← hk]; ring
    rw [e]; linarith
  have hmin := min_le_sqrt he0 (div_pos (by norm_num : (0 : ℝ) < 16) hk0)
  have hsq : Real.sqrt (16 / kappaV ps) = 4 / Real.sqrt (kappaV ps) := by
    rw [Real.sqrt_div (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [hsq] at hmin
  have hmsq : min (1 - β) (4 * η * pLast ps) ≤ 4 / Real.sqrt (kappaV ps) :=
    le_trans (min_le_min le_rfl h16.le) hmin
  have hl := copy_load_lt_one_of_stable hp hb0.le hb1 hη (hstab (Fin.last n))
  have hq := noise_part_le_inverseCriticalRate (d := d) (B := B) (ps (Fin.last n)) hb0.le hb1
  have hηD : η * Dv d ps < 2 * B := by
    have h1 : η * (Dv d ps / (2 * B)) < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hq hη.le) hl
    have : η * (Dv d ps / (2 * B)) = η * Dv d ps / (2 * B) := by ring
    rw [this, div_lt_one (by positivity)] at h1
    exact h1
  have hmem : ((η, β) : ℝ × ℝ) ∈ admSet d B ν ps momClass := ⟨hη, ⟨hb0.le, hb1⟩, fun j => hstab j⟩
  have hLpos : 0 < Lmin d B ν β η ps := by
    have := Lmin_pos_of_mem hp hκ1 momClass_sub hmem
    exact this
  exact mom_real_aux hBb hD hpl hη he0 hs4 hηD hmsq hrho rfl hLpos

/-- Fewest samples with momentum, lower bound: for every `B ≥ 1`
`E_mom(B) ≥ (1 - 4/√κ) D / (8 p_V)` (`κ > 16`). -/
theorem Efun_mom_ge (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 16 < kappaV ps) (hB : 1 ≤ B) :
    (1 - 4 / Real.sqrt (kappaV ps)) * Dv d ps / (8 * pLast ps) ≤ Efun d B ν ps momClass := by
  have hκ1 : 1 < kappaV ps := by linarith
  have hBb : (0 : ℝ) < B := by exact_mod_cast hB
  have hD := Dv_pos d ps
  have hpl : 0 < pLast ps := hp _
  have hk0 : 0 < kappaV ps := by linarith
  have hs0 : 0 < Real.sqrt (kappaV ps) := Real.sqrt_pos.2 hk0
  have hc : (1 - 4 / Real.sqrt (kappaV ps)) * Dv d ps / (8 * pLast ps) / B
      ≤ Sfun d B ν ps momClass := by
    apply Sfun_ge hp zero_mem_momClass hB
    intro x hx
    obtain ⟨η, β⟩ := x
    obtain ⟨hη, hβ, hst⟩ := hx
    have hβ' : 0 ≤ β ∧ β < 1 := hβ
    rw [div_le_iff₀ hBb]
    rcases hβ'.1.lt_or_eq with hpos | hz
    · exact (mom_B_div_Lmin hp hκ hB hη hpos hβ'.2 hst).trans (le_of_eq (mul_comm _ _))
    · have hz' : β = 0 := hz.symm
      subst hz'
      have h := (sgd_B_div_Lmin hp hκ1 hB hη hst).2
      have h5 : (1 - 4 / Real.sqrt (kappaV ps)) * Dv d ps / (8 * pLast ps)
          ≤ Dv d ps / pLast ps := by
        rw [div_le_div_iff₀ (by positivity) hpl]
        have h4 : 0 ≤ 4 / Real.sqrt (kappaV ps) := by positivity
        nlinarith [mul_pos hD hpl]
      exact (h5.trans h).trans (le_of_eq (mul_comm _ _))
  unfold Efun
  calc _ = B * ((1 - 4 / Real.sqrt (kappaV ps)) * Dv d ps / (8 * pLast ps) / B) := by
        field_simp
    _ ≤ B * Sfun d B ν ps momClass := mul_le_mul_of_nonneg_left hc hBb.le

/-- Fewest samples with momentum, lower bound with the sharp constant of the tex: for every `B ≥ 1`
`E_mom(B) ≥ c_κ D / (8 p_V)`, `c_κ = max(1 - 4/√κ, 1/√5)` (`κ > 16`). -/
theorem Efun_mom_ge' (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 16 < kappaV ps) (hB : 1 ≤ B) :
    max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Dv d ps / (8 * pLast ps)
      ≤ Efun d B ν ps momClass := by
  have hκ1 : 1 < kappaV ps := by linarith
  have hBb : (0 : ℝ) < B := by exact_mod_cast hB
  have hD := Dv_pos d ps
  have hpl : 0 < pLast ps := hp _
  have hc : max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Dv d ps / (8 * pLast ps) / B
      ≤ Sfun d B ν ps momClass := by
    apply Sfun_ge hp zero_mem_momClass hB
    intro x hx
    obtain ⟨η, β⟩ := x
    obtain ⟨hη, hβ, hst⟩ := hx
    have hβ' : 0 ≤ β ∧ β < 1 := hβ
    rw [div_le_iff₀ hBb]
    rcases hβ'.1.lt_or_eq with hpos | hz
    · exact (mom_B_div_Lmin' hp hκ hB hη hpos hβ'.2 hst).trans (le_of_eq (mul_comm _ _))
    · have hz' : β = 0 := hz.symm
      subst hz'
      have h := (sgd_B_div_Lmin hp hκ1 hB hη hst).2
      have hc1 : max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) ≤ 1 :=
        max_le (by have : 0 ≤ 4 / Real.sqrt (kappaV ps) := by positivity
                   linarith)
          (by rw [div_le_one (Real.sqrt_pos.2 (by norm_num))]
              rw [show (1 : ℝ) = Real.sqrt 1 by simp]
              exact Real.sqrt_le_sqrt (by norm_num))
      have hc0 : 0 ≤ max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) :=
        le_trans (by positivity) (le_max_right _ _)
      have h5 : max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Dv d ps / (8 * pLast ps)
          ≤ Dv d ps / pLast ps := by
        rw [div_le_div_iff₀ (by positivity) hpl]
        nlinarith [mul_pos hD hpl, mul_nonneg hc0 (mul_pos hD hpl).le]
      exact (h5.trans h).trans (le_of_eq (mul_comm _ _))
  unfold Efun
  calc _ = B * (max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Dv d ps
          / (8 * pLast ps) / B) := by
        field_simp
    _ ≤ B * Sfun d B ν ps momClass := mul_le_mul_of_nonneg_left hc hBb.le

theorem Efun_mom_le_sgd (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) (hB : 1 ≤ B) :
    Efun d B ν ps momClass ≤ Efun d B ν ps sgdClass :=
  mul_le_mul_of_nonneg_left (Sfun_mom_le_sgd hp hκ hB) (Nat.cast_nonneg B)

/-! ### The fewest steps: `S_O = 1/λ_O` -/

theorem lamSGD_pos (hκ : 1 < kappaV ps) : 0 < lamSGD ps := by
  have hk0 : 0 < kappaV ps := by linarith
  have := (two_log_bounds hκ).1
  have : 0 < 4 / kappaV ps := by positivity
  unfold lamSGD; linarith [(two_log_bounds hκ).1]

theorem lamMom_pos (hκ : 1 < kappaV ps) : 0 < lamMom ps := by
  have hs1 := sqrt_kappa_gt_one hκ
  have h4 : 0 < 4 / Real.sqrt (kappaV ps) := by positivity
  unfold lamMom; linarith [(two_log_bounds hs1).1]

theorem Sfun_sgd_ge (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) (hB : 1 ≤ B) :
    1 / lamSGD ps ≤ Sfun d B ν ps sgdClass :=
  Sfun_ge hp zero_mem_sgdClass hB (fun _ hx =>
    one_div_le_one_div_of_le (Lmin_pos_of_mem hp hκ sgdClass_sub hx)
      (Lmin_le_lamSGD hp hκ hx))

theorem Sfun_mom_ge (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) (hB : 1 ≤ B) :
    1 / lamMom ps ≤ Sfun d B ν ps momClass :=
  Sfun_ge hp zero_mem_momClass hB (fun _ hx =>
    one_div_le_one_div_of_le (Lmin_pos_of_mem hp hκ momClass_sub hx)
      (Lmin_le_lamMom hp hκ momClass_sub hx))

/-- `S_SGD(B) → 1/λ_SGD` as `B → ∞`; the lower bound `S_SGD(B) ≥ 1/λ_SGD` holds at every `B ≥ 1`. -/
theorem Sfun_tendsto_sgd (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps) :
    Tendsto (fun B : ℕ => Sfun d B ν ps sgdClass) atTop (𝓝 (1 / lamSGD ps)) := by
  have hs : 0 < (ps 0 : ℝ) + (ps (Fin.last n) : ℝ) := by
    have := hp 0; have := hp (Fin.last n); linarith
  obtain ⟨-, hL, hev⟩ := largeBatch_sgd (d := d) (ν := ν) (beta := 0)
    (eta := 2 / ((ps 0 : ℝ) + (ps (Fin.last n) : ℝ))) hp hanti rfl rfl hκ
  have hlim : Tendsto (fun B : ℕ => 1 / Lmin d B ν 0 (2 / ((ps 0 : ℝ) + (ps (Fin.last n) : ℝ))) ps)
      atTop (𝓝 (1 / lamSGD ps)) :=
    tendsto_const_nhds.div hL (lamSGD_pos hκ).ne'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with B hB
    exact Sfun_sgd_ge hp hκ hB
  · filter_upwards [hev, eventually_ge_atTop 1] with B hst hB
    exact Sfun_le hp hκ sgdClass_sub
      (x := (2 / ((ps 0 : ℝ) + (ps (Fin.last n) : ℝ)), (0 : ℝ)))
      ⟨by positivity, Set.mem_singleton _, fun j => hst j⟩

theorem mom_params_exist (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) :
    ∃ β η : ℝ, 0 < β ∧ β < 1 ∧ 0 < η ∧
      Real.sqrt β = (Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1) ∧
      η * (1 - β) * (ps 0 : ℝ) = (1 + Real.sqrt β) ^ 2 := by
  have hs1 := sqrt_kappa_gt_one hκ
  set q : ℝ := (Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1) with hq
  have hq0 : 0 < q := div_pos (by linarith) (by linarith)
  have hq1 : q < 1 := by rw [hq, div_lt_one (by linarith)]; linarith
  have hβ0 : 0 < q ^ 2 := by positivity
  have hβ1 : q ^ 2 < 1 := by nlinarith
  have hsq : Real.sqrt (q ^ 2) = q := Real.sqrt_sq hq0.le
  refine ⟨q ^ 2, (1 + q) ^ 2 / ((1 - q ^ 2) * (ps 0 : ℝ)), hβ0, hβ1, ?_, hsq, ?_⟩
  · have := hp 0
    have : 0 < 1 - q ^ 2 := by linarith
    positivity
  · rw [hsq]
    have h1 : (1 - q ^ 2) ≠ 0 := by linarith
    have h2 : (ps 0 : ℝ) ≠ 0 := (hp 0).ne'
    field_simp

theorem Sfun_tendsto_mom (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps) :
    Tendsto (fun B : ℕ => Sfun d B ν ps momClass) atTop (𝓝 (1 / lamMom ps)) := by
  obtain ⟨β, η, hb0, hb1, hη, hr, hηe⟩ := mom_params_exist hp hκ
  obtain ⟨-, hL, hev⟩ := largeBatch_momentum (d := d) (ν := ν) (beta := β) (eta := η) hp hanti
    hb0 hb1 hκ hr hηe
  have hs1 := sqrt_kappa_gt_one hκ
  have hβe : -Real.log β = lamMom ps := by
    have hβ : β = ((Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1)) ^ 2 := by
      rw [← hr]; exact (Real.sq_sqrt hb0.le).symm
    rw [hβ]; exact neg_log_sq_div
  rw [hβe] at hL
  have hlim : Tendsto (fun B : ℕ => 1 / Lmin d B ν β η ps) atTop (𝓝 (1 / lamMom ps)) :=
    tendsto_const_nhds.div hL (lamMom_pos hκ).ne'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with B hB
    exact Sfun_mom_ge hp hκ hB
  · filter_upwards [hev, eventually_ge_atTop 1] with B hst hB
    exact Sfun_le hp hκ momClass_sub (x := (η, β)) ⟨hη, ⟨hb0.le, hb1⟩, fun j => hst j⟩

theorem Sinf_eq_of_tendsto (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) {K : Set ℝ}
    (hK : K ⊆ Set.Ico 0 1) (h0K : (0 : ℝ) ∈ K) {c : ℝ}
    (hge : ∀ B : ℕ, 1 ≤ B → c ≤ Sfun d B ν ps K)
    (hlim : Tendsto (fun B : ℕ => Sfun d B ν ps K) atTop (𝓝 c)) : Sinf d ν ps K = c :=
  le_antisymm
    (ge_of_tendsto hlim (by
      filter_upwards [eventually_ge_atTop 1] with B hB
      exact Sinf_le hp hκ hK h0K hB))
    (Sinf_ge hge)

/-- (i), exact values: `S_SGD = 1/λ_SGD`. -/
theorem Sinf_sgd (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps) :
    Sinf d ν ps sgdClass = 1 / lamSGD ps :=
  Sinf_eq_of_tendsto hp hκ sgdClass_sub zero_mem_sgdClass (fun _ hB => Sfun_sgd_ge hp hκ hB)
    (Sfun_tendsto_sgd hp hanti hκ)

/-- (i), exact values: `S_mom = 1/λ_mom`. -/
theorem Sinf_mom (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps) :
    Sinf d ν ps momClass = 1 / lamMom ps :=
  Sinf_eq_of_tendsto hp hκ momClass_sub zero_mem_momClass (fun _ hB => Sfun_mom_ge hp hκ hB)
    (Sfun_tendsto_mom hp hanti hκ)

/-- `1/(2 log ((y+1)/(y-1)))` between `(y/4)(1 - 1/y²)` and `y/4`, for `y > 1`. -/
theorem inv_two_log_bounds {y : ℝ} (hy : 1 < y) :
    y / 4 * (1 - 1 / y ^ 2) ≤ 1 / (2 * Real.log ((y + 1) / (y - 1))) ∧
      1 / (2 * Real.log ((y + 1) / (y - 1))) ≤ y / 4 := by
  obtain ⟨h1, h2⟩ := two_log_bounds hy
  have hy0 : 0 < y := by linarith
  have hy2 : 0 < y ^ 2 - 1 := by nlinarith
  have h4 : 0 < 4 / y := by positivity
  constructor
  · have hpos : 0 < 4 * y / (y ^ 2 - 1) := by positivity
    have := one_div_le_one_div_of_le (lt_of_lt_of_le h4 h1) h2
    refine le_trans (le_of_eq ?_) (by simpa using this)
    field_simp
  · have := one_div_le_one_div_of_le h4 h1
    refine le_trans (by simpa using this) (le_of_eq ?_)
    field_simp

/-! ### Part (ii): the fewest samples -/

theorem Einf_mom_ge (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 16 < kappaV ps) :
    (1 - 4 / Real.sqrt (kappaV ps)) * Dv d ps / (8 * pLast ps) ≤ Einf d ν ps momClass :=
  Einf_ge (fun _ hB => Efun_mom_ge hp hκ hB)

theorem Einf_mom_ge' (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 16 < kappaV ps) :
    max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Dv d ps / (8 * pLast ps)
      ≤ Einf d ν ps momClass :=
  Einf_ge (fun _ hB => Efun_mom_ge' hp hκ hB)

theorem Einf_mom_le_sgd (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps) :
    Einf d ν ps momClass ≤ Einf d ν ps sgdClass := by
  rw [Einf_sgd hp hanti hκ]
  have h1 := Einf_le hp hκ momClass_sub zero_mem_momClass (d := d) (ν := ν) (B := 1) (le_refl 1)
  have h2 := Efun_mom_le_sgd (d := d) (ν := ν) hp hκ (le_refl 1)
  rw [Efun_sgd_one hp hanti hκ] at h2
  exact h1.trans h2

/-! ### Part (iii): critical batch sizes -/

theorem Bcrit_sgd_eq (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps) :
    Bcrit d ν ps sgdClass = Esgd1 d ps * lamSGD ps := by
  unfold Bcrit
  rw [Einf_sgd hp hanti hκ, Sinf_sgd hp hanti hκ, one_div, div_inv_eq_mul]

theorem Bcrit_mom_eq (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps) :
    Bcrit d ν ps momClass = Einf d ν ps momClass * lamMom ps := by
  unfold Bcrit
  rw [Sinf_mom hp hanti hκ, one_div, div_inv_eq_mul]

theorem Esgd1_pos (hp : ∀ j, 0 < (ps j : ℝ)) : 0 < Esgd1 d ps := by
  have h := Esgd1_bounds d ps (hp _)
  have : 0 < Dv d ps / pLast ps := div_pos (Dv_pos d ps) (hp _)
  linarith [h.1]

theorem kappa_mul_pLast (hp : ∀ j, 0 < (ps j : ℝ)) : kappaV ps * pLast ps = (ps 0 : ℝ) :=
  div_mul_cancel₀ _ (hp _).ne'

/-- Real identity behind the lower bound of (iii) (`κ = s²`). -/
theorem ratio_identity {s κ D pV dd : ℝ} (hs : 1 < s) (hκ : κ = s ^ 2) (hpV : pV ≠ 0)
    (hdd : dd ≠ 0) (hD : D = dd - pV) :
    ((s - 4) / 8) * (1 - 1 / κ ^ 2) * (1 - pV / dd) * ((dd / pV) * (4 * κ / (κ ^ 2 - 1)))
      = (1 - 4 / s) * D / (8 * pV) * (4 / s) := by
  have hs0 : s ≠ 0 := by linarith
  have hs2 : 1 < s ^ 2 := by nlinarith
  have hs4 : 1 < s ^ 4 := by nlinarith
  have h1 : s ^ 4 - 1 ≠ 0 := by linarith
  subst hκ hD
  have e : (s ^ 2) ^ 2 = s ^ 4 := by ring
  rw [e]
  field_simp

/-- Real identity behind the lower bound of (iii) with a general constant `c` (`κ = s²`). -/
theorem ratio_identity_c {c s κ D pV dd : ℝ} (hs : 1 < s) (hκ : κ = s ^ 2) (hpV : pV ≠ 0)
    (hdd : dd ≠ 0) (hD : D = dd - pV) :
    (c * s / 8) * (1 - 1 / κ ^ 2) * (1 - pV / dd) * ((dd / pV) * (4 * κ / (κ ^ 2 - 1)))
      = c * D / (8 * pV) * (4 / s) := by
  have hs0 : s ≠ 0 := by linarith
  have hs2 : 1 < s ^ 2 := by nlinarith
  have hs4 : 1 < s ^ 4 := by nlinarith
  have h1 : s ^ 4 - 1 ≠ 0 := by linarith
  subst hκ hD
  have e : (s ^ 2) ^ 2 = s ^ 4 := by ring
  rw [e]
  field_simp

theorem Bcrit_sgd_bounds (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps) :
    4 * Dv d ps / (ps 0 : ℝ) ≤ Bcrit d ν ps sgdClass ∧
      Bcrit d ν ps sgdClass
        ≤ kappaV ps ^ 2 / (kappaV ps ^ 2 - 1) * (4 * ((d : ℝ) + 2) / (ps 0 : ℝ)) := by
  rw [Bcrit_sgd_eq hp hanti hκ]
  have hk0 : 0 < kappaV ps := by linarith
  have hpl : 0 < pLast ps := hp _
  have hD := Dv_pos d ps
  have hk2 : 0 < kappaV ps ^ 2 - 1 := by nlinarith
  have hEs := Esgd1_bounds d ps hpl
  obtain ⟨hl1, hl2⟩ := two_log_bounds hκ
  have hls : 4 / kappaV ps ≤ lamSGD ps := hl1
  have hlu : lamSGD ps ≤ 4 * kappaV ps / (kappaV ps ^ 2 - 1) := hl2
  have hlpos := lamSGD_pos (ps := ps) hκ
  have hkp := kappa_mul_pLast hp
  have hp0 : (ps 0 : ℝ) = kappaV ps * pLast ps := hkp.symm
  constructor
  · have h1 : Dv d ps / pLast ps * (4 / kappaV ps) ≤ Esgd1 d ps * lamSGD ps :=
      mul_le_mul hEs.1 hls (by positivity) (le_trans (by positivity) hEs.1)
    refine le_trans (le_of_eq ?_) h1
    rw [hp0]; field_simp
  · have h1 : Esgd1 d ps * lamSGD ps
        ≤ ((d : ℝ) + 2) / pLast ps * (4 * kappaV ps / (kappaV ps ^ 2 - 1)) :=
      mul_le_mul hEs.2 hlu hlpos.le (by positivity)
    refine le_trans h1 (le_of_eq ?_)
    rw [hp0]; field_simp

theorem Bratio_le (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps) :
    Bcrit d ν ps momClass / Bcrit d ν ps sgdClass
      ≤ kappaV ps * Real.sqrt (kappaV ps) / (kappaV ps - 1) := by
  have hs1 := sqrt_kappa_gt_one hκ
  have hk0 : 0 < kappaV ps := by linarith
  have hs2 : Real.sqrt (kappaV ps) ^ 2 = kappaV ps := Real.sq_sqrt hk0.le
  have hEs := Esgd1_pos (d := d) hp
  have hlpos := lamSGD_pos (ps := ps) hκ
  have hmpos := lamMom_pos (ps := ps) hκ
  have hBs : 0 < Bcrit d ν ps sgdClass := by rw [Bcrit_sgd_eq hp hanti hκ]; positivity
  rw [Bcrit_mom_eq hp hanti hκ, Bcrit_sgd_eq hp hanti hκ, div_le_iff₀ (by positivity)]
  have hEm := Einf_mom_le_sgd (d := d) (ν := ν) hp hanti hκ
  rw [Einf_sgd hp hanti hκ] at hEm
  have hls : 4 / kappaV ps ≤ lamSGD ps := (two_log_bounds hκ).1
  have hlm : lamMom ps ≤ 4 * Real.sqrt (kappaV ps) / (Real.sqrt (kappaV ps) ^ 2 - 1) :=
    (two_log_bounds hs1).2
  rw [hs2] at hlm
  have hk1 : 0 < kappaV ps - 1 := by linarith
  have hM : lamMom ps ≤ kappaV ps * Real.sqrt (kappaV ps) / (kappaV ps - 1) * lamSGD ps := by
    refine hlm.trans ?_
    have : 4 * Real.sqrt (kappaV ps) / (kappaV ps - 1)
        = kappaV ps * Real.sqrt (kappaV ps) / (kappaV ps - 1) * (4 / kappaV ps) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hls (by positivity)
  calc Einf d ν ps momClass * lamMom ps ≤ Esgd1 d ps * lamMom ps :=
        mul_le_mul_of_nonneg_right hEm hmpos.le
    _ ≤ Esgd1 d ps * (kappaV ps * Real.sqrt (kappaV ps) / (kappaV ps - 1) * lamSGD ps) :=
        mul_le_mul_of_nonneg_left hM hEs.le
    _ = kappaV ps * Real.sqrt (kappaV ps) / (kappaV ps - 1) * (Esgd1 d ps * lamSGD ps) := by ring

theorem Bratio_ge (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 16 < kappaV ps) :
    (Real.sqrt (kappaV ps) - 4) / 8 * (1 - 1 / kappaV ps ^ 2) * (1 - pLast ps / ((d : ℝ) + 2))
      ≤ Bcrit d ν ps momClass / Bcrit d ν ps sgdClass := by
  have hκ1 : 1 < kappaV ps := by linarith
  have hs1 := sqrt_kappa_gt_one hκ1
  have hk0 : 0 < kappaV ps := by linarith
  have hs2 : Real.sqrt (kappaV ps) ^ 2 = kappaV ps := Real.sq_sqrt hk0.le
  have hs4 : 4 < Real.sqrt (kappaV ps) := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) hκ
  have hEs := Esgd1_pos (d := d) hp
  have hlpos := lamSGD_pos (ps := ps) hκ1
  have hpl : 0 < pLast ps := hp _
  have hD := Dv_pos d ps
  have hBs : 0 < Bcrit d ν ps sgdClass := by rw [Bcrit_sgd_eq hp hanti hκ1]; positivity
  rw [le_div_iff₀ hBs, Bcrit_mom_eq hp hanti hκ1, Bcrit_sgd_eq hp hanti hκ1]
  have hEm := Einf_mom_ge (d := d) (ν := ν) hp hκ
  have hEs2 := (Esgd1_bounds d ps hpl).2
  have hk2 : 0 < kappaV ps ^ 2 - 1 := by nlinarith
  have hlu : lamSGD ps ≤ 4 * kappaV ps / (kappaV ps ^ 2 - 1) := (two_log_bounds hκ1).2
  have hlm : 4 / Real.sqrt (kappaV ps) ≤ lamMom ps := (two_log_bounds hs1).1
  have hdd : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hc1 : 0 ≤ (1 - 4 / Real.sqrt (kappaV ps)) * Dv d ps / (8 * pLast ps) := by
    have : 4 / Real.sqrt (kappaV ps) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have : 0 ≤ 1 - 4 / Real.sqrt (kappaV ps) := by linarith
    positivity
  have h4s : 0 < 4 / Real.sqrt (kappaV ps) := by positivity
  have hU : Esgd1 d ps * lamSGD ps
      ≤ ((d : ℝ) + 2) / pLast ps * (4 * kappaV ps / (kappaV ps ^ 2 - 1)) :=
    mul_le_mul hEs2 hlu hlpos.le (by positivity)
  have htarget : 0 ≤ (Real.sqrt (kappaV ps) - 4) / 8 * (1 - 1 / kappaV ps ^ 2)
      * (1 - pLast ps / ((d : ℝ) + 2)) := by
    have h1 : 1 / kappaV ps ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have h2 : pLast ps / ((d : ℝ) + 2) ≤ 1 := by
      rw [div_le_one hdd]
      have : pLast ps ≤ 1 := (ps (Fin.last n)).2.2
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have : 0 ≤ 1 - 1 / kappaV ps ^ 2 := by linarith
    have : 0 ≤ 1 - pLast ps / ((d : ℝ) + 2) := by linarith
    have : 0 ≤ (Real.sqrt (kappaV ps) - 4) / 8 := by linarith
    positivity
  have hid := ratio_identity (s := Real.sqrt (kappaV ps)) (κ := kappaV ps) (D := Dv d ps)
    (pV := pLast ps) (dd := (d : ℝ) + 2) hs1 hs2.symm hpl.ne' hdd.ne' rfl
  calc _ ≤ (Real.sqrt (kappaV ps) - 4) / 8 * (1 - 1 / kappaV ps ^ 2)
          * (1 - pLast ps / ((d : ℝ) + 2))
          * (((d : ℝ) + 2) / pLast ps * (4 * kappaV ps / (kappaV ps ^ 2 - 1))) :=
        mul_le_mul_of_nonneg_left hU htarget
    _ = (1 - 4 / Real.sqrt (kappaV ps)) * Dv d ps / (8 * pLast ps) * (4 / Real.sqrt (kappaV ps)) := by
        rw [← hid]
    _ ≤ Einf d ν ps momClass * lamMom ps :=
        mul_le_mul hEm hlm h4s.le (le_trans hc1 hEm)

/-- Lower bound of (iii) with the sharp constant of the tex:
`(c_κ √κ/8)(1-κ⁻²)(1-p_V/(d+2)) ≤ B_mom/B_SGD`, `c_κ = max(1 - 4/√κ, 1/√5)` (`κ > 16`). -/
theorem Bratio_ge' (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 16 < kappaV ps) :
    max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Real.sqrt (kappaV ps) / 8
        * (1 - 1 / kappaV ps ^ 2) * (1 - pLast ps / ((d : ℝ) + 2))
      ≤ Bcrit d ν ps momClass / Bcrit d ν ps sgdClass := by
  have hκ1 : 1 < kappaV ps := by linarith
  have hs1 := sqrt_kappa_gt_one hκ1
  have hk0 : 0 < kappaV ps := by linarith
  have hs2 : Real.sqrt (kappaV ps) ^ 2 = kappaV ps := Real.sq_sqrt hk0.le
  have hEs := Esgd1_pos (d := d) hp
  have hlpos := lamSGD_pos (ps := ps) hκ1
  have hpl : 0 < pLast ps := hp _
  have hD := Dv_pos d ps
  have hBs : 0 < Bcrit d ν ps sgdClass := by rw [Bcrit_sgd_eq hp hanti hκ1]; positivity
  rw [le_div_iff₀ hBs, Bcrit_mom_eq hp hanti hκ1, Bcrit_sgd_eq hp hanti hκ1]
  have hEm := Einf_mom_ge' (d := d) (ν := ν) hp hκ
  have hEs2 := (Esgd1_bounds d ps hpl).2
  have hk2 : 0 < kappaV ps ^ 2 - 1 := by nlinarith
  have hlu : lamSGD ps ≤ 4 * kappaV ps / (kappaV ps ^ 2 - 1) := (two_log_bounds hκ1).2
  have hlm : 4 / Real.sqrt (kappaV ps) ≤ lamMom ps := (two_log_bounds hs1).1
  have hdd : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hc0 : 0 ≤ max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) :=
    le_trans (by positivity) (le_max_right _ _)
  have hc1 : 0 ≤ max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Dv d ps
      / (8 * pLast ps) := by positivity
  have h4s : 0 < 4 / Real.sqrt (kappaV ps) := by positivity
  have hU : Esgd1 d ps * lamSGD ps
      ≤ ((d : ℝ) + 2) / pLast ps * (4 * kappaV ps / (kappaV ps ^ 2 - 1)) :=
    mul_le_mul hEs2 hlu hlpos.le (by positivity)
  have htarget : 0 ≤ max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5)
      * Real.sqrt (kappaV ps) / 8 * (1 - 1 / kappaV ps ^ 2)
      * (1 - pLast ps / ((d : ℝ) + 2)) := by
    have h1 : 1 / kappaV ps ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have h2 : pLast ps / ((d : ℝ) + 2) ≤ 1 := by
      rw [div_le_one hdd]
      have : pLast ps ≤ 1 := (ps (Fin.last n)).2.2
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have : 0 ≤ 1 - 1 / kappaV ps ^ 2 := by linarith
    have : 0 ≤ 1 - pLast ps / ((d : ℝ) + 2) := by linarith
    positivity
  have hid := ratio_identity_c
    (c := max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5))
    (s := Real.sqrt (kappaV ps)) (κ := kappaV ps) (D := Dv d ps)
    (pV := pLast ps) (dd := (d : ℝ) + 2) hs1 hs2.symm hpl.ne' hdd.ne' rfl
  calc _ ≤ max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Real.sqrt (kappaV ps) / 8
          * (1 - 1 / kappaV ps ^ 2) * (1 - pLast ps / ((d : ℝ) + 2))
          * (((d : ℝ) + 2) / pLast ps * (4 * kappaV ps / (kappaV ps ^ 2 - 1))) :=
        mul_le_mul_of_nonneg_left hU htarget
    _ = max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Dv d ps / (8 * pLast ps)
          * (4 / Real.sqrt (kappaV ps)) := by
        rw [← hid]
    _ ≤ Einf d ν ps momClass * lamMom ps :=
        mul_le_mul hEm hlm h4s.le (le_trans hc1 hEm)

/-- The last claim of (iii): for `κ > 16` the left side of the ratio bound is at least `√κ/19`
(only `p_1 ≤ 1` and `d ≥ 0` are used; `1/√5 > 0.447`, `p_V/(d+2) < 1/32`, `κ⁻² < 1/256`). -/
theorem Bratio_ge_div19 (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 16 < kappaV ps) :
    Real.sqrt (kappaV ps) / 19
      ≤ max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Real.sqrt (kappaV ps) / 8
        * (1 - 1 / kappaV ps ^ 2) * (1 - pLast ps / ((d : ℝ) + 2)) := by
  have hk0 : 0 < kappaV ps := by linarith
  have hs0 : 0 < Real.sqrt (kappaV ps) := Real.sqrt_pos.2 hk0
  have hpl : 0 < pLast ps := hp _
  have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hc : (447 / 1000 : ℝ) ≤ max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) := by
    refine le_trans ?_ (le_max_right _ _)
    rw [le_div_iff₀ h5]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  have h2 : (255 / 256 : ℝ) ≤ 1 - 1 / kappaV ps ^ 2 := by
    have : 1 / kappaV ps ^ 2 ≤ 1 / 256 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hp0 : kappaV ps * pLast ps = (ps 0 : ℝ) := div_mul_cancel₀ _ hpl.ne'
  have hp01 : (ps 0 : ℝ) ≤ 1 := (ps 0).2.2
  have hpV : pLast ps < 1 / 16 := by
    rw [lt_div_iff₀ (by norm_num)]; nlinarith
  have hd : (2 : ℝ) ≤ (d : ℝ) + 2 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have h3 : (31 / 32 : ℝ) ≤ 1 - pLast ps / ((d : ℝ) + 2) := by
    have : pLast ps / ((d : ℝ) + 2) ≤ 1 / 32 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hprod : (447 / 1000 : ℝ) * (255 / 256) * (31 / 32)
      ≤ max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * (1 - 1 / kappaV ps ^ 2)
        * (1 - pLast ps / ((d : ℝ) + 2)) := by
    gcongr
  have e : max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Real.sqrt (kappaV ps) / 8
        * (1 - 1 / kappaV ps ^ 2) * (1 - pLast ps / ((d : ℝ) + 2))
      = Real.sqrt (kappaV ps) / 8
        * (max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * (1 - 1 / kappaV ps ^ 2)
          * (1 - pLast ps / ((d : ℝ) + 2))) := by ring
  rw [e]
  nlinarith

/-- Real identity for the equal-sample case (`κ = s²`). -/
theorem ratio_identity_eq {s κ : ℝ} (hs : 1 < s) (hκ : κ = s ^ 2) :
    s * (1 - 1 / κ ^ 2) * (4 * κ / (κ ^ 2 - 1)) = 4 / s := by
  have hs0 : s ≠ 0 := by linarith
  have hs2 : 1 < s ^ 2 := by nlinarith
  have hs4 : 1 < s ^ 4 := by nlinarith
  have h1 : s ^ 4 - 1 ≠ 0 := by linarith
  subst hκ
  have e : (s ^ 2) ^ 2 = s ^ 4 := by ring
  rw [e]
  field_simp

/-- The remark after the proposition: if `E_mom = E_SGD` then
`B_mom/B_SGD = λ_mom/λ_SGD = S_SGD/S_mom`, between `√κ (1 - κ⁻²)` and `κ√κ/(κ-1)`. -/
theorem Bratio_of_Einf_eq (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps)
    (hE : Einf d ν ps momClass = Einf d ν ps sgdClass) :
    Bcrit d ν ps momClass / Bcrit d ν ps sgdClass = lamMom ps / lamSGD ps ∧
      Real.sqrt (kappaV ps) * (1 - 1 / kappaV ps ^ 2)
        ≤ Bcrit d ν ps momClass / Bcrit d ν ps sgdClass ∧
      Bcrit d ν ps momClass / Bcrit d ν ps sgdClass
        ≤ kappaV ps * Real.sqrt (kappaV ps) / (kappaV ps - 1) := by
  have hs1 := sqrt_kappa_gt_one hκ
  have hk0 : 0 < kappaV ps := by linarith
  have hs2 : Real.sqrt (kappaV ps) ^ 2 = kappaV ps := Real.sq_sqrt hk0.le
  have hEs := Esgd1_pos (d := d) hp
  have hlpos := lamSGD_pos (ps := ps) hκ
  have hmpos := lamMom_pos (ps := ps) hκ
  have heq : Bcrit d ν ps momClass / Bcrit d ν ps sgdClass = lamMom ps / lamSGD ps := by
    rw [Bcrit_mom_eq hp hanti hκ, Bcrit_sgd_eq hp hanti hκ, hE, Einf_sgd hp hanti hκ]
    exact mul_div_mul_left _ _ hEs.ne'
  refine ⟨heq, ?_, Bratio_le hp hanti hκ⟩
  rw [heq, le_div_iff₀ hlpos]
  have hlu : lamSGD ps ≤ 4 * kappaV ps / (kappaV ps ^ 2 - 1) := (two_log_bounds hκ).2
  have hlm : 4 / Real.sqrt (kappaV ps) ≤ lamMom ps := (two_log_bounds hs1).1
  have hk2 : 0 < kappaV ps ^ 2 - 1 := by nlinarith
  have hq : 0 ≤ Real.sqrt (kappaV ps) * (1 - 1 / kappaV ps ^ 2) := by
    have h1 : 1 / kappaV ps ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have : 0 ≤ 1 - 1 / kappaV ps ^ 2 := by linarith
    positivity
  have hid := ratio_identity_eq (s := Real.sqrt (kappaV ps)) (κ := kappaV ps) hs1 hs2.symm
  calc _ ≤ Real.sqrt (kappaV ps) * (1 - 1 / kappaV ps ^ 2) * (4 * kappaV ps / (kappaV ps ^ 2 - 1)) :=
        mul_le_mul_of_nonneg_left hlu hq
    _ = 4 / Real.sqrt (kappaV ps) := hid
    _ ≤ lamMom ps := hlm

/-! ### The proposition -/

/-- `v2 prop:helps-critical` (i): the fewest steps. `S_SGD = 1/(2 log((κ+1)/(κ-1)))` and
`S_mom = 1/(2 log((√κ+1)/(√κ-1)))`, with the two-sided bounds; hypothesis `κ > 1`. -/
theorem helps_critical_i (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps) :
    Sinf d ν ps sgdClass = 1 / (2 * Real.log ((kappaV ps + 1) / (kappaV ps - 1))) ∧
      Sinf d ν ps momClass
        = 1 / (2 * Real.log ((Real.sqrt (kappaV ps) + 1) / (Real.sqrt (kappaV ps) - 1))) ∧
      kappaV ps / 4 * (1 - 1 / kappaV ps ^ 2) ≤ Sinf d ν ps sgdClass ∧
      Sinf d ν ps sgdClass ≤ kappaV ps / 4 ∧
      Real.sqrt (kappaV ps) / 4 * (1 - 1 / kappaV ps) ≤ Sinf d ν ps momClass ∧
      Sinf d ν ps momClass ≤ Real.sqrt (kappaV ps) / 4 := by
  have hs1 := sqrt_kappa_gt_one hκ
  have hk0 : 0 < kappaV ps := by linarith
  have hs2 : Real.sqrt (kappaV ps) ^ 2 = kappaV ps := Real.sq_sqrt hk0.le
  have h1 := Sinf_sgd (d := d) (ν := ν) hp hanti hκ
  have h2 := Sinf_mom (d := d) (ν := ν) hp hanti hκ
  have b1 := inv_two_log_bounds hκ
  have b2 := inv_two_log_bounds hs1
  rw [hs2] at b2
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · rw [h1]; exact b1.1
  · rw [h1]; exact b1.2
  · rw [h2]; exact b2.1
  · rw [h2]; exact b2.2

/-- `v2 prop:helps-critical` (ii), SGD and the upper bound for momentum:
`E_SGD = E_SGD(1) = 1/log((d+2)/(d+2-p_V))`, `(d+2-p_V)/p_V ≤ E_SGD ≤ (d+2)/p_V` and
`E_mom ≤ E_SGD`; hypothesis `κ > 1`. -/
theorem helps_critical_ii (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps) :
    Einf d ν ps sgdClass = Efun d 1 ν ps sgdClass ∧
      Einf d ν ps sgdClass
        = 1 / Real.log (((d : ℝ) + 2) / ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))) ∧
      ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) / (ps (Fin.last n) : ℝ) ≤ Einf d ν ps sgdClass ∧
      Einf d ν ps sgdClass ≤ ((d : ℝ) + 2) / (ps (Fin.last n) : ℝ) ∧
      Einf d ν ps momClass ≤ Einf d ν ps sgdClass := by
  have h := Einf_sgd (d := d) (ν := ν) hp hanti hκ
  have hb := Esgd1_bounds d ps (hp (Fin.last n))
  refine ⟨?_, h, ?_, ?_, Einf_mom_le_sgd hp hanti hκ⟩
  · rw [h, Efun_sgd_one hp hanti hκ]
  · rw [h]; exact hb.1
  · rw [h]; exact hb.2

/-- `v2 prop:helps-critical` (ii), momentum lower bound (uses `κ > 16`):
`E_mom ≥ (1 - 4/√κ)(d+2-p_V)/(8 p_V)`. -/
theorem helps_critical_ii_mom (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 16 < kappaV ps) :
    (1 - 4 / Real.sqrt (kappaV ps)) * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))
        / (8 * (ps (Fin.last n) : ℝ)) ≤ Einf d ν ps momClass :=
  Einf_mom_ge hp hκ

/-- `v2 prop:helps-critical` (ii), momentum lower bound with the sharp constant of the tex (uses
`κ > 16`): `E_mom ≥ c_κ (d+2-p_V)/(8 p_V)`, `c_κ = max(1 - 4/√κ, 1/√5)`. -/
theorem helps_critical_ii_mom' (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 16 < kappaV ps) :
    max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))
        / (8 * (ps (Fin.last n) : ℝ)) ≤ Einf d ν ps momClass :=
  Einf_mom_ge' hp hκ

/-- `v2 prop:helps-critical` (iii), SGD: `4(d+2-p_V)/p_1 ≤ B_SGD ≤ κ²/(κ²-1) · 4(d+2)/p_1`;
hypothesis `κ > 1`. -/
theorem helps_critical_iii_sgd (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hκ : 1 < kappaV ps) :
    4 * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) / (ps 0 : ℝ) ≤ Bcrit d ν ps sgdClass ∧
      Bcrit d ν ps sgdClass
        ≤ kappaV ps ^ 2 / (kappaV ps ^ 2 - 1) * (4 * ((d : ℝ) + 2) / (ps 0 : ℝ)) :=
  Bcrit_sgd_bounds hp hanti hκ

/-- `v2 prop:helps-critical` (iii), the ratio (lower bound uses `κ > 16`):
`((√κ-4)/8)(1-κ⁻²)(1-p_V/(d+2)) ≤ B_mom/B_SGD ≤ κ√κ/(κ-1)`. -/
theorem helps_critical_iii_ratio (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hκ : 16 < kappaV ps) :
    (Real.sqrt (kappaV ps) - 4) / 8 * (1 - 1 / kappaV ps ^ 2)
        * (1 - (ps (Fin.last n) : ℝ) / ((d : ℝ) + 2))
      ≤ Bcrit d ν ps momClass / Bcrit d ν ps sgdClass ∧
      Bcrit d ν ps momClass / Bcrit d ν ps sgdClass
        ≤ kappaV ps * Real.sqrt (kappaV ps) / (kappaV ps - 1) :=
  ⟨Bratio_ge hp hanti hκ, Bratio_le hp hanti (by linarith)⟩

/-- `v2 prop:helps-critical` (iii), the ratio with the sharp constant of the tex (lower bound uses
`κ > 16`): `(c_κ√κ/8)(1-κ⁻²)(1-p_V/(d+2)) ≤ B_mom/B_SGD ≤ κ√κ/(κ-1)`, and the left side is at
least `√κ/19`. -/
theorem helps_critical_iii_ratio' (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hκ : 16 < kappaV ps) :
    max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Real.sqrt (kappaV ps) / 8
        * (1 - 1 / kappaV ps ^ 2) * (1 - (ps (Fin.last n) : ℝ) / ((d : ℝ) + 2))
      ≤ Bcrit d ν ps momClass / Bcrit d ν ps sgdClass ∧
      Bcrit d ν ps momClass / Bcrit d ν ps sgdClass
        ≤ kappaV ps * Real.sqrt (kappaV ps) / (kappaV ps - 1) ∧
      Real.sqrt (kappaV ps) / 19
        ≤ max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Real.sqrt (kappaV ps) / 8
          * (1 - 1 / kappaV ps ^ 2) * (1 - (ps (Fin.last n) : ℝ) / ((d : ℝ) + 2)) :=
  ⟨Bratio_ge' hp hanti hκ, Bratio_le hp hanti (by linarith), Bratio_ge_div19 hp hκ⟩

/-- `v2 prop:helps-critical`, finite-`B` statements behind the discussion: for every `B ≥ 1`,
`S_O(B) ≥ 1/λ_O` and `E_SGD(B) ≥ 1/log((d+2)/(d+2-p_V))`, `E_mom(B) ≤ E_SGD(B)`; and as `B → ∞`
`S_O(B) → 1/λ_O` (the fewest steps are approached as `B → ∞`). -/
theorem helps_critical_finiteB (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hκ : 1 < kappaV ps) :
    (∀ B : ℕ, 1 ≤ B →
      1 / lamSGD ps ≤ Sfun d B ν ps sgdClass ∧ 1 / lamMom ps ≤ Sfun d B ν ps momClass ∧
        Esgd1 d ps ≤ Efun d B ν ps sgdClass ∧
        Efun d B ν ps momClass ≤ Efun d B ν ps sgdClass) ∧
      Tendsto (fun B : ℕ => Sfun d B ν ps sgdClass) atTop (𝓝 (1 / lamSGD ps)) ∧
      Tendsto (fun B : ℕ => Sfun d B ν ps momClass) atTop (𝓝 (1 / lamMom ps)) :=
  ⟨fun _ hB => ⟨Sfun_sgd_ge hp hκ hB, Sfun_mom_ge hp hκ hB, Efun_sgd_ge hp hκ hB,
      Efun_mom_le_sgd hp hκ hB⟩,
    Sfun_tendsto_sgd hp hanti hκ, Sfun_tendsto_mom hp hanti hκ⟩

/-- `v2 prop:helps-critical`, all parts for `κ_V > 16`, in the order (i), (ii), (iii) of the tex.
(Parts not involving the momentum lower bounds hold for `κ_V > 1`; see the individual theorems.) -/
theorem prop_helps_critical (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hκ : 16 < kappaV ps) :
    -- (i)
    (Sinf d ν ps sgdClass = 1 / (2 * Real.log ((kappaV ps + 1) / (kappaV ps - 1))) ∧
      Sinf d ν ps momClass
        = 1 / (2 * Real.log ((Real.sqrt (kappaV ps) + 1) / (Real.sqrt (kappaV ps) - 1))) ∧
      kappaV ps / 4 * (1 - 1 / kappaV ps ^ 2) ≤ Sinf d ν ps sgdClass ∧
      Sinf d ν ps sgdClass ≤ kappaV ps / 4 ∧
      Real.sqrt (kappaV ps) / 4 * (1 - 1 / kappaV ps) ≤ Sinf d ν ps momClass ∧
      Sinf d ν ps momClass ≤ Real.sqrt (kappaV ps) / 4) ∧
    -- (ii)
    (Einf d ν ps sgdClass = Efun d 1 ν ps sgdClass ∧
      Einf d ν ps sgdClass
        = 1 / Real.log (((d : ℝ) + 2) / ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))) ∧
      ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) / (ps (Fin.last n) : ℝ) ≤ Einf d ν ps sgdClass ∧
      Einf d ν ps sgdClass ≤ ((d : ℝ) + 2) / (ps (Fin.last n) : ℝ) ∧
      max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5)
          * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))
          / (8 * (ps (Fin.last n) : ℝ)) ≤ Einf d ν ps momClass ∧
      Einf d ν ps momClass ≤ Einf d ν ps sgdClass) ∧
    -- (iii)
    (4 * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) / (ps 0 : ℝ) ≤ Bcrit d ν ps sgdClass ∧
      Bcrit d ν ps sgdClass
        ≤ kappaV ps ^ 2 / (kappaV ps ^ 2 - 1) * (4 * ((d : ℝ) + 2) / (ps 0 : ℝ)) ∧
      max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Real.sqrt (kappaV ps) / 8
          * (1 - 1 / kappaV ps ^ 2) * (1 - (ps (Fin.last n) : ℝ) / ((d : ℝ) + 2))
        ≤ Bcrit d ν ps momClass / Bcrit d ν ps sgdClass ∧
      Bcrit d ν ps momClass / Bcrit d ν ps sgdClass
        ≤ kappaV ps * Real.sqrt (kappaV ps) / (kappaV ps - 1) ∧
      Real.sqrt (kappaV ps) / 19
        ≤ max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Real.sqrt (kappaV ps) / 8
          * (1 - 1 / kappaV ps ^ 2) * (1 - (ps (Fin.last n) : ℝ) / ((d : ℝ) + 2))) := by
  have hκ1 : 1 < kappaV ps := by linarith
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := helps_critical_i (d := d) (ν := ν) hp hanti hκ1
  obtain ⟨b1, b2, b3, b4, b5⟩ := helps_critical_ii (d := d) (ν := ν) hp hanti hκ1
  obtain ⟨c1, c2⟩ := helps_critical_iii_sgd (d := d) (ν := ν) hp hanti hκ1
  obtain ⟨c3, c4, c5⟩ := helps_critical_iii_ratio' (d := d) (ν := ν) hp hanti hκ
  exact ⟨⟨a1, a2, a3, a4, a5, a6⟩,
    ⟨b1, b2, b3, b4, helps_critical_ii_mom' hp hκ, b5⟩, ⟨c1, c2, c3, c4, c5⟩⟩

end Basic2

/-! ## v2 additions (`critical-batch-v2`)

Appended after the pre-merge statements; no existing declaration is changed.

* (K1) `Sfun_tendsto_Sinf_sgd`, `Sfun_tendsto_Sinf_mom`: v2 `prop:helps-critical` (i), the limit form.
* (K2) `Bcrit_mom_le_abs` (`κ_V > 1`), `Bcrit_mom_ge_abs` (`κ_V > 16`): v2 `prop:helps-critical` (iii),
  absolute bounds on `B_mom`; discussion lemmas `Bratio_lower_gt_one`, `Einf_ratio_lt_19`.
* (K3) `Sfun_sgd_eq_of_le_Bx`, `Sfun_sgd_eq_of_gt_Bx`: v2 `lem:helps-vocab` (v) read off at the level of
  `S_SGD(B)` (from `helps_vocab_v_case1`, `helps_vocab_v_case2`).
* (K4) v2 `prop:helps-critical` (iv), a single fixed `β ∈ [0,1)` (class `{β}`): `wStar`, `rhoBeta`,
  `Sbeta`; `Sfun_fixed_ge_pointwise`, `Sfun_fixed_ge`, `Sfun_fixed_tendsto`, `Sinf_fixed_eq`,
  `rhoBeta_zero`, `rhoBeta_eq_sqrt_iff`, `rhoBeta_ge_polyak`, `rhoBeta_polyak`, `Sbeta_isLeast`,
  `Sbeta_inf_eq_Sinf_mom`, `Sbeta_le_A`, `Sbeta_ge`.
* (K5) `prop_helps_critical_v2`: the bundle.

Hypotheses added to the tex statements: `External.JuryStability` is needed for
`Sfun_fixed_ge`/`Sinf_fixed_eq` (non-emptiness of `A_{β}(B)` for every `B`, since `sInf ∅ = 0`); the
limit `Sfun_fixed_tendsto` needs none.  `Antitone ps` and positivity of all `ps j` are as in the earlier
statements.  The tex symbol `ρ(F)` is `meanRadius` of `StepSpeed.lean`.
-/

/-! ### Fixed `β`: real-variable facts about `ρ_β` -/

section FixedBetaReal

/-- `w_* = 2(1+β)/(κ+1)` (v2 `prop:helps-critical` (iv), Step 6). -/
def wStar (κ β : ℝ) : ℝ := 2 * (1 + β) / (κ + 1)

/-- `ρ_β` for a real `κ`: the spectral radius `ρ(F)` at `w = w_*`, i.e. the largest root modulus of
`z² - (1+β)(κ-1)/(κ+1) z + β` (v2 `prop:helps-critical` (iv)). -/
def rhoBetaR (κ β : ℝ) : ℝ := meanRadius β (wStar κ β)

theorem wStar_pos {κ β : ℝ} (hκ : 1 < κ) (hb0 : 0 ≤ β) : 0 < wStar κ β :=
  div_pos (by linarith) (by linarith)

theorem wStar_lt {κ β : ℝ} (hκ : 1 < κ) (hb0 : 0 ≤ β) : wStar κ β < 1 + β := by
  unfold wStar
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

theorem one_add_sub_wStar {κ β : ℝ} (hκ : 1 < κ) :
    1 + β - wStar κ β = (1 + β) * (κ - 1) / (κ + 1) := by
  unfold wStar
  have : κ + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem kappa_mul_wStar {κ β : ℝ} (hκ : 1 < κ) :
    κ * wStar κ β = 2 * (1 + β) - wStar κ β := by
  unfold wStar
  have : κ + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem rhoBetaR_lt_one {κ β : ℝ} (hκ : 1 < κ) (hb0 : 0 ≤ β) (hb1 : β < 1) :
    rhoBetaR κ β < 1 :=
  meanRadius_lt_one β _ hb0 hb1 (wStar_pos hκ hb0)
    (by have := wStar_lt hκ hb0; linarith)

theorem real_root_mem_meanRoots {β w l : ℝ} (h : l ^ 2 - (1 + β - w) * l + β = 0) :
    (l : ℂ) ∈ meanRoots β w := by
  show (l : ℂ) ^ 2 - (1 + (β : ℂ) - (w : ℂ)) * (l : ℂ) + (β : ℂ) = 0
  have := congrArg (fun y : ℝ => (y : ℂ)) h
  push_cast at this
  linear_combination this

theorem real_root_sq_le_meanRadius {β w l : ℝ} (h : l ^ 2 - (1 + β - w) * l + β = 0) :
    l ^ 2 ≤ meanRadius β w ^ 2 := by
  have := norm_le_meanRadius β w (real_root_mem_meanRoots h)
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  calc l ^ 2 = |l| ^ 2 := (sq_abs l).symm
    _ ≤ _ := pow_le_pow_left₀ (abs_nonneg l) this 2

/-- v2 `prop:helps-critical` (iv): `ρ_β ≥ (√κ-1)/(√κ+1)`, from `twocurv_real` with
`c = w_*/p_V` (`lem:helps-twocurv`). -/
theorem rhoBetaR_ge_polyak {κ β : ℝ} (hκ : 1 < κ) (hb0 : 0 ≤ β) (hb1 : β < 1) :
    (Real.sqrt κ - 1) / (Real.sqrt κ + 1) ≤ rhoBetaR κ β := by
  have hw := wStar_pos hκ hb0
  have key := twocurv_real (β := β) (c := wStar κ β) (p1 := κ) (pV := 1) hb0 hw one_pos hκ
    (meanRadius_nonneg _ _) (rhoBetaR_lt_one hκ hb0 hb1) (beta_le_meanRadius_sq β _ hb0)
    (by
      intro l hl
      have e : 1 + β - wStar κ β * κ = 1 + β - (2 * (1 + β) - wStar κ β) := by
        rw [mul_comm, kappa_mul_wStar hκ]
      rw [e] at hl
      have := real_root_sq_le_meanRadius hl
      rwa [meanRadius_symm] at this)
    (by
      intro l hl
      rw [mul_one] at hl
      exact real_root_sq_le_meanRadius hl)
  show _ ≤ meanRadius β (wStar κ β)
  simpa [div_one] using key.1

theorem rhoBetaR_pos {κ β : ℝ} (hκ : 1 < κ) (hb0 : 0 ≤ β) (hb1 : β < 1) : 0 < rhoBetaR κ β := by
  have hs : 1 < Real.sqrt κ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) hκ
  have : 0 < (Real.sqrt κ - 1) / (Real.sqrt κ + 1) := div_pos (by linarith) (by linarith)
  exact lt_of_lt_of_le this (rhoBetaR_ge_polyak hκ hb0 hb1)

/-- v2 `prop:helps-critical` (iv): `ρ_0 = (κ-1)/(κ+1)`. -/
theorem rhoBetaR_zero {κ : ℝ} (hκ : 1 < κ) : rhoBetaR κ 0 = (κ - 1) / (κ + 1) := by
  unfold rhoBetaR
  rw [meanRadius_eq_max 0 _ le_rfl, one_add_sub_wStar hκ]
  have ht0 : 0 < (1 + 0) * (κ - 1) / (κ + 1) := div_pos (by linarith) (by linarith)
  have e : (1 + 0) * (κ - 1) / (κ + 1) = (κ - 1) / (κ + 1) := by rw [add_zero, one_mul]
  rw [e] at ht0 ⊢
  rw [abs_of_pos ht0, mul_zero, sub_zero, Real.sqrt_sq ht0.le, Real.sqrt_zero]
  rw [max_eq_right (by linarith)]
  ring

/-- `ρ_β = √β` iff `t = (1+β)(κ-1)/(κ+1) ≤ 2√β`. -/
theorem rhoBetaR_eq_sqrt_iff_t {κ β : ℝ} (hκ : 1 < κ) (hb0 : 0 < β) (hb1 : β < 1) :
    rhoBetaR κ β = Real.sqrt β ↔ (1 + β) * (κ - 1) / (κ + 1) ≤ 2 * Real.sqrt β := by
  have ht : 1 + β - wStar κ β = (1 + β) * (κ - 1) / (κ + 1) := one_add_sub_wStar hκ
  have ht0 : 0 < (1 + β) * (κ - 1) / (κ + 1) := div_pos (by nlinarith) (by linarith)
  have hs0 : 0 < Real.sqrt β := Real.sqrt_pos.2 hb0
  have hs2 : Real.sqrt β ^ 2 = β := Real.sq_sqrt hb0.le
  unfold rhoBetaR
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hD : 4 * β < (1 + β - wStar κ β) ^ 2 := by rw [ht]; nlinarith
    rw [meanRadius_of_gt β _ hb0.le hD, ht, abs_of_pos ht0] at h
    have := Real.sqrt_nonneg (((1 + β) * (κ - 1) / (κ + 1)) ^ 2 - 4 * β)
    linarith
  · intro h
    apply meanRadius_of_le β _ hb0.le
    rw [ht]
    nlinarith

/-- v2 `prop:helps-critical` (iv): `ρ_β = √β` iff `κ ≤ κ_β = ((1+√β)/(1-√β))²`. -/
theorem rhoBetaR_eq_sqrt_iff {κ β : ℝ} (hκ : 1 < κ) (hb0 : 0 < β) (hb1 : β < 1) :
    rhoBetaR κ β = Real.sqrt β ↔ κ ≤ ((1 + Real.sqrt β) / (1 - Real.sqrt β)) ^ 2 := by
  rw [rhoBetaR_eq_sqrt_iff_t hκ hb0 hb1]
  have hs0 : 0 < Real.sqrt β := Real.sqrt_pos.2 hb0
  have hs2 : Real.sqrt β ^ 2 = β := Real.sq_sqrt hb0.le
  have hs1 : Real.sqrt β < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hb0.le hb1
  set s := Real.sqrt β with hs
  have h1s : 0 < 1 - s := by linarith
  rw [div_pow, le_div_iff₀ (by positivity), div_le_iff₀ (by linarith), ← hs2]
  constructor <;> intro h <;> nlinarith

/-- v2 `prop:helps-critical` (iv): at `β_P`, `κ = κ_{β_P}` and
`ρ_{β_P} = (√κ-1)/(√κ+1)`. -/
theorem rhoBetaR_polyak {κ : ℝ} (hκ : 1 < κ) :
    rhoBetaR κ (((Real.sqrt κ - 1) / (Real.sqrt κ + 1)) ^ 2)
      = (Real.sqrt κ - 1) / (Real.sqrt κ + 1) := by
  have hs : 1 < Real.sqrt κ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) hκ
  have hs2 : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt (by linarith)
  set q := (Real.sqrt κ - 1) / (Real.sqrt κ + 1) with hq
  have hq0 : 0 < q := div_pos (by linarith) (by linarith)
  have hq1 : q < 1 := by rw [hq, div_lt_one (by linarith)]; linarith
  have hsq : Real.sqrt (q ^ 2) = q := Real.sqrt_sq hq0.le
  have hiff := rhoBetaR_eq_sqrt_iff hκ (β := q ^ 2) (by positivity) (by nlinarith)
  rw [hsq] at hiff
  have hr : (1 + q) / (1 - q) = Real.sqrt κ := by
    rw [hq]
    have : Real.sqrt κ + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hr, hs2] at hiff
  exact hiff.2 le_rfl

/-! #### The two-sided bounds on `S_β` -/

/-- `S_β` in the real variable `κ`: `-1/(2 log ρ_β)`. -/
def SbR (κ β : ℝ) : ℝ := -1 / (2 * Real.log (rhoBetaR κ β))

theorem SbR_eq {κ β : ℝ} : SbR κ β = 1 / (-(2 * Real.log (rhoBetaR κ β))) := by
  unfold SbR
  rw [div_neg, neg_div]

/-- If `ρ > 0` is a root of `z² - (1+β-w) z + β` then `w ≤ (1-β)(-log ρ)`: the concavity of
`g(L) = 1+β-e^{-L}-βe^L` in `prop:helps-critical` Step 6 (`g(L) ≤ (1-β)L`). -/
theorem fixedBeta_core_le {β ρ w : ℝ} (hb0 : 0 ≤ β) (hρ0 : 0 < ρ)
    (hroot : ρ ^ 2 - (1 + β - w) * ρ + β = 0) : w ≤ (1 - β) * (-Real.log ρ) := by
  set L := -Real.log ρ with hL
  have hE : Real.exp L = ρ⁻¹ := by rw [hL, Real.exp_neg, Real.exp_log hρ0]
  have hρE : ρ * Real.exp L = 1 := by rw [hE]; field_simp
  have h1 : 1 - ρ ≤ L := by
    have := Real.log_le_sub_one_of_pos hρ0
    rw [hL]; linarith
  have h2 := Real.add_one_le_exp L
  have hw : w = 1 + β - ρ - β * Real.exp L := by
    linear_combination Real.exp L * hroot - (ρ + w - 1 - β) * hρE
  rw [hw]
  nlinarith [mul_nonneg hb0 (sub_nonneg.2 h2)]

/-- `g(a) ≥ a(1-β-a)` for `a ≥ 0`, `β ≤ e^{-2a}` (the function `h ≥ 0` of `prop:helps-critical`
Step 6; here by an algebraic argument instead of `h'' ≥ 1-√β`). -/
theorem fixedBeta_h_nonneg {β a : ℝ} (ha : 0 ≤ a) (hβa : β ≤ Real.exp (-(2 * a))) :
    a * (1 - β - a) ≤ 1 + β - Real.exp (-a) - β * Real.exp a := by
  set y := Real.exp (-a) with hy
  set E := Real.exp a with hE
  have hyE : y * E = 1 := by rw [hy, hE, ← Real.exp_add]; simp
  have hy0 : 0 < y := Real.exp_pos _
  have hE1 : 1 + a ≤ E := by have := Real.add_one_le_exp a; rw [hE]; linarith
  have hy2 : Real.exp (-(2 * a)) = y ^ 2 := by
    rw [hy, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hy2] at hβa
  have c1 : y ^ 2 * (1 - E + a) ≤ β * (1 - E + a) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hβa) (sub_nonneg.2 hE1)]
  have c2 : y ^ 2 * E = y := by
    calc y ^ 2 * E = y * (y * E) := by ring
      _ = y := by rw [hyE, mul_one]
  have c3 : 0 ≤ (1 - y) ^ 2 - a * (1 - y ^ 2) + a ^ 2 := by
    have h : 0 ≤ (1 + a) * ((1 - y) ^ 2 - a * (1 - y ^ 2) + a ^ 2) := by
      nlinarith [sq_nonneg ((1 + a) * (1 - y) - a), pow_nonneg ha 3]
    exact nonneg_of_mul_nonneg_right h (by linarith)
  nlinarith [c1, c2, c3]

/-- The lower bound `L ≤ L_-` behind the two-sided bound of `prop:helps-critical` (iv): if
`ρ ∈ (0,1)` is the larger root (`β ≤ ρ²`) and `Δ = w/(1-β)² ≤ 1/4`, then
`-log ρ ≤ (1-β)(1-√(1-4Δ))/2`. -/
theorem fixedBeta_core_ge {β ρ w : ℝ} (hb1 : β < 1) (hρ0 : 0 < ρ)
    (hβρ : β ≤ ρ ^ 2) (hroot : ρ ^ 2 - (1 + β - w) * ρ + β = 0) (hw : 0 < w)
    (hΔ : w / (1 - β) ^ 2 ≤ 1 / 4) :
    -Real.log ρ ≤ (1 - β) * (1 - Real.sqrt (1 - 4 * (w / (1 - β) ^ 2))) / 2 := by
  set L := -Real.log ρ with hL
  set Δ := w / (1 - β) ^ 2 with hΔdef
  have h1β : 0 < 1 - β := by linarith
  have hΔ0 : 0 < Δ := div_pos hw (by positivity)
  set s := Real.sqrt (1 - 4 * Δ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - 4 * Δ := Real.sq_sqrt (by linarith)
  set Lm := (1 - β) * (1 - s) / 2 with hLm
  have hLm0 : 0 ≤ Lm := by
    have : s ≤ 1 := by nlinarith
    rw [hLm]; have := mul_nonneg h1β.le (sub_nonneg.2 this); linarith
  have hLm1 : 2 * Lm ≤ 1 - β := by rw [hLm]; nlinarith
  have hLmw : Lm * (1 - β - Lm) = w := by
    have hΔw : Δ * (1 - β) ^ 2 = w := by rw [hΔdef]; field_simp
    rw [hLm]
    have : (1 - β) * (1 - s) / 2 * (1 - β - (1 - β) * (1 - s) / 2)
        = (1 - β) ^ 2 * (1 - s ^ 2) / 4 := by ring
    rw [this, hs2]
    nlinarith [hΔw]
  by_contra hcon
  push Not at hcon
  -- hcon : Lm < L
  have hE : Real.exp L = ρ⁻¹ := by rw [hL, Real.exp_neg, Real.exp_log hρ0]
  have hρe : ρ = Real.exp (-L) := by rw [hL, neg_neg, Real.exp_log hρ0]
  have hρE : ρ * Real.exp L = 1 := by rw [hE]; field_simp
  have hgL : w = 1 + β - Real.exp (-L) - β * Real.exp L := by
    rw [← hρe]
    linear_combination Real.exp L * hroot - (ρ + w - 1 - β) * hρE
  -- `g(Lm) ≥ w`
  have hβLm : β ≤ Real.exp (-(2 * Lm)) := by
    have h1 : β - 1 + 1 ≤ Real.exp (β - 1) := Real.add_one_le_exp _
    have h2 : Real.exp (β - 1) ≤ Real.exp (-(2 * Lm)) := Real.exp_le_exp.2 (by linarith)
    linarith
  have hgLm := fixedBeta_h_nonneg hLm0 hβLm
  rw [hLmw] at hgLm
  -- `g(Lm) < g(L)`
  have hβL : β < Real.exp (-(Lm + L)) := by
    have h1 : β ≤ Real.exp (-(2 * L)) := by
      have : Real.exp (-(2 * L)) = ρ ^ 2 := by
        rw [hρe, ← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [this]; exact hβρ
    have h2 : Real.exp (-(2 * L)) < Real.exp (-(Lm + L)) := Real.exp_lt_exp.2 (by linarith)
    linarith
  have hdiff : (1 + β - Real.exp (-L) - β * Real.exp L) - (1 + β - Real.exp (-Lm) - β * Real.exp Lm)
      = (Real.exp L - Real.exp Lm) * (Real.exp (-(Lm + L)) - β) := by
    have e1 : Real.exp (-(Lm + L)) = Real.exp (-Lm) * Real.exp (-L) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-L) * Real.exp L = 1 := by rw [← Real.exp_add]; simp
    have e3 : Real.exp (-Lm) * Real.exp Lm = 1 := by rw [← Real.exp_add]; simp
    rw [e1]
    linear_combination (-Real.exp (-Lm)) * e2 + Real.exp (-L) * e3
  have hpos : 0 < (Real.exp L - Real.exp Lm) * (Real.exp (-(Lm + L)) - β) :=
    mul_pos (sub_pos.2 (Real.exp_lt_exp.2 hcon)) (sub_pos.2 hβL)
  linarith

theorem wStar_mul {κ β : ℝ} (hκ : 1 < κ) : wStar κ β * (κ + 1) = 2 * (1 + β) := by
  unfold wStar
  have : κ + 1 ≠ 0 := by linarith
  field_simp

/-- If `2√β ≤ t = 1+β-w_*`, then `ρ_β` is the larger real root of `z² - t z + β`, and
`β ≤ ρ_β²`. -/
theorem rhoBetaR_root {κ β : ℝ} (hκ : 1 < κ) (hb0 : 0 ≤ β)
    (ht : 2 * Real.sqrt β ≤ 1 + β - wStar κ β) :
    rhoBetaR κ β ^ 2 - (1 + β - wStar κ β) * rhoBetaR κ β + β = 0 ∧ β ≤ rhoBetaR κ β ^ 2 := by
  refine ⟨?_, beta_le_meanRadius_sq β _ hb0⟩
  have hs0 := Real.sqrt_nonneg β
  have hs2 : Real.sqrt β ^ 2 = β := Real.sq_sqrt hb0
  set t := 1 + β - wStar κ β with htdef
  have ht0 : 0 ≤ t := by linarith
  have hD : 0 ≤ t ^ 2 - 4 * β := by nlinarith
  set r := Real.sqrt (t ^ 2 - 4 * β) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = t ^ 2 - 4 * β := Real.sq_sqrt hD
  have hρ : rhoBetaR κ β = (t + r) / 2 := by
    unfold rhoBetaR
    rw [meanRadius_eq_max β _ hb0, ← htdef, abs_of_nonneg ht0]
    exact max_eq_right (by linarith)
  rw [hρ]
  nlinarith

theorem two_sqrt_le_t_of_kappa {κ β : ℝ} (hκ : 1 < κ) (hb0 : 0 ≤ β) (hb1 : β < 1)
    (hκβ : ((1 + Real.sqrt β) / (1 - Real.sqrt β)) ^ 2 ≤ κ) :
    2 * Real.sqrt β ≤ 1 + β - wStar κ β := by
  have hs0 := Real.sqrt_nonneg β
  have hs2 : Real.sqrt β ^ 2 = β := Real.sq_sqrt hb0
  have hs1 : Real.sqrt β < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hb0 hb1
  have h1s : 0 < 1 - Real.sqrt β := by linarith
  rw [one_add_sub_wStar hκ, le_div_iff₀ (by linarith)]
  rw [div_pow, div_le_iff₀ (by positivity)] at hκβ
  set s := Real.sqrt β
  rw [← hs2]
  nlinarith

theorem two_sqrt_le_t_of_delta {κ β : ℝ} (hκ : 1 < κ) (hb0 : 0 ≤ β) (hb1 : β < 1)
    (hΔ : 2 * (1 + β) / ((1 - β) ^ 2 * (κ + 1)) ≤ 1 / 4) :
    2 * Real.sqrt β ≤ 1 + β - wStar κ β := by
  have hs0 := Real.sqrt_nonneg β
  have hs2 : Real.sqrt β ^ 2 = β := Real.sq_sqrt hb0
  have hs1 : Real.sqrt β < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hb0 hb1
  have h1β : 0 < 1 - β := by linarith
  have hw : wStar κ β ≤ (1 - β) ^ 2 / 4 := by
    have : wStar κ β = 2 * (1 + β) / (κ + 1) := rfl
    rw [div_le_div_iff₀ (by positivity) (by norm_num)] at hΔ
    rw [this, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  set s := Real.sqrt β
  have : (1 - β) ^ 2 / 4 ≤ (1 - s) ^ 2 := by
    rw [← hs2]
    have h1 : 0 < 1 - s := by linarith
    have : (1 - s ^ 2) ^ 2 = (1 - s) ^ 2 * (1 + s) ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg (1 - s), mul_pos h1 h1]
  rw [← hs2] at hw ⊢
  nlinarith

/-- v2 `prop:helps-critical` (iv): `S_β ≤ A_β` for `κ ≥ κ_β`. -/
theorem SbR_le_A {κ β : ℝ} (hκ : 1 < κ) (hb0 : 0 ≤ β) (hb1 : β < 1)
    (hκβ : ((1 + Real.sqrt β) / (1 - Real.sqrt β)) ^ 2 ≤ κ) :
    SbR κ β ≤ (1 - β) * (κ + 1) / (4 * (1 + β)) := by
  obtain ⟨hroot, -⟩ := rhoBetaR_root hκ hb0 (two_sqrt_le_t_of_kappa hκ hb0 hb1 hκβ)
  have hρ0 := rhoBetaR_pos hκ hb0 hb1
  have hρ1 := rhoBetaR_lt_one hκ hb0 hb1
  have hcore := fixedBeta_core_le hb0 hρ0 hroot
  have hL : 0 < -Real.log (rhoBetaR κ β) := by
    have := Real.log_neg hρ0 hρ1; linarith
  rw [SbR_eq]
  have e : -(2 * Real.log (rhoBetaR κ β)) = 2 * (-Real.log (rhoBetaR κ β)) := by ring
  rw [e, div_le_div_iff₀ (by positivity) (by linarith)]
  have hm := wStar_mul (β := β) hκ
  have hk1 : 0 < κ + 1 := by linarith
  have := mul_le_mul_of_nonneg_right hcore hk1.le
  nlinarith

/-- v2 `prop:helps-critical` (iv): `½(1+√(1-4Δ_β)) A_β ≤ S_β` for `Δ_β ≤ 1/4`. -/
theorem SbR_ge {κ β : ℝ} (hκ : 1 < κ) (hb0 : 0 ≤ β) (hb1 : β < 1)
    (hΔ : 2 * (1 + β) / ((1 - β) ^ 2 * (κ + 1)) ≤ 1 / 4) :
    1 / 2 * (1 + Real.sqrt (1 - 4 * (2 * (1 + β) / ((1 - β) ^ 2 * (κ + 1)))))
        * ((1 - β) * (κ + 1) / (4 * (1 + β))) ≤ SbR κ β := by
  obtain ⟨hroot, hβρ⟩ := rhoBetaR_root hκ hb0 (two_sqrt_le_t_of_delta hκ hb0 hb1 hΔ)
  have hρ0 := rhoBetaR_pos hκ hb0 hb1
  have hρ1 := rhoBetaR_lt_one hκ hb0 hb1
  have h1β : 0 < 1 - β := by linarith
  have hw := wStar_pos hκ hb0
  have hΔe : wStar κ β / (1 - β) ^ 2 = 2 * (1 + β) / ((1 - β) ^ 2 * (κ + 1)) := by
    unfold wStar
    have : κ + 1 ≠ 0 := by linarith
    field_simp
  have hcore := fixedBeta_core_ge hb1 hρ0 hβρ hroot hw (by rw [hΔe]; exact hΔ)
  rw [hΔe] at hcore
  set Δ := 2 * (1 + β) / ((1 - β) ^ 2 * (κ + 1)) with hΔdef
  have hΔ0 : 0 < Δ := by rw [hΔdef]; positivity
  set s := Real.sqrt (1 - 4 * Δ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - 4 * Δ := Real.sq_sqrt (by linarith)
  have hs1 : s < 1 := by nlinarith
  set A := (1 - β) * (κ + 1) / (4 * (1 + β)) with hA
  set Lm := (1 - β) * (1 - s) / 2 with hLm
  have hLm0 : 0 < Lm := by rw [hLm]; have := sub_pos.2 hs1; positivity
  have hL : 0 < -Real.log (rhoBetaR κ β) := by
    have := Real.log_neg hρ0 hρ1; linarith
  have hid : (1 + s) * A * Lm = 1 := by
    calc (1 + s) * A * Lm = A * (1 - β) / 2 * ((1 + s) * (1 - s)) := by rw [hLm]; ring
      _ = A * (1 - β) / 2 * (4 * Δ) := by
        rw [show (1 + s) * (1 - s) = 1 - s ^ 2 by ring, hs2]; ring
      _ = 1 := by
        rw [hA, hΔdef]
        have : κ + 1 ≠ 0 := by linarith
        have : 1 + β ≠ 0 := by linarith
        have : 1 - β ≠ 0 := h1β.ne'
        field_simp
  rw [SbR_eq]
  have e : -(2 * Real.log (rhoBetaR κ β)) = 2 * (-Real.log (rhoBetaR κ β)) := by ring
  rw [e]
  have h2 : 1 / (2 * Lm) ≤ 1 / (2 * (-Real.log (rhoBetaR κ β))) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  refine le_trans (le_of_eq ?_) h2
  field_simp
  exact hid

/-- `ρ(F(w)) ≤ ρ_β` for `w ∈ [w_*, 2(1+β) - w_*]` (monotonicity and symmetry of `ρ(F)`). -/
theorem meanRadius_le_rhoBetaR {κ β w : ℝ} (hκ : 1 < κ) (hb0 : 0 ≤ β)
    (h1 : wStar κ β ≤ w) (h2 : w ≤ 2 * (1 + β) - wStar κ β) : meanRadius β w ≤ rhoBetaR κ β := by
  have hw := wStar_pos hκ hb0
  have hwl := wStar_lt hκ hb0
  by_cases hw1 : w ≤ 1 + β
  · exact meanRadius_antitoneOn β hb0 ⟨hw, hwl.le⟩ ⟨by linarith, hw1⟩ h1
  · push Not at hw1
    have := meanRadius_monotoneOn β hb0 (a := w) (b := 2 * (1 + β) - wStar κ β)
      ⟨hw1.le, by linarith⟩ ⟨by linarith, by linarith⟩ h2
    rwa [meanRadius_symm] at this

/-- If `w_V > 0` and `κ w_V < 2(1+β)`, then `ρ_β ≤ ρ(F(κ w_V))` or `ρ_β ≤ ρ(F(w_V))`
(the case split `w_1 + w_V ≤ 2(1+β)` or not, in `prop:helps-critical` Step 6). -/
theorem rhoBetaR_le_or {κ β wV : ℝ} (hκ : 1 < κ) (hb0 : 0 ≤ β) (hwV : 0 < wV)
    (hw1 : κ * wV < 2 * (1 + β)) :
    rhoBetaR κ β ≤ meanRadius β (κ * wV) ∨ rhoBetaR κ β ≤ meanRadius β wV := by
  have hw := wStar_pos hκ hb0
  have hwl := wStar_lt hκ hb0
  by_cases h : wV ≤ wStar κ β
  · exact Or.inr (meanRadius_antitoneOn β hb0 ⟨hwV, by linarith⟩ ⟨hw, hwl.le⟩ h)
  · push Not at h
    left
    have hk := kappa_mul_wStar (β := β) hκ
    have h3 : κ * wStar κ β < κ * wV := mul_lt_mul_of_pos_left h (by linarith)
    have := meanRadius_monotoneOn β hb0 (a := 2 * (1 + β) - wStar κ β) (b := κ * wV)
      ⟨by linarith, by linarith⟩ ⟨by linarith, hw1⟩ (by linarith)
    rwa [meanRadius_symm] at this

end FixedBetaReal

/-! ### Fixed `β`: the dynamics (v2 `prop:helps-critical` (iv), Step 6) -/

section FixedBeta

variable {n : ℕ} {d B : ℕ} {ν : Measure ℝ} {ps : Fin (n + 1) → unitInterval}

/-- `ρ_β`: the largest root modulus of `z² - (1+β)(κ-1)/(κ+1) z + β`, as `ρ(F)` at
`w_* = 2(1+β)/(κ+1)` (v2 `prop:helps-critical` (iv)). -/
def rhoBeta (ps : Fin (n + 1) → unitInterval) (β : ℝ) : ℝ := rhoBetaR (kappaV ps) β

/-- `S_β = -1/(2 ln ρ_β)` (v2 `prop:helps-critical` (iv)). -/
def Sbeta (ps : Fin (n + 1) → unitInterval) (β : ℝ) : ℝ :=
  -1 / (2 * Real.log (rhoBeta ps β))

theorem Sbeta_eq_SbR {β : ℝ} : Sbeta ps β = SbR (kappaV ps) β := rfl

theorem meanRadius_sq_le_rhoMax (hp : ∀ j, 0 < (ps j : ℝ)) {β η : ℝ} (hb0 : 0 ≤ β)
    (hb1 : β < 1) (hη : 0 < η) (j : Fin (n + 1)) :
    meanRadius β (η * (1 - β) * (ps j : ℝ)) ^ 2 ≤ rhoMax d B ν β η ps := by
  have hw : 0 ≤ (copyParams d B ν β η ps j).w := by
    rw [copyParams_w]
    have := hp j
    have : 0 < 1 - β := by linarith
    positivity
  have := meanRadius_sq_le_stepRadius (copyParams d B ν β η ps j) hb0 hb1 hw
    (copyParams_noise_nonneg hp hη.le j)
  simp only [copyParams_beta, copyParams_w] at this
  exact this.trans (le_rhoMax j)

/-- v2 `prop:helps-critical` (iv), Step 6, lower bound: a stable choice has `ρ_β² ≤ rhoMax`
(`first_copy_ceiling`, the case split of `rhoBetaR_le_or`, and `meanRadius_sq_le_stepRadius`). -/
theorem rhoBeta_sq_le_rhoMax (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) {β η : ℝ}
    (hb0 : 0 ≤ β) (hb1 : β < 1) (hη : 0 < η)
    (hstab : ∀ j, stepRadius (copyParams d B ν β η ps j) < 1) :
    rhoBeta ps β ^ 2 ≤ rhoMax d B ν β η ps := by
  have hpV := hp (Fin.last n)
  have hceil := first_copy_ceiling hp hη hb0 hb1 (hstab 0)
  have hk : kappaV ps * (η * (1 - β) * (ps (Fin.last n) : ℝ)) = η * (1 - β) * (ps 0 : ℝ) := by
    have := kappa_mul_pLast hp
    unfold pLast at this
    calc _ = η * (1 - β) * (kappaV ps * (ps (Fin.last n) : ℝ)) := by ring
      _ = _ := by rw [this]
  have hwV : 0 < η * (1 - β) * (ps (Fin.last n) : ℝ) := by
    have : 0 < 1 - β := by linarith
    positivity
  have hdis := rhoBetaR_le_or hκ hb0 hwV (by rw [hk]; exact hceil)
  have hr0 := rhoBetaR_pos hκ hb0 hb1
  have hr0' : 0 ≤ rhoBeta ps β := hr0.le
  rcases hdis with h | h
  · rw [hk] at h
    exact (pow_le_pow_left₀ hr0' h 2).trans (meanRadius_sq_le_rhoMax hp hb0 hb1 hη 0)
  · exact (pow_le_pow_left₀ hr0' h 2).trans (meanRadius_sq_le_rhoMax hp hb0 hb1 hη (Fin.last n))

theorem Lmin_le_two_mul_log (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) {β η : ℝ}
    (hb0 : 0 ≤ β) (hb1 : β < 1) (hη : 0 < η)
    (hstab : ∀ j, stepRadius (copyParams d B ν β η ps j) < 1) :
    Lmin d B ν β η ps ≤ -(2 * Real.log (rhoBeta ps β)) := by
  have h := rhoBeta_sq_le_rhoMax (d := d) (B := B) (ν := ν) hp hκ hb0 hb1 hη hstab
  have hr0 := rhoBetaR_pos hκ hb0 hb1
  have hsq : 0 < rhoBeta ps β ^ 2 := by
    have : 0 < rhoBeta ps β := hr0
    positivity
  have := Real.log_le_log hsq h
  rw [Real.log_pow] at this
  unfold Lmin
  push_cast at this
  linarith

theorem rhoBeta_pos (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1) :
    0 < rhoBeta ps β := rhoBetaR_pos hκ hb0 hb1

theorem rhoBeta_lt_one (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1) :
    rhoBeta ps β < 1 := rhoBetaR_lt_one hκ hb0 hb1

theorem Sbeta_eq (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1) :
    Sbeta ps β = 1 / (-(2 * Real.log (rhoBeta ps β))) := SbR_eq

theorem neg_two_log_pos (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1) :
    0 < -(2 * Real.log (rhoBeta ps β)) := by
  have := Real.log_neg (rhoBeta_pos hκ hb0 hb1) (rhoBeta_lt_one hκ hb0 hb1)
  linarith

theorem Sbeta_pos (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1) :
    0 < Sbeta ps β := by
  rw [Sbeta_eq hκ hb0 hb1]
  exact one_div_pos.2 (neg_two_log_pos hκ hb0 hb1)

theorem singleton_sub_Ico {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1) : ({β} : Set ℝ) ⊆ Set.Ico 0 1 :=
  Set.singleton_subset_iff.2 ⟨hb0, hb1⟩

/-- v2 `prop:helps-critical` (iv), Step 6 lower bound, pointwise: every admissible `(η, β)` of the
class `{β}` has `S_β ≤ 1/Λ_min`.  No Jury hypothesis. -/
theorem Sfun_fixed_ge_pointwise (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) {β : ℝ}
    (hb0 : 0 ≤ β) (hb1 : β < 1) {x : ℝ × ℝ} (hx : x ∈ admSet d B ν ps {β}) :
    Sbeta ps β ≤ 1 / Lmin d B ν x.2 x.1 ps := by
  obtain ⟨hη, hβ, hst⟩ := hx
  have hx2 : x.2 = β := hβ
  rw [hx2] at hst ⊢
  have hpos := Lmin_pos_of_mem hp hκ (singleton_sub_Ico hb0 hb1) (x := x)
    ⟨hη, hβ, by rw [hx2]; exact hst⟩
  rw [hx2] at hpos
  rw [Sbeta_eq hκ hb0 hb1]
  exact one_div_le_one_div_of_le hpos (Lmin_le_two_mul_log hp hκ hb0 hb1 hη hst)

theorem Sfun_fixed_ge_of_mem (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) {β : ℝ}
    (hb0 : 0 ≤ β) (hb1 : β < 1) {x : ℝ × ℝ} (hx : x ∈ admSet d B ν ps {β}) :
    Sbeta ps β ≤ Sfun d B ν ps {β} :=
  le_csInf ((Set.nonempty_of_mem hx).image _)
    (by rintro _ ⟨y, hy, rfl⟩; exact Sfun_fixed_ge_pointwise hp hκ hb0 hb1 hy)

/-- Under Jury, the admissible set at fixed `β` is nonempty for every `B ≥ 1`. -/
theorem admSet_fixed_nonempty (jury : External.JuryStability) (hp : ∀ j, 0 < (ps j : ℝ))
    (hanti : Antitone ps) (hB : 1 ≤ B) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1) :
    (admSet d B ν ps {β}).Nonempty := by
  have hB0 : 0 < B := hB
  set m := min (criticalRate d B (ps 0) β) (criticalRate d B (ps (Fin.last n)) β) with hm
  have hm0 : 0 < m := by
    rw [hm, lt_min_iff]
    constructor <;> exact inv_pos.2 (inverseCriticalRate_pos d B hB0 _ β hb0 hb1)
  refine ⟨(m / 2, β), by positivity, rfl, ?_⟩
  exact (all_stable_iff_lt_min jury hB0 hp hanti hb0 hb1 (by positivity)).2 (by linarith)

/-- v2 `prop:helps-critical` (iv): `S_β ≤ S_β(B)` for every `B ≥ 1` (uses Jury for non-emptiness
of `A_{β}(B)`, since `sInf ∅ = 0`). -/
theorem Sfun_fixed_ge (jury : External.JuryStability) (hp : ∀ j, 0 < (ps j : ℝ))
    (hanti : Antitone ps) (hκ : 1 < kappaV ps) (hB : 1 ≤ B) {β : ℝ} (hb0 : 0 ≤ β)
    (hb1 : β < 1) : Sbeta ps β ≤ Sfun d B ν ps {β} := by
  obtain ⟨x, hx⟩ := admSet_fixed_nonempty (d := d) (ν := ν) jury hp hanti hB hb0 hb1
  exact Sfun_fixed_ge_of_mem hp hκ hb0 hb1 hx

/-- The balancing learning rate `η(1-β)(p_1+p_V) = 2(1+β)` of `prop:helps-critical` Step 6. -/
def etaFixedBeta (ps : Fin (n + 1) → unitInterval) (β : ℝ) : ℝ :=
  2 * (1 + β) / ((1 - β) * ((ps 0 : ℝ) + (ps (Fin.last n) : ℝ)))

theorem etaFixedBeta_w (hp : ∀ j, 0 < (ps j : ℝ)) {β : ℝ} (hb1 : β < 1) (p : ℝ) :
    etaFixedBeta ps β * (1 - β) * p
      = 2 * (1 + β) * p / ((ps 0 : ℝ) + (ps (Fin.last n) : ℝ)) := by
  have h0 := hp 0
  have hl := hp (Fin.last n)
  have : 1 - β ≠ 0 := by linarith
  have : (ps 0 : ℝ) + (ps (Fin.last n) : ℝ) ≠ 0 := by linarith
  unfold etaFixedBeta
  field_simp

theorem wStar_kappaV (hp : ∀ j, 0 < (ps j : ℝ)) (β : ℝ) :
    wStar (kappaV ps) β
      = 2 * (1 + β) * (ps (Fin.last n) : ℝ) / ((ps 0 : ℝ) + (ps (Fin.last n) : ℝ)) := by
  have h0 := hp 0
  have hl := hp (Fin.last n)
  have : (ps 0 : ℝ) + (ps (Fin.last n) : ℝ) ≠ 0 := by linarith
  unfold wStar kappaV
  field_simp

theorem etaFixedBeta_pos (hp : ∀ j, 0 < (ps j : ℝ)) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1) :
    0 < etaFixedBeta ps β := by
  have h0 := hp 0
  have hl := hp (Fin.last n)
  have : 0 < 1 - β := by linarith
  unfold etaFixedBeta
  positivity

/-- At the balancing rate, the noise-free radii are `ρ(F_j)² ≤ ρ_β²` with equality at `j = V`, so
`rhoMax0 = ρ_β²` (`stepRadius_noiseFree_eq_meanRadius_sq`). -/
theorem rhoMax0_fixed (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps)
    {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1) :
    rhoMax0 β (etaFixedBeta ps β) ps = rhoBeta ps β ^ 2 := by
  have hs : 0 < (ps 0 : ℝ) + (ps (Fin.last n) : ℝ) := by
    have := hp 0; have := hp (Fin.last n); linarith
  have hrad : ∀ j, stepRadius (copyParams0 β (etaFixedBeta ps β) ps j)
      = meanRadius β (etaFixedBeta ps β * (1 - β) * (ps j : ℝ)) ^ 2 := fun j =>
    stepRadius_noiseFree_eq_meanRadius_sq (copyParams0 β (etaFixedBeta ps β) ps j) hb0 rfl
  have hwV : etaFixedBeta ps β * (1 - β) * (ps (Fin.last n) : ℝ) = wStar (kappaV ps) β := by
    rw [etaFixedBeta_w hp hb1, wStar_kappaV hp]
  apply le_antisymm
  · unfold rhoMax0
    refine Finset.sup'_le _ _ (fun j _ => ?_)
    rw [hrad j]
    refine pow_le_pow_left₀ (meanRadius_nonneg _ _) (meanRadius_le_rhoBetaR hκ hb0 ?_ ?_) 2
    · rw [etaFixedBeta_w hp hb1, wStar_kappaV hp]
      apply div_le_div_of_nonneg_right _ hs.le
      have := last_le_ps hanti j
      have : 0 ≤ 2 * (1 + β) := by linarith
      nlinarith
    · rw [etaFixedBeta_w hp hb1]
      have e : 2 * (1 + β) - wStar (kappaV ps) β
          = 2 * (1 + β) * (ps 0 : ℝ) / ((ps 0 : ℝ) + (ps (Fin.last n) : ℝ)) := by
        rw [wStar_kappaV hp]; field_simp; ring
      rw [e]
      apply div_le_div_of_nonneg_right _ hs.le
      have := ps_le_first hanti j
      have : 0 ≤ 2 * (1 + β) := by linarith
      nlinarith
  · have := le_rhoMax0 (beta := β) (eta := etaFixedBeta ps β) (ps := ps) (Fin.last n)
    rw [hrad, hwV] at this
    exact this

/-- v2 `prop:helps-critical` (iv): `S_β(B) → S_β` as `B → ∞` (no Jury hypothesis). -/
theorem Sfun_fixed_tendsto (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1) :
    Tendsto (fun B : ℕ => Sfun d B ν ps {β}) atTop (𝓝 (Sbeta ps β)) := by
  set η := etaFixedBeta ps β with hη
  have hη0 : 0 < η := etaFixedBeta_pos hp hb0 hb1
  have hr := rhoMax0_fixed hp hanti hκ hb0 hb1
  have hρ0 := rhoBeta_pos hκ hb0 hb1 (ps := ps)
  have hρ1 := rhoBeta_lt_one hκ hb0 hb1 (ps := ps)
  have hρ2 : rhoBeta ps β ^ 2 < 1 := by nlinarith
  have hev : ∀ᶠ B : ℕ in atTop, ∀ j, stepRadius (copyParams d B ν β η ps j) < 1 :=
    eventually_stable hp (fun j => lt_of_le_of_lt (le_rhoMax0 j) (by rw [hr]; exact hρ2))
  have hlim1 : Tendsto (fun B : ℕ => rhoMax d B ν β η ps) atTop (𝓝 (rhoBeta ps β ^ 2)) := by
    have := tendsto_rhoMax (d := d) (ν := ν) (beta := β) (eta := η) hp
    rwa [hr] at this
  have hne : rhoBeta ps β ^ 2 ≠ 0 := by positivity
  have hlim2 : Tendsto (fun B : ℕ => Lmin d B ν β η ps) atTop
      (𝓝 (-(2 * Real.log (rhoBeta ps β)))) := by
    have h2 := ((Real.continuousAt_log hne).tendsto.comp hlim1).neg
    have e : -Real.log (rhoBeta ps β ^ 2) = -(2 * Real.log (rhoBeta ps β)) := by
      rw [Real.log_pow]; push_cast; ring
    rw [e] at h2
    exact h2
  have hlim : Tendsto (fun B : ℕ => 1 / Lmin d B ν β η ps) atTop (𝓝 (Sbeta ps β)) := by
    rw [Sbeta_eq hκ hb0 hb1]
    exact tendsto_const_nhds.div hlim2 (neg_two_log_pos hκ hb0 hb1).ne'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [hev] with B hst
    exact Sfun_fixed_ge_of_mem hp hκ hb0 hb1 (x := (η, β)) ⟨hη0, rfl, hst⟩
  · filter_upwards [hev] with B hst
    exact Sfun_le hp hκ (singleton_sub_Ico hb0 hb1) (x := (η, β)) ⟨hη0, rfl, hst⟩

/-- v2 `prop:helps-critical` (iv): `S_β = inf_{B ≥ 1} S_β(B)` (uses Jury for the lower bound at
every `B`). -/
theorem Sinf_fixed_eq (jury : External.JuryStability) (hp : ∀ j, 0 < (ps j : ℝ))
    (hanti : Antitone ps) (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1) :
    Sinf d ν ps {β} = Sbeta ps β := by
  have hge : ∀ B : ℕ, 1 ≤ B → Sbeta ps β ≤ Sfun d B ν ps {β} :=
    fun B hB => Sfun_fixed_ge jury hp hanti hκ hB hb0 hb1
  have hpos := Sbeta_pos hκ hb0 hb1 (ps := ps)
  apply le_antisymm
  · refine ge_of_tendsto (Sfun_fixed_tendsto (d := d) (ν := ν) hp hanti hκ hb0 hb1) ?_
    filter_upwards [eventually_ge_atTop 1] with B hB
    exact csInf_le ⟨0, by
      rintro _ ⟨B', hB', rfl⟩
      exact (hpos.trans_le (hge B' hB')).le⟩ ⟨B, hB, rfl⟩
  · exact Sinf_ge hge

/-- `κ_β = ((1+√β)/(1-√β))²` (v2 `prop:helps-critical` (iv)). -/
def kappaBeta (β : ℝ) : ℝ := ((1 + Real.sqrt β) / (1 - Real.sqrt β)) ^ 2

/-- `Δ_β = 2(1+β)/((1-β)²(κ+1))` (v2 `prop:helps-critical` (iv)). -/
def DeltaBeta (ps : Fin (n + 1) → unitInterval) (β : ℝ) : ℝ :=
  2 * (1 + β) / ((1 - β) ^ 2 * (kappaV ps + 1))

/-- `A_β = (1-β)(κ+1)/(4(1+β))` (v2 `prop:helps-critical` (iv)). -/
def ABeta (ps : Fin (n + 1) → unitInterval) (β : ℝ) : ℝ :=
  (1 - β) * (kappaV ps + 1) / (4 * (1 + β))

/-- `β_P = ((√κ-1)/(√κ+1))²`, Polyak's momentum (v2 `prop:helps-critical` (iv)). -/
def betaPolyak (ps : Fin (n + 1) → unitInterval) : ℝ :=
  ((Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1)) ^ 2

/-- v2 `prop:helps-critical` (iv): `ρ_0 = (κ-1)/(κ+1)`. -/
theorem rhoBeta_zero (hκ : 1 < kappaV ps) :
    rhoBeta ps 0 = (kappaV ps - 1) / (kappaV ps + 1) := rhoBetaR_zero hκ

/-- v2 `prop:helps-critical` (iv): for `0 < β < 1`, `ρ_β = √β` iff `κ ≤ κ_β`. -/
theorem rhoBeta_eq_sqrt_iff (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 < β) (hb1 : β < 1) :
    rhoBeta ps β = Real.sqrt β ↔ kappaV ps ≤ kappaBeta β :=
  rhoBetaR_eq_sqrt_iff hκ hb0 hb1

/-- v2 `prop:helps-critical` (iv): `ρ_β ≥ (√κ-1)/(√κ+1)`. -/
theorem rhoBeta_ge_polyak (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1) :
    (Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1) ≤ rhoBeta ps β :=
  rhoBetaR_ge_polyak hκ hb0 hb1

/-- v2 `prop:helps-critical` (iv): equality at Polyak's `β_P`. -/
theorem rhoBeta_polyak (hκ : 1 < kappaV ps) :
    rhoBeta ps (betaPolyak ps)
      = (Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1) := rhoBetaR_polyak hκ

theorem betaPolyak_mem (hκ : 1 < kappaV ps) : 0 ≤ betaPolyak ps ∧ betaPolyak ps < 1 := by
  have hs : 1 < Real.sqrt (kappaV ps) := sqrt_kappa_gt_one hκ
  have hq0 : 0 < (Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1) :=
    div_pos (by linarith) (by linarith)
  have hq1 : (Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  unfold betaPolyak
  constructor
  · positivity
  · nlinarith

theorem lamMom_eq_neg_log (hκ : 1 < kappaV ps) :
    lamMom ps = -(2 * Real.log ((Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1))) := by
  unfold lamMom
  rw [← neg_log_sq_div (s := Real.sqrt (kappaV ps)), Real.log_pow]
  push_cast; ring

/-- v2 `prop:helps-critical` (iv): `S_β ≥ 1/λ_mom` for every `β ∈ [0,1)`. -/
theorem Sbeta_ge_inv_lamMom (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1) :
    1 / lamMom ps ≤ Sbeta ps β := by
  rw [Sbeta_eq hκ hb0 hb1]
  have hs : 1 < Real.sqrt (kappaV ps) := sqrt_kappa_gt_one hκ
  have hq0 : 0 < (Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1) :=
    div_pos (by linarith) (by linarith)
  have hlog := Real.log_le_log hq0 (rhoBeta_ge_polyak hκ hb0 hb1)
  rw [lamMom_eq_neg_log hκ]
  refine one_div_le_one_div_of_le (neg_two_log_pos hκ hb0 hb1) ?_
  linarith

/-- v2 `prop:helps-critical` (iv): `S_{β_P} = 1/λ_mom`. -/
theorem Sbeta_polyak (hκ : 1 < kappaV ps) : Sbeta ps (betaPolyak ps) = 1 / lamMom ps := by
  obtain ⟨h0, h1⟩ := betaPolyak_mem hκ
  rw [Sbeta_eq hκ h0 h1, rhoBeta_polyak hκ, lamMom_eq_neg_log hκ]

/-- v2 `prop:helps-critical` (iv): the infimum over `β ∈ [0,1)` of `S_β` is attained at Polyak's
`β_P` and equals `1/λ_mom`. -/
theorem Sbeta_isLeast (hκ : 1 < kappaV ps) :
    IsLeast (Sbeta ps '' Set.Ico (0 : ℝ) 1) (1 / lamMom ps) := by
  refine ⟨⟨betaPolyak ps, betaPolyak_mem hκ, Sbeta_polyak hκ⟩, ?_⟩
  rintro _ ⟨β, ⟨hb0, hb1⟩, rfl⟩
  exact Sbeta_ge_inv_lamMom hκ hb0 hb1

/-- v2 `prop:helps-critical` (iv): `inf_β S_β = S_mom`, which recovers (i). -/
theorem Sbeta_inf_eq_Sinf_mom (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hκ : 1 < kappaV ps) :
    sInf (Sbeta ps '' Set.Ico (0 : ℝ) 1) = Sinf d ν ps momClass := by
  rw [(Sbeta_isLeast hκ).csInf_eq, Sinf_mom hp hanti hκ]

/-- v2 `prop:helps-critical` (iv): `S_β ≤ A_β` for `κ ≥ κ_β`. -/
theorem Sbeta_le_A (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1)
    (hκβ : kappaBeta β ≤ kappaV ps) : Sbeta ps β ≤ ABeta ps β :=
  SbR_le_A hκ hb0 hb1 hκβ

/-- v2 `prop:helps-critical` (iv): `½(1+√(1-4Δ_β)) A_β ≤ S_β` for `Δ_β ≤ 1/4`. -/
theorem Sbeta_ge (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1)
    (hΔ : DeltaBeta ps β ≤ 1 / 4) :
    1 / 2 * (1 + Real.sqrt (1 - 4 * DeltaBeta ps β)) * ABeta ps β ≤ Sbeta ps β :=
  SbR_ge hκ hb0 hb1 hΔ

/-! ### (K1) Part (i), limit form -/

/-- v2 `prop:helps-critical` (i): `S_SGD(B) → S_SGD` as `B → ∞` (`κ_V > 1`). -/
theorem Sfun_tendsto_Sinf_sgd (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hκ : 1 < kappaV ps) :
    Tendsto (fun B : ℕ => Sfun d B ν ps sgdClass) atTop (𝓝 (Sinf d ν ps sgdClass)) := by
  rw [Sinf_sgd hp hanti hκ]
  exact Sfun_tendsto_sgd hp hanti hκ

/-- v2 `prop:helps-critical` (i): `S_mom(B) → S_mom` as `B → ∞` (`κ_V > 1`). -/
theorem Sfun_tendsto_Sinf_mom (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hκ : 1 < kappaV ps) :
    Tendsto (fun B : ℕ => Sfun d B ν ps momClass) atTop (𝓝 (Sinf d ν ps momClass)) := by
  rw [Sinf_mom hp hanti hκ]
  exact Sfun_tendsto_mom hp hanti hκ

/-! ### (K2) Part (iii), absolute bounds on `B_mom` -/

theorem lamMom_bounds (hκ : 1 < kappaV ps) :
    4 / Real.sqrt (kappaV ps) ≤ lamMom ps ∧
      lamMom ps ≤ 4 * Real.sqrt (kappaV ps) / (kappaV ps - 1) := by
  have hs := sqrt_kappa_gt_one hκ
  have hk0 : 0 < kappaV ps := by linarith
  have hs2 : Real.sqrt (kappaV ps) ^ 2 = kappaV ps := Real.sq_sqrt hk0.le
  obtain ⟨h1, h2⟩ := two_log_bounds hs
  rw [hs2] at h2
  exact ⟨h1, h2⟩

theorem sqrt_mul_pLast (hp : ∀ j, 0 < (ps j : ℝ)) :
    Real.sqrt ((ps 0 : ℝ) * (ps (Fin.last n) : ℝ))
      = Real.sqrt (kappaV ps) * (ps (Fin.last n) : ℝ) := by
  have hpV := hp (Fin.last n)
  have hk : kappaV ps * (ps (Fin.last n) : ℝ) = (ps 0 : ℝ) := kappa_mul_pLast hp
  have hk0 : 0 ≤ kappaV ps := by
    have : 0 < kappaV ps := div_pos (hp 0) hpV
    exact this.le
  rw [← hk, show kappaV ps * (ps (Fin.last n) : ℝ) * (ps (Fin.last n) : ℝ)
    = (Real.sqrt (kappaV ps) * (ps (Fin.last n) : ℝ)) ^ 2 by
      rw [mul_pow, Real.sq_sqrt hk0]; ring]
  exact Real.sqrt_sq (by positivity)

/-- v2 `prop:helps-critical` (iii) (`κ_V > 1`): `B_mom ≤ κ/(κ-1) · 4(d+2)/√(p_1 p_V)`. -/
theorem Bcrit_mom_le_abs (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 1 < kappaV ps) :
    Bcrit d ν ps momClass
      ≤ kappaV ps / (kappaV ps - 1)
        * (4 * ((d : ℝ) + 2) / Real.sqrt ((ps 0 : ℝ) * (ps (Fin.last n) : ℝ))) := by
  rw [Bcrit_mom_eq hp hanti hκ]
  have hs := sqrt_kappa_gt_one hκ
  have hk0 : 0 < kappaV ps := by linarith
  have hs2 : Real.sqrt (kappaV ps) ^ 2 = kappaV ps := Real.sq_sqrt hk0.le
  have hpV := hp (Fin.last n)
  have hE0 : 0 ≤ Einf d ν ps momClass :=
    Einf_ge (fun B hB => Efun_nonneg hp hκ momClass_sub zero_mem_momClass hB)
  have hE1 : Einf d ν ps momClass ≤ ((d : ℝ) + 2) / (ps (Fin.last n) : ℝ) := by
    have h1 := Einf_mom_le_sgd (d := d) (ν := ν) hp hanti hκ
    rw [Einf_sgd hp hanti hκ] at h1
    exact h1.trans (Esgd1_bounds d ps hpV).2
  obtain ⟨-, hl2⟩ := lamMom_bounds (ps := ps) hκ
  have hden : 0 < kappaV ps - 1 := by linarith
  calc Einf d ν ps momClass * lamMom ps
      ≤ (((d : ℝ) + 2) / (ps (Fin.last n) : ℝ))
          * (4 * Real.sqrt (kappaV ps) / (kappaV ps - 1)) :=
        mul_le_mul hE1 hl2 (lamMom_pos hκ).le (by positivity)
    _ = _ := by
      rw [sqrt_mul_pLast hp]
      set s := Real.sqrt (kappaV ps) with hsdef
      have hsne : s ≠ 0 := by linarith
      have hne : s ^ 2 - 1 ≠ 0 := by rw [hs2]; exact hden.ne'
      have hpne : (ps (Fin.last n) : ℝ) ≠ 0 := hpV.ne'
      rw [← hs2]
      field_simp

/-- v2 `prop:helps-critical` (iii) (`κ_V > 16`):
`c_κ (d+2-p_V)/(2√(p_1 p_V)) ≤ B_mom`, `c_κ = max(1-4/√κ, 1/√5)`. -/
theorem Bcrit_mom_ge_abs (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 16 < kappaV ps) :
    max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5)
        * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))
        / (2 * Real.sqrt ((ps 0 : ℝ) * (ps (Fin.last n) : ℝ)))
      ≤ Bcrit d ν ps momClass := by
  have hκ1 : 1 < kappaV ps := by linarith
  rw [Bcrit_mom_eq hp hanti hκ1]
  have hs := sqrt_kappa_gt_one hκ1
  have hpV := hp (Fin.last n)
  have hDv := Dv_pos d ps
  set c := max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) with hc
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hE := Einf_mom_ge' (d := d) (ν := ν) hp hκ
  rw [← hc] at hE
  obtain ⟨hl1, -⟩ := lamMom_bounds (ps := ps) hκ1
  have hDv' : Dv d ps = (d : ℝ) + 2 - (ps (Fin.last n) : ℝ) := rfl
  have hpL : pLast ps = (ps (Fin.last n) : ℝ) := rfl
  rw [hpL, hDv'] at hE
  calc c * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))
        / (2 * Real.sqrt ((ps 0 : ℝ) * (ps (Fin.last n) : ℝ)))
      = (c * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) / (8 * (ps (Fin.last n) : ℝ)))
          * (4 / Real.sqrt (kappaV ps)) := by
        rw [sqrt_mul_pLast hp]
        have : Real.sqrt (kappaV ps) ≠ 0 := by linarith
        have : (ps (Fin.last n) : ℝ) ≠ 0 := hpV.ne'
        field_simp
        ring
    _ ≤ Einf d ν ps momClass * lamMom ps := by
        apply mul_le_mul hE hl1 (by positivity)
        exact (lt_of_lt_of_le (by
          have : 0 < c * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) / (8 * (ps (Fin.last n) : ℝ)) := by
            have : 0 < (d : ℝ) + 2 - (ps (Fin.last n) : ℝ) := hDv
            positivity
          exact this) hE).le

/-! ### Optional discussion lemmas for (iii) -/

theorem pLast_le_inv_of_kappa (hp : ∀ j, 0 < (ps j : ℝ)) {c : ℝ} (hc : 0 < c)
    (hκ : c ≤ kappaV ps) : (ps (Fin.last n) : ℝ) ≤ 1 / c := by
  have hpV := hp (Fin.last n)
  have hk : kappaV ps * (ps (Fin.last n) : ℝ) = (ps 0 : ℝ) := kappa_mul_pLast hp
  have h1 : (ps 0 : ℝ) ≤ 1 := (ps 0).2.2
  rw [le_div_iff₀ hc]
  nlinarith

/-- v2 `prop:helps-critical` (iii), discussion: for `κ_V ≥ 150` and `d ≥ 1` the lower bound on
`B_mom/B_SGD` exceeds `1`. -/
theorem Bratio_lower_gt_one (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 150 ≤ kappaV ps) (hd : 1 ≤ d) :
    1 < max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Real.sqrt (kappaV ps) / 8
      * (1 - 1 / kappaV ps ^ 2) * (1 - (ps (Fin.last n) : ℝ) / ((d : ℝ) + 2)) := by
  have hk0 : 0 < kappaV ps := by linarith
  have hs2 : Real.sqrt (kappaV ps) ^ 2 = kappaV ps := Real.sq_sqrt hk0.le
  have hs0 : 0 ≤ Real.sqrt (kappaV ps) := Real.sqrt_nonneg _
  set s := Real.sqrt (kappaV ps) with hsdef
  have hs : 12.2 ≤ s := by
    by_contra h
    push Not at h
    nlinarith
  have hspos : 0 < s := by linarith
  have hX : 8.2 ≤ max (1 - 4 / s) (1 / Real.sqrt 5) * s := by
    have h1 : (1 - 4 / s) * s ≤ max (1 - 4 / s) (1 / Real.sqrt 5) * s :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hspos.le
    have h2 : (1 - 4 / s) * s = s - 4 := by field_simp
    linarith
  have hu : 22499 / 22500 ≤ 1 - 1 / kappaV ps ^ 2 := by
    have : 1 / kappaV ps ^ 2 ≤ 1 / 22500 := by
      apply one_div_le_one_div_of_le (by norm_num)
      nlinarith
    linarith
  have hpV : (ps (Fin.last n) : ℝ) ≤ 1 / 150 := pLast_le_inv_of_kappa hp (by norm_num) hκ
  have hD : (3 : ℝ) ≤ (d : ℝ) + 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hv : 449 / 450 ≤ 1 - (ps (Fin.last n) : ℝ) / ((d : ℝ) + 2) := by
    have : (ps (Fin.last n) : ℝ) / ((d : ℝ) + 2) ≤ 1 / 450 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  calc (1 : ℝ) < 8.2 / 8 * (22499 / 22500) * (449 / 450) := by norm_num
    _ ≤ _ := by gcongr

/-- v2 `prop:helps-critical` (iii), discussion: for `κ_V > 16` and `d ≥ 1`,
`E_SGD/E_mom ≤ 8(d+2)/(c_κ(d+2-p_V)) < 19`. -/
theorem Einf_ratio_lt_19 (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hκ : 16 < kappaV ps)
    (hd : 1 ≤ d) :
    Einf d ν ps sgdClass / Einf d ν ps momClass
        ≤ 8 * ((d : ℝ) + 2) / (max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5)
            * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))) ∧
      8 * ((d : ℝ) + 2) / (max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5)
            * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))) < 19 := by
  have hκ1 : 1 < kappaV ps := by linarith
  have hpV := hp (Fin.last n)
  have hDv := Dv_pos d ps
  have hDv' : Dv d ps = (d : ℝ) + 2 - (ps (Fin.last n) : ℝ) := rfl
  have hpL : pLast ps = (ps (Fin.last n) : ℝ) := rfl
  set c := max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) with hc
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hE := Einf_mom_ge' (d := d) (ν := ν) hp hκ
  rw [← hc, hpL, hDv'] at hE
  have hDvp : 0 < (d : ℝ) + 2 - (ps (Fin.last n) : ℝ) := by rw [← hDv']; exact hDv
  have hEpos : 0 < c * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) / (8 * (ps (Fin.last n) : ℝ)) := by
    positivity
  have hEs : Einf d ν ps sgdClass ≤ ((d : ℝ) + 2) / (ps (Fin.last n) : ℝ) := by
    rw [Einf_sgd hp hanti hκ1]; exact (Esgd1_bounds d ps hpV).2
  have hEs0 : 0 ≤ ((d : ℝ) + 2) / (ps (Fin.last n) : ℝ) := by positivity
  constructor
  · refine le_trans (div_le_div₀ hEs0 hEs hEpos hE) (le_of_eq ?_)
    have : (ps (Fin.last n) : ℝ) ≠ 0 := hpV.ne'
    field_simp
  · have hp16 : (ps (Fin.last n) : ℝ) ≤ 1 / 16 := pLast_le_inv_of_kappa hp (by norm_num) hκ.le
    have hD : (3 : ℝ) ≤ (d : ℝ) + 2 := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have h5 : Real.sqrt 5 < 2.24 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hc1 : 1 / 2.24 ≤ c := by
      have : 1 / 2.24 ≤ 1 / Real.sqrt 5 :=
        one_div_le_one_div_of_le (Real.sqrt_pos.2 (by norm_num)) h5.le
      exact this.trans (le_max_right _ _)
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hc1 hDvp.le]

/-! ### (K3) Part (v) of `lem:helps-vocab` at the level of `S_SGD(B)` -/

theorem sgd_Lmin_pos (hB : 1 ≤ B) (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) {η : ℝ}
    (hη : 0 < η) (hst : ∀ j, stepRadius (copyParams d B ν 0 η ps j) < 1) :
    0 < Lmin d B ν 0 η ps := by
  have hB0 : 0 < B := hB
  have hmin := (vv_stable_iff (d := d) (ν := ν) hB0 hp hanti hη rfl).1 hst
  rw [vv_Lmin_eq hB0 hp hanti hη rfl]
  have hlt : min (sgdGain d B ((ps 0 : unitInterval) : ℝ) η)
      (sgdGain d B ((ps (Fin.last n) : unitInterval) : ℝ) η) < 1 :=
    (min_le_left _ _).trans_lt ((vv_gain_le (d := d) hB0 (hp 0) η).trans_lt
      (vv_gain_max_lt_one (d := d) hB0 (hp 0) (ps 0).2.2))
  have h1 : 0 < 1 - min (sgdGain d B ((ps 0 : unitInterval) : ℝ) η)
      (sgdGain d B ((ps (Fin.last n) : unitInterval) : ℝ) η) := by linarith
  have := Real.log_neg h1 (by linarith)
  linarith

/-- If `L*` is the largest decay rate of `A_SGD(B)`, then `S_SGD(B) = 1/L*`. -/
theorem Sfun_sgd_eq_of_isGreatest (hB : 1 ≤ B) (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    {Ls : ℝ} (hmax : IsGreatest (sgdLminSet d B ν ps) Ls) :
    Sfun d B ν ps sgdClass = 1 / Ls := by
  obtain ⟨⟨η0, ⟨hη0, hst0⟩, hL0⟩, hub⟩ := hmax
  have hLpos : 0 < Ls := by rw [← hL0]; exact sgd_Lmin_pos hB hp hanti hη0 hst0
  unfold Sfun
  refine IsLeast.csInf_eq ⟨⟨(η0, 0), ⟨hη0, rfl, hst0⟩, ?_⟩, ?_⟩
  · have hL0' : Lmin d B ν 0 η0 ps = Ls := hL0
    show 1 / Lmin d B ν 0 η0 ps = 1 / Ls
    rw [hL0']
  · rintro _ ⟨x, ⟨hη, hβ, hst⟩, rfl⟩
    have hx2 : x.2 = 0 := hβ
    show 1 / Ls ≤ 1 / Lmin d B ν x.2 x.1 ps
    rw [hx2] at hst ⊢
    have hpos := sgd_Lmin_pos hB hp hanti hη hst
    have hle : Lmin d B ν 0 x.1 ps ≤ Ls := hub ⟨x.1, ⟨hη, hst⟩, rfl⟩
    exact one_div_le_one_div_of_le hpos hle

/-- v2 `lem:helps-vocab` (v), case 1, in terms of `S_SGD(B)` (v2 `prop:helps-critical`,
`prop:vocab_full`): if `(B-1)(p_1-p_V) ≤ d+2` then `S_SGD(B) = 1/log(1 + B p_V/(d+2-p_V))`. -/
theorem Sfun_sgd_eq_of_le_Bx (hB : 1 ≤ B) (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hcase : ((B : ℝ) - 1) * ((ps 0 : ℝ) - (ps (Fin.last n) : ℝ)) ≤ (d : ℝ) + 2) :
    Sfun d B ν ps sgdClass
      = 1 / Real.log (1 + (B : ℝ) * (ps (Fin.last n) : ℝ)
          / ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))) :=
  Sfun_sgd_eq_of_isGreatest hB hp hanti (helps_vocab_v_case1 hB hp hanti hcase).1

/-- v2 `lem:helps-vocab` (v), case 2, in terms of `S_SGD(B)`: if `d+2 < (B-1)(p_1-p_V)` then
`S_SGD(B) = 1/(-log(1 - 4B(B-1)p_1p_V/D_B²))`. -/
theorem Sfun_sgd_eq_of_gt_Bx (hB : 1 ≤ B) (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hcase : (d : ℝ) + 2 < ((B : ℝ) - 1) * ((ps 0 : ℝ) - (ps (Fin.last n) : ℝ))) :
    Sfun d B ν ps sgdClass
      = 1 / (-Real.log (1 - 4 * (B : ℝ) * ((B : ℝ) - 1) * (ps 0 : ℝ) * (ps (Fin.last n) : ℝ)
          / (DB d B ps) ^ 2)) :=
  Sfun_sgd_eq_of_isGreatest hB hp hanti (helps_vocab_v_case2 hB hp hanti hcase).1

/-! ### (K5) The v2 bundle -/

/-- v2 `prop:helps-critical`, all four parts.  Hypotheses: `κ_V > 16` (used only by the momentum
lower bounds in (ii) and (iii); everything else holds for `κ_V > 1`, see the individual theorems)
and `External.JuryStability` (used only for `S_β ≤ S_β(B)` and `S_β = inf_B S_β(B)` in (iv); the
limit `S_β(B) → S_β` needs no Jury hypothesis).

* (i) the limits `S_O(B) → S_O` with the values and two-sided bounds;
* (ii) `E_SGD = E_SGD(1)`, its bounds, `E_mom ≤ E_SGD` and `E_mom ≥ c_κ (d+2-p_V)/(8p_V)`;
* (iii) `B_SGD`, the ratio, the absolute bounds `B_mom ≤ …` and `B_mom ≥ c_κ(d+2-p_V)/(2√(p_1p_V))`;
* (iv) for every `β ∈ [0,1)`: the limit, `S_β = inf_B S_β(B)`, `ρ_0`, `ρ_β = √β ↔ κ ≤ κ_β`,
  `ρ_β ≥ (√κ-1)/(√κ+1)`, `S_β ≤ A_β`, the lower bound; and Polyak: `ρ_{β_P}` attains the minimum,
  `S_{β_P} = 1/λ_mom` and `inf_β S_β = S_mom`. -/
theorem prop_helps_critical_v2 (jury : External.JuryStability) (hp : ∀ j, 0 < (ps j : ℝ))
    (hanti : Antitone ps) (hκ : 16 < kappaV ps) :
    -- (i)
    (Tendsto (fun B : ℕ => Sfun d B ν ps sgdClass) atTop (𝓝 (Sinf d ν ps sgdClass)) ∧
      Tendsto (fun B : ℕ => Sfun d B ν ps momClass) atTop (𝓝 (Sinf d ν ps momClass)) ∧
      Sinf d ν ps sgdClass = 1 / (2 * Real.log ((kappaV ps + 1) / (kappaV ps - 1))) ∧
      Sinf d ν ps momClass
        = 1 / (2 * Real.log ((Real.sqrt (kappaV ps) + 1) / (Real.sqrt (kappaV ps) - 1))) ∧
      kappaV ps / 4 * (1 - 1 / kappaV ps ^ 2) ≤ Sinf d ν ps sgdClass ∧
      Sinf d ν ps sgdClass ≤ kappaV ps / 4 ∧
      Real.sqrt (kappaV ps) / 4 * (1 - 1 / kappaV ps) ≤ Sinf d ν ps momClass ∧
      Sinf d ν ps momClass ≤ Real.sqrt (kappaV ps) / 4) ∧
    -- (ii)
    (Einf d ν ps sgdClass = Efun d 1 ν ps sgdClass ∧
      Einf d ν ps sgdClass
        = 1 / Real.log (((d : ℝ) + 2) / ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))) ∧
      ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) / (ps (Fin.last n) : ℝ) ≤ Einf d ν ps sgdClass ∧
      Einf d ν ps sgdClass ≤ ((d : ℝ) + 2) / (ps (Fin.last n) : ℝ) ∧
      max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5)
          * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))
          / (8 * (ps (Fin.last n) : ℝ)) ≤ Einf d ν ps momClass ∧
      Einf d ν ps momClass ≤ Einf d ν ps sgdClass) ∧
    -- (iii)
    (4 * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) / (ps 0 : ℝ) ≤ Bcrit d ν ps sgdClass ∧
      Bcrit d ν ps sgdClass
        ≤ kappaV ps ^ 2 / (kappaV ps ^ 2 - 1) * (4 * ((d : ℝ) + 2) / (ps 0 : ℝ)) ∧
      Bcrit d ν ps momClass / Bcrit d ν ps sgdClass
        ≤ kappaV ps * Real.sqrt (kappaV ps) / (kappaV ps - 1) ∧
      Bcrit d ν ps momClass
        ≤ kappaV ps / (kappaV ps - 1)
          * (4 * ((d : ℝ) + 2) / Real.sqrt ((ps 0 : ℝ) * (ps (Fin.last n) : ℝ))) ∧
      max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Real.sqrt (kappaV ps) / 8
          * (1 - 1 / kappaV ps ^ 2) * (1 - (ps (Fin.last n) : ℝ) / ((d : ℝ) + 2))
        ≤ Bcrit d ν ps momClass / Bcrit d ν ps sgdClass ∧
      max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5)
          * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))
          / (2 * Real.sqrt ((ps 0 : ℝ) * (ps (Fin.last n) : ℝ)))
        ≤ Bcrit d ν ps momClass ∧
      Real.sqrt (kappaV ps) / 19
        ≤ max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * Real.sqrt (kappaV ps) / 8
          * (1 - 1 / kappaV ps ^ 2) * (1 - (ps (Fin.last n) : ℝ) / ((d : ℝ) + 2))) ∧
    -- (iv)
    (∀ β : ℝ, 0 ≤ β → β < 1 →
      (Tendsto (fun B : ℕ => Sfun d B ν ps {β}) atTop (𝓝 (Sbeta ps β)) ∧
        (∀ B : ℕ, 1 ≤ B → Sbeta ps β ≤ Sfun d B ν ps {β}) ∧
        Sinf d ν ps {β} = Sbeta ps β ∧
        Sbeta ps β = -1 / (2 * Real.log (rhoBeta ps β)) ∧
        (β = 0 → rhoBeta ps β = (kappaV ps - 1) / (kappaV ps + 1)) ∧
        (0 < β → (rhoBeta ps β = Real.sqrt β ↔ kappaV ps ≤ kappaBeta β)) ∧
        (Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1) ≤ rhoBeta ps β ∧
        (kappaBeta β ≤ kappaV ps → Sbeta ps β ≤ ABeta ps β) ∧
        (DeltaBeta ps β ≤ 1 / 4 →
          1 / 2 * (1 + Real.sqrt (1 - 4 * DeltaBeta ps β)) * ABeta ps β ≤ Sbeta ps β))) ∧
    (rhoBeta ps (betaPolyak ps) = (Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1) ∧
      Sbeta ps (betaPolyak ps) = 1 / lamMom ps ∧
      sInf (Sbeta ps '' Set.Ico (0 : ℝ) 1) = Sinf d ν ps momClass) := by
  have hκ1 : 1 < kappaV ps := by linarith
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := helps_critical_i (d := d) (ν := ν) hp hanti hκ1
  obtain ⟨b1, b2, b3, b4, b5⟩ := helps_critical_ii (d := d) (ν := ν) hp hanti hκ1
  obtain ⟨c1, c2⟩ := helps_critical_iii_sgd (d := d) (ν := ν) hp hanti hκ1
  obtain ⟨c3, c4, c5⟩ := helps_critical_iii_ratio' (d := d) (ν := ν) hp hanti hκ
  refine ⟨⟨Sfun_tendsto_Sinf_sgd hp hanti hκ1, Sfun_tendsto_Sinf_mom hp hanti hκ1,
      a1, a2, a3, a4, a5, a6⟩,
    ⟨b1, b2, b3, b4, helps_critical_ii_mom' hp hκ, b5⟩,
    ⟨c1, c2, c4, Bcrit_mom_le_abs hp hanti hκ1, c3, Bcrit_mom_ge_abs hp hanti hκ, c5⟩,
    fun β hb0 hb1 => ⟨Sfun_fixed_tendsto hp hanti hκ1 hb0 hb1,
      fun B hB => Sfun_fixed_ge jury hp hanti hκ1 hB hb0 hb1,
      Sinf_fixed_eq jury hp hanti hκ1 hb0 hb1, rfl,
      fun h0 => by rw [h0]; exact rhoBeta_zero hκ1,
      fun hb => rhoBeta_eq_sqrt_iff hκ1 hb hb1,
      rhoBeta_ge_polyak hκ1 hb0 hb1,
      fun h => Sbeta_le_A hκ1 hb0 hb1 h,
      fun h => Sbeta_ge hκ1 hb0 hb1 h⟩,
    rhoBeta_polyak hκ1, Sbeta_polyak hκ1, Sbeta_inf_eq_Sinf_mom hp hanti hκ1⟩

end FixedBeta

end

end SparseSGD.Scaling.Helps
