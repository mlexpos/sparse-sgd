import SparseSGD.Scaling.Helps.ExactRate
import SparseSGD.Scaling.Helps.Stability
import SparseSGD.Scaling.Helps.RootPerturbation

/-!
# One learning rate for a vocabulary (momentum-helps appendix)

Paper labels: `lem:helps-vocab` (exact parts (i), (ii), (iii) first two bounds, (iv)(a), (iv)(b),
and the large-batch limit), `rem:vocab` (supporting exact bounds).

v2 additions (end of the file, section `V2`/`V3`; no earlier declaration is changed), for the
merged `lem:helps-vocab` of `paper/appendix/momentum_helps.tex` (draft block
`helps-vocab-v2`):
* (iii) v2, `beta in [0,1)` and the constant `d+2-p_V`: `mom_one_sub_le_rhoMax_v2`,
  `mom_inv_Lmin_ge_first_v2`, `mom_inv_Lmin_ge_second_v2`, and `sgd_inv_Lmin_ge_first_v2`
  (the (ii) bound without the hypothesis `y < 1`);
* (v), `beta = 0`: `etaStar`, `DB`, `sgdGain`, `copy_stable_iff_gain_pos`,
  `rhoMax_sgd_eq_one_sub_min`, `helps_vocab_v_case1`, `helps_vocab_v_case2`,
  `helps_vocab_v_threshold`;
* the bundle `lem_helps_vocab_v2` of (i), (ii), (iii) v2, (iv) and (v) (the co-scaling-ray clause
  of (iii) is `helps_vocab_asymptotic` in `Limits.lean`).

Setup.  `V = n + 1` copies of the least-squares model, `ps : Fin (n+1) → unitInterval` antitone
with every `ps j > 0`; `p1 = ps 0`, `pV = ps (Fin.last n)`, `kappa = p1 / pV`.  Copy `j` has
parameters `copyParams j = params d B (ps j) nu beta eta`; its noise-free version (`u_n`
replaced by `0`) is `copyParams0 j`.  Since `Real.log 0 = 0`, we work with the radii.  We put
`rhoMax = max_j stepRadius (copyParams j)` and `Lmin = -log rhoMax`; this equals
`min_j Lambda_j` whenever all radii are positive, and it avoids `Lambda_j = infinity`.

Every upper bound `Lambda <= X` of the tex is stated as a lower bound on the radius
(`radius >= exp(-X)` or `>= 1 - y`), and the `1/Lmin` bounds are derived only when
`rhoMax in (0,1)`.

Deviations from, and hypotheses added to, the tex statements (details in the docstrings):
* `V >= 2` is not needed by any statement except through `kappa > 1` (which forces `n >= 1`).
* (ii) and (iii): in the tex proof `x_V` lies in `(0,1)` (not `(0,1]`).
* The `if` direction of (i) uses `External.JuryStability` (via St1), as in `Stability.lean`;
  all other parts use only the elementary direction.
* The batch size `B` is positive, and `beta in [0,1)` in (i), `beta = 0` in (ii), (iv)(a),
  `beta in (0,1)` in (iii), (iv)(b).
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD SparseSGD.Probability.LeastSquares MeasureTheory Filter
open scoped Topology

noncomputable section

/-! ### (V0) Scalar lemmas -/

/-- (V0) `-log (1 - y) <= y / (1 - y)` for `y < 1` (the tex states `0 <= y < 1`). -/
theorem neg_log_one_sub_le_vocab {y : ℝ} (hy1 : y < 1) :
    -Real.log (1 - y) ≤ y / (1 - y) := by
  have hpos : 0 < 1 - y := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
  rw [Real.log_inv] at h
  have : (1 - y)⁻¹ - 1 = y / (1 - y) := by field_simp; ring
  linarith

/-- (V0) `log ((1 + x) / (1 - x)) >= 2 x` for `0 <= x < 1`. -/
theorem two_mul_le_log_div {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    2 * x ≤ Real.log ((1 + x) / (1 - x)) := by
  have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have h := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hnn : ∀ k : ℕ, 0 ≤ (2 : ℝ) * (1 / (2 * k + 1)) * x ^ (2 * k + 1) := fun k => by positivity
  have h0 := le_hasSum h 0 (fun k _ => hnn k)
  have e : Real.log ((1 + x) / (1 - x)) = Real.log (1 + x) - Real.log (1 - x) :=
    Real.log_div (by linarith) (by linarith)
  rw [e]
  simpa using h0

/-- (V0) `min eps (a / eps) <= sqrt a` for `eps, a > 0`. -/
theorem min_le_sqrt {eps a : ℝ} (he : 0 < eps) (ha : 0 < a) :
    min eps (a / eps) ≤ Real.sqrt a := by
  by_cases h : eps ≤ Real.sqrt a
  · exact (min_le_left _ _).trans h
  · push Not at h
    refine (min_le_right _ _).trans ?_
    have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    rw [div_le_iff₀ he]
    have : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
    nlinarith

/-- (V0) If `1 - z <= rho < 1` with `0 < z < 1`, then `1/z - 1 <= 1/(-log rho)`. -/
theorem inv_neg_log_ge {rho z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) (h1 : 1 - z ≤ rho) (h2 : rho < 1) :
    1 / z - 1 ≤ 1 / (-Real.log rho) := by
  have hr0 : 0 < rho := by linarith
  have hL : 0 < -Real.log rho := by
    have := Real.log_neg hr0 h2
    linarith
  have hle : -Real.log rho ≤ z / (1 - z) := by
    have := Real.log_le_log (by linarith) h1
    have h3 := neg_log_one_sub_le_vocab hz1
    linarith
  have hzz : 0 < z / (1 - z) := div_pos hz0 (by linarith)
  have := one_div_le_one_div_of_le hL hle
  have e : 1 / (z / (1 - z)) = 1 / z - 1 := by field_simp
  rw [e] at this
  exact this

/-! ### Copies, radii -/

/-- Copy `j` of the LS model: `params d B (ps j) nu beta eta` (`lem:helps-vocab` setup). -/
def copyParams {n : ℕ} (d B : ℕ) (ν : Measure ℝ) (beta eta : ℝ)
    (ps : Fin (n + 1) → unitInterval) (j : Fin (n + 1)) : Params :=
  params d B (ps j) ν beta eta

/-- Copy `j` with `u_n` replaced by `0` (`lem:helps-vocab` (iv)). -/
def copyParams0 {n : ℕ} (beta eta : ℝ) (ps : Fin (n + 1) → unitInterval) (j : Fin (n + 1)) :
    Params :=
  ⟨beta, eta * (1 - beta) * (ps j : ℝ), 0, 0⟩

/-- The slowest-copy radius `max_j rho(L_j)`. -/
def rhoMax {n : ℕ} (d B : ℕ) (ν : Measure ℝ) (beta eta : ℝ)
    (ps : Fin (n + 1) → unitInterval) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => stepRadius (copyParams d B ν beta eta ps j))

/-- The slowest-copy radius with `u_n` replaced by `0`. -/
def rhoMax0 {n : ℕ} (beta eta : ℝ) (ps : Fin (n + 1) → unitInterval) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => stepRadius (copyParams0 beta eta ps j))

/-- `Lmin = -log rhoMax`; equals `min_j Lambda_j` when the radii are positive. -/
def Lmin {n : ℕ} (d B : ℕ) (ν : Measure ℝ) (beta eta : ℝ)
    (ps : Fin (n + 1) → unitInterval) : ℝ :=
  -Real.log (rhoMax d B ν beta eta ps)

/-- `Lmin0 = -log rhoMax0`. -/
def Lmin0 {n : ℕ} (beta eta : ℝ) (ps : Fin (n + 1) → unitInterval) : ℝ :=
  -Real.log (rhoMax0 beta eta ps)

/-- The condition number `kappa_V = p_1 / p_V`. -/
def kappaV {n : ℕ} (ps : Fin (n + 1) → unitInterval) : ℝ :=
  (ps 0 : ℝ) / (ps (Fin.last n) : ℝ)

section Basic

variable {n : ℕ} {d B : ℕ} {ν : Measure ℝ} {beta eta : ℝ} {ps : Fin (n + 1) → unitInterval}

theorem copyParams_beta (j : Fin (n + 1)) : (copyParams d B ν beta eta ps j).beta = beta := rfl

theorem copyParams_w (j : Fin (n + 1)) :
    (copyParams d B ν beta eta ps j).w = eta * (1 - beta) * (ps j : ℝ) := rfl

theorem copyParams_noise (hp : ∀ j, 0 < (ps j : ℝ)) (j : Fin (n + 1)) :
    (copyParams d B ν beta eta ps j).noise = eta * (((d : ℝ) + 2 - (ps j : ℝ)) / (2 * B)) := by
  have hp' : (ps j : ℝ) ≠ 0 := (hp j).ne'
  simp only [copyParams, params, oracleParams, vinc]
  by_cases hB : (B : ℝ) = 0
  · simp [hB]
  · field_simp

theorem copyParams_noise_nonneg (hp : ∀ j, 0 < (ps j : ℝ)) (hη : 0 ≤ eta) (j : Fin (n + 1)) :
    0 ≤ (copyParams d B ν beta eta ps j).noise := by
  rw [copyParams_noise hp]
  have h1 : (ps j : ℝ) ≤ 1 := (ps j).2.2
  have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have : 0 ≤ ((d : ℝ) + 2 - (ps j : ℝ)) / (2 * B) := div_nonneg (by linarith) (by positivity)
  positivity

theorem stepRadius_eq_noise_form (p : Params) :
    stepRadius p = stepRadius ⟨p.beta, p.w, p.noise, 0⟩ := rfl

theorem le_rhoMax (j : Fin (n + 1)) :
    stepRadius (copyParams d B ν beta eta ps j) ≤ rhoMax d B ν beta eta ps :=
  Finset.le_sup' (fun j => stepRadius (copyParams d B ν beta eta ps j)) (Finset.mem_univ j)

theorem le_rhoMax0 (j : Fin (n + 1)) :
    stepRadius (copyParams0 beta eta ps j) ≤ rhoMax0 beta eta ps :=
  Finset.le_sup' (fun j => stepRadius (copyParams0 beta eta ps j)) (Finset.mem_univ j)

theorem rhoMax_lt_one_iff :
    rhoMax d B ν beta eta ps < 1 ↔ ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1 := by
  unfold rhoMax
  rw [Finset.sup'_lt_iff]
  simp

theorem rhoMax0_lt_one_iff :
    rhoMax0 beta eta ps < 1 ↔ ∀ j, stepRadius (copyParams0 beta eta ps j) < 1 := by
  unfold rhoMax0
  rw [Finset.sup'_lt_iff]
  simp

theorem ps_le_first (hanti : Antitone ps) (j : Fin (n + 1)) : (ps j : ℝ) ≤ (ps 0 : ℝ) :=
  Subtype.coe_le_coe.2 (hanti (Fin.zero_le j))

theorem last_le_ps (hanti : Antitone ps) (j : Fin (n + 1)) :
    (ps (Fin.last n) : ℝ) ≤ (ps j : ℝ) :=
  Subtype.coe_le_coe.2 (hanti (Fin.le_last j))

/-- Easy direction of stability for a copy (`S7`): a stable copy has `eta * (1/eta_+) < 1`. -/
theorem copy_load_lt_one_of_stable (hp : ∀ j, 0 < (ps j : ℝ)) (hb0 : 0 ≤ beta)
    (hb1 : beta < 1) (hη : 0 < eta) {j : Fin (n + 1)}
    (h : stepRadius (copyParams d B ν beta eta ps j) < 1) :
    eta * inverseCriticalRate d B (ps j) beta < 1 := by
  by_contra hcon
  push Not at hcon
  have hw : 0 < (copyParams d B ν beta eta ps j).w := by
    rw [copyParams_w]
    have : 0 < 1 - beta := by linarith
    have := hp j
    positivity
  have hload : (copyParams d B ν beta eta ps j).totalLoad = eta * inverseCriticalRate d B (ps j) beta :=
    params_totalLoad d B (ps j) (hp j).ne' ν beta eta
  have := one_le_stepRadius_of_one_le_totalLoad (copyParams d B ν beta eta ps j) hw
    (by rw [copyParams_beta]; exact hb1) (by rw [copyParams_beta]; linarith)
    (by rw [hload]; exact hcon)
  linarith


/-! ### (V1) Part (i): the stability range -/

/-- `1/eta_+(p)` is affine in `p` (`lem:helps-vocab` (i)): the slope is
`(1-beta)/(2(1+beta)) - 1/(2B)`. -/
theorem inverseCriticalRate_affine (d B : ℕ) (p : unitInterval) (beta : ℝ) :
    inverseCriticalRate d B p beta =
      ((d : ℝ) + 2) / (2 * B) + (p : ℝ) * ((1 - beta) / (2 * (1 + beta)) - 1 / (2 * B)) := by
  unfold inverseCriticalRate
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem eta_lt_critical_iff (hB : 0 < B) (p : unitInterval) (hb0 : 0 ≤ beta) (hb1 : beta < 1) :
    eta < criticalRate d B p beta ↔ eta * inverseCriticalRate d B p beta < 1 := by
  rw [criticalRate, ← one_div]
  exact lt_div_iff₀ (inverseCriticalRate_pos d B hB p beta hb0 hb1)

/-- A copy is stable iff `eta < eta_+(p_j)` (`lem:helps-vocab` (i), via St1). -/
theorem copy_stable_iff_lt_critical (jury : External.JuryStability) (hB : 0 < B)
    (hp : ∀ j, 0 < (ps j : ℝ)) (hb0 : 0 ≤ beta) (hb1 : beta < 1) (hη : 0 < eta)
    (j : Fin (n + 1)) :
    stepRadius (copyParams d B ν beta eta ps j) < 1 ↔ eta < criticalRate d B (ps j) beta := by
  have hw : 0 < (copyParams d B ν beta eta ps j).w := by
    rw [copyParams_w]
    have : 0 < 1 - beta := by linarith
    have := hp j
    positivity
  rw [stepRadius_lt_one_iff jury _ hb0 hb1 hw (copyParams_noise_nonneg hp hη.le j)]
  exact totalLoad_lt_one_iff_eta_lt_critical d B hB (ps j) (hp j) ν beta eta hb0 hb1

/-- (V1) `lem:helps-vocab` (i), first claim: every copy is stable iff
`eta < min (eta_+(p_1)) (eta_+(p_V))`.  Uses `External.JuryStability` through St1.
Hypotheses added: `0 < eta`, `0 < B`, `0 <= beta < 1`. -/
theorem all_stable_iff_lt_min (jury : External.JuryStability) (hB : 0 < B)
    (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (hη : 0 < eta) :
    (∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) ↔
      eta < min (criticalRate d B (ps 0) beta) (criticalRate d B (ps (Fin.last n)) beta) := by
  simp only [copy_stable_iff_lt_critical jury hB hp hb0 hb1 hη]
  rw [lt_min_iff]
  constructor
  · intro h
    exact ⟨h 0, h (Fin.last n)⟩
  · rintro ⟨h0, hl⟩ j
    rw [eta_lt_critical_iff hB _ hb0 hb1] at h0 hl ⊢
    have hη0 : 0 ≤ eta := hη.le
    set s : ℝ := (1 - beta) / (2 * (1 + beta)) - 1 / (2 * B) with hs
    have a0 := inverseCriticalRate_affine d B (ps 0) beta
    have al := inverseCriticalRate_affine d B (ps (Fin.last n)) beta
    have aj := inverseCriticalRate_affine d B (ps j) beta
    have hj1 := ps_le_first hanti j
    have hj2 := last_le_ps hanti j
    rcases le_total 0 s with hs0 | hs0
    · have : inverseCriticalRate d B (ps j) beta ≤ inverseCriticalRate d B (ps 0) beta := by
        rw [aj, a0]; nlinarith
      nlinarith
    · have : inverseCriticalRate d B (ps j) beta ≤ inverseCriticalRate d B (ps (Fin.last n)) beta := by
        rw [aj, al]; nlinarith
      nlinarith

/-- (V1) `lem:helps-vocab` (i), second claim: if `B > (1+beta)/(1-beta)` then the minimum is
`eta_+(p_1)`. -/
theorem min_critical_eq_first (hB : 0 < B) (hanti : Antitone ps) (hb0 : 0 ≤ beta)
    (hb1 : beta < 1) (hBlarge : (1 + beta) / (1 - beta) < (B : ℝ)) :
    min (criticalRate d B (ps 0) beta) (criticalRate d B (ps (Fin.last n)) beta)
      = criticalRate d B (ps 0) beta := by
  have h1 : 0 < 1 - beta := by linarith
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hBl : 1 + beta < (B : ℝ) * (1 - beta) := by
    rwa [div_lt_iff₀ h1] at hBlarge
  have hs : 0 < (1 - beta) / (2 * (1 + beta)) - 1 / (2 * B) := by
    have : (1 - beta) / (2 * (1 + beta)) - 1 / (2 * B)
        = ((1 - beta) * B - (1 + beta)) / (2 * (1 + beta) * B) := by
      field_simp
    rw [this]
    apply div_pos (by linarith) (by positivity)
  have hle : inverseCriticalRate d B (ps (Fin.last n)) beta ≤ inverseCriticalRate d B (ps 0) beta := by
    rw [inverseCriticalRate_affine, inverseCriticalRate_affine]
    have : (ps (Fin.last n) : ℝ) ≤ (ps 0 : ℝ) := last_le_ps hanti 0
    nlinarith
  apply min_eq_left
  unfold criticalRate
  exact inv_anti₀ (inverseCriticalRate_pos d B hB _ beta hb0 hb1) hle

/-! ### Auxiliary bounds on `1/eta_+` -/

theorem noise_part_le_inverseCriticalRate (p : unitInterval) (hb0 : 0 ≤ beta)
    (hb1 : beta < 1) :
    ((d : ℝ) + 2 - p) / (2 * B) ≤ inverseCriticalRate d B p beta := by
  unfold inverseCriticalRate
  have : 0 ≤ (p : ℝ) / 2 * ((1 - beta) / (1 + beta)) := by
    have := p.2.1
    have : 0 < 1 - beta := by linarith
    positivity
  linarith

theorem noise_part_pos (hB : 0 < B) (p : unitInterval) :
    0 < ((d : ℝ) + 2 - p) / (2 * B) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have h1 : (p : ℝ) ≤ 1 := p.2.2
  have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  apply div_pos (by linarith) (by positivity)

theorem half_lt_inverseCriticalRate_zero (hB : 0 < B) (p : unitInterval) :
    (p : ℝ) / 2 < inverseCriticalRate d B p 0 := by
  have := noise_part_pos (d := d) hB p
  unfold inverseCriticalRate
  simp only [sub_zero, add_zero, div_one, mul_one]
  linarith

/-! ### (V2) Part (ii): SGD -/

/-- For `beta = 0` and a stable copy `j`, the radius is `1 - x` with
`0 < x <= min (p_j eta_+(p_j) / 2) (2 eta p_j)` (`lem:helps-sgd`; `lem:helps-vocab` (ii)). -/
theorem sgd_radius_eq (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hη : 0 < eta) (hβ : beta = 0)
    {j : Fin (n + 1)} (hstab : stepRadius (copyParams d B ν beta eta ps j) < 1) :
    ∃ x : ℝ, stepRadius (copyParams d B ν beta eta ps j) = 1 - x ∧ 0 < x ∧
      x ≤ (ps j : ℝ) * criticalRate d B (ps j) 0 / 2 ∧ x ≤ 2 * eta * (ps j : ℝ) := by
  subst hβ
  have hload := copy_load_lt_one_of_stable hp le_rfl zero_lt_one hη hstab
  set p := copyParams d B ν 0 eta ps j with hpdef
  have hb : p.beta = 0 := rfl
  have hw : 0 < p.w := by
    have := hp j
    show 0 < eta * (1 - 0) * (ps j : ℝ)
    simp only [sub_zero, mul_one]; positivity
  have hun : 0 ≤ p.noise := copyParams_noise_nonneg hp hη.le j
  have hu : p.totalLoad < 1 := by
    have : p.totalLoad = eta * inverseCriticalRate d B (ps j) 0 :=
      params_totalLoad d B (ps j) (hp j).ne' ν 0 eta
    rw [this]; exact hload
  obtain ⟨h0, h1, _⟩ := sgd_coeff_bounds p hb hw hun hu
  refine ⟨2 * p.w * (1 - p.totalLoad), ?_, by linarith, ?_, ?_⟩
  · rw [stepRadius_beta_zero p hb, abs_of_nonneg h0]
  · have hcrit : eta < criticalRate d B (ps j) 0 :=
      (totalLoad_lt_one_iff_eta_lt_critical d B hB (ps j) (hp j) ν 0 eta le_rfl zero_lt_one).1 hu
    have hG := (ls_beta_zero_sup d B hB (ps j) (hp j) ν).1.2 ⟨eta, ⟨hη, hcrit⟩, rfl⟩
    exact hG
  · have hcurv : 0 ≤ p.curvature := by
      unfold Params.curvature
      exact div_nonneg hw.le (by rw [hb]; norm_num)
    have : 0 ≤ p.totalLoad := by unfold Params.totalLoad; linarith
    have hwe : p.w = eta * (ps j : ℝ) := by
      show eta * (1 - 0) * (ps j : ℝ) = _
      ring
    rw [hwe] at *
    nlinarith [mul_pos hη (hp j)]

theorem half_mul_crit_le (hB : 0 < B) (p : unitInterval) (hp : 0 < (p : ℝ)) :
    (p : ℝ) * criticalRate d B p 0 / 2 ≤ B * p / ((d : ℝ) + 2 - p) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hq := noise_part_pos (d := d) hB p
  have hinv := noise_part_le_inverseCriticalRate (d := d) (B := B) p (le_refl (0 : ℝ)) zero_lt_one
  have hcr : criticalRate d B p 0 ≤ (((d : ℝ) + 2 - p) / (2 * B))⁻¹ := by
    unfold criticalRate
    exact inv_anti₀ hq hinv
  have hd : 0 < (d : ℝ) + 2 - p := by
    have h1 : (p : ℝ) ≤ 1 := p.2.2
    have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have e : (p : ℝ) * (((d : ℝ) + 2 - p) / (2 * B))⁻¹ / 2 = B * p / ((d : ℝ) + 2 - p) := by
    field_simp
  rw [← e]
  have := mul_le_mul_of_nonneg_left hcr hp.le
  linarith

/-- (V2) `lem:helps-vocab` (ii), first bound, radius form: for `beta = 0` and all copies stable,
`y := B p_V / (d+2-p_V) < 1` gives `1 - y <= rhoMax`.  (The tex proof's `x_V in (0,1]` is
`x_V in (0,1)`.) -/
theorem sgd_one_sub_le_rhoMax (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hη : 0 < eta)
    (hβ : beta = 0) (hstab : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) :
    1 - (B : ℝ) * (ps (Fin.last n) : ℝ) / ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) ≤
      rhoMax d B ν beta eta ps := by
  obtain ⟨x, hx, _, hx2, _⟩ := sgd_radius_eq hB hp hη hβ (hstab (Fin.last n))
  have hy := half_mul_crit_le (d := d) hB (ps (Fin.last n)) (hp _)
  have := le_rhoMax (d := d) (B := B) (ν := ν) (beta := beta) (eta := eta) (ps := ps) (Fin.last n)
  linarith

/-- (V2) `lem:helps-vocab` (ii), first bound: `1/y - 1 <= 1/Lmin`, that is
`(d+2-p_V)/(B p_V) - 1 <= 1/Lmin`, when `y := B p_V/(d+2-p_V) < 1`. -/
theorem sgd_inv_Lmin_ge_first (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hη : 0 < eta)
    (hβ : beta = 0) (hstab : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1)
    (hy : (B : ℝ) * (ps (Fin.last n) : ℝ) / ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) < 1) :
    1 / ((B : ℝ) * (ps (Fin.last n) : ℝ) / ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))) - 1 ≤
      1 / Lmin d B ν beta eta ps := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hq := (noise_part_pos (d := d) hB (ps (Fin.last n)))
  have hd : 0 < (d : ℝ) + 2 - (ps (Fin.last n) : ℝ) := by
    have := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * B)).1 hq
    exact this
  have hy0 : 0 < (B : ℝ) * (ps (Fin.last n) : ℝ) / ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) :=
    div_pos (mul_pos hB' (hp _)) hd
  exact inv_neg_log_ge hy0 hy (sgd_one_sub_le_rhoMax hB hp hη hβ hstab)
    (rhoMax_lt_one_iff.2 hstab)

/-- (V2) `lem:helps-vocab` (ii), second bound, radius form: for `beta = 0`, all copies stable and
`kappa > 4`, `1 - 4/kappa <= rhoMax`. -/
theorem sgd_one_sub_four_div_le_rhoMax (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hη : 0 < eta)
    (hβ : beta = 0) (hstab : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) :
    1 - 4 / kappaV ps ≤ rhoMax d B ν beta eta ps := by
  obtain ⟨x, hx, _, _, hx4⟩ := sgd_radius_eq hB hp hη hβ (hstab (Fin.last n))
  have hl := copy_load_lt_one_of_stable hp (by rw [hβ]) (by rw [hβ]; norm_num) hη (hstab 0)
  have hhalf : (ps 0 : ℝ) / 2 < inverseCriticalRate d B (ps 0) beta := by
    rw [hβ]; exact half_lt_inverseCriticalRate_zero hB _
  have h2 : eta * (ps 0 : ℝ) < 2 := by nlinarith
  have hk : kappaV ps * (ps (Fin.last n) : ℝ) = (ps 0 : ℝ) :=
    div_mul_cancel₀ _ (hp _).ne'
  have hk0 : 0 < kappaV ps := div_pos (hp 0) (hp _)
  have h3 : 2 * eta * (ps (Fin.last n) : ℝ) < 4 / kappaV ps := by
    rw [lt_div_iff₀ hk0]
    nlinarith
  have := le_rhoMax (d := d) (B := B) (ν := ν) (beta := beta) (eta := eta) (ps := ps) (Fin.last n)
  linarith

/-- (V2) `lem:helps-vocab` (ii), second bound: `kappa/4 - 1 <= 1/Lmin` for `kappa > 4`. -/
theorem sgd_inv_Lmin_ge_second (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hη : 0 < eta)
    (hβ : beta = 0) (hstab : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1)
    (hκ : 4 < kappaV ps) :
    kappaV ps / 4 - 1 ≤ 1 / Lmin d B ν beta eta ps := by
  have hk0 : 0 < kappaV ps := by linarith
  have hz0 : 0 < 4 / kappaV ps := by positivity
  have hz1 : 4 / kappaV ps < 1 := by rw [div_lt_one hk0]; exact hκ
  have := inv_neg_log_ge hz0 hz1 (sgd_one_sub_four_div_le_rhoMax hB hp hη hβ hstab)
    (rhoMax_lt_one_iff.2 hstab)
  have e : 1 / (4 / kappaV ps) - 1 = kappaV ps / 4 - 1 := by rw [one_div_div]
  rw [e] at this
  exact this

/-! ### (V3) Part (iii): momentum -/

/-- Radius lower bounds for a copy with `0 < beta < 1` (E1, E6): `beta <= radius` and, if
`4 eta p_j < 1`, `1 - 4 eta p_j <= radius`. -/
theorem momentum_radius_lower (hp : ∀ j, 0 < (ps j : ℝ)) (hb0 : 0 < beta) (hb1 : beta < 1)
    (hη : 0 < eta) (j : Fin (n + 1)) :
    beta ≤ stepRadius (copyParams d B ν beta eta ps j) ∧
      (4 * eta * (ps j : ℝ) < 1 →
        1 - 4 * eta * (ps j : ℝ) ≤ stepRadius (copyParams d B ν beta eta ps j)) := by
  have he : 0 < 1 - beta := by linarith
  have hw : 0 < (copyParams d B ν beta eta ps j).w := by
    rw [copyParams_w]; have := hp j; positivity
  have hun := copyParams_noise_nonneg (d := d) (B := B) (ν := ν) (beta := beta) hp hη.le j
  refine ⟨beta_le_stepRadius _ hb0.le hb1.le hw.le hun, fun h4 => ?_⟩
  have hDelta : (copyParams d B ν beta eta ps j).w
      = (copyParams d B ν beta eta ps j).eps ^ 2 * (eta * (ps j : ℝ) / (1 - beta)) := by
    show eta * (1 - beta) * (ps j : ℝ) = (1 - beta) ^ 2 * (eta * (ps j : ℝ) / (1 - beta))
    field_simp
  have e : 4 * (copyParams d B ν beta eta ps j).eps * (eta * (ps j : ℝ) / (1 - beta))
      = 4 * eta * (ps j : ℝ) := by
    show 4 * (1 - beta) * (eta * (ps j : ℝ) / (1 - beta)) = _
    field_simp
  have := one_sub_four_le_stepRadius (copyParams d B ν beta eta ps j) (eta * (ps j : ℝ) / (1 - beta))
    hb0 hb1 hw hun hDelta (by rw [e]; exact h4)
  rwa [e] at this

/-- (V3) `lem:helps-vocab` (iii), first bound, radius form: for `0 < beta < 1` and all copies
stable, with `y := 8 B p_V/(d+1) < 1`, `1 - y <= rhoMax`. -/
theorem mom_one_sub_le_rhoMax (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hη : 0 < eta)
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (hstab : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1)
    (hy : 8 * (B : ℝ) * (ps (Fin.last n) : ℝ) / ((d : ℝ) + 1) < 1) :
    1 - 8 * (B : ℝ) * (ps (Fin.last n) : ℝ) / ((d : ℝ) + 1) ≤ rhoMax d B ν beta eta ps := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hl := copy_load_lt_one_of_stable hp hb0.le hb1 hη (hstab (Fin.last n))
  have hq := noise_part_le_inverseCriticalRate (d := d) (B := B) (ps (Fin.last n)) hb0.le hb1
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hpV1 : (ps (Fin.last n) : ℝ) ≤ 1 := (ps (Fin.last n)).2.2
  have hq2 : ((d : ℝ) + 1) / (2 * B) ≤ ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) / (2 * B) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h1 : eta * (((d : ℝ) + 1) / (2 * B)) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hq2.trans hq) hη.le) hl
  have h2 : eta * ((d : ℝ) + 1) < 2 * B := by
    have : eta * (((d : ℝ) + 1) / (2 * B)) = eta * ((d : ℝ) + 1) / (2 * B) := by ring
    rw [this, div_lt_one (by positivity)] at h1
    exact h1
  have h3 : 4 * eta * (ps (Fin.last n) : ℝ) < 8 * (B : ℝ) * (ps (Fin.last n) : ℝ) / ((d : ℝ) + 1) := by
    rw [lt_div_iff₀ hd1]
    nlinarith [hp (Fin.last n)]
  have hlow := (momentum_radius_lower (d := d) (B := B) (ν := ν) hp hb0 hb1 hη (Fin.last n)).2
    (by linarith)
  have := le_rhoMax (d := d) (B := B) (ν := ν) (beta := beta) (eta := eta) (ps := ps) (Fin.last n)
  linarith

/-- (V3) `lem:helps-vocab` (iii), first bound: `1/y - 1 <= 1/Lmin`, with
`y := 8 B p_V/(d+1) < 1`. -/
theorem mom_inv_Lmin_ge_first (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hη : 0 < eta)
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (hstab : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1)
    (hy : 8 * (B : ℝ) * (ps (Fin.last n) : ℝ) / ((d : ℝ) + 1) < 1) :
    1 / (8 * (B : ℝ) * (ps (Fin.last n) : ℝ) / ((d : ℝ) + 1)) - 1 ≤
      1 / Lmin d B ν beta eta ps := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hy0 : 0 < 8 * (B : ℝ) * (ps (Fin.last n) : ℝ) / ((d : ℝ) + 1) :=
    div_pos (by have := hp (Fin.last n); positivity) (by positivity)
  exact inv_neg_log_ge hy0 hy (mom_one_sub_le_rhoMax hB hp hη hb0 hb1 hstab hy)
    (rhoMax_lt_one_iff.2 hstab)

/-- (V3) `lem:helps-vocab` (iii), second bound, radius form: for `0 < beta < 1`, all copies
stable and `kappa > 16`, `1 - 4/sqrt kappa <= rhoMax`. -/
theorem mom_one_sub_four_div_sqrt_le_rhoMax (hp : ∀ j, 0 < (ps j : ℝ))
    (hη : 0 < eta) (hb0 : 0 < beta) (hb1 : beta < 1)
    (hstab : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) (hκ : 16 < kappaV ps) :
    1 - 4 / Real.sqrt (kappaV ps) ≤ rhoMax d B ν beta eta ps := by
  have hk0 : 0 < kappaV ps := by linarith
  have hs0 : 0 < Real.sqrt (kappaV ps) := Real.sqrt_pos.2 hk0
  have hs4 : 4 < Real.sqrt (kappaV ps) := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) hκ
  have he0 : 0 < 1 - beta := by linarith
  -- stability of copy 1 gives `eta p_1 (1 - beta) < 2 (1 + beta)`
  have hl := copy_load_lt_one_of_stable hp hb0.le hb1 hη (hstab 0)
  have hceil : eta * (1 - beta) * (ps 0 : ℝ) < 2 * (1 + beta) := by
    have hcurv : (copyParams d B ν beta eta ps 0).curvature < 1 := by
      have h := copyParams_noise_nonneg (d := d) (B := B) (ν := ν) (beta := beta) hp hη.le 0
      have hload : (copyParams d B ν beta eta ps 0).totalLoad = eta * inverseCriticalRate d B (ps 0) beta :=
        params_totalLoad d B (ps 0) (hp 0).ne' ν beta eta
      unfold Params.totalLoad at hload
      linarith
    unfold Params.curvature at hcurv
    rw [div_lt_one (by show 0 < 2 * (1 + beta); linarith)] at hcurv
    exact hcurv
  have hk : kappaV ps * (ps (Fin.last n) : ℝ) = (ps 0 : ℝ) := div_mul_cancel₀ _ (hp _).ne'
  -- `4 eta p_V < 16/(eps kappa)`
  have h16 : 4 * eta * (ps (Fin.last n) : ℝ) < (16 / kappaV ps) / (1 - beta) := by
    rw [lt_div_iff₀ he0, lt_div_iff₀ hk0]
    have e : 4 * eta * (ps (Fin.last n) : ℝ) * (1 - beta) * kappaV ps
        = 4 * (eta * (1 - beta) * (ps 0 : ℝ)) := by rw [← hk]; ring
    rw [e]
    linarith
  have hmin := min_le_sqrt he0 (div_pos (by norm_num : (0:ℝ) < 16) hk0)
  have hsq : Real.sqrt (16 / kappaV ps) = 4 / Real.sqrt (kappaV ps) := by
    rw [Real.sqrt_div (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [hsq] at hmin
  have hlow := momentum_radius_lower (d := d) (B := B) (ν := ν) (ps := ps) hp hb0 hb1 hη (Fin.last n)
  have := le_rhoMax (d := d) (B := B) (ν := ν) (beta := beta) (eta := eta) (ps := ps) (Fin.last n)
  have h4s : 4 / Real.sqrt (kappaV ps) < 1 := by rw [div_lt_one hs0]; exact hs4
  rcases le_total (1 - beta) (16 / kappaV ps / (1 - beta)) with hc | hc
  · have : 1 - beta ≤ 4 / Real.sqrt (kappaV ps) := (min_eq_left hc ▸ hmin)
    linarith [hlow.1]
  · have h' : 16 / kappaV ps / (1 - beta) ≤ 4 / Real.sqrt (kappaV ps) := (min_eq_right hc ▸ hmin)
    have h4 : 4 * eta * (ps (Fin.last n) : ℝ) < 1 := by linarith
    linarith [hlow.2 h4]

/-- (V3) `lem:helps-vocab` (iii), second bound: `sqrt kappa/4 - 1 <= 1/Lmin` for `kappa > 16`. -/
theorem mom_inv_Lmin_ge_second (hp : ∀ j, 0 < (ps j : ℝ))
    (hη : 0 < eta) (hb0 : 0 < beta) (hb1 : beta < 1)
    (hstab : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) (hκ : 16 < kappaV ps) :
    Real.sqrt (kappaV ps) / 4 - 1 ≤ 1 / Lmin d B ν beta eta ps := by
  have hk0 : 0 < kappaV ps := by linarith
  have hs0 : 0 < Real.sqrt (kappaV ps) := Real.sqrt_pos.2 hk0
  have hs4 : 4 < Real.sqrt (kappaV ps) := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) hκ
  have hz0 : 0 < 4 / Real.sqrt (kappaV ps) := by positivity
  have hz1 : 4 / Real.sqrt (kappaV ps) < 1 := by rw [div_lt_one hs0]; exact hs4
  have := inv_neg_log_ge hz0 hz1
    (mom_one_sub_four_div_sqrt_le_rhoMax hp hη hb0 hb1 hstab hκ) (rhoMax_lt_one_iff.2 hstab)
  have e : 1 / (4 / Real.sqrt (kappaV ps)) - 1 = Real.sqrt (kappaV ps) / 4 - 1 := by
    rw [one_div_div]
  rw [e] at this
  exact this

/-! ### (V4) Part (iv)(a): SGD without noise -/

/-- Noise-free SGD copy: `rho = (1 - w)^2` with `w = eta p_j` (`lem:helps-sgd`, `lem:helps-vocab`
(iv)(a)). -/
theorem copy0_radius_beta_zero (hβ : beta = 0) (j : Fin (n + 1)) :
    stepRadius (copyParams0 beta eta ps j) = (1 - eta * (ps j : ℝ)) ^ 2 := by
  subst hβ
  set p := copyParams0 0 eta ps j with hpdef
  have hb : p.beta = 0 := rfl
  have hn : p.noise = 0 := rfl
  have hw : p.w = eta * (ps j : ℝ) := by
    show eta * (1 - 0) * (ps j : ℝ) = _
    ring
  rw [stepRadius_beta_zero p hb, totalLoad_beta_zero p hb, hn, hw]
  have : 1 - 2 * (eta * (ps j : ℝ)) * (1 - (0 + eta * (ps j : ℝ) / 2))
      = (1 - eta * (ps j : ℝ)) ^ 2 := by ring
  rw [this, abs_of_nonneg (sq_nonneg _)]

/-- (V4) `lem:helps-vocab` (iv)(a), radius form: for `beta = 0`, `eta = 2/(p_1 + p_V)` and
no noise, `rhoMax0 = ((kappa-1)/(kappa+1))^2`, and every copy has radius `< 1`.  Needs only
`p_V > 0`; the tex hypothesis `kappa > 1` is used only for `Lmin0`. -/
theorem sgd_rhoMax0 (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hβ : beta = 0)
    (hη : eta = 2 / ((ps 0 : ℝ) + (ps (Fin.last n) : ℝ))) :
    rhoMax0 beta eta ps = ((kappaV ps - 1) / (kappaV ps + 1)) ^ 2 ∧
      ∀ j, stepRadius (copyParams0 beta eta ps j) < 1 := by
  have h0 := hp 0
  have hV := hp (Fin.last n)
  have hs : 0 < (ps 0 : ℝ) + (ps (Fin.last n) : ℝ) := by linarith
  have hq : (kappaV ps - 1) / (kappaV ps + 1)
      = ((ps 0 : ℝ) - ps (Fin.last n)) / ((ps 0 : ℝ) + ps (Fin.last n)) := by
    unfold kappaV
    field_simp
  set q : ℝ := ((ps 0 : ℝ) - ps (Fin.last n)) / ((ps 0 : ℝ) + ps (Fin.last n)) with hqdef
  have hq1 : q < 1 := by
    rw [hqdef, div_lt_one hs]; linarith
  have hq0 : 0 ≤ q := by
    rw [hqdef]
    exact div_nonneg (by linarith [last_le_ps hanti 0]) hs.le
  have hrad : ∀ j, stepRadius (copyParams0 beta eta ps j) ≤ q ^ 2 := by
    intro j
    rw [copy0_radius_beta_zero hβ, hη]
    have e : 1 - 2 / ((ps 0 : ℝ) + ps (Fin.last n)) * (ps j : ℝ)
        = ((ps 0 : ℝ) + ps (Fin.last n) - 2 * (ps j : ℝ)) / ((ps 0 : ℝ) + ps (Fin.last n)) := by
      field_simp
    rw [e, div_pow]
    have hj1 := ps_le_first hanti j
    have hj2 := last_le_ps hanti j
    have habs : ((ps 0 : ℝ) + ps (Fin.last n) - 2 * (ps j : ℝ)) ^ 2
        ≤ ((ps 0 : ℝ) - ps (Fin.last n)) ^ 2 := by
      apply sq_le_sq'  <;> nlinarith
    rw [hqdef, div_pow]
    exact div_le_div_of_nonneg_right habs (by positivity)
  have hattain : stepRadius (copyParams0 beta eta ps 0) = q ^ 2 := by
    rw [copy0_radius_beta_zero hβ, hη, hqdef]
    have e : 1 - 2 / ((ps 0 : ℝ) + ps (Fin.last n)) * (ps 0 : ℝ)
        = -(((ps 0 : ℝ) - ps (Fin.last n)) / ((ps 0 : ℝ) + ps (Fin.last n))) := by
      field_simp
      ring
    rw [e, neg_sq]
  refine ⟨?_, fun j => lt_of_le_of_lt (hrad j) (by nlinarith)⟩
  rw [hq]
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun j _ => hrad j)
  · rw [← hattain]; exact le_rhoMax0 0

/-- (V4) `lem:helps-vocab` (iv)(a): `Lmin0 = 2 log ((kappa+1)/(kappa-1))` and
`1/Lmin0 <= kappa/4`, for `kappa > 1`. -/
theorem sgd_Lmin0 (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hβ : beta = 0)
    (hη : eta = 2 / ((ps 0 : ℝ) + (ps (Fin.last n) : ℝ))) (hκ : 1 < kappaV ps) :
    Lmin0 beta eta ps = 2 * Real.log ((kappaV ps + 1) / (kappaV ps - 1)) ∧
      1 / Lmin0 beta eta ps ≤ kappaV ps / 4 := by
  have hk0 : 0 < kappaV ps := by linarith
  have hr := (sgd_rhoMax0 hp hanti hβ hη).1
  have hL : Lmin0 beta eta ps = 2 * Real.log ((kappaV ps + 1) / (kappaV ps - 1)) := by
    unfold Lmin0
    rw [hr, Real.log_pow, ← inv_div, Real.log_inv]
    push_cast; ring
  refine ⟨hL, ?_⟩
  set x : ℝ := 1 / kappaV ps with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one hk0]; exact hκ
  have e : (kappaV ps + 1) / (kappaV ps - 1) = (1 + x) / (1 - x) := by
    rw [hx]
    have : kappaV ps - 1 ≠ 0 := by linarith
    field_simp
  have hlog := two_mul_le_log_div hx0.le hx1
  rw [← e] at hlog
  have h4 : 4 / kappaV ps ≤ Lmin0 beta eta ps := by
    rw [hL]
    have : 4 / kappaV ps = 2 * (2 * x) := by rw [hx]; ring
    rw [this]; linarith
  have hpos : 0 < 4 / kappaV ps := by positivity
  have := one_div_le_one_div_of_le hpos h4
  rwa [one_div_div] at this

/-! ### (V5) Part (iv)(b): momentum without noise -/

/-- (V5) `lem:helps-vocab` (iv)(b), first claim, radius form: for `0 < beta < 1` the noise-free
radius is `>= beta` (that is `Lambda_j^0 <= -log beta`), with equality iff
`(1 - sqrt beta)^2 <= w_j <= (1 + sqrt beta)^2` (E1, E3). -/
theorem copy0_radius_ge_beta (hη : 0 ≤ eta) (hb0 : 0 < beta) (hb1 : beta < 1)
    (hp : ∀ j, 0 < (ps j : ℝ)) (j : Fin (n + 1)) :
    beta ≤ stepRadius (copyParams0 beta eta ps j) := by
  have hw : 0 ≤ (copyParams0 beta eta ps j).w := by
    show 0 ≤ eta * (1 - beta) * (ps j : ℝ)
    have : 0 < 1 - beta := by linarith
    have := hp j
    positivity
  exact beta_le_stepRadius (copyParams0 beta eta ps j) hb0.le hb1.le hw le_rfl

/-- (V5) `lem:helps-vocab` (iv)(b): equality case, via E3. -/
theorem copy0_radius_eq_beta_iff (hb0 : 0 < beta) (j : Fin (n + 1)) :
    stepRadius (copyParams0 beta eta ps j) = beta ↔
      (1 - Real.sqrt beta) ^ 2 ≤ eta * (1 - beta) * (ps j : ℝ) ∧
        eta * (1 - beta) * (ps j : ℝ) ≤ (1 + Real.sqrt beta) ^ 2 :=
  stepRadius_noiseFree_eq_beta_iff beta (eta * (1 - beta) * (ps j : ℝ)) 0 hb0

/-- (V5) `lem:helps-vocab` (iv)(b), rate form: `Lambda_j^0 = perStepRate <= -log beta`. -/
theorem copy0_perStepRate_le (hη : 0 < eta) (hb0 : 0 < beta) (hb1 : beta < 1)
    (hp : ∀ j, 0 < (ps j : ℝ)) (j : Fin (n + 1)) :
    perStepRate (copyParams0 beta eta ps j) ≤ -Real.log beta := by
  have hw : 0 < (copyParams0 beta eta ps j).w := by
    show 0 < eta * (1 - beta) * (ps j : ℝ)
    have : 0 < 1 - beta := by linarith
    have := hp j
    positivity
  exact perStepRate_le_neg_log_beta _ hb0 hb1 hw le_rfl

/-- (V5) `lem:helps-vocab` (iv)(b), second claim: for `kappa > 1`,
`sqrt beta = (sqrt kappa - 1)/(sqrt kappa + 1)` and `eta (1-beta) p_1 = (1 + sqrt beta)^2`
(that is `eta eps p_1 = (1 + sqrt beta)^2`), every noise-free copy has radius exactly `beta`,
`rhoMax0 = beta`, every copy has curvature feedback `u_c < 1`, and `1/Lmin0 = 1/(-log beta) <=
sqrt kappa / 4`. -/
theorem mom_rhoMax0 (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hb0 : 0 < beta)
    (hb1 : beta < 1) (hκ : 1 < kappaV ps)
    (hr : Real.sqrt beta = (Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1))
    (hη : eta * (1 - beta) * (ps 0 : ℝ) = (1 + Real.sqrt beta) ^ 2) :
    (∀ j, stepRadius (copyParams0 beta eta ps j) = beta) ∧ rhoMax0 beta eta ps = beta ∧
      (∀ j, (copyParams0 beta eta ps j).curvature < 1) ∧
      Lmin0 beta eta ps = -Real.log beta ∧
      1 / Lmin0 beta eta ps ≤ Real.sqrt (kappaV ps) / 4 := by
  have h0 := hp 0
  have hV := hp (Fin.last n)
  have hk0 : 0 < kappaV ps := by linarith
  set s : ℝ := Real.sqrt (kappaV ps) with hsdef
  set r : ℝ := Real.sqrt beta with hrdef
  have hs1 : 1 < s := by
    rw [hsdef, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) hκ
  have hs2 : s ^ 2 = kappaV ps := Real.sq_sqrt hk0.le
  have hr2 : r ^ 2 = beta := Real.sq_sqrt hb0.le
  have hr0 : 0 < r := Real.sqrt_pos.2 hb0
  have hr1 : r < 1 := by
    rw [hrdef, Real.sqrt_lt' one_pos]; simpa using hb1
  have hrs : r * (s + 1) = s - 1 := by
    rw [hr]; field_simp
  have h1r : 1 + r = s * (1 - r) := by linarith
  have hsq : (1 + r) ^ 2 = kappaV ps * (1 - r) ^ 2 := by
    rw [h1r, mul_pow, hs2]
  have hk : kappaV ps * (ps (Fin.last n) : ℝ) = (ps 0 : ℝ) := div_mul_cancel₀ _ hV.ne'
  have hc0 : 0 < eta * (1 - beta) := by
    have : 0 < eta * (1 - beta) * (ps 0 : ℝ) := by rw [hη]; positivity
    exact (mul_pos_iff_of_pos_right h0).1 this
  have hlow : (1 - r) ^ 2 = eta * (1 - beta) * (ps (Fin.last n) : ℝ) := by
    have : kappaV ps * (eta * (1 - beta) * (ps (Fin.last n) : ℝ)) = kappaV ps * (1 - r) ^ 2 := by
      rw [← hsq, ← hη, ← hk]; ring
    exact (mul_left_cancel₀ hk0.ne' this).symm
  have hrange : ∀ j, (1 - r) ^ 2 ≤ eta * (1 - beta) * (ps j : ℝ) ∧
      eta * (1 - beta) * (ps j : ℝ) ≤ (1 + r) ^ 2 := by
    intro j
    refine ⟨?_, ?_⟩
    · rw [hlow]; exact mul_le_mul_of_nonneg_left (last_le_ps hanti j) hc0.le
    · rw [← hη]; exact mul_le_mul_of_nonneg_left (ps_le_first hanti j) hc0.le
  have hrad : ∀ j, stepRadius (copyParams0 beta eta ps j) = beta :=
    fun j => (copy0_radius_eq_beta_iff hb0 j).2 (hrange j)
  have hrho : rhoMax0 beta eta ps = beta := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun j _ => (hrad j).le)
    · have := le_rhoMax0 (beta := beta) (eta := eta) (ps := ps) 0
      rw [hrad 0] at this; exact this
  refine ⟨hrad, hrho, ?_, ?_, ?_⟩
  · intro j
    show eta * (1 - beta) * (ps j : ℝ) / (2 * (1 + beta)) < 1
    rw [div_lt_one (by linarith)]
    have := (hrange j).2
    nlinarith [sq_pos_of_pos (sub_pos.2 hr1)]
  · unfold Lmin0; rw [hrho]
  · have hL : Lmin0 beta eta ps = -Real.log beta := by unfold Lmin0; rw [hrho]
    rw [hL]
    set x : ℝ := 1 / s with hx
    have hx0 : 0 < x := by positivity
    have hx1 : x < 1 := by rw [hx, div_lt_one (by linarith)]; exact hs1
    have e : (s + 1) / (s - 1) = (1 + x) / (1 - x) := by
      rw [hx]
      have : s - 1 ≠ 0 := by linarith
      field_simp
    have hlog := two_mul_le_log_div hx0.le hx1
    rw [← e] at hlog
    have hbeta : -Real.log beta = 2 * Real.log ((s + 1) / (s - 1)) := by
      rw [← hr2, Real.log_pow, hr, ← inv_div, Real.log_inv]
      push_cast; ring
    have h4 : 4 / s ≤ -Real.log beta := by
      rw [hbeta]
      have : 4 / s = 2 * (2 * x) := by rw [hx]; ring
      rw [this]; linarith
    have hpos : 0 < 4 / s := by positivity
    have := one_div_le_one_div_of_le hpos h4
    rwa [one_div_div] at this

/-! ### (V6) The large-batch limit -/

theorem stepRoots_eq_cubicRoots (p : Params) :
    stepRoots p = cubicRoots (stepC2 p.beta p.w p.noise : ℂ) (stepC1 p.beta p.w p.noise : ℂ)
      (stepC0 p.beta : ℂ) := by
  ext z
  show stepCharPoly p.beta p.w p.noise z = 0 ↔ _
  rw [stepCharPoly_expand]
  rfl

theorem stepRadius_eq_maxNorm (p : Params) :
    stepRadius p = maxNorm (cubicRoots (stepC2 p.beta p.w p.noise : ℂ)
      (stepC1 p.beta p.w p.noise : ℂ) (stepC0 p.beta : ℂ)) := by
  unfold stepRadius maxNorm
  rw [stepRoots_eq_cubicRoots]

/-- Continuity of the radius in the noise parameter at `u_n = 0` (via P3, `lem:helps-roots`). -/
theorem tendsto_stepRadius_noise (beta w a : ℝ) :
    Tendsto (fun un : ℝ => stepRadius (⟨beta, w, un, a⟩ : Params)) (𝓝 0)
      (𝓝 (stepRadius (⟨beta, w, 0, a⟩ : Params))) := by
  set K0 : ℝ := 2 * |w| * |1 - beta| with hK0
  have hK0nn : 0 ≤ K0 := by positivity
  set M : ℝ := 1 + (|stepC2 beta w 0| + K0 + |stepC1 beta w 0| + K0 * |beta| + |stepC0 beta|)
    with hM
  set C : ℝ := K0 * M ^ 2 + K0 * |beta| * M with hC
  have hd2 : ∀ un : ℝ, stepC2 beta w un - stepC2 beta w 0 = -(2 * w * (1 - beta)) * un := by
    intro un; simp only [stepC2]; ring
  have hd1 : ∀ un : ℝ, stepC1 beta w un - stepC1 beta w 0 = -(2 * w * (1 - beta) * beta) * un := by
    intro un; simp only [stepC1]; ring
  have habs : ∀ c un : ℝ, |c * un| = |c| * |un| := fun c un => abs_mul c un
  have hM1 : 1 ≤ M := by
    have := abs_nonneg (stepC2 beta w 0); have := abs_nonneg (stepC1 beta w 0)
    have := abs_nonneg (stepC0 beta); have : 0 ≤ K0 * |beta| := by positivity
    rw [hM]; linarith
  have hM0 : 0 ≤ M := by linarith
  have key : ∀ un : ℝ, |un| ≤ 1 →
      |stepRadius (⟨beta, w, un, a⟩ : Params) - stepRadius (⟨beta, w, 0, a⟩ : Params)|
        ≤ (C * |un|) ^ ((1 : ℝ) / 3) := by
    intro un hun
    rw [stepRadius_eq_maxNorm, stepRadius_eq_maxNorm (⟨beta, w, 0, a⟩ : Params)]
    simp only []
    have hc2 : |stepC2 beta w un| ≤ |stepC2 beta w 0| + K0 := by
      have h := hd2 un
      have : stepC2 beta w un = stepC2 beta w 0 + (-(2 * w * (1 - beta)) * un) := by linarith
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [habs]
      have : |-(2 * w * (1 - beta))| = K0 := by
        rw [abs_neg, hK0, abs_mul, abs_mul, abs_two]
      rw [this]
      nlinarith [abs_nonneg un]
    have hc1 : |stepC1 beta w un| ≤ |stepC1 beta w 0| + K0 * |beta| := by
      have h := hd1 un
      have : stepC1 beta w un = stepC1 beta w 0 + (-(2 * w * (1 - beta) * beta) * un) := by linarith
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [habs]
      have : |-(2 * w * (1 - beta) * beta)| = K0 * |beta| := by
        rw [abs_neg, hK0, abs_mul, abs_mul, abs_mul, abs_two]
      rw [this]
      nlinarith [abs_nonneg un, mul_nonneg hK0nn (abs_nonneg beta)]
    have hP : ∀ z ∈ cubicRoots (stepC2 beta w un : ℂ) (stepC1 beta w un : ℂ)
        (stepC0 beta : ℂ), ‖z‖ ≤ M := by
      intro z hz
      have := cubicRoots_norm_le_sum hz
      simp only [Complex.norm_real, Real.norm_eq_abs] at this
      rw [hM]; linarith
    have hQ : ∀ z ∈ cubicRoots (stepC2 beta w 0 : ℂ) (stepC1 beta w 0 : ℂ)
        (stepC0 beta : ℂ), ‖z‖ ≤ M := by
      intro z hz
      have := cubicRoots_norm_le_sum hz
      simp only [Complex.norm_real, Real.norm_eq_abs] at this
      have : 0 ≤ K0 * |beta| := by positivity
      rw [hM]; linarith
    have hcl := maxNorm_cubicRoots_close_coeff hP hQ
    refine hcl.trans (le_of_eq ?_)
    congr 1
    have n2 : ‖(stepC2 beta w un : ℂ) - (stepC2 beta w 0 : ℂ)‖ = K0 * |un| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hd2, abs_mul, abs_neg,
        hK0, abs_mul, abs_mul, abs_two]
    have n1 : ‖(stepC1 beta w un : ℂ) - (stepC1 beta w 0 : ℂ)‖ = K0 * |beta| * |un| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hd1, abs_mul, abs_neg,
        hK0, abs_mul, abs_mul, abs_mul, abs_two]
    have n0 : ‖(stepC0 beta : ℂ) - (stepC0 beta : ℂ)‖ = 0 := by simp
    rw [n2, n1, n0, hC]; ring
  have hlim : Tendsto (fun un : ℝ => (C * |un|) ^ ((1 : ℝ) / 3)) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun un : ℝ => (C * |un|) ^ ((1 : ℝ) / 3)) :=
      (continuous_const.mul continuous_abs).rpow_const (fun _ => Or.inr (by norm_num))
    have := hcont.tendsto 0
    simpa using this
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) ?_ hlim
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with un hun
  rw [Real.dist_eq]
  refine key un ?_
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hun
  exact hun.le

/-- The noise of a copy, as a function of `B`, tends to `0`. -/
theorem tendsto_copyParams_noise (hp : ∀ j, 0 < (ps j : ℝ)) (j : Fin (n + 1)) :
    Tendsto (fun B : ℕ => (copyParams d B ν beta eta ps j).noise) atTop (𝓝 0) := by
  have e : (fun B : ℕ => (copyParams d B ν beta eta ps j).noise)
      = fun B : ℕ => (eta * ((d : ℝ) + 2 - (ps j : ℝ)) / 2) / (B : ℝ) := by
    funext B
    rw [copyParams_noise hp]
    ring
  rw [e]
  exact tendsto_const_div_atTop_nhds_zero_nat _

/-- (V6) Each copy's radius converges to its noise-free radius as `B -> infinity`. -/
theorem tendsto_stepRadius_copy (hp : ∀ j, 0 < (ps j : ℝ)) (j : Fin (n + 1)) :
    Tendsto (fun B : ℕ => stepRadius (copyParams d B ν beta eta ps j)) atTop
      (𝓝 (stepRadius (copyParams0 beta eta ps j))) := by
  have hn := tendsto_copyParams_noise (d := d) (ν := ν) (beta := beta) (eta := eta) hp j
  have h1 := (tendsto_stepRadius_noise beta (eta * (1 - beta) * (ps j : ℝ)) 0).comp hn
  have e : (fun B : ℕ => stepRadius (copyParams d B ν beta eta ps j))
      = (fun un : ℝ => stepRadius (⟨beta, eta * (1 - beta) * (ps j : ℝ), un, 0⟩ : Params))
        ∘ (fun B : ℕ => (copyParams d B ν beta eta ps j).noise) := by
    funext B
    exact stepRadius_eq_noise_form _
  rw [e]
  exact h1

/-- (V6) `lem:helps-vocab` large batch: `rhoMax -> rhoMax0` as `B -> infinity`
(`d`, `eta`, `beta`, `ps` fixed), for any `beta`, `eta`. -/
theorem tendsto_rhoMax (hp : ∀ j, 0 < (ps j : ℝ)) :
    Tendsto (fun B : ℕ => rhoMax d B ν beta eta ps) atTop (𝓝 (rhoMax0 beta eta ps)) :=
  Filter.Tendsto.finset_sup'_nhds_apply Finset.univ_nonempty
    (fun j _ => tendsto_stepRadius_copy hp j)

/-- (V6) If every noise-free copy has radius `< 1`, then for `B` large every copy is stable. -/
theorem eventually_stable (hp : ∀ j, 0 < (ps j : ℝ))
    (h0 : ∀ j, stepRadius (copyParams0 beta eta ps j) < 1) :
    ∀ᶠ B : ℕ in atTop, ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1 := by
  rw [Filter.eventually_all]
  intro j
  exact (tendsto_stepRadius_copy hp j).eventually_lt_const (h0 j)

/-- (V6) `lem:helps-vocab` large batch for (iv)(a): with `beta = 0`, `eta = 2/(p_1+p_V)` and
`kappa > 1`, as `B -> infinity`: `rhoMax -> ((kappa-1)/(kappa+1))^2`,
`Lmin -> 2 log ((kappa+1)/(kappa-1))`, and eventually every copy is stable. -/
theorem largeBatch_sgd (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hβ : beta = 0)
    (hη : eta = 2 / ((ps 0 : ℝ) + (ps (Fin.last n) : ℝ))) (hκ : 1 < kappaV ps) :
    Tendsto (fun B : ℕ => rhoMax d B ν beta eta ps) atTop
        (𝓝 (((kappaV ps - 1) / (kappaV ps + 1)) ^ 2)) ∧
      Tendsto (fun B : ℕ => Lmin d B ν beta eta ps) atTop
        (𝓝 (2 * Real.log ((kappaV ps + 1) / (kappaV ps - 1)))) ∧
      (∀ᶠ B : ℕ in atTop, ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) := by
  obtain ⟨hr, hlt⟩ := sgd_rhoMax0 hp hanti hβ hη
  have h1 : Tendsto (fun B : ℕ => rhoMax d B ν beta eta ps) atTop
      (𝓝 (((kappaV ps - 1) / (kappaV ps + 1)) ^ 2)) := by
    rw [← hr]; exact tendsto_rhoMax hp
  have hne : ((kappaV ps - 1) / (kappaV ps + 1)) ^ 2 ≠ 0 := by
    have hk : 0 < kappaV ps := by linarith
    have : 0 < (kappaV ps - 1) / (kappaV ps + 1) := div_pos (by linarith) (by linarith)
    positivity
  refine ⟨h1, ?_, eventually_stable hp hlt⟩
  have h2 := ((Real.continuousAt_log hne).tendsto.comp h1).neg
  have e : -Real.log (((kappaV ps - 1) / (kappaV ps + 1)) ^ 2)
      = 2 * Real.log ((kappaV ps + 1) / (kappaV ps - 1)) := by
    rw [Real.log_pow, ← inv_div, Real.log_inv]; push_cast; ring
  rw [e] at h2
  exact h2

/-- (V6) `lem:helps-vocab` large batch for (iv)(b): under the hypotheses of `mom_rhoMax0`,
`rhoMax -> beta`, `Lmin -> -log beta`, and eventually every copy is stable. -/
theorem largeBatch_momentum (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) (hb0 : 0 < beta)
    (hb1 : beta < 1) (hκ : 1 < kappaV ps)
    (hr : Real.sqrt beta = (Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1))
    (hη : eta * (1 - beta) * (ps 0 : ℝ) = (1 + Real.sqrt beta) ^ 2) :
    Tendsto (fun B : ℕ => rhoMax d B ν beta eta ps) atTop (𝓝 beta) ∧
      Tendsto (fun B : ℕ => Lmin d B ν beta eta ps) atTop (𝓝 (-Real.log beta)) ∧
      (∀ᶠ B : ℕ in atTop, ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) := by
  obtain ⟨hrad, hrho, _, _, _⟩ := mom_rhoMax0 hp hanti hb0 hb1 hκ hr hη
  have h1 : Tendsto (fun B : ℕ => rhoMax d B ν beta eta ps) atTop (𝓝 beta) := by
    have := tendsto_rhoMax (d := d) (ν := ν) (beta := beta) (eta := eta) hp
    rwa [hrho] at this
  refine ⟨h1, ?_, eventually_stable hp (fun j => by rw [hrad j]; exact hb1)⟩
  exact ((Real.continuousAt_log hb0.ne').tendsto.comp h1).neg

end Basic

/-! ### (V7) Part (iii), sharpened (v2): constant `d+2-p_V` and `beta in [0,1)` -/

section V2

variable {n : ℕ} {d B : ℕ} {ν : Measure ℝ} {beta eta : ℝ} {ps : Fin (n + 1) → unitInterval}

local notation "pFst" => ((ps 0 : unitInterval) : ℝ)
local notation "pLst" => ((ps (Fin.last n) : unitInterval) : ℝ)

/-- `d + 2 - p > 0` for `p in [0,1]`. -/
theorem vv_D_pos (p : unitInterval) : 0 < (d : ℝ) + 2 - p := by
  have h1 : (p : ℝ) ≤ 1 := p.2.2
  have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

/-- If every copy is stable then `1/Lmin >= 0` (`Lmin = -log rhoMax >= 0`). -/
theorem vv_one_div_Lmin_nonneg (hstab : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) :
    0 ≤ 1 / Lmin d B ν beta eta ps := by
  have h0 : 0 ≤ rhoMax d B ν beta eta ps :=
    (stepRadius_nonneg _).trans
      (le_rhoMax (d := d) (B := B) (ν := ν) (beta := beta) (eta := eta) (ps := ps) 0)
  have h1 : rhoMax d B ν beta eta ps < 1 := rhoMax_lt_one_iff.2 hstab
  have h2 : Real.log (rhoMax d B ν beta eta ps) ≤ 0 := Real.log_nonpos h0 h1.le
  unfold Lmin
  exact one_div_nonneg.2 (by linarith)

/-- From a radius lower bound `1 - y <= rhoMax` (needed only when `y < 1`) to
`1/y - 1 <= 1/Lmin`; for `y >= 1` the left side is `<= 0 <= 1/Lmin`. -/
theorem vv_inv_Lmin_ge {y : ℝ} (hy0 : 0 < y)
    (hlow : y < 1 → 1 - y ≤ rhoMax d B ν beta eta ps)
    (hstab : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) :
    1 / y - 1 ≤ 1 / Lmin d B ν beta eta ps := by
  by_cases hy : y < 1
  · exact inv_neg_log_ge hy0 hy (hlow hy) (rhoMax_lt_one_iff.2 hstab)
  · push Not at hy
    have h1 : 1 / y ≤ 1 := (div_le_one hy0).2 hy
    have := vv_one_div_Lmin_nonneg (d := d) (B := B) (ν := ν) (beta := beta) (eta := eta)
      (ps := ps) hstab
    linarith

/-- For `beta in [0,1)` and a stable copy `j`: `1 - 4 eta p_j <= radius` (E1/E6 for `beta > 0`,
`lem:helps-sgd` for `beta = 0`). -/
theorem vv_radius_lower_four (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hη : 0 < eta)
    (hb0 : 0 ≤ beta) (hb1 : beta < 1) {j : Fin (n + 1)}
    (hstab : stepRadius (copyParams d B ν beta eta ps j) < 1) :
    1 - 4 * eta * (ps j : ℝ) ≤ stepRadius (copyParams d B ν beta eta ps j) := by
  rcases hb0.eq_or_lt with h | h
  · obtain ⟨x, hx, _, _, hx4⟩ := sgd_radius_eq hB hp hη h.symm hstab
    have := mul_pos hη (hp j)
    rw [hx]; linarith
  · rcases lt_or_ge (4 * eta * (ps j : ℝ)) 1 with h4 | h4
    · exact (momentum_radius_lower hp h hb1 hη j).2 h4
    · have := stepRadius_nonneg (copyParams d B ν beta eta ps j)
      linarith

/-- (V7) `lem:helps-vocab` (iii) (v2), first bound, radius form: for `0 <= beta < 1`, all copies
stable and `y := 8 B p_V/(d+2-p_V) < 1`, `1 - y <= rhoMax`.  (The hypothesis `y < 1` is not
used by this proof; it is kept to match the statement.) -/
theorem mom_one_sub_le_rhoMax_v2 (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hη : 0 < eta)
    (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (hstab : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1)
    (_hy : 8 * (B : ℝ) * pLst / ((d : ℝ) + 2 - pLst) < 1) :
    1 - 8 * (B : ℝ) * pLst / ((d : ℝ) + 2 - pLst) ≤ rhoMax d B ν beta eta ps := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hl := copy_load_lt_one_of_stable hp hb0 hb1 hη (hstab (Fin.last n))
  have hq := noise_part_le_inverseCriticalRate (d := d) (B := B) (ps (Fin.last n)) hb0 hb1
  have hd := vv_D_pos (d := d) (ps (Fin.last n))
  have h1 : eta * (((d : ℝ) + 2 - pLst) / (2 * B)) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hq hη.le) hl
  have h2 : eta * ((d : ℝ) + 2 - pLst) < 2 * B := by
    have : eta * (((d : ℝ) + 2 - pLst) / (2 * B)) = eta * ((d : ℝ) + 2 - pLst) / (2 * B) := by
      ring
    rw [this, div_lt_one (by positivity)] at h1
    exact h1
  have h3 : 4 * eta * pLst < 8 * (B : ℝ) * pLst / ((d : ℝ) + 2 - pLst) := by
    rw [lt_div_iff₀ hd]
    nlinarith [mul_lt_mul_of_pos_left h2 (hp (Fin.last n))]
  have hlow := vv_radius_lower_four hB hp hη hb0 hb1 (hstab (Fin.last n))
  have := le_rhoMax (d := d) (B := B) (ν := ν) (beta := beta) (eta := eta) (ps := ps) (Fin.last n)
  linarith

/-- (V7) `lem:helps-vocab` (iii) (v2), first bound: for `0 <= beta < 1` and all copies stable,
`(d+2-p_V)/(8 B p_V) - 1 <= 1/Lmin`.  No hypothesis on `y`: the bound is trivial for `y >= 1`. -/
theorem mom_inv_Lmin_ge_first_v2 (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hη : 0 < eta)
    (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (hstab : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) :
    ((d : ℝ) + 2 - pLst) / (8 * (B : ℝ) * pLst) - 1 ≤ 1 / Lmin d B ν beta eta ps := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hd := vv_D_pos (d := d) (ps (Fin.last n))
  have hy0 : 0 < 8 * (B : ℝ) * pLst / ((d : ℝ) + 2 - pLst) :=
    div_pos (mul_pos (mul_pos (by norm_num) hB') (hp (Fin.last n))) hd
  have := vv_inv_Lmin_ge hy0
    (fun hy => mom_one_sub_le_rhoMax_v2 hB hp hη hb0 hb1 hstab hy) hstab
  rwa [one_div_div] at this

/-- (V7) `lem:helps-vocab` (iii) (v2), second bound: for `0 <= beta < 1`, all copies stable and
`kappa > 16`, `sqrt kappa/4 - 1 <= 1/Lmin`.  For `beta > 0` this is `mom_inv_Lmin_ge_second`;
for `beta = 0` it follows from the SGD bound `kappa/4 - 1` and `sqrt kappa <= kappa`
(hypotheses `0 < B`, `0 < eta` added for the `beta = 0` case). -/
theorem mom_inv_Lmin_ge_second_v2 (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hη : 0 < eta)
    (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (hstab : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) (hκ : 16 < kappaV ps) :
    Real.sqrt (kappaV ps) / 4 - 1 ≤ 1 / Lmin d B ν beta eta ps := by
  rcases hb0.eq_or_lt with h | h
  · have hk0 : 0 < kappaV ps := by linarith
    have h1 : 1 ≤ Real.sqrt (kappaV ps) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith)
    have h2 := Real.sq_sqrt hk0.le
    have hs : Real.sqrt (kappaV ps) ≤ kappaV ps := by nlinarith
    have := sgd_inv_Lmin_ge_second hB hp hη h.symm hstab (by linarith)
    linarith
  · exact mom_inv_Lmin_ge_second hp hη h hb1 hstab hκ

/-- (V7) `lem:helps-vocab` (ii) without the hypothesis `y < 1`: for `beta = 0` and all copies
stable, `(d+2-p_V)/(B p_V) - 1 <= 1/Lmin`. -/
theorem sgd_inv_Lmin_ge_first_v2 (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hη : 0 < eta)
    (hβ : beta = 0) (hstab : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) :
    ((d : ℝ) + 2 - pLst) / ((B : ℝ) * pLst) - 1 ≤ 1 / Lmin d B ν beta eta ps := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hd := vv_D_pos (d := d) (ps (Fin.last n))
  have hy0 : 0 < (B : ℝ) * pLst / ((d : ℝ) + 2 - pLst) :=
    div_pos (mul_pos hB' (hp (Fin.last n))) hd
  have := vv_inv_Lmin_ge hy0 (fun _ => sgd_one_sub_le_rhoMax hB hp hη hβ hstab) hstab
  rwa [one_div_div] at this

end V2

/-! ### (V8) Part (v) (v2): the best shared learning rate of SGD, exactly -/

/-- `eta*_p = B/(d+2+(B-1)p)`: the optimum of the SGD gain of a row with frequency `p`
(`v2 lem:helps-vocab (v)`); `eta_+(p) = 2 eta*_p` at `beta = 0`. -/
def etaStar (d B : ℕ) (p : ℝ) : ℝ := (B : ℝ) / ((d : ℝ) + 2 + ((B : ℝ) - 1) * p)

/-- `D_B = d + 2 + (B-1)(p_1 + p_V)` (`v2 lem:helps-vocab (v)`). -/
def DB {n : ℕ} (d B : ℕ) (ps : Fin (n + 1) → unitInterval) : ℝ :=
  (d : ℝ) + 2 + ((B : ℝ) - 1) * ((ps 0 : ℝ) + (ps (Fin.last n) : ℝ))

/-- The SGD gain `g(eta) = 2 eta p (1 - eta (d+2+(B-1)p)/(2B)) = 2 w (1 - u)` of a row with
frequency `p` at `beta = 0`: the radius of the row is `1 - g` (`v2 lem:helps-vocab (v)`). -/
def sgdGain (d B : ℕ) (p eta : ℝ) : ℝ :=
  2 * eta * p * (1 - eta * ((d : ℝ) + 2 + ((B : ℝ) - 1) * p) / (2 * B))

/-- The set `{Lmin(eta) | eta > 0, every copy stable}` of decay rates at `beta = 0` over the
learning rates at which every copy is stable (`v2 lem:helps-vocab (v)`). -/
abbrev sgdLminSet {n : ℕ} (d B : ℕ) (ν : Measure ℝ) (ps : Fin (n + 1) → unitInterval) :
    Set ℝ :=
  (fun η : ℝ => Lmin d B ν 0 η ps) ''
    {η : ℝ | 0 < η ∧ ∀ j, stepRadius (copyParams d B ν 0 η ps j) < 1}

section V3

variable {n : ℕ} {d B : ℕ} {ν : Measure ℝ} {beta eta : ℝ} {ps : Fin (n + 1) → unitInterval}

local notation "pFst" => ((ps 0 : unitInterval) : ℝ)
local notation "pLst" => ((ps (Fin.last n) : unitInterval) : ℝ)

/-! #### Real-variable lemmas on `sgdGain` -/

theorem vv_K_pos (hB : 0 < B) {p : ℝ} (hp : 0 ≤ p) : 0 < (d : ℝ) + 2 + ((B : ℝ) - 1) * p := by
  have hb1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have h1 := mul_nonneg (sub_nonneg.2 hb1) hp
  have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

/-- `g_p(eta) <= B p/(d+2+(B-1)p)` (the maximum, at `eta*_p`). -/
theorem vv_gain_le (hB : 0 < B) {p : ℝ} (hp : 0 < p) (eta : ℝ) :
    sgdGain d B p eta ≤ (B : ℝ) * p / ((d : ℝ) + 2 + ((B : ℝ) - 1) * p) := by
  have hK := vv_K_pos (d := d) hB hp.le
  have hK' : (d : ℝ) + 2 + ((B : ℝ) - 1) * p ≠ 0 := hK.ne'
  have hB' : (B : ℝ) ≠ 0 := by positivity
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have key : (B : ℝ) * p / ((d : ℝ) + 2 + ((B : ℝ) - 1) * p) - sgdGain d B p eta
      = p * ((d : ℝ) + 2 + ((B : ℝ) - 1) * p) / B
        * (eta - B / ((d : ℝ) + 2 + ((B : ℝ) - 1) * p)) ^ 2 := by
    unfold sgdGain
    generalize (d : ℝ) + 2 + ((B : ℝ) - 1) * p = K at hK' ⊢
    field_simp
    ring
  have : 0 ≤ p * ((d : ℝ) + 2 + ((B : ℝ) - 1) * p) / B
        * (eta - B / ((d : ℝ) + 2 + ((B : ℝ) - 1) * p)) ^ 2 := by positivity
  linarith

/-- `B p/(d+2+(B-1)p) < 1` for `0 < p < d + 2`. -/
theorem vv_gain_max_lt_one (hB : 0 < B) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (B : ℝ) * p / ((d : ℝ) + 2 + ((B : ℝ) - 1) * p) < 1 := by
  have hK := vv_K_pos (d := d) hB hp.le
  have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [div_lt_one hK]
  have : (B : ℝ) * p = ((B : ℝ) - 1) * p + p := by ring
  linarith

theorem vv_gain_at_etaStar (hB : 0 < B) {p : ℝ} (hp : 0 < p) :
    sgdGain d B p (etaStar d B p) = (B : ℝ) * p / ((d : ℝ) + 2 + ((B : ℝ) - 1) * p) := by
  have hK := vv_K_pos (d := d) hB hp.le
  have hK' : (d : ℝ) + 2 + ((B : ℝ) - 1) * p ≠ 0 := hK.ne'
  have hB' : (B : ℝ) ≠ 0 := by positivity
  unfold sgdGain etaStar
  field_simp
  ring

/-- `g_{p_1} - g_{p_V} = (p_1 - p_V) eta (2B - eta D_B)/B`. -/
theorem vv_gain_diff (hB : 0 < B) (p1 pV eta : ℝ) :
    sgdGain d B p1 eta - sgdGain d B pV eta
      = (p1 - pV) * eta * (2 * B - eta * ((d : ℝ) + 2 + ((B : ℝ) - 1) * (p1 + pV))) / B := by
  have hB' : (B : ℝ) ≠ 0 := by positivity
  unfold sgdGain
  field_simp
  ring

theorem vv_gain_sub (hB : 0 < B) (p e0 e1 : ℝ) :
    sgdGain d B p e0 - sgdGain d B p e1
      = p * (e0 - e1) * (2 * B - ((d : ℝ) + 2 + ((B : ℝ) - 1) * p) * (e0 + e1)) / B := by
  have hB' : (B : ℝ) ≠ 0 := by positivity
  unfold sgdGain
  field_simp
  ring

/-- The two gains cross at `eta = 2B/D` with value `4B(B-1)pq/D^2`, for `D = d+2+(B-1)(p+q)`. -/
theorem vv_gain_at_two (hB : 0 < B) (p q D : ℝ)
    (hD : D = (d : ℝ) + 2 + ((B : ℝ) - 1) * p + ((B : ℝ) - 1) * q) (hD0 : D ≠ 0) :
    sgdGain d B p (2 * B / D) = 4 * (B : ℝ) * ((B : ℝ) - 1) * p * q / D ^ 2 := by
  have hB' : (B : ℝ) ≠ 0 := by positivity
  subst hD
  unfold sgdGain
  field_simp
  ring

/-- A positive-sign lemma for `eta < eta0` (decreasing side of the `p_V` gain). -/
theorem vv_aux_lt {b K e0 e p : ℝ} (hb : 0 < b) (hp : 0 < p) (hK : 0 < K) (hK0 : K * e0 ≤ b)
    (h : e < e0) : 0 < p * (e0 - e) * (2 * b - K * (e0 + e)) / b := by
  apply div_pos _ hb
  apply mul_pos (mul_pos hp (sub_pos.2 h))
  nlinarith [mul_lt_mul_of_pos_left h hK]

/-- A positive-sign lemma for `eta > eta0` (decreasing side of the `p_1` gain). -/
theorem vv_aux_gt {b K e0 e p : ℝ} (hb : 0 < b) (hp : 0 < p) (hK : 0 < K) (hK0 : b ≤ K * e0)
    (h : e0 < e) : 0 < p * (e0 - e) * (2 * b - K * (e0 + e)) / b := by
  apply div_pos _ hb
  have h1 : e0 - e < 0 := by linarith
  have h2 : 2 * b - K * (e0 + e) < 0 := by nlinarith [mul_lt_mul_of_pos_left h hK]
  rw [mul_assoc]
  exact mul_pos hp (mul_pos_of_neg_of_neg h1 h2)

/-- Concavity of `A p - c p^2` (`c >= 0`): the middle value dominates the smaller endpoint. -/
theorem vv_min_le_concave {A c p p1 pV : ℝ} (hc : 0 ≤ c) (h1 : pV ≤ p) (h2 : p ≤ p1) :
    min (A * p1 - c * p1 ^ 2) (A * pV - c * pV ^ 2) ≤ A * p - c * p ^ 2 := by
  by_contra h
  push Not at h
  rw [lt_min_iff] at h
  obtain ⟨ha, hb⟩ := h
  have hw1 : 0 ≤ p1 - p := by linarith
  have hw2 : 0 ≤ p - pV := by linarith
  have key : (p1 - pV) * (A * p - c * p ^ 2) - (p1 - p) * (A * pV - c * pV ^ 2)
      - (p - pV) * (A * p1 - c * p1 ^ 2) = c * (p - pV) * (p1 - p) * (p1 - pV) := by ring
  have hpos : 0 ≤ c * (p - pV) * (p1 - p) * (p1 - pV) :=
    mul_nonneg (mul_nonneg (mul_nonneg hc hw2) hw1) (by linarith)
  have S1 : 0 < (A * p1 - c * p1 ^ 2) - (A * p - c * p ^ 2) := by linarith
  have S2 : 0 < (A * pV - c * pV ^ 2) - (A * p - c * p ^ 2) := by linarith
  have t1 : 0 ≤ (p1 - p) * ((A * pV - c * pV ^ 2) - (A * p - c * p ^ 2)) :=
    mul_nonneg hw1 S2.le
  have t2 : 0 ≤ (p - pV) * ((A * p1 - c * p1 ^ 2) - (A * p - c * p ^ 2)) :=
    mul_nonneg hw2 S1.le
  have hsum : (p1 - p) * ((A * pV - c * pV ^ 2) - (A * p - c * p ^ 2))
      + (p - pV) * ((A * p1 - c * p1 ^ 2) - (A * p - c * p ^ 2)) ≤ 0 := by nlinarith
  have e1 : (p1 - p) * ((A * pV - c * pV ^ 2) - (A * p - c * p ^ 2)) = 0 := by linarith
  have e2 : (p - pV) * ((A * p1 - c * p1 ^ 2) - (A * p - c * p ^ 2)) = 0 := by linarith
  have hp1 : p1 - p = 0 := (mul_eq_zero.1 e1).resolve_right S2.ne'
  have hp2 : p - pV = 0 := (mul_eq_zero.1 e2).resolve_right S1.ne'
  have : p1 = p := by linarith
  rw [this] at S1
  simp at S1

/-- `sgdGain` of an intermediate frequency dominates the smaller endpoint gain
(`v2 lem:helps-vocab (v)`: concavity in `p`, whose `p^2` coefficient is `-eta^2 (B-1)/B`). -/
theorem vv_min_gain_le_mid (hB : 0 < B) {p p1 pV : ℝ} (eta : ℝ) (h1 : pV ≤ p) (h2 : p ≤ p1) :
    min (sgdGain d B p1 eta) (sgdGain d B pV eta) ≤ sgdGain d B p eta := by
  have hB' : (B : ℝ) ≠ 0 := by positivity
  have hb0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hb1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have e : ∀ q : ℝ, sgdGain d B q eta
      = (2 * eta - eta ^ 2 * ((d : ℝ) + 2) / B) * q - (eta ^ 2 * ((B : ℝ) - 1) / B) * q ^ 2 := by
    intro q
    unfold sgdGain
    field_simp
    ring
  rw [e p1, e pV, e p]
  exact vv_min_le_concave (div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.2 hb1)) hb0.le) h1 h2

theorem vv_neg_log_mono {G G' : ℝ} (h : G ≤ G') (h' : G' < 1) :
    -Real.log (1 - G) ≤ -Real.log (1 - G') := by
  have h0 : 0 < 1 - G' := by linarith
  have := Real.log_le_log h0 (by linarith : 1 - G' ≤ 1 - G)
  linarith

theorem vv_neg_log_strict {G G' : ℝ} (h : G < G') (h' : G' < 1) :
    -Real.log (1 - G) < -Real.log (1 - G') := by
  have h0 : 0 < 1 - G' := by linarith
  have := Real.log_lt_log h0 (by linarith : 1 - G' < 1 - G)
  linarith

/-! #### The copies at `beta = 0` -/

theorem vv_icr_zero (hB : 0 < B) (p : unitInterval) :
    inverseCriticalRate d B p 0 = ((d : ℝ) + 2 + ((B : ℝ) - 1) * p) / (2 * B) := by
  have hB' : (B : ℝ) ≠ 0 := by positivity
  unfold inverseCriticalRate
  field_simp
  ring

/-- At `beta = 0` the radius of copy `j` is exactly `1 - g_j(eta)`
(`lem:helps-sgd` with `u = eta (d+2+(B-1)p)/(2B)`). -/
theorem vv_copy_radius (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (_hη : 0 < eta)
    (hβ : beta = 0) (j : Fin (n + 1)) :
    stepRadius (copyParams d B ν beta eta ps j) = 1 - sgdGain d B (ps j : ℝ) eta := by
  subst hβ
  have hg := vv_gain_le (d := d) hB (hp j) eta
  have hlt := vv_gain_max_lt_one (d := d) hB (hp j) (ps j).2.2
  have hload : (copyParams d B ν 0 eta ps j).totalLoad = eta * inverseCriticalRate d B (ps j) 0 :=
    params_totalLoad d B (ps j) (hp j).ne' ν 0 eta
  have e : 1 - 2 * (copyParams d B ν 0 eta ps j).w * (1 - (copyParams d B ν 0 eta ps j).totalLoad)
      = 1 - sgdGain d B (ps j : ℝ) eta := by
    rw [hload, copyParams_w, vv_icr_zero hB]
    unfold sgdGain
    ring
  rw [stepRadius_beta_zero _ (copyParams_beta j), e, abs_of_nonneg (by linarith)]

/-- (V8) `v2 lem:helps-vocab (v)`: at `beta = 0`, copy `j` is stable iff `0 < g_j(eta)`. -/
theorem copy_stable_iff_gain_pos (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hη : 0 < eta)
    (hβ : beta = 0) (j : Fin (n + 1)) :
    stepRadius (copyParams d B ν beta eta ps j) < 1 ↔ 0 < sgdGain d B (ps j : ℝ) eta := by
  rw [vv_copy_radius hB hp hη hβ j]
  constructor <;> intro h <;> linarith

/-- (V8) `v2 lem:helps-vocab (v)`: at `beta = 0`, `rhoMax = 1 - min (g_1, g_V)`; the minimum over
`j` is attained at an endpoint by concavity of `g` in `p`. -/
theorem rhoMax_sgd_eq_one_sub_min (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hη : 0 < eta) (hβ : beta = 0) :
    rhoMax d B ν beta eta ps = 1 - min (sgdGain d B pFst eta) (sgdGain d B pLst eta) := by
  have hr : ∀ j, stepRadius (copyParams d B ν beta eta ps j) = 1 - sgdGain d B (ps j : ℝ) eta :=
    fun j => vv_copy_radius hB hp hη hβ j
  apply le_antisymm
  · unfold rhoMax
    refine Finset.sup'_le _ _ (fun j _ => ?_)
    rw [hr j]
    have := vv_min_gain_le_mid (d := d) hB eta (last_le_ps hanti j) (ps_le_first hanti j)
    linarith
  · have h0 := le_rhoMax (d := d) (B := B) (ν := ν) (beta := beta) (eta := eta) (ps := ps) 0
    have hl := le_rhoMax (d := d) (B := B) (ν := ν) (beta := beta) (eta := eta) (ps := ps)
      (Fin.last n)
    rw [hr 0] at h0
    rw [hr (Fin.last n)] at hl
    rcases le_total (sgdGain d B pFst eta) (sgdGain d B pLst eta) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith

theorem vv_Lmin_eq (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hη : 0 < eta) (hβ : beta = 0) :
    Lmin d B ν beta eta ps
      = -Real.log (1 - min (sgdGain d B pFst eta) (sgdGain d B pLst eta)) := by
  unfold Lmin
  rw [rhoMax_sgd_eq_one_sub_min hB hp hanti hη hβ]

theorem vv_stable_iff (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hη : 0 < eta) (hβ : beta = 0) :
    (∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) ↔
      0 < min (sgdGain d B pFst eta) (sgdGain d B pLst eta) := by
  rw [← rhoMax_lt_one_iff, rhoMax_sgd_eq_one_sub_min hB hp hanti hη hβ]
  constructor <;> intro h <;> linarith

/-! #### The two regimes of `v2 lem:helps-vocab (v)` -/

/-- Case `(B-1)(p_1-p_V) <= d+2`: `min (g_1, g_V) <= g_V <= B p_V/(d+2+(B-1)p_V)` for every `eta`,
with equality at `eta*_V`. -/
theorem vv_case1_core (hB : 0 < B) {p1 pV : ℝ} (hpV : 0 < pV) (hle : pV ≤ p1)
    (hcase : ((B : ℝ) - 1) * (p1 - pV) ≤ (d : ℝ) + 2) (eta : ℝ) :
    min (sgdGain d B p1 eta) (sgdGain d B pV eta)
        ≤ (B : ℝ) * pV / ((d : ℝ) + 2 + ((B : ℝ) - 1) * pV) ∧
      min (sgdGain d B p1 (etaStar d B pV)) (sgdGain d B pV (etaStar d B pV))
        = (B : ℝ) * pV / ((d : ℝ) + 2 + ((B : ℝ) - 1) * pV) := by
  have hb0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hKV := vv_K_pos (d := d) hB hpV.le
  refine ⟨(min_le_right _ _).trans (vv_gain_le hB hpV eta), ?_⟩
  rw [← vv_gain_at_etaStar (d := d) hB hpV]
  apply min_eq_right
  have hη : 0 < etaStar d B pV := div_pos hb0 hKV
  have h2 : (d : ℝ) + 2 + ((B : ℝ) - 1) * (p1 + pV)
      ≤ 2 * ((d : ℝ) + 2 + ((B : ℝ) - 1) * pV) := by linarith
  have hfac0 : etaStar d B pV * ((d : ℝ) + 2 + ((B : ℝ) - 1) * (p1 + pV)) ≤ 2 * B := by
    unfold etaStar
    rw [div_mul_eq_mul_div, div_le_iff₀ hKV]
    nlinarith [mul_le_mul_of_nonneg_left h2 hb0.le]
  have hfac : 0 ≤ 2 * (B : ℝ)
      - etaStar d B pV * ((d : ℝ) + 2 + ((B : ℝ) - 1) * (p1 + pV)) := by linarith
  have hdiff := vv_gain_diff (d := d) hB p1 pV (etaStar d B pV)
  have : 0 ≤ sgdGain d B p1 (etaStar d B pV) - sgdGain d B pV (etaStar d B pV) := by
    rw [hdiff]
    exact div_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 hle) hη.le) hfac) hb0.le
  linarith

/-- `-log (1 - B p_V/(d+2+(B-1)p_V)) = log (1 + B p_V/(d+2-p_V))`. -/
theorem vv_case1_value (hB : 0 < B) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    -Real.log (1 - (B : ℝ) * p / ((d : ℝ) + 2 + ((B : ℝ) - 1) * p))
      = Real.log (1 + (B : ℝ) * p / ((d : ℝ) + 2 - p)) := by
  have hK := vv_K_pos (d := d) hB hp.le
  have hD : 0 < (d : ℝ) + 2 - p := by
    have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have e : 1 - (B : ℝ) * p / ((d : ℝ) + 2 + ((B : ℝ) - 1) * p)
      = ((d : ℝ) + 2 - p) / ((d : ℝ) + 2 + ((B : ℝ) - 1) * p) := by
    rw [eq_div_iff hK.ne', sub_mul, one_mul, div_mul_cancel₀ _ hK.ne']
    ring
  rw [e, ← Real.log_inv, inv_div]
  congr 1
  rw [div_eq_iff hD.ne', add_mul, one_mul, div_mul_cancel₀ _ hD.ne']
  ring

/-- The numerical facts at the crossing point `eta = 2B/D_B` (case `d + 2 < (B-1)(p_1-p_V)`). -/
theorem vv_case2_facts (hB : 0 < B) {p1 pV D : ℝ} (hpV : 0 < pV) (hle : pV ≤ p1) (hp1 : p1 ≤ 1)
    (hcase : (d : ℝ) + 2 < ((B : ℝ) - 1) * (p1 - pV))
    (hD : D = (d : ℝ) + 2 + ((B : ℝ) - 1) * (p1 + pV)) :
    0 < D ∧ 0 < 4 * (B : ℝ) * ((B : ℝ) - 1) * p1 * pV / D ^ 2 ∧
      4 * (B : ℝ) * ((B : ℝ) - 1) * p1 * pV / D ^ 2 < 1 ∧ 0 < 2 * (B : ℝ) / D ∧
      sgdGain d B p1 (2 * B / D) = 4 * (B : ℝ) * ((B : ℝ) - 1) * p1 * pV / D ^ 2 ∧
      sgdGain d B pV (2 * B / D) = 4 * (B : ℝ) * ((B : ℝ) - 1) * p1 * pV / D ^ 2 := by
  have hb1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hb0 : (0 : ℝ) < B := by linarith
  have ha : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hB1 : 0 < (B : ℝ) - 1 := by
    by_contra h
    push Not at h
    have : ((B : ℝ) - 1) * (p1 - pV) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (sub_nonneg.2 hle)
    linarith
  have hp1pos : 0 < p1 := lt_of_lt_of_le hpV hle
  have hDpos : 0 < D := by
    rw [hD]
    have := mul_pos hB1 (add_pos hp1pos hpV)
    linarith
  have hG0V : sgdGain d B pV (2 * B / D) = 4 * (B : ℝ) * ((B : ℝ) - 1) * p1 * pV / D ^ 2 := by
    rw [vv_gain_at_two (d := d) hB pV p1 D (by rw [hD]; ring) hDpos.ne']
    ring
  have hG01 : sgdGain d B p1 (2 * B / D) = 4 * (B : ℝ) * ((B : ℝ) - 1) * p1 * pV / D ^ 2 :=
    vv_gain_at_two (d := d) hB p1 pV D (by rw [hD]; ring) hDpos.ne'
  have hpos : 0 < 4 * (B : ℝ) * ((B : ℝ) - 1) * p1 * pV / D ^ 2 :=
    div_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hb0) hB1) hp1pos) hpV)
      (pow_pos hDpos 2)
  refine ⟨hDpos, hpos, ?_, div_pos (by linarith) hDpos, hG01, hG0V⟩
  rw [← hG0V]
  exact lt_of_le_of_lt (vv_gain_le (d := d) hB hpV _)
    (vv_gain_max_lt_one (d := d) hB hpV (hle.trans hp1))

/-- Case 2, strict form: for `eta != 2B/D_B`, `min (g_1, g_V) < 4B(B-1)p_1p_V/D_B^2`
(`g_V` increases on `eta <= eta*_V` and `g_1` decreases on `eta >= eta*_1`, and
`eta*_1 <= 2B/D_B <= eta*_V`). -/
theorem vv_case2_lt (hB : 0 < B) {p1 pV D : ℝ} (hpV : 0 < pV) (hle : pV ≤ p1)
    (hcase : (d : ℝ) + 2 ≤ ((B : ℝ) - 1) * (p1 - pV))
    (hD : D = (d : ℝ) + 2 + ((B : ℝ) - 1) * (p1 + pV)) (hDpos : 0 < D) {eta : ℝ}
    (hne : eta ≠ 2 * B / D) :
    min (sgdGain d B p1 eta) (sgdGain d B pV eta)
      < 4 * (B : ℝ) * ((B : ℝ) - 1) * p1 * pV / D ^ 2 := by
  have hb1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hb0 : (0 : ℝ) < B := by linarith
  have ha : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hp1pos : 0 < p1 := lt_of_lt_of_le hpV hle
  have hKV := vv_K_pos (d := d) hB hpV.le
  have hK1 := vv_K_pos (d := d) hB hp1pos.le
  have hGV : sgdGain d B pV (2 * B / D) = 4 * (B : ℝ) * ((B : ℝ) - 1) * p1 * pV / D ^ 2 := by
    rw [vv_gain_at_two (d := d) hB pV p1 D (by rw [hD]; ring) hDpos.ne']
    ring
  have hG1 : sgdGain d B p1 (2 * B / D) = 4 * (B : ℝ) * ((B : ℝ) - 1) * p1 * pV / D ^ 2 :=
    vv_gain_at_two (d := d) hB p1 pV D (by rw [hD]; ring) hDpos.ne'
  have he0 : 0 < 2 * (B : ℝ) / D := div_pos (by linarith) hDpos
  have hKVle : 2 * ((d : ℝ) + 2 + ((B : ℝ) - 1) * pV) ≤ D := by rw [hD]; linarith
  have hK1ge : D ≤ 2 * ((d : ℝ) + 2 + ((B : ℝ) - 1) * p1) := by
    rw [hD]
    have := mul_nonneg (sub_nonneg.2 hb1) (sub_nonneg.2 hle)
    linarith
  have hDe : D * (2 * (B : ℝ) / D) = 2 * B := mul_div_cancel₀ _ hDpos.ne'
  have hKVη0 : ((d : ℝ) + 2 + ((B : ℝ) - 1) * pV) * (2 * (B : ℝ) / D) ≤ B := by
    have := mul_le_mul_of_nonneg_right hKVle he0.le
    nlinarith
  have hK1η0 : (B : ℝ) ≤ ((d : ℝ) + 2 + ((B : ℝ) - 1) * p1) * (2 * (B : ℝ) / D) := by
    have := mul_le_mul_of_nonneg_right hK1ge he0.le
    nlinarith
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 := vv_aux_lt hb0 hpV hKV hKVη0 h
    have e := vv_gain_sub (d := d) hB pV (2 * B / D) eta
    calc min (sgdGain d B p1 eta) (sgdGain d B pV eta) ≤ sgdGain d B pV eta := min_le_right _ _
      _ < sgdGain d B pV (2 * B / D) := by linarith
      _ = _ := hGV
  · have h1 := vv_aux_gt hb0 hp1pos hK1 hK1η0 h
    have e := vv_gain_sub (d := d) hB p1 (2 * B / D) eta
    calc min (sgdGain d B p1 eta) (sgdGain d B pV eta) ≤ sgdGain d B p1 eta := min_le_left _ _
      _ < sgdGain d B p1 (2 * B / D) := by linarith
      _ = _ := hG1

/-! #### (V8) The theorems -/

/-- (V8) `v2 lem:helps-vocab (v)`, case `(B-1)(p_1-p_V) <= d+2`: at `beta = 0` the maximum over the
`eta` at which every copy is stable of `Lmin` is `log (1 + B p_V/(d+2-p_V))`, attained at
`eta = etaStar d B p_V` (second conjunct), and `1 <= eta*_V/eta*_j < 2` for every `j` (third
conjunct), so every row is stable at `eta*_V`.  `B >= 1` is `hB : 1 ≤ B`. -/
theorem helps_vocab_v_case1 (hB : 1 ≤ B) (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hcase : ((B : ℝ) - 1) * (pFst - pLst) ≤ (d : ℝ) + 2) :
    IsGreatest (sgdLminSet d B ν ps)
      (Real.log (1 + (B : ℝ) * pLst / ((d : ℝ) + 2 - pLst))) ∧
    (0 < etaStar d B pLst ∧
      (∀ j, stepRadius (copyParams d B ν 0 (etaStar d B pLst) ps j) < 1) ∧
      Lmin d B ν 0 (etaStar d B pLst) ps
        = Real.log (1 + (B : ℝ) * pLst / ((d : ℝ) + 2 - pLst))) ∧
    ∀ j, 1 ≤ etaStar d B pLst / etaStar d B (ps j : ℝ) ∧
      etaStar d B pLst / etaStar d B (ps j : ℝ) < 2 := by
  have hB0 : 0 < B := hB
  have hb1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hb0 : (0 : ℝ) < B := by linarith
  have hV := hp (Fin.last n)
  have hle : pLst ≤ pFst := last_le_ps hanti 0
  have hup := fun eta => (vv_case1_core (d := d) hB0 hV hle hcase eta).1
  have hat := (vv_case1_core (d := d) hB0 hV hle hcase 0).2
  have hKV := vv_K_pos (d := d) hB0 hV.le
  have hGs1 := vv_gain_max_lt_one (d := d) hB0 hV (ps (Fin.last n)).2.2
  have hGs0 : 0 < (B : ℝ) * pLst / ((d : ℝ) + 2 + ((B : ℝ) - 1) * pLst) :=
    div_pos (mul_pos hb0 hV) hKV
  have hval := vv_case1_value (d := d) hB0 hV (ps (Fin.last n)).2.2
  have hη : 0 < etaStar d B pLst := div_pos hb0 hKV
  have hstab : ∀ j, stepRadius (copyParams d B ν 0 (etaStar d B pLst) ps j) < 1 :=
    (vv_stable_iff (d := d) (ν := ν) (beta := 0) hB0 hp hanti hη rfl).2 (by rw [hat]; exact hGs0)
  have hLat : Lmin d B ν 0 (etaStar d B pLst) ps
      = Real.log (1 + (B : ℝ) * pLst / ((d : ℝ) + 2 - pLst)) := by
    rw [vv_Lmin_eq hB0 hp hanti hη rfl, hat, hval]
  refine ⟨⟨⟨etaStar d B pLst, ⟨hη, hstab⟩, hLat⟩, ?_⟩, ⟨hη, hstab, hLat⟩, ?_⟩
  · rintro _ ⟨eta, ⟨hη', _⟩, rfl⟩
    show Lmin d B ν 0 eta ps ≤ _
    rw [vv_Lmin_eq hB0 hp hanti hη' rfl, ← hval]
    exact vv_neg_log_mono (hup eta) hGs1
  · intro j
    have hKj := vv_K_pos (d := d) hB0 (hp j).le
    have e : etaStar d B pLst / etaStar d B (ps j : ℝ)
        = ((d : ℝ) + 2 + ((B : ℝ) - 1) * (ps j : ℝ)) / ((d : ℝ) + 2 + ((B : ℝ) - 1) * pLst) := by
      unfold etaStar
      have hB' : (B : ℝ) ≠ 0 := hb0.ne'
      have h1 := hKV.ne'
      have h2 := hKj.ne'
      generalize (d : ℝ) + 2 + ((B : ℝ) - 1) * pLst = K1 at h1 ⊢
      generalize (d : ℝ) + 2 + ((B : ℝ) - 1) * (ps j : ℝ) = K2 at h2 ⊢
      field_simp
    rw [e]
    have ht0 : 0 ≤ (B : ℝ) - 1 := sub_nonneg.2 hb1
    constructor
    · rw [le_div_iff₀ hKV, one_mul]
      have := mul_le_mul_of_nonneg_left (last_le_ps hanti j) ht0
      linarith
    · rw [div_lt_iff₀ hKV]
      have h3 : ((B : ℝ) - 1) * ((ps j : ℝ) - pLst) ≤ (d : ℝ) + 2 :=
        le_trans (mul_le_mul_of_nonneg_left (by linarith [ps_le_first hanti j]) ht0) hcase
      have ha : (0 : ℝ) < (d : ℝ) + 2 := by positivity
      rcases ht0.eq_or_lt with h0 | h0
      · rw [← h0]; nlinarith
      · have := mul_pos h0 hV
        nlinarith

/-- (V8) `v2 lem:helps-vocab (v)`, case `d + 2 < (B-1)(p_1-p_V)`: the maximum of `Lmin` over the
`eta` at which every copy is stable is `-log (1 - 4B(B-1)p_1p_V/D_B^2)`, attained at
`eta = 2B/D_B` (second conjunct), and `2B/D_B < eta_+(p_j)` for every `j` (third conjunct). -/
theorem helps_vocab_v_case2 (hB : 1 ≤ B) (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hcase : (d : ℝ) + 2 < ((B : ℝ) - 1) * (pFst - pLst)) :
    IsGreatest (sgdLminSet d B ν ps)
      (-Real.log (1 - 4 * (B : ℝ) * ((B : ℝ) - 1) * pFst * pLst / (DB d B ps) ^ 2)) ∧
    (0 < 2 * (B : ℝ) / DB d B ps ∧
      (∀ j, stepRadius (copyParams d B ν 0 (2 * (B : ℝ) / DB d B ps) ps j) < 1) ∧
      Lmin d B ν 0 (2 * (B : ℝ) / DB d B ps) ps
        = -Real.log (1 - 4 * (B : ℝ) * ((B : ℝ) - 1) * pFst * pLst / (DB d B ps) ^ 2)) ∧
    ∀ j, 2 * (B : ℝ) / DB d B ps < criticalRate d B (ps j) 0 := by
  have hB0 : 0 < B := hB
  have hb1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hb0 : (0 : ℝ) < B := by linarith
  have hV := hp (Fin.last n)
  have hle : pLst ≤ pFst := last_le_ps hanti 0
  have hD : DB d B ps = (d : ℝ) + 2 + ((B : ℝ) - 1) * (pFst + pLst) := rfl
  obtain ⟨hDpos, hGs0, hGs1, hη0, hG1, hGV⟩ :=
    vv_case2_facts (d := d) hB0 hV hle (ps 0).2.2 hcase hD
  have hmin : min (sgdGain d B pFst (2 * B / DB d B ps)) (sgdGain d B pLst (2 * B / DB d B ps))
      = 4 * (B : ℝ) * ((B : ℝ) - 1) * pFst * pLst / (DB d B ps) ^ 2 := by
    rw [hG1, hGV, min_self]
  have hstab : ∀ j, stepRadius (copyParams d B ν 0 (2 * (B : ℝ) / DB d B ps) ps j) < 1 :=
    (vv_stable_iff (d := d) (ν := ν) (beta := 0) hB0 hp hanti hη0 rfl).2
      (by rw [hmin]; exact hGs0)
  have hLat : Lmin d B ν 0 (2 * (B : ℝ) / DB d B ps) ps
      = -Real.log (1 - 4 * (B : ℝ) * ((B : ℝ) - 1) * pFst * pLst / (DB d B ps) ^ 2) := by
    rw [vv_Lmin_eq hB0 hp hanti hη0 rfl, hmin]
  refine ⟨⟨⟨2 * (B : ℝ) / DB d B ps, ⟨hη0, hstab⟩, hLat⟩, ?_⟩, ⟨hη0, hstab, hLat⟩, ?_⟩
  · rintro _ ⟨eta, ⟨hη', _⟩, rfl⟩
    show Lmin d B ν 0 eta ps ≤ _
    rw [vv_Lmin_eq hB0 hp hanti hη' rfl]
    refine vv_neg_log_mono ?_ hGs1
    by_cases heq : eta = 2 * (B : ℝ) / DB d B ps
    · rw [heq, hmin]
    · exact (vv_case2_lt (d := d) hB0 hV hle hcase.le hD hDpos heq).le
  · intro j
    have hKj := vv_K_pos (d := d) hB0 (hp j).le
    have hB1 : 0 < (B : ℝ) - 1 := by
      by_contra h
      push Not at h
      have : ((B : ℝ) - 1) * (pFst - pLst) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h (sub_nonneg.2 hle)
      have ha : (0 : ℝ) < (d : ℝ) + 2 := by positivity
      linarith
    have hKjD : (d : ℝ) + 2 + ((B : ℝ) - 1) * (ps j : ℝ) < DB d B ps := by
      rw [hD]
      have h1 := mul_pos hB1 hV
      have h2 := mul_nonneg hB1.le (sub_nonneg.2 (ps_le_first hanti j))
      nlinarith
    unfold criticalRate
    rw [vv_icr_zero hB0, inv_div, div_lt_div_iff₀ hDpos hKj]
    nlinarith

/-- (V8) `v2 lem:helps-vocab (v)`, the threshold: for `p_V <= p_1` (antitone `ps`) and `B >= 1`,
`g_V(eta*_V) <= g_1(eta*_V)` iff `(B-1)(p_1-p_V) <= d+2`.  Moreover, in case 2 the value of
`Lmin` at `eta*_V` is strictly below the maximum of `helps_vocab_v_case2`. -/
theorem helps_vocab_v_threshold (hB : 1 ≤ B) (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) :
    (sgdGain d B pLst (etaStar d B pLst) ≤ sgdGain d B pFst (etaStar d B pLst) ↔
      ((B : ℝ) - 1) * (pFst - pLst) ≤ (d : ℝ) + 2) ∧
    ((d : ℝ) + 2 < ((B : ℝ) - 1) * (pFst - pLst) →
      Lmin d B ν 0 (etaStar d B pLst) ps
        < -Real.log (1 - 4 * (B : ℝ) * ((B : ℝ) - 1) * pFst * pLst / (DB d B ps) ^ 2)) := by
  have hB0 : 0 < B := hB
  have hb1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hb0 : (0 : ℝ) < B := by linarith
  have hV := hp (Fin.last n)
  have hle : pLst ≤ pFst := last_le_ps hanti 0
  have hKV := vv_K_pos (d := d) hB0 hV.le
  have hη : 0 < etaStar d B pLst := div_pos hb0 hKV
  have hD : DB d B ps = (d : ℝ) + 2 + ((B : ℝ) - 1) * (pFst + pLst) := rfl
  have hdiff := vv_gain_diff (d := d) hB0 pFst pLst (etaStar d B pLst)
  -- `2B - eta*_V D_B = B (d+2 - (B-1)(p_1-p_V)) / K_V`
  have hfac : 2 * (B : ℝ) - etaStar d B pLst * ((d : ℝ) + 2 + ((B : ℝ) - 1) * (pFst + pLst))
      = B * ((d : ℝ) + 2 - ((B : ℝ) - 1) * (pFst - pLst))
        / ((d : ℝ) + 2 + ((B : ℝ) - 1) * pLst) := by
    unfold etaStar
    rw [eq_div_iff hKV.ne', sub_mul, div_mul_eq_mul_div, div_mul_cancel₀ _ hKV.ne']
    ring
  have hfac' : sgdGain d B pFst (etaStar d B pLst) - sgdGain d B pLst (etaStar d B pLst)
      = (pFst - pLst) * etaStar d B pLst / ((d : ℝ) + 2 + ((B : ℝ) - 1) * pLst)
        * ((d : ℝ) + 2 - ((B : ℝ) - 1) * (pFst - pLst)) := by
    rw [hdiff, hfac]
    have hB' : (B : ℝ) ≠ 0 := hb0.ne'
    have hK' := hKV.ne'
    generalize (d : ℝ) + 2 + ((B : ℝ) - 1) * pLst = K at hK' ⊢
    field_simp
  have ha : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  refine ⟨?_, fun hcase => ?_⟩
  · rw [← sub_nonneg, hfac']
    rcases (sub_nonneg.2 hle).eq_or_lt with h0 | h0
    · rw [← h0]
      exact ⟨fun _ => by rw [mul_zero]; linarith, fun _ => by simp⟩
    · have hcpos : 0 < (pFst - pLst) * etaStar d B pLst
          / ((d : ℝ) + 2 + ((B : ℝ) - 1) * pLst) := div_pos (mul_pos h0 hη) hKV
      rw [mul_nonneg_iff_of_pos_left hcpos]
      constructor <;> intro h <;> linarith
  · obtain ⟨hDpos, _, hGs1, _, _, _⟩ :=
      vv_case2_facts (d := d) hB0 hV hle (ps 0).2.2 hcase hD
    have hne : etaStar d B pLst ≠ 2 * (B : ℝ) / DB d B ps := by
      intro h
      unfold etaStar at h
      rw [div_eq_div_iff hKV.ne' hDpos.ne', hD] at h
      nlinarith [mul_pos hb0 (sub_pos.2 hcase)]
    rw [vv_Lmin_eq hB0 hp hanti hη rfl]
    exact vv_neg_log_strict (vv_case2_lt (d := d) hB0 hV hle hcase.le hD hDpos hne) hGs1

/-! #### (V9) The v2 bundle -/

/-- (V9) `v2 lem:helps-vocab`, parts (i)-(v), with the v2 sharpenings.  Each part is a universally
quantified implication carrying its own hypotheses (`beta in [0,1)` in (i), (iii); `beta = 0` in
(ii), (iv)(a), (v); `beta in (0,1)` in (iv)(b)):

* (i) `all_stable_iff_lt_min` and `min_critical_eq_first` (uses `External.JuryStability`);
* (ii) `sgd_inv_Lmin_ge_first_v2` (no hypothesis `y < 1`) and `sgd_inv_Lmin_ge_second`;
* (iii) `mom_inv_Lmin_ge_first_v2` (constant `d+2-p_V`, `beta in [0,1)`) and
  `mom_inv_Lmin_ge_second_v2`;
* (iv)(a) `sgd_rhoMax0`, `sgd_Lmin0`, `largeBatch_sgd`; (iv)(b) `copy0_radius_ge_beta`,
  `copy0_radius_eq_beta_iff`, `mom_rhoMax0`, `largeBatch_momentum`;
* (v) `helps_vocab_v_case1`, `helps_vocab_v_case2`, `helps_vocab_v_threshold`.

Not included: the co-scaling-ray clause of (iii) (`helps_vocab_asymptotic`, in `Limits.lean`,
which imports this file). -/
theorem lem_helps_vocab_v2 (jury : External.JuryStability) (hB : 1 ≤ B)
    (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps) :
    -- (i)
    (∀ beta eta : ℝ, 0 ≤ beta → beta < 1 → 0 < eta →
      ((∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) ↔
        eta < min (criticalRate d B (ps 0) beta) (criticalRate d B (ps (Fin.last n)) beta))) ∧
    (∀ beta : ℝ, 0 ≤ beta → beta < 1 → (1 + beta) / (1 - beta) < (B : ℝ) →
      min (criticalRate d B (ps 0) beta) (criticalRate d B (ps (Fin.last n)) beta)
        = criticalRate d B (ps 0) beta) ∧
    -- (ii)
    (∀ beta eta : ℝ, 0 < eta → beta = 0 →
      (∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) →
      ((d : ℝ) + 2 - pLst) / ((B : ℝ) * pLst) - 1 ≤ 1 / Lmin d B ν beta eta ps ∧
        (4 < kappaV ps → kappaV ps / 4 - 1 ≤ 1 / Lmin d B ν beta eta ps)) ∧
    -- (iii)
    (∀ beta eta : ℝ, 0 < eta → 0 ≤ beta → beta < 1 →
      (∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) →
      ((d : ℝ) + 2 - pLst) / (8 * (B : ℝ) * pLst) - 1 ≤ 1 / Lmin d B ν beta eta ps ∧
        (16 < kappaV ps →
          Real.sqrt (kappaV ps) / 4 - 1 ≤ 1 / Lmin d B ν beta eta ps)) ∧
    -- (iv)(a)
    (∀ eta : ℝ, eta = 2 / (pFst + pLst) → 1 < kappaV ps →
      (rhoMax0 0 eta ps = ((kappaV ps - 1) / (kappaV ps + 1)) ^ 2 ∧
        ∀ j, stepRadius (copyParams0 0 eta ps j) < 1) ∧
      (Lmin0 0 eta ps = 2 * Real.log ((kappaV ps + 1) / (kappaV ps - 1)) ∧
        1 / Lmin0 0 eta ps ≤ kappaV ps / 4) ∧
      (Tendsto (fun B' : ℕ => rhoMax d B' ν 0 eta ps) atTop
          (𝓝 (((kappaV ps - 1) / (kappaV ps + 1)) ^ 2)) ∧
        Tendsto (fun B' : ℕ => Lmin d B' ν 0 eta ps) atTop
          (𝓝 (2 * Real.log ((kappaV ps + 1) / (kappaV ps - 1)))) ∧
        (∀ᶠ B' : ℕ in atTop, ∀ j, stepRadius (copyParams d B' ν 0 eta ps j) < 1))) ∧
    -- (iv)(b)
    (∀ beta eta : ℝ, 0 < beta → beta < 1 → 0 ≤ eta → ∀ j : Fin (n + 1),
      beta ≤ stepRadius (copyParams0 beta eta ps j) ∧
        (stepRadius (copyParams0 beta eta ps j) = beta ↔
          (1 - Real.sqrt beta) ^ 2 ≤ eta * (1 - beta) * (ps j : ℝ) ∧
            eta * (1 - beta) * (ps j : ℝ) ≤ (1 + Real.sqrt beta) ^ 2)) ∧
    (∀ beta eta : ℝ, 0 < beta → beta < 1 → 1 < kappaV ps →
      Real.sqrt beta = (Real.sqrt (kappaV ps) - 1) / (Real.sqrt (kappaV ps) + 1) →
      eta * (1 - beta) * pFst = (1 + Real.sqrt beta) ^ 2 →
      ((∀ j, stepRadius (copyParams0 beta eta ps j) = beta) ∧ rhoMax0 beta eta ps = beta ∧
        (∀ j, (copyParams0 beta eta ps j).curvature < 1) ∧
        Lmin0 beta eta ps = -Real.log beta ∧
        1 / Lmin0 beta eta ps ≤ Real.sqrt (kappaV ps) / 4) ∧
      (Tendsto (fun B' : ℕ => rhoMax d B' ν beta eta ps) atTop (𝓝 beta) ∧
        Tendsto (fun B' : ℕ => Lmin d B' ν beta eta ps) atTop (𝓝 (-Real.log beta)) ∧
        (∀ᶠ B' : ℕ in atTop, ∀ j, stepRadius (copyParams d B' ν beta eta ps j) < 1))) ∧
    -- (v)
    (((B : ℝ) - 1) * (pFst - pLst) ≤ (d : ℝ) + 2 →
      IsGreatest (sgdLminSet d B ν ps)
        (Real.log (1 + (B : ℝ) * pLst / ((d : ℝ) + 2 - pLst))) ∧
      (0 < etaStar d B pLst ∧
        (∀ j, stepRadius (copyParams d B ν 0 (etaStar d B pLst) ps j) < 1) ∧
        Lmin d B ν 0 (etaStar d B pLst) ps
          = Real.log (1 + (B : ℝ) * pLst / ((d : ℝ) + 2 - pLst))) ∧
      ∀ j, 1 ≤ etaStar d B pLst / etaStar d B (ps j : ℝ) ∧
        etaStar d B pLst / etaStar d B (ps j : ℝ) < 2) ∧
    ((d : ℝ) + 2 < ((B : ℝ) - 1) * (pFst - pLst) →
      IsGreatest (sgdLminSet d B ν ps)
        (-Real.log (1 - 4 * (B : ℝ) * ((B : ℝ) - 1) * pFst * pLst / (DB d B ps) ^ 2)) ∧
      (0 < 2 * (B : ℝ) / DB d B ps ∧
        (∀ j, stepRadius (copyParams d B ν 0 (2 * (B : ℝ) / DB d B ps) ps j) < 1) ∧
        Lmin d B ν 0 (2 * (B : ℝ) / DB d B ps) ps
          = -Real.log (1 - 4 * (B : ℝ) * ((B : ℝ) - 1) * pFst * pLst / (DB d B ps) ^ 2)) ∧
      ∀ j, 2 * (B : ℝ) / DB d B ps < criticalRate d B (ps j) 0) ∧
    ((sgdGain d B pLst (etaStar d B pLst) ≤ sgdGain d B pFst (etaStar d B pLst) ↔
        ((B : ℝ) - 1) * (pFst - pLst) ≤ (d : ℝ) + 2) ∧
      ((d : ℝ) + 2 < ((B : ℝ) - 1) * (pFst - pLst) →
        Lmin d B ν 0 (etaStar d B pLst) ps
          < -Real.log (1 - 4 * (B : ℝ) * ((B : ℝ) - 1) * pFst * pLst / (DB d B ps) ^ 2))) := by
  have hB0 : 0 < B := hB
  refine ⟨fun beta eta hb0 hb1 hη => all_stable_iff_lt_min jury hB0 hp hanti hb0 hb1 hη,
    fun beta hb0 hb1 hBl => min_critical_eq_first hB0 hanti hb0 hb1 hBl,
    fun beta eta hη hβ hst => ⟨sgd_inv_Lmin_ge_first_v2 hB0 hp hη hβ hst,
      fun hκ => sgd_inv_Lmin_ge_second hB0 hp hη hβ hst hκ⟩,
    fun beta eta hη hb0 hb1 hst => ⟨mom_inv_Lmin_ge_first_v2 hB0 hp hη hb0 hb1 hst,
      fun hκ => mom_inv_Lmin_ge_second_v2 hB0 hp hη hb0 hb1 hst hκ⟩,
    fun eta hη hκ => ⟨sgd_rhoMax0 hp hanti rfl hη, sgd_Lmin0 hp hanti rfl hη hκ,
      largeBatch_sgd hp hanti rfl hη hκ⟩,
    fun beta eta hb0 hb1 hη j => ⟨copy0_radius_ge_beta hη hb0 hb1 hp j,
      copy0_radius_eq_beta_iff hb0 j⟩,
    fun beta eta hb0 hb1 hκ hr hη => ⟨mom_rhoMax0 hp hanti hb0 hb1 hκ hr hη,
      largeBatch_momentum hp hanti hb0 hb1 hκ hr hη⟩,
    fun hc => helps_vocab_v_case1 hB hp hanti hc,
    fun hc => helps_vocab_v_case2 hB hp hanti hc,
    helps_vocab_v_threshold hB hp hanti⟩

end V3

end

end SparseSGD.Scaling.Helps
