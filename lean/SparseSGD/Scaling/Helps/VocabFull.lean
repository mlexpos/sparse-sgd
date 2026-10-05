import SparseSGD.Scaling.Helps.CriticalBatch

/-!
# Full statement of the vocabulary proposition (v2 `prop:vocab_full` = `rem:vocab`)

Paper labels (v2): `prop:vocab_full`, `rem:vocab` (draft block `vocab-full-v2`, appendix
`momentum_helps.tex`, section "Benefits of momentum").

Setup as in `CriticalBatch.lean`: `ps : Fin (n+1) → unitInterval` antitone with every `ps j > 0`,
`κ_V = kappaV ps = p_1/p_V > 1`, `pLast ps = p_V`, `Dv d ps = d + 2 - p_V`.  The crossing batch size
is `B_× = vocabBx d ps = (d+2)/(p_1 - p_V)`, and `E_min = Einf d ν ps sgdClass`.

## Map from the tex to the Lean statements

* Part (i), SGD (W1).
  - `vocab_full_sgd_iff`: SGD runs the rarest token at its own fastest learning rate (the decay rate
    `Lmin` at `η*_V = etaStar d B p_V` is the maximum of `Lmin` over the learning rates at which
    every copy is stable) iff `B - 1 ≤ B_×`.
  - `vocab_full_sgd_S`: then `S_SGD(B) = 1/log(1 + B p_V/(d+2-p_V))`.
  - `vocab_full_per_token`, `vocab_full_per_token_Lambda`: per-token learning rates do not lower `S`:
    the slowest copy has radius at least `(d+2-p_V)/(d+2+(B-1)p_V)` whatever `η_j > 0` is used for
    copy `V`, equivalently `min_j Λ_j ≤ log(1 + B p_V/(d+2-p_V))`.  (Proved from `vv_copy_radius`,
    i.e. the exact `β = 0` radius `1 - g_V(η)` of `lem:helps-sgd` and `g_V ≤ B p_V/K_V`, which is
    the content of `ls_beta_zero_sup` / `sgd_radius_eq`; no stability hypothesis is needed.)
  - The converse sentence of the proof (for `B - 1 > B_×` per-token rates would lower `S`) is not
    part of the statement and is not formalized.
* Part (i), momentum (W2): `vocab_full_momentum`
  (`κ > 16`, `B - 1 ≤ B_×`: `c_κ(κ-1)(d+2-p_V)/(8κ(d+2)) S_SGD(B) ≤ S_mom(B)`).
* Part (i), co-scaling clause (`S_β(B) ≥ S_SGD(B)(1 + o(1))` along a co-scaling ray, `γ > 0`):
  it is `vocab_full_i_coscaling` in `SampleCost` (v2 `cor:sample_cost` (ii), `rem:sgd_cost`), not
  restated here (this file does not import it).
* Part (ii) (W3): `vocab_full_Sinf_le_sgd`, `vocab_full_Sinf_le_mom`, `vocab_full_Sinf_le_fixed`
  (`S_∞ ≤ S(B)` for every `B ≥ 1`), `vocab_full_tendsto_fixed` (limits; the SGD and momentum limits
  are `Sfun_tendsto_Sinf_sgd`, `Sfun_tendsto_Sinf_mom`), `vocab_full_Sbeta_retention`
  (`S_β = 1/log(1/β)` for `κ ≤ κ_β`), `kappaBeta_le_of_delta` (`Δ_β ≤ 1/4 → κ_β ≤ κ`, used for
  the upper bound `S_β ≤ A_β` in the two-sided bound), `vocab_full_Sbeta_two_sided`.
* Part (iii) (W4): `Bcrit_sgd_bounds`, `Bcrit_mom_le_abs`, `Bcrit_mom_ge_abs` of `CriticalBatch.lean`.
* Remark after the proposition (W5): `vocab_full_remark`.
* Bundle (W6): `prop_vocab_full`.

## Hypotheses added to, or differences from, the tex

* `jury : External.JuryStability` is used only for the fixed-`β` statements `S_β = inf_B S_β(B)`
  (nonemptiness of the admissible set at every `B`, as in `prop_helps_critical_v2`), and in the
  remark after the proposition.  The limits `S_β(B) → S_β` need no Jury hypothesis.
* `κ_V > 1` suffices for everything except the momentum lower bounds (`vocab_full_momentum` and
  the lower bound on `B_mom`), which need `κ_V > 16` as in the tex.
* The tex asserts `S_β ≤ A_β` under `Δ_β ≤ 1/4`; this follows from the case `κ ≥ κ_β` because
  `Δ_β ≤ 1/4` implies `κ ≥ κ_β` (`kappaBeta_le_of_delta`, a derived implication, not an added
  hypothesis).
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD SparseSGD.Probability.LeastSquares MeasureTheory Filter
open scoped Topology

noncomputable section

section VocabFull

variable {n : ℕ} {d B : ℕ} {ν : Measure ℝ} {ps : Fin (n + 1) → unitInterval}

/-- The crossing batch size `B_× = (d+2)/(p_max - p_min)` (v2 `prop:vocab_full`). -/
def vocabBx (d : ℕ) (ps : Fin (n + 1) → unitInterval) : ℝ :=
  ((d : ℝ) + 2) / ((ps 0 : ℝ) - (ps (Fin.last n) : ℝ))

/-- `B - 1 ≤ B_×` is the case-1 condition `(B-1)(p_1-p_V) ≤ d+2` of `lem:helps-vocab` (v). -/
theorem le_vocabBx_iff (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) :
    (B : ℝ) - 1 ≤ vocabBx d ps ↔
      ((B : ℝ) - 1) * ((ps 0 : ℝ) - (ps (Fin.last n) : ℝ)) ≤ (d : ℝ) + 2 := by
  have h := kappaV_gt_one_lt hp hκ
  have hpos : 0 < (ps 0 : ℝ) - (ps (Fin.last n) : ℝ) := by linarith
  unfold vocabBx
  rw [le_div_iff₀ hpos]

/-! ### Part (i), SGD -/

/-- v2 `prop:vocab_full` (i), SGD, first sentence: the decay rate at the rarest token's own
fastest learning rate `η*_V` is the maximum of `Lmin` over the learning rates at which every copy
is stable if and only if `B - 1 ≤ B_×`. -/
theorem vocab_full_sgd_iff (hB : 1 ≤ B) (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hκ : 1 < kappaV ps) :
    IsGreatest (sgdLminSet d B ν ps)
        (Lmin d B ν 0 (etaStar d B (ps (Fin.last n) : ℝ)) ps) ↔
      (B : ℝ) - 1 ≤ vocabBx d ps := by
  rw [le_vocabBx_iff hp hκ]
  constructor
  · intro hmax
    by_contra hcase
    push Not at hcase
    have h2 := helps_vocab_v_case2 (d := d) (ν := ν) hB hp hanti hcase
    have hlt := (helps_vocab_v_threshold (d := d) (ν := ν) hB hp hanti).2 hcase
    have hge := hmax.2 h2.1.1
    linarith
  · intro hcase
    obtain ⟨hgr, ⟨-, -, hL⟩, -⟩ := helps_vocab_v_case1 (d := d) (ν := ν) hB hp hanti hcase
    rw [hL]
    exact hgr

/-- v2 `prop:vocab_full` (i), SGD, second sentence: for `B - 1 ≤ B_×`,
`S_SGD(B) = 1/log(1 + B p_V/(d+2-p_V))`. -/
theorem vocab_full_sgd_S (hB : 1 ≤ B) (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hκ : 1 < kappaV ps) (hBx : (B : ℝ) - 1 ≤ vocabBx d ps) :
    Sfun d B ν ps sgdClass
      = 1 / Real.log (1 + (B : ℝ) * (ps (Fin.last n) : ℝ)
          / ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))) :=
  Sfun_sgd_eq_of_le_Bx hB hp hanti ((le_vocabBx_iff hp hκ).1 hBx)

/-- v2 `prop:vocab_full` (i), per-token learning rates: whatever positive learning rate `η_V` is
used for the rarest copy, the slowest copy has radius at least `(d+2-p_V)/(d+2+(B-1)p_V)`.  Only
`0 < η_V` is assumed (stability of the copies is not needed: an unstable copy has radius `≥ 1`,
and the radius of the stable copy `V` is `1 - g_V(η_V)` with `g_V ≤ B p_V/K_V`). -/
theorem vocab_full_per_token (hB : 1 ≤ B) (hp : ∀ j, 0 < (ps j : ℝ))
    (η : Fin (n + 1) → ℝ) (hη : 0 < η (Fin.last n)) :
    ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))
        / ((d : ℝ) + 2 + ((B : ℝ) - 1) * (ps (Fin.last n) : ℝ))
      ≤ Finset.univ.sup' Finset.univ_nonempty
          (fun j => stepRadius (copyParams d B ν 0 (η j) ps j)) := by
  have hB0 : 0 < B := hB
  have hpV := hp (Fin.last n)
  have hK := vv_K_pos (d := d) hB0 hpV.le
  refine le_trans ?_ (Finset.le_sup' (fun j => stepRadius (copyParams d B ν 0 (η j) ps j))
    (Finset.mem_univ (Fin.last n)))
  show _ ≤ stepRadius (copyParams d B ν 0 (η (Fin.last n)) ps (Fin.last n))
  rw [vv_copy_radius (d := d) (ν := ν) hB0 hp hη rfl (Fin.last n)]
  have hg := vv_gain_le (d := d) hB0 hpV (η (Fin.last n))
  have e : ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))
        / ((d : ℝ) + 2 + ((B : ℝ) - 1) * (ps (Fin.last n) : ℝ))
      = 1 - (B : ℝ) * (ps (Fin.last n) : ℝ)
          / ((d : ℝ) + 2 + ((B : ℝ) - 1) * (ps (Fin.last n) : ℝ)) := by
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hK.ne']
    ring
  rw [e]
  linarith

/-- v2 `prop:vocab_full` (i), per-token learning rates, in terms of the decay rates
`Λ_j = -log(radius_j)`: `min_j Λ_j ≤ log(1 + B p_V/(d+2-p_V))`. -/
theorem vocab_full_per_token_Lambda (hB : 1 ≤ B) (hp : ∀ j, 0 < (ps j : ℝ))
    (η : Fin (n + 1) → ℝ) (hη : 0 < η (Fin.last n)) :
    Finset.univ.inf' Finset.univ_nonempty
        (fun j => -Real.log (stepRadius (copyParams d B ν 0 (η j) ps j)))
      ≤ Real.log (1 + (B : ℝ) * (ps (Fin.last n) : ℝ)
          / ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))) := by
  have hB0 : 0 < B := hB
  have hpV := hp (Fin.last n)
  have hK := vv_K_pos (d := d) hB0 hpV.le
  refine le_trans (Finset.inf'_le (fun j => -Real.log (stepRadius (copyParams d B ν 0 (η j) ps j)))
    (Finset.mem_univ (Fin.last n))) ?_
  show -Real.log (stepRadius (copyParams d B ν 0 (η (Fin.last n)) ps (Fin.last n))) ≤ _
  rw [← vv_case1_value (d := d) hB0 hpV (ps (Fin.last n)).2.2]
  have hy := vv_gain_max_lt_one (d := d) hB0 hpV (ps (Fin.last n)).2.2
  have hr : 1 - (B : ℝ) * (ps (Fin.last n) : ℝ)
        / ((d : ℝ) + 2 + ((B : ℝ) - 1) * (ps (Fin.last n) : ℝ))
      ≤ stepRadius (copyParams d B ν 0 (η (Fin.last n)) ps (Fin.last n)) := by
    rw [vv_copy_radius (d := d) (ν := ν) hB0 hp hη rfl (Fin.last n)]
    have := vv_gain_le (d := d) hB0 hpV (η (Fin.last n))
    linarith
  have := Real.log_le_log (by linarith) hr
  linarith

/-! ### Part (i), momentum -/

/-- v2 `prop:vocab_full` (i), momentum: for `κ_V > 16` and `B - 1 ≤ B_×`,
`c_κ(κ-1)(d+2-p_V)/(8κ(d+2)) · S_SGD(B) ≤ S_mom(B)`, `c_κ = max(1 - 4/√κ, 1/√5)`. -/
theorem vocab_full_momentum (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hκ : 16 < kappaV ps) (hB : 1 ≤ B) (hBx : (B : ℝ) - 1 ≤ vocabBx d ps) :
    max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * (kappaV ps - 1)
        * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))
        / (8 * kappaV ps * ((d : ℝ) + 2)) * Sfun d B ν ps sgdClass
      ≤ Sfun d B ν ps momClass := by
  have hκ1 : 1 < kappaV ps := by linarith
  have hB0 : 0 < B := hB
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB0
  have hpV := hp (Fin.last n)
  have hcase := (le_vocabBx_iff hp hκ1).1 hBx
  have hK := vv_K_pos (d := d) hB0 hpV.le
  have hD := vv_D_pos (d := d) (ps (Fin.last n))
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set pV : ℝ := (ps (Fin.last n) : ℝ) with hpVdef
  set p0 : ℝ := (ps 0 : ℝ) with hp0def
  set K : ℝ := (d : ℝ) + 2 + ((B : ℝ) - 1) * pV with hKdef
  set c : ℝ := max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) with hcdef
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  set κ : ℝ := kappaV ps with hκdef
  -- (1) the SGD side
  have hy0 : 0 < (B : ℝ) * pV / K := by positivity
  have hy1 : (B : ℝ) * pV / K < 1 := vv_gain_max_lt_one (d := d) hB0 hpV (ps (Fin.last n)).2.2
  have hS : Sfun d B ν ps sgdClass ≤ K / ((B : ℝ) * pV) := by
    rw [vocab_full_sgd_S hB hp hanti hκ1 hBx, ← vv_case1_value (d := d) hB0 hpV
      (ps (Fin.last n)).2.2]
    have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - (B : ℝ) * pV / K)
    have h1 : (B : ℝ) * pV / K ≤ -Real.log (1 - (B : ℝ) * pV / K) := by linarith
    calc 1 / -Real.log (1 - (B : ℝ) * pV / K) ≤ 1 / ((B : ℝ) * pV / K) :=
          one_div_le_one_div_of_le hy0 h1
      _ = K / ((B : ℝ) * pV) := one_div_div _ _
  -- (2) the momentum side
  have hE : c * ((d : ℝ) + 2 - pV) / (8 * pV) ≤ (B : ℝ) * Sfun d B ν ps momClass :=
    Efun_mom_ge' (d := d) (ν := ν) hp hκ hB
  have hM : c * ((d : ℝ) + 2 - pV) / (8 * pV * B) ≤ Sfun d B ν ps momClass := by
    rw [div_le_iff₀ (by positivity)]
    have : c * ((d : ℝ) + 2 - pV) / (8 * pV) * 8 * pV = c * ((d : ℝ) + 2 - pV) := by
      field_simp
    nlinarith [hE]
  -- (3) the key inequality `(κ-1) K ≤ κ (d+2)`
  have hκpV : (κ - 1) * pV = p0 - pV := by
    rw [hκdef, kappaV]
    change (p0 / pV - 1) * pV = p0 - pV
    field_simp
  have hkey : (κ - 1) * K ≤ κ * ((d : ℝ) + 2) := by
    have e1 : (κ - 1) * K = (κ - 1) * ((d : ℝ) + 2) + ((B : ℝ) - 1) * ((κ - 1) * pV) := by
      rw [hKdef]; ring
    rw [e1, hκpV]
    nlinarith [hcase]
  have hκ0 : 0 < κ := by linarith
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by linarith
  calc c * (κ - 1) * ((d : ℝ) + 2 - pV) / (8 * κ * ((d : ℝ) + 2)) * Sfun d B ν ps sgdClass
      ≤ c * (κ - 1) * ((d : ℝ) + 2 - pV) / (8 * κ * ((d : ℝ) + 2)) * (K / ((B : ℝ) * pV)) :=
        mul_le_mul_of_nonneg_left hS (by
          have : 0 < κ - 1 := by linarith
          positivity)
    _ = c * ((d : ℝ) + 2 - pV) / (8 * pV * B) * ((κ - 1) * K / (κ * ((d : ℝ) + 2))) := by
        field_simp
    _ ≤ c * ((d : ℝ) + 2 - pV) / (8 * pV * B) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_one (by positivity)]
        exact hkey
    _ ≤ Sfun d B ν ps momClass := by rw [mul_one]; exact hM

/-! ### Part (ii) -/

/-- v2 `prop:vocab_full` (ii), SGD: `S_∞ ≤ S_SGD(B)` for every `B ≥ 1`. -/
theorem vocab_full_Sinf_le_sgd (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) (hB : 1 ≤ B) :
    Sinf d ν ps sgdClass ≤ Sfun d B ν ps sgdClass :=
  Sinf_le hp hκ sgdClass_sub zero_mem_sgdClass hB

/-- v2 `prop:vocab_full` (ii), momentum: `S_∞ ≤ S_mom(B)` for every `B ≥ 1`. -/
theorem vocab_full_Sinf_le_mom (hp : ∀ j, 0 < (ps j : ℝ)) (hκ : 1 < kappaV ps) (hB : 1 ≤ B) :
    Sinf d ν ps momClass ≤ Sfun d B ν ps momClass :=
  Sinf_le hp hκ momClass_sub zero_mem_momClass hB

/-- v2 `prop:vocab_full` (ii), fixed `β ∈ [0,1)` (Jury): `S_∞ = S_β ≤ S_β(B)` for every `B ≥ 1`. -/
theorem vocab_full_Sinf_le_fixed (jury : External.JuryStability) (hp : ∀ j, 0 < (ps j : ℝ))
    (hanti : Antitone ps) (hκ : 1 < kappaV ps) (hB : 1 ≤ B) {β : ℝ} (hb0 : 0 ≤ β)
    (hb1 : β < 1) :
    Sinf d ν ps {β} ≤ Sfun d B ν ps {β} := by
  rw [Sinf_fixed_eq jury hp hanti hκ hb0 hb1]
  exact Sfun_fixed_ge jury hp hanti hκ hB hb0 hb1

/-- v2 `prop:vocab_full` (ii), fixed `β ∈ [0,1)` (Jury): `S_β(B) → S_∞` as `B → ∞`. -/
theorem vocab_full_tendsto_fixed (jury : External.JuryStability) (hp : ∀ j, 0 < (ps j : ℝ))
    (hanti : Antitone ps) (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1) :
    Tendsto (fun B : ℕ => Sfun d B ν ps {β}) atTop (𝓝 (Sinf d ν ps {β})) := by
  rw [Sinf_fixed_eq jury hp hanti hκ hb0 hb1]
  exact Sfun_fixed_tendsto hp hanti hκ hb0 hb1

/-- `κ_0 = 1`, so `κ ≤ κ_β` forces `β > 0` when `κ > 1`. -/
theorem kappaBeta_zero : kappaBeta 0 = 1 := by
  unfold kappaBeta
  simp

/-- v2 `prop:vocab_full` (ii), fixed `β`: if `κ_V ≤ κ_β` then `S_β = 1/log(1/β)` (the retention
cap; `0 < β` is forced because `κ_0 = 1 < κ_V`). -/
theorem vocab_full_Sbeta_retention (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1)
    (h : kappaV ps ≤ kappaBeta β) :
    Sbeta ps β = 1 / Real.log (1 / β) := by
  have hβ : 0 < β := by
    rcases hb0.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      rw [← h', kappaBeta_zero] at h
      linarith
  have hr : rhoBeta ps β = Real.sqrt β := (rhoBeta_eq_sqrt_iff hκ hβ hb1).2 h
  unfold Sbeta
  rw [hr, Real.log_sqrt hβ.le, one_div β, Real.log_inv]
  have hlog : Real.log β < 0 := Real.log_neg hβ hb1
  field_simp

/-- `Δ_β ≤ 1/4` implies `κ_V ≥ κ_β` (so the upper bound `S_β ≤ A_β` of the case `κ ≥ κ_β` also
holds under `Δ_β ≤ 1/4`, as the tex states). -/
theorem kappaBeta_le_of_delta (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1)
    (hΔ : DeltaBeta ps β ≤ 1 / 4) : kappaBeta β ≤ kappaV ps := by
  have h2 := two_sqrt_le_t_of_delta hκ hb0 hb1 (by unfold DeltaBeta at hΔ; exact hΔ)
  rw [one_add_sub_wStar hκ] at h2
  have hs0 := Real.sqrt_nonneg β
  have hs2 : Real.sqrt β ^ 2 = β := Real.sq_sqrt hb0
  have hs1 : Real.sqrt β < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hb0 hb1
  have h1s : 0 < 1 - Real.sqrt β := by linarith
  have hk1 : 0 < kappaV ps + 1 := by linarith
  rw [le_div_iff₀ hk1] at h2
  unfold kappaBeta
  rw [div_pow, div_le_iff₀ (by positivity)]
  set s := Real.sqrt β
  rw [← hs2] at h2
  nlinarith

/-- v2 `prop:vocab_full` (ii), fixed `β` with `Δ_β ≤ 1/4`: `½(1+√(1-4Δ_β)) A_β ≤ S_β ≤ A_β`. -/
theorem vocab_full_Sbeta_two_sided (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1)
    (hΔ : DeltaBeta ps β ≤ 1 / 4) :
    1 / 2 * (1 + Real.sqrt (1 - 4 * DeltaBeta ps β)) * ABeta ps β ≤ Sbeta ps β ∧
      Sbeta ps β ≤ ABeta ps β :=
  ⟨Sbeta_ge hκ hb0 hb1 hΔ, Sbeta_le_A hκ hb0 hb1 (kappaBeta_le_of_delta hκ hb0 hb1 hΔ)⟩

/-- v2 `prop:vocab_full` (ii), momentum: `S_mom = min_β S_β`, attained at Polyak's `β_P`. -/
theorem vocab_full_Sinf_mom_min (hp : ∀ j, 0 < (ps j : ℝ)) (hanti : Antitone ps)
    (hκ : 1 < kappaV ps) :
    IsLeast (Sbeta ps '' Set.Ico (0 : ℝ) 1) (Sinf d ν ps momClass) ∧
      Sbeta ps (betaPolyak ps) = Sinf d ν ps momClass := by
  rw [Sinf_mom hp hanti hκ]
  exact ⟨Sbeta_isLeast hκ, Sbeta_polyak hκ⟩

/-! ### Remark after the proposition -/

/-- v2 `prop:vocab_full`, remark after the proof: at fixed `β` with `κ_V ≥ κ_β` (Jury),
`E_min/S_β ≥ 4(d+2-p_V)(1+β)/((1-β)(p_1+p_V))`, with `E_min = E_SGD` and `S_β = S_∞`. -/
theorem vocab_full_remark (jury : External.JuryStability) (hp : ∀ j, 0 < (ps j : ℝ))
    (hanti : Antitone ps) (hκ : 1 < kappaV ps) {β : ℝ} (hb0 : 0 ≤ β) (hb1 : β < 1)
    (hκβ : kappaBeta β ≤ kappaV ps) :
    4 * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) * (1 + β)
        / ((1 - β) * ((ps 0 : ℝ) + (ps (Fin.last n) : ℝ)))
      ≤ Einf d ν ps sgdClass / Sinf d ν ps {β} := by
  rw [Sinf_fixed_eq jury hp hanti hκ hb0 hb1, Einf_sgd hp hanti hκ]
  have hpV := hp (Fin.last n)
  have hE : ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) / (ps (Fin.last n) : ℝ) ≤ Esgd1 d ps :=
    (Esgd1_bounds d ps hpV).1
  have hE0 : 0 ≤ Esgd1 d ps :=
    le_trans (div_nonneg (by have := vv_D_pos (d := d) (ps (Fin.last n)); linarith) hpV.le) hE
  have hSpos := Sbeta_pos hκ hb0 hb1 (ps := ps)
  have hSA := Sbeta_le_A hκ hb0 hb1 hκβ
  have hA : 0 < ABeta ps β := lt_of_lt_of_le hSpos hSA
  have hid : 4 * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) * (1 + β)
        / ((1 - β) * ((ps 0 : ℝ) + (ps (Fin.last n) : ℝ)))
      = (((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) / (ps (Fin.last n) : ℝ)) / ABeta ps β := by
    unfold ABeta kappaV
    have h1 : (1 - β) ≠ 0 := by linarith
    have h2 : (1 + β) ≠ 0 := by linarith
    have h3 : (0 : ℝ) < (ps 0 : ℝ) := hp 0
    have h4 : (ps (Fin.last n) : ℝ) ≠ 0 := hpV.ne'
    have h5 : (ps 0 : ℝ) + (ps (Fin.last n) : ℝ) ≠ 0 := by linarith
    field_simp
  rw [hid]
  exact div_le_div₀ hE0 hE hSpos hSA

/-! ### The bundle -/

/-- v2 `prop:vocab_full` = `rem:vocab`, all parts and the remark, for `κ_V > 16` and
`External.JuryStability` (Jury is used only for the fixed-`β` clauses of (ii) and for the remark;
`κ_V > 16` only for the momentum lower bounds of (i) and (iii); the rest holds for `κ_V > 1`).
The co-scaling clause of (i) (`S_β(B) ≥ S_SGD(B)(1+o(1))` along a co-scaling ray with `γ > 0`) is
`vocab_full_i_coscaling` in `SampleCost` and is not part of this bundle.

* (i): `vocab_full_sgd_iff`, `vocab_full_sgd_S`, `vocab_full_per_token` (with
  `vocab_full_per_token_Lambda`), `vocab_full_momentum`;
* (ii): `S_∞ ≤ S(B)` and `S(B) → S_∞` for SGD, momentum and every fixed `β`, the values and bounds
  of `S_∞` (SGD; fixed `β`: the retention cap `1/log(1/β)` for `κ ≤ κ_β`, the `A_β` bounds for
  `Δ_β ≤ 1/4`; momentum: `S_mom = min_β S_β`, attained at `β_P`);
* (iii): the bounds on `B_SGD` and `B_mom`;
* the remark: `E_min/S_β ≥ 4(d+2-p_V)(1+β)/((1-β)(p_1+p_V))` for `κ ≥ κ_β`. -/
theorem prop_vocab_full (jury : External.JuryStability) (hp : ∀ j, 0 < (ps j : ℝ))
    (hanti : Antitone ps) (hκ : 16 < kappaV ps) :
    -- (i)
    ((∀ B : ℕ, 1 ≤ B →
        (IsGreatest (sgdLminSet d B ν ps)
            (Lmin d B ν 0 (etaStar d B (ps (Fin.last n) : ℝ)) ps) ↔
          (B : ℝ) - 1 ≤ vocabBx d ps)) ∧
      (∀ B : ℕ, 1 ≤ B → (B : ℝ) - 1 ≤ vocabBx d ps →
        Sfun d B ν ps sgdClass
          = 1 / Real.log (1 + (B : ℝ) * (ps (Fin.last n) : ℝ)
              / ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)))) ∧
      (∀ B : ℕ, 1 ≤ B → ∀ η : Fin (n + 1) → ℝ, 0 < η (Fin.last n) →
        ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))
            / ((d : ℝ) + 2 + ((B : ℝ) - 1) * (ps (Fin.last n) : ℝ))
          ≤ Finset.univ.sup' Finset.univ_nonempty
              (fun j => stepRadius (copyParams d B ν 0 (η j) ps j)) ∧
        Finset.univ.inf' Finset.univ_nonempty
            (fun j => -Real.log (stepRadius (copyParams d B ν 0 (η j) ps j)))
          ≤ Real.log (1 + (B : ℝ) * (ps (Fin.last n) : ℝ)
              / ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)))) ∧
      (∀ B : ℕ, 1 ≤ B → (B : ℝ) - 1 ≤ vocabBx d ps →
        max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5) * (kappaV ps - 1)
            * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))
            / (8 * kappaV ps * ((d : ℝ) + 2)) * Sfun d B ν ps sgdClass
          ≤ Sfun d B ν ps momClass)) ∧
    -- (ii), SGD
    ((∀ B : ℕ, 1 ≤ B → Sinf d ν ps sgdClass ≤ Sfun d B ν ps sgdClass) ∧
      Tendsto (fun B : ℕ => Sfun d B ν ps sgdClass) atTop (𝓝 (Sinf d ν ps sgdClass)) ∧
      Sinf d ν ps sgdClass = 1 / (2 * Real.log ((kappaV ps + 1) / (kappaV ps - 1))) ∧
      kappaV ps / 4 * (1 - 1 / kappaV ps ^ 2) ≤ Sinf d ν ps sgdClass ∧
      Sinf d ν ps sgdClass ≤ kappaV ps / 4) ∧
    -- (ii), fixed β
    (∀ β : ℝ, 0 ≤ β → β < 1 →
      ((∀ B : ℕ, 1 ≤ B → Sinf d ν ps {β} ≤ Sfun d B ν ps {β}) ∧
        Tendsto (fun B : ℕ => Sfun d B ν ps {β}) atTop (𝓝 (Sinf d ν ps {β})) ∧
        Sinf d ν ps {β} = Sbeta ps β ∧
        (kappaV ps ≤ kappaBeta β → Sinf d ν ps {β} = 1 / Real.log (1 / β)) ∧
        (kappaBeta β ≤ kappaV ps → Sinf d ν ps {β} ≤ ABeta ps β) ∧
        (DeltaBeta ps β ≤ 1 / 4 →
          1 / 2 * (1 + Real.sqrt (1 - 4 * DeltaBeta ps β)) * ABeta ps β ≤ Sinf d ν ps {β} ∧
            Sinf d ν ps {β} ≤ ABeta ps β) ∧
        (kappaBeta β ≤ kappaV ps →
          4 * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) * (1 + β)
              / ((1 - β) * ((ps 0 : ℝ) + (ps (Fin.last n) : ℝ)))
            ≤ Einf d ν ps sgdClass / Sinf d ν ps {β}))) ∧
    -- (ii), tuned momentum
    ((∀ B : ℕ, 1 ≤ B → Sinf d ν ps momClass ≤ Sfun d B ν ps momClass) ∧
      Tendsto (fun B : ℕ => Sfun d B ν ps momClass) atTop (𝓝 (Sinf d ν ps momClass)) ∧
      Sinf d ν ps momClass
        = 1 / (2 * Real.log ((Real.sqrt (kappaV ps) + 1) / (Real.sqrt (kappaV ps) - 1))) ∧
      Real.sqrt (kappaV ps) / 4 * (1 - 1 / kappaV ps) ≤ Sinf d ν ps momClass ∧
      Sinf d ν ps momClass ≤ Real.sqrt (kappaV ps) / 4 ∧
      IsLeast (Sbeta ps '' Set.Ico (0 : ℝ) 1) (Sinf d ν ps momClass) ∧
      Sbeta ps (betaPolyak ps) = Sinf d ν ps momClass) ∧
    -- (iii)
    (4 * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) / (ps 0 : ℝ) ≤ Bcrit d ν ps sgdClass ∧
      Bcrit d ν ps sgdClass
        ≤ kappaV ps ^ 2 / (kappaV ps ^ 2 - 1) * (4 * ((d : ℝ) + 2) / (ps 0 : ℝ)) ∧
      Bcrit d ν ps momClass
        ≤ kappaV ps / (kappaV ps - 1)
          * (4 * ((d : ℝ) + 2) / Real.sqrt ((ps 0 : ℝ) * (ps (Fin.last n) : ℝ))) ∧
      max (1 - 4 / Real.sqrt (kappaV ps)) (1 / Real.sqrt 5)
          * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))
          / (2 * Real.sqrt ((ps 0 : ℝ) * (ps (Fin.last n) : ℝ)))
        ≤ Bcrit d ν ps momClass) := by
  have hκ1 : 1 < kappaV ps := by linarith
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := helps_critical_i (d := d) (ν := ν) hp hanti hκ1
  obtain ⟨c1, c2⟩ := helps_critical_iii_sgd (d := d) (ν := ν) hp hanti hκ1
  refine ⟨⟨fun B hB => vocab_full_sgd_iff hB hp hanti hκ1,
      fun B hB hBx => vocab_full_sgd_S hB hp hanti hκ1 hBx,
      fun B hB η hη => ⟨vocab_full_per_token hB hp η hη, vocab_full_per_token_Lambda hB hp η hη⟩,
      fun B hB hBx => vocab_full_momentum hp hanti hκ hB hBx⟩,
    ⟨fun B hB => vocab_full_Sinf_le_sgd hp hκ1 hB, Sfun_tendsto_Sinf_sgd hp hanti hκ1,
      a1, a3, a4⟩,
    fun β hb0 hb1 => ⟨fun B hB => vocab_full_Sinf_le_fixed jury hp hanti hκ1 hB hb0 hb1,
      vocab_full_tendsto_fixed jury hp hanti hκ1 hb0 hb1,
      Sinf_fixed_eq jury hp hanti hκ1 hb0 hb1,
      fun h => by
        rw [Sinf_fixed_eq jury hp hanti hκ1 hb0 hb1]
        exact vocab_full_Sbeta_retention hκ1 hb0 hb1 h,
      fun h => by
        rw [Sinf_fixed_eq jury hp hanti hκ1 hb0 hb1]
        exact Sbeta_le_A hκ1 hb0 hb1 h,
      fun h => by
        rw [Sinf_fixed_eq jury hp hanti hκ1 hb0 hb1]
        exact vocab_full_Sbeta_two_sided hκ1 hb0 hb1 h,
      fun h => vocab_full_remark jury hp hanti hκ1 hb0 hb1 h⟩,
    ⟨fun B hB => vocab_full_Sinf_le_mom hp hκ1 hB, Sfun_tendsto_Sinf_mom hp hanti hκ1,
      a2, a5, a6, (vocab_full_Sinf_mom_min hp hanti hκ1).1,
      (vocab_full_Sinf_mom_min hp hanti hκ1).2⟩,
    ⟨c1, c2, Bcrit_mom_le_abs hp hanti hκ1, Bcrit_mom_ge_abs hp hanti hκ⟩⟩

end VocabFull

end

end SparseSGD.Scaling.Helps
