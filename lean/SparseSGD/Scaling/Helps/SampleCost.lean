import SparseSGD.Scaling.Helps.SmallDelta
import SparseSGD.Scaling.Helps.SampleCostAbove
import SparseSGD.Scaling.Helps.CriticalBatch

/-!
# Sample cost: the case `s → ∞`, uniformity in `s`, and the vocabulary co-scaling clauses (v2)

Paper labels (v2): `cor:sample_cost = cor:samplecost` (ii), `rem:sgd_cost`, `lem:helps-vocab` (iii)
(last claim), `prop:vocab_full` (i) (last clause).

Notation: `s = lsNu d B p β`, `ε = 1 - β`, `N_1 = lsNfold`, `N = hyperbolaN (lsNstab) (lsNmem)`.

* (C1) `samplecost_below`: the case `s → ∞` in uniform form (`s ≥ 100`, `ε ≤ 1/50`), from
  `lem:small_delta` (`lsRate_small_delta`).
* (C2) `cor_sample_cost_uniform`: `|N_1/N - 1| ≤ δ` as soon as `ε ≤ ε₀(δ)`, uniformly in
  all `s ∈ (0, ∞)` (and in `d, B, p, ν`).
* (C3) `cor_sample_cost_tendsto`: `N_1/N → 1` along every sequence with `ε_n → 0+`.
* (C4) `samplecost_ge_max_uniform`, `samplecost_ge_sgd_uniform` (`rem:sgd_cost`).
* (C5) `helps_vocab_iii_coscaling`: the last claim of `lem:helps-vocab` (iii).
* (C6) `vocab_full_i_coscaling`: the last clause of `prop:vocab_full` (i).
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD SparseSGD.Probability.LeastSquares MeasureTheory

noncomputable section

/-! ### (C1) the case `s → ∞` -/

section C1

variable {d B : ℕ} {p : unitInterval} {beta : ℝ}

/-- `lem:small_delta` along the ray, for `s ≥ 100`: for every `η ∈ (0, η_+)`, `Δ = η p/ε` lies in
`(0, 2/s)`, the total feedback is `s Δ/2`, and
`|Λ(η) - ε (2Δ - sΔ²)| ≤ 25 (ε + Δ) · ε (2Δ - sΔ²)`. -/
theorem lsRate_ray_approx (ν : Measure ℝ) (hB : 0 < B) (hp : 0 < (p : ℝ)) (he : 0 < 1 - beta)
    (he50 : 1 - beta ≤ 1 / 50) (hs : 100 ≤ lsNu d B p beta) {eta : ℝ}
    (heta : eta ∈ Set.Ioo 0 (criticalRate d B p beta)) :
    0 < eta * p / (1 - beta) ∧ eta * p / (1 - beta) < 2 / lsNu d B p beta ∧
      |lsRate d B p ν beta eta
          - (1 - beta) * (2 * (eta * p / (1 - beta))
            - lsNu d B p beta * (eta * p / (1 - beta)) ^ 2)|
        ≤ 25 * ((1 - beta) + eta * p / (1 - beta))
          * ((1 - beta) * (2 * (eta * p / (1 - beta))
            - lsNu d B p beta * (eta * p / (1 - beta)) ^ 2)) := by
  have hb1 : beta < 1 := by linarith
  have hb0 : 0 ≤ beta := by linarith
  have hnu := lsNu_pos (d := d) (B := B) (p := p) hB hb0 hb1 hp
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ, Δ = eta * p / (1 - beta) := ⟨_, rfl⟩
  rw [← hΔ]
  have hmem : Δ ∈ Set.Ioo 0 (2 / lsNu d B p beta) := by
    rw [← ls_Delta_image hB hb0 hb1 hp]
    exact ⟨eta, heta, hΔ.symm⟩
  have h2s : 2 / lsNu d B p beta ≤ 1 / 50 := by
    rw [div_le_iff₀ hnu]; linarith
  have hΔs : Δ * lsNu d B p beta < 2 := (lt_div_iff₀ hnu).1 hmem.2
  have hηp : eta * p = (1 - beta) * Δ := by rw [hΔ]; field_simp
  have hu : lsNu d B p beta * Δ / 2 = eta / criticalRate d B p beta := by
    have h1 := params_totalLoad_ray (d := d) (B := B) (p := p) hB hb0 hb1 hp ν eta
    have h2 := params_totalLoad d B p hp.ne' ν beta eta
    have h3 : eta / criticalRate d B p beta = eta * inverseCriticalRate d B p beta := by
      unfold criticalRate; rw [div_inv_eq_mul]
    rw [h3, ← h2, h1, ← hΔ]
  have hu1 : lsNu d B p beta * Δ / 2 < 1 := by linarith
  have hmain := lsRate_small_delta (d := d) (B := B) (p := p) (beta := beta) ν hB hp
    (eps := 1 - beta) (Delta := Δ) (u := lsNu d B p beta * Δ / 2) (eta := eta) rfl he he50
    heta.1 hΔ (hmem.2.le.trans h2s) hu hu1
  have key : 2 * eta * p * (1 - lsNu d B p beta * Δ / 2)
      = (1 - beta) * (2 * Δ - lsNu d B p beta * Δ ^ 2) := by
    have : 2 * eta * p * (1 - lsNu d B p beta * Δ / 2)
        = 2 * (eta * p) * (1 - lsNu d B p beta * Δ / 2) := by ring
    rw [this, hηp]; ring
  rw [key] at hmain
  exact ⟨hmem.1, hmem.2, hmain⟩

/-- The scalar `2Δ - sΔ²` is nonnegative and at most `1/s` on `(0, 2/s)`. -/
theorem ray_quad_bounds {s Δ : ℝ} (hs : 0 < s) (hΔ : 0 < Δ) (hΔs : Δ * s < 2) :
    0 ≤ 2 * Δ - s * Δ ^ 2 ∧ 2 * Δ - s * Δ ^ 2 ≤ 1 / s := by
  constructor
  · have : 2 * Δ - s * Δ ^ 2 = Δ * (2 - Δ * s) := by ring
    rw [this]; exact mul_nonneg hΔ.le (by linarith)
  · rw [le_div_iff₀ hs]
    nlinarith [sq_nonneg (1 - s * Δ)]

/-- (C1, first step) two-sided bound for `Λ*` when `s ≥ 100` and `ε ≤ 1/50`:
`(ε/s)(1 - 25(ε + 1/s)) ≤ Λ* ≤ (ε/s)(1 + 25(ε + 2/s))`. -/
theorem lsLamStar_bounds_large_nu (ν : Measure ℝ) (hB : 0 < B) (hp : 0 < (p : ℝ))
    (he : 0 < 1 - beta) (he50 : 1 - beta ≤ 1 / 50) (hs : 100 ≤ lsNu d B p beta) :
    (1 - beta) / lsNu d B p beta * (1 - 25 * ((1 - beta) + 1 / lsNu d B p beta))
        ≤ lsLamStar d B p ν beta ∧
      lsLamStar d B p ν beta
        ≤ (1 - beta) / lsNu d B p beta * (1 + 25 * ((1 - beta) + 2 / lsNu d B p beta)) := by
  have hb1 : beta < 1 := by linarith
  have hb0 : 0 < beta := by linarith
  have hnu : 0 < lsNu d B p beta := by linarith
  have hcp := criticalRate_pos' (d := d) (B := B) (p := p) hB hb0.le hb1
  have hbdd := lsRate_bddAbove (d := d) (p := p) hB hp ν hb0 hb1
  constructor
  · -- lower bound: the point `Δ = 1/s`
    have hDm : 1 / lsNu d B p beta ∈ Set.Ioo 0 (2 / lsNu d B p beta) :=
      ⟨by positivity, div_lt_div_of_pos_right (by norm_num) hnu⟩
    obtain ⟨eta0, heta0, hDe⟩ : ∃ eta0 ∈ Set.Ioo 0 (criticalRate d B p beta),
        eta0 * p / (1 - beta) = 1 / lsNu d B p beta := by
      rw [← ls_Delta_image hB hb0.le hb1 hp] at hDm
      obtain ⟨eta, h, e⟩ := hDm
      exact ⟨eta, h, e⟩
    obtain ⟨_, _, happ⟩ := lsRate_ray_approx (d := d) (B := B) (p := p) ν hB hp he he50 hs heta0
    rw [hDe] at happ
    have hq : 2 * (1 / lsNu d B p beta) - lsNu d B p beta * (1 / lsNu d B p beta) ^ 2
        = 1 / lsNu d B p beta := by
      field_simp; ring
    rw [hq] at happ
    have hlow := (abs_le.1 happ).1
    have hle : lsRate d B p ν beta eta0 ≤ lsLamStar d B p ν beta :=
      le_csSup hbdd ⟨eta0, heta0, rfl⟩
    have e : (1 - beta) / lsNu d B p beta * (1 - 25 * ((1 - beta) + 1 / lsNu d B p beta))
        = (1 - beta) * (1 / lsNu d B p beta)
          - 25 * ((1 - beta) + 1 / lsNu d B p beta) * ((1 - beta) * (1 / lsNu d B p beta)) := by
      ring
    rw [e]
    linarith
  · have hne : (lsRate d B p ν beta '' Set.Ioo 0 (criticalRate d B p beta)).Nonempty :=
      ⟨_, criticalRate d B p beta / 2, ⟨by linarith, by linarith⟩, rfl⟩
    refine csSup_le hne ?_
    rintro _ ⟨eta, heta, rfl⟩
    obtain ⟨hD0, hDs, happ⟩ := lsRate_ray_approx (d := d) (B := B) (p := p) ν hB hp he he50 hs heta
    obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ, Δ = eta * p / (1 - beta) := ⟨_, rfl⟩
    rw [← hΔ] at hD0 hDs happ
    obtain ⟨hq0, hq1⟩ := ray_quad_bounds hnu hD0 ((lt_div_iff₀ hnu).1 hDs)
    set a : ℝ := (1 - beta) * (2 * Δ - lsNu d B p beta * Δ ^ 2) with ha
    have ha0 : 0 ≤ a := mul_nonneg he.le hq0
    have ha1 : a ≤ (1 - beta) / lsNu d B p beta := by
      rw [ha, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hq1 he.le
    have hup := (abs_le.1 happ).2
    have hΔ2 : Δ ≤ 2 / lsNu d B p beta := hDs.le
    have h1 : lsRate d B p ν beta eta ≤ a * (1 + 25 * ((1 - beta) + 2 / lsNu d B p beta)) := by
      have h25 : 25 * ((1 - beta) + Δ) * a ≤ 25 * ((1 - beta) + 2 / lsNu d B p beta) * a :=
        mul_le_mul_of_nonneg_right (by linarith) ha0
      nlinarith
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right ha1 (by positivity)

/-- `N_1 / N = ε r_*(s) / Λ*` (`cor:sample_cost`, the identity `N = N_mem / r_*(s)`). -/
theorem lsNfold_div_hyperbola (ν : Measure ℝ) (hB : 0 < B) (hp : 0 < (p : ℝ))
    (hb0 : 0 ≤ beta) (hb1 : beta < 1) :
    lsNfold d B p ν beta / hyperbolaN (lsNstab d B p beta) (lsNmem B p beta)
      = (1 - beta) * rayRate (lsNu d B p beta) / lsLamStar d B p ν beta := by
  have hnu := lsNu_pos (d := d) (B := B) (p := p) hB hb0 hb1 hp
  have hMpos : 0 < lsNmem B p beta := lsNmem_pos hB hb1 hp
  have hSpos : 0 < lsNstab d B p beta := lsNstab_pos hB hb0 hb1
  have hSM : lsNstab d B p beta / lsNmem B p beta = lsNu d B p beta := by
    rw [lsNstab_eq_nu_mul hB hb0 hb1 hp, mul_div_cancel_right₀ _ hMpos.ne']
  have hN := hyperbola_eq hSpos hMpos
  rw [hSM] at hN
  rw [← hN]
  have hr := rayRate_pos hnu
  have he : 0 < 1 - beta := by linarith
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  by_cases hL : lsLamStar d B p ν beta = 0
  · simp [lsNfold, hL]
  · unfold lsNfold lsNmem
    field_simp

/-- `r_*(s) ≤ 1/s` (from `1/r_* = (1 + s + √(1+s²))/2 ≥ s`). -/
theorem rayRate_le_inv {nu : ℝ} (hnu : 0 < nu) : rayRate nu ≤ 1 / nu := by
  have hr := rayRate_pos hnu
  have h := inv_rayRate hnu
  have hsq : nu ≤ Real.sqrt (1 + nu ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have h1 : nu ≤ 1 / rayRate nu := by rw [h]; linarith
  rw [le_div_iff₀ hr] at h1
  rw [le_div_iff₀ hnu]; linarith

/-- (C1) `v2 cor:sample_cost` (ii), case `s → ∞`, uniform form: for `s ≥ 100` and `ε ≤ 1/50`,
`|Λ* - ε r_*(s)| ≤ C (ε + 1/s) ε r_*(s)` and `|N_1/N - 1| ≤ C (ε + 1/s)`. -/
theorem samplecost_below :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta : ℝ),
        0 < B → 0 < (p : ℝ) → 0 < 1 - beta → 1 - beta ≤ 1 / 50 → 100 ≤ lsNu d B p beta →
        |lsLamStar d B p ν beta - (1 - beta) * rayRate (lsNu d B p beta)|
            ≤ C * ((1 - beta) + 1 / lsNu d B p beta) * ((1 - beta) * rayRate (lsNu d B p beta)) ∧
        |lsNfold d B p ν beta / hyperbolaN (lsNstab d B p beta) (lsNmem B p beta) - 1|
            ≤ C * ((1 - beta) + 1 / lsNu d B p beta) := by
  refine ⟨408, by norm_num, ?_⟩
  intro d B p ν beta hB hp he he50 hs
  have hb1 : beta < 1 := by linarith
  have hb0 : 0 ≤ beta := by linarith
  have hnu : 0 < lsNu d B p beta := by linarith
  obtain ⟨hL, hU⟩ := lsLamStar_bounds_large_nu (d := d) (B := B) (p := p) ν hB hp he he50 hs
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = lsNu d B p beta := ⟨_, rfl⟩
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 1 - beta := ⟨_, rfl⟩
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = lsLamStar d B p ν beta := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = rayRate s := ⟨_, rfl⟩
  have hratio := lsNfold_div_hyperbola (d := d) (B := B) (p := p) ν hB hp hb0 hb1
  rw [← hsdef, ← hedef, ← hΛdef] at hL hU
  rw [← hsdef, ← hedef, ← hΛdef, ← hrdef]
  rw [← hsdef, ← hedef, ← hΛdef, ← hrdef] at hratio
  rw [hratio]
  rw [← hsdef] at hs hnu
  rw [← hedef] at he he50
  have hs0 : 0 < s := hnu
  have hr0 : 0 < r := by rw [hrdef]; exact rayRate_pos hs0
  have hrge : 1 / (1 + s) ≤ r := by rw [hrdef]; exact rayRate_ge hs0
  have hrle : r ≤ 1 / s := by rw [hrdef]; exact rayRate_le_inv hs0
  -- elementary consequences
  have hinv : 1 / s ≤ 1 / 100 := one_div_le_one_div_of_le (by norm_num) hs
  have hinv0 : 0 < 1 / s := by positivity
  have hes : e / s ≤ 2 * (e * r) := by
    have h1 : 1 / s ≤ 2 * r := by
      have h2 : 1 / (1 + s) ≥ 1 / (2 * s) := one_div_le_one_div_of_le (by linarith) (by linarith)
      have h3 : 1 / (2 * s) = 1 / s / 2 := by field_simp
      linarith
    calc e / s = e * (1 / s) := by ring
      _ ≤ e * (2 * r) := mul_le_mul_of_nonneg_left h1 he.le
      _ = 2 * (e * r) := by ring
  have her : e * r ≤ e / s := by
    calc e * r ≤ e * (1 / s) := mul_le_mul_of_nonneg_left hrle he.le
      _ = e / s := by ring
  have herpos : 0 < e * r := mul_pos he hr0
  set t : ℝ := e + 1 / s with ht
  have ht0 : 0 < t := by positivity
  have ht3 : t ≤ 3 / 100 := by rw [ht]; linarith
  -- the difference `1/s - r`
  have hdiff : 1 / s - r ≤ (1 / s) * (1 / (1 + s)) := by
    have : 1 / s - 1 / (1 + s) = (1 / s) * (1 / (1 + s)) := by field_simp; ring
    linarith
  have hdiff0 : 0 ≤ 1 / s - r := by linarith
  -- upper bound for `Λ - e r`
  have hup : Λ - e * r ≤ 102 * t * (e * r) := by
    have hU' : Λ ≤ e / s + 25 * (e / s) * (e + 2 / s) := by nlinarith
    have h1 : e / s - e * r ≤ e * ((1 / s) * (1 / (1 + s))) := by
      have : e / s - e * r = e * (1 / s - r) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hdiff he.le
    have h2 : e * ((1 / s) * (1 / (1 + s))) ≤ 2 * t * (e * r) := by
      have h4 : 1 / (1 + s) ≤ 1 / s := one_div_le_one_div_of_le hs0 (by linarith)
      calc e * ((1 / s) * (1 / (1 + s))) = (e / s) * (1 / (1 + s)) := by ring
        _ ≤ (2 * (e * r)) * (1 / s) :=
          mul_le_mul hes h4 (by positivity) (by positivity)
        _ ≤ (2 * (e * r)) * t := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [ht]; linarith
        _ = 2 * t * (e * r) := by ring
    have h3 : 25 * (e / s) * (e + 2 / s) ≤ 100 * t * (e * r) := by
      have h5 : e + 2 / s ≤ 2 * t := by
        have h6 : 2 / s = 2 * (1 / s) := by ring
        rw [ht, h6]; have : 0 ≤ e := he.le; linarith
      calc 25 * (e / s) * (e + 2 / s) ≤ 25 * (2 * (e * r)) * (2 * t) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hes (by norm_num)) h5
              (by positivity) (by positivity)
        _ = 100 * t * (e * r) := by ring
    linarith
  have hlo : -(102 * t * (e * r)) ≤ Λ - e * r := by
    have h1 : e / s * (1 - 25 * (e + 1 / s)) = e / s - 25 * (e / s) * t := by rw [ht]; ring
    have h2 : 25 * (e / s) * t ≤ 50 * (e * r) * t := by
      have := mul_le_mul_of_nonneg_right hes ht0.le
      nlinarith
    nlinarith
  have habs : |Λ - e * r| ≤ 102 * t * (e * r) := abs_le.2 ⟨hlo, hup⟩
  -- positivity of Λ
  have hΛlow : e * r / 4 ≤ Λ := by
    have h1 : e / s * (1 - 25 * (e + 1 / s)) ≥ e / s * (1 / 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : e + 1 / s ≤ 3 / 100 := by linarith
      linarith
    nlinarith
  have hΛ0 : 0 < Λ := by linarith
  refine ⟨by nlinarith, ?_⟩
  have e1 : e * r / Λ - 1 = (e * r - Λ) / Λ := by field_simp
  rw [e1, abs_div, abs_of_pos hΛ0, div_le_iff₀ hΛ0, abs_sub_comm]
  nlinarith

end C1

/-! ### (C2) uniformity in `s ∈ (0, ∞)` -/

section C2

/-- (C2, window) `cor:samplecost` on one window `s ∈ [ν₀/2, 2ν₀]`, in the form `|N_1/N - 1| ≤ δ`
for `ε ≤ ε₀(ν₀, δ)`. -/
theorem samplecost_window (nu0 : ℝ) (hnu0 : 0 < nu0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta : ℝ),
        0 < B → 0 < (p : ℝ) → 0 < 1 - beta → 1 - beta ≤ eps0 →
        lsNu d B p beta ∈ Set.Icc (nu0 / 2) (2 * nu0) →
        |lsNfold d B p ν beta / hyperbolaN (lsNstab d B p beta) (lsNmem B p beta) - 1| ≤ δ := by
  obtain ⟨eps1, h1, _, C, hC0, hC⟩ := cor_samplecost nu0 hnu0
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = δ / (C + 1) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; positivity
  refine ⟨min eps1 (t ^ 3), lt_min h1 (by positivity), ?_⟩
  intro d B p ν beta hB hp he hε hν
  have hr := (hC d B p ν beta hB hp he (hε.trans (min_le_left _ _)) hν).1.2
  have hsm : (1 - beta) ^ ((1 : ℝ) / 3) ≤ t :=
    rpow_third_le he.le ht0.le (hε.trans (min_le_right _ _))
  refine hr.trans ?_
  calc C * (1 - beta) ^ ((1 : ℝ) / 3) ≤ C * t := mul_le_mul_of_nonneg_left hsm hC0
    _ ≤ δ := by
      rw [htdef, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith

/-- (C2, finitely many windows) `s ∈ [s_lo, s_lo 2^K]` is covered by `K+1` windows
`[ν₀/2, 2ν₀]`, `ν₀ = s_lo 2^k`; `ε₀` is the minimum of the window thresholds. -/
theorem samplecost_chain {slo : ℝ} (hslo : 0 < slo) {δ : ℝ} (hδ : 0 < δ) (K : ℕ) :
    ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta : ℝ),
        0 < B → 0 < (p : ℝ) → 0 < 1 - beta → 1 - beta ≤ eps0 →
        lsNu d B p beta ∈ Set.Icc slo (slo * 2 ^ K) →
        |lsNfold d B p ν beta / hyperbolaN (lsNstab d B p beta) (lsNmem B p beta) - 1| ≤ δ := by
  induction K with
  | zero =>
    obtain ⟨eps0, h0, h⟩ := samplecost_window slo hslo hδ
    refine ⟨eps0, h0, fun d B p ν beta hB hp he hε hν => h d B p ν beta hB hp he hε ?_⟩
    simp only [pow_zero, mul_one] at hν
    exact ⟨by linarith [hν.1], by linarith [hν.2]⟩
  | succ K ih =>
    obtain ⟨eps1, h1, hih⟩ := ih
    have hpos : 0 < slo * 2 ^ K := by positivity
    obtain ⟨eps2, h2, hw⟩ := samplecost_window (slo * 2 ^ K) hpos hδ
    refine ⟨min eps1 eps2, lt_min h1 h2, ?_⟩
    intro d B p ν beta hB hp he hε hν
    by_cases hcase : lsNu d B p beta ≤ slo * 2 ^ K
    · exact hih d B p ν beta hB hp he (hε.trans (min_le_left _ _)) ⟨hν.1, hcase⟩
    · push Not at hcase
      refine hw d B p ν beta hB hp he (hε.trans (min_le_right _ _)) ⟨by linarith, ?_⟩
      have := hν.2
      rw [pow_succ] at this
      linarith

/-- (C2) `v2 cor:sample_cost` (ii), uniform in `s ∈ (0, ∞)`: for every `δ > 0` there is `ε₀ > 0`
such that every LS point with `0 < ε ≤ ε₀` has `|N_1/N - 1| ≤ δ`, whatever `s = ν(B,p,β)`. -/
theorem cor_sample_cost_uniform {δ : ℝ} (hδ : 0 < δ) :
    ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta : ℝ),
        0 < B → 0 < (p : ℝ) → 0 < 1 - beta → 1 - beta ≤ eps0 →
        |lsNfold d B p ν beta / hyperbolaN (lsNstab d B p beta) (lsNmem B p beta) - 1| ≤ δ := by
  obtain ⟨epsA, hA0, _, CA, hCA0, hA⟩ := samplecost_above
  obtain ⟨C, hC0, hC⟩ := samplecost_below
  -- region `s ≤ s_lo`
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = δ / (2 * (CA + 1)) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; positivity
  obtain ⟨slo, hslodef⟩ : ∃ slo : ℝ, slo = min 1 (t ^ 3) := ⟨_, rfl⟩
  have hslo0 : 0 < slo := by rw [hslodef]; exact lt_min one_pos (by positivity)
  -- region `s ≥ S_hi`
  obtain ⟨Shi, hShidef⟩ : ∃ Shi : ℝ, Shi = max 100 (2 * (C + 1) / δ) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (Shi / slo) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨epsM, hM0, hM⟩ := samplecost_chain hslo0 hδ K
  obtain ⟨e1, he1def⟩ : ∃ e1 : ℝ, e1 = min (1 / 50) (δ / (2 * (C + 1))) := ⟨_, rfl⟩
  have he10 : 0 < e1 := by rw [he1def]; exact lt_min (by norm_num) (by positivity)
  refine ⟨min (min epsA (t ^ 3)) (min e1 epsM),
    lt_min (lt_min hA0 (by positivity)) (lt_min he10 hM0), ?_⟩
  intro d B p ν beta hB hp he hε
  have hεA : 1 - beta ≤ epsA := hε.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεt : 1 - beta ≤ t ^ 3 := hε.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε1 : 1 - beta ≤ e1 := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεM : 1 - beta ≤ epsM := hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb1 : beta < 1 := by linarith
  have hb0 : 0 ≤ beta := by
    have : 1 - beta ≤ 1 / 50 := hε1.trans (by rw [he1def]; exact min_le_left _ _)
    linarith
  have hnu := lsNu_pos (d := d) (B := B) (p := p) hB hb0 hb1 hp
  by_cases hlow : lsNu d B p beta ≤ slo
  · -- small `s`
    have hs1 : lsNu d B p beta ≤ 1 := hlow.trans (by rw [hslodef]; exact min_le_left _ _)
    have hst : lsNu d B p beta ≤ t ^ 3 := hlow.trans (by rw [hslodef]; exact min_le_right _ _)
    have hr := (hA d B p ν beta hB hp he hεA hs1).2
    have h3 : (1 - beta) ^ ((1 : ℝ) / 3) ≤ t := rpow_third_le he.le ht0.le hεt
    have h4 : lsNu d B p beta ^ ((1 : ℝ) / 3) ≤ t := rpow_third_le hnu.le ht0.le hst
    refine hr.trans ?_
    calc CA * ((1 - beta) ^ ((1 : ℝ) / 3) + lsNu d B p beta ^ ((1 : ℝ) / 3))
        ≤ CA * (2 * t) := mul_le_mul_of_nonneg_left (by linarith) hCA0
      _ ≤ δ := by
        rw [htdef, show CA * (2 * (δ / (2 * (CA + 1)))) = CA * δ / (CA + 1) by field_simp,
          div_le_iff₀ (by positivity)]
        nlinarith
  · push Not at hlow
    by_cases hhigh : Shi ≤ lsNu d B p beta
    · -- large `s`
      have hs100 : 100 ≤ lsNu d B p beta := by
        refine le_trans ?_ hhigh; rw [hShidef]; exact le_max_left _ _
      have he50 : 1 - beta ≤ 1 / 50 := hε1.trans (by rw [he1def]; exact min_le_left _ _)
      have hr := (hC d B p ν beta hB hp he he50 hs100).2
      refine hr.trans ?_
      have hinv : 1 / lsNu d B p beta ≤ δ / (2 * (C + 1)) := by
        have h2 : 2 * (C + 1) / δ ≤ lsNu d B p beta :=
          le_trans (by rw [hShidef]; exact le_max_right _ _) hhigh
        rw [div_le_div_iff₀ hnu (by positivity)]
        rw [div_le_iff₀ hδ] at h2
        nlinarith
      have hε2 : 1 - beta ≤ δ / (2 * (C + 1)) := hε1.trans (by rw [he1def]; exact min_le_right _ _)
      calc C * ((1 - beta) + 1 / lsNu d B p beta) ≤ C * (δ / (2 * (C + 1)) + δ / (2 * (C + 1))) :=
            mul_le_mul_of_nonneg_left (by linarith) hC0
        _ ≤ δ := by
          rw [show C * (δ / (2 * (C + 1)) + δ / (2 * (C + 1))) = C * δ / (C + 1) by
              field_simp; ring,
            div_le_iff₀ (by positivity)]
          nlinarith
    · -- intermediate `s`
      push Not at hhigh
      refine hM d B p ν beta hB hp he hεM ⟨hlow.le, ?_⟩
      have h1 : Shi / slo < 2 ^ K := hK
      rw [div_lt_iff₀ hslo0] at h1
      linarith

end C2

/-! ### (C3) the co-scaling form -/

section C3

/-- (C3) `v2 cor:sample_cost` (ii), co-scaling form: along every sequence of LS points with
`B_n > 0`, `p_n > 0` and `ε_n = 1 - β_n → 0+` (as on every co-scaling ray with `γ > 0`, whatever
the behaviour of `s_n`), `N_1/N → 1`. -/
theorem cor_sample_cost_tendsto (d B : ℕ → ℕ) (p : ℕ → unitInterval) (ν : ℕ → Measure ℝ)
    (beta : ℕ → ℝ) (hB : ∀ n, 0 < B n) (hp : ∀ n, 0 < (p n : ℝ)) (he : ∀ n, 0 < 1 - beta n)
    (hε : Filter.Tendsto (fun n => 1 - beta n) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => lsNfold (d n) (B n) (p n) (ν n) (beta n)
        / hyperbolaN (lsNstab (d n) (B n) (p n) (beta n)) (lsNmem (B n) (p n) (beta n)))
      Filter.atTop (nhds 1) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨eps0, h0, h⟩ := cor_sample_cost_uniform (δ := δ / 2) (by positivity)
  filter_upwards [hε.eventually (Iio_mem_nhds h0)] with n hn
  have := h (d n) (B n) (p n) (ν n) (beta n) (hB n) (hp n) (he n) (le_of_lt hn)
  rw [Real.dist_eq]
  linarith

end C3

/-! ### (C4) `rem:sgd_cost`: momentum does not lower the sample cost to leading order -/

section C4

/-- (C4, both bounds at once) for `ε ≤ ε₀(δ)`: `N_1 ≥ (1-δ) max(N_stab, N_mem)` and
`N_1 ≥ (1-δ) N_fold^SGD`. -/
theorem samplecost_ge_both {δ : ℝ} (hδ : 0 < δ) :
    ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta : ℝ),
        0 < B → 0 < (p : ℝ) → 0 < 1 - beta → 1 - beta ≤ eps0 →
        (1 - δ) * max (lsNstab d B p beta) (lsNmem B p beta) ≤ lsNfold d B p ν beta ∧
          (1 - δ) * lsNfoldSGD d B p ν ≤ lsNfold d B p ν beta := by
  obtain ⟨δ', hδ'def⟩ : ∃ δ' : ℝ, δ' = min (δ / 2) (1 / 2) := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := by rw [hδ'def]; exact lt_min (by positivity) (by norm_num)
  have hδ'1 : δ' ≤ δ / 2 := by rw [hδ'def]; exact min_le_left _ _
  have hδ'2 : δ' ≤ 1 / 2 := by rw [hδ'def]; exact min_le_right _ _
  obtain ⟨eps1, h1, h⟩ := cor_sample_cost_uniform hδ'0
  refine ⟨min eps1 (min (δ / 2) (1 / 2)), lt_min h1 (lt_min (by positivity) (by norm_num)), ?_⟩
  intro d B p ν beta hB hp he hε
  have hε1 : 1 - beta ≤ eps1 := hε.trans (min_le_left _ _)
  have hεd : 1 - beta ≤ δ / 2 := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε2 : 1 - beta ≤ 1 / 2 := hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb1 : beta < 1 := by linarith
  have hb0 : 0 ≤ beta := by linarith
  have hr := h d B p ν beta hB hp he hε1
  have hSpos : 0 < lsNstab d B p beta := lsNstab_pos hB hb0 hb1
  have hMpos : 0 < lsNmem B p beta := lsNmem_pos hB hb1 hp
  have hNge := hyperbola_ge_max hSpos hMpos
  have hmax0 : 0 ≤ max (lsNstab d B p beta) (lsNmem B p beta) :=
    (le_max_left _ _).trans' hSpos.le
  have hNpos : 0 < hyperbolaN (lsNstab d B p beta) (lsNmem B p beta) :=
    lt_of_lt_of_le (lt_max_of_lt_left hSpos) hNge
  have hratio : 1 - δ' ≤ lsNfold d B p ν beta
      / hyperbolaN (lsNstab d B p beta) (lsNmem B p beta) := by
    have := (abs_le.1 hr).1; linarith
  rw [le_div_iff₀ hNpos] at hratio
  have hmain : (1 - δ') * max (lsNstab d B p beta) (lsNmem B p beta) ≤ lsNfold d B p ν beta := by
    refine le_trans ?_ hratio
    exact mul_le_mul_of_nonneg_left hNge (by linarith)
  refine ⟨le_trans (mul_le_mul_of_nonneg_right (by linarith) hmax0) hmain, ?_⟩
  -- SGD
  obtain ⟨hsgd, _⟩ := lsNfoldSGD_le_max (d := d) (p := p) hB hp ν hb0 hb1
  have hsgd' : lsNfoldSGD d B p ν ≤ (1 + (1 - beta)) * max (lsNstab d B p beta) (lsNmem B p beta) := by
    obtain ⟨_, h2⟩ := lsNfoldSGD_le_max (d := d) (p := p) hB hp ν hb0 hb1
    linarith
  have hsgd0 : 0 ≤ lsNfoldSGD d B p ν := lsNfoldSGD_nonneg hB hp ν
  by_cases hδ1 : δ ≤ 1
  · have h3 : (1 - δ) * lsNfoldSGD d B p ν
        ≤ (1 - δ) * ((1 + (1 - beta)) * max (lsNstab d B p beta) (lsNmem B p beta)) :=
      mul_le_mul_of_nonneg_left hsgd' (by linarith)
    refine le_trans h3 (le_trans ?_ hmain)
    have h4 : (1 - δ) * (1 + (1 - beta)) ≤ 1 - δ' := by nlinarith
    calc (1 - δ) * ((1 + (1 - beta)) * max (lsNstab d B p beta) (lsNmem B p beta))
        = ((1 - δ) * (1 + (1 - beta))) * max (lsNstab d B p beta) (lsNmem B p beta) := by ring
      _ ≤ (1 - δ') * max (lsNstab d B p beta) (lsNmem B p beta) :=
        mul_le_mul_of_nonneg_right h4 hmax0
  · push Not at hδ1
    have : (1 - δ) * lsNfoldSGD d B p ν ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hsgd0
    exact this.trans (le_trans (mul_nonneg (by linarith) hmax0) hmain)

/-- (C4) `v2 rem:sgd_cost`: for `ε ≤ ε₀(δ)`, `N_1 ≥ (1-δ) max(N_stab, N_mem)`. -/
theorem samplecost_ge_max_uniform {δ : ℝ} (hδ : 0 < δ) :
    ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta : ℝ),
        0 < B → 0 < (p : ℝ) → 0 < 1 - beta → 1 - beta ≤ eps0 →
        (1 - δ) * max (lsNstab d B p beta) (lsNmem B p beta) ≤ lsNfold d B p ν beta := by
  obtain ⟨eps0, h0, h⟩ := samplecost_ge_both hδ
  exact ⟨eps0, h0, fun d B p ν beta hB hp he hε => (h d B p ν beta hB hp he hε).1⟩

/-- (C4) `v2 rem:sgd_cost`: for `ε ≤ ε₀(δ)`, `N_1 ≥ (1-δ) N_fold^SGD`; momentum does not lower the
sample cost to leading order. -/
theorem samplecost_ge_sgd_uniform {δ : ℝ} (hδ : 0 < δ) :
    ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta : ℝ),
        0 < B → 0 < (p : ℝ) → 0 < 1 - beta → 1 - beta ≤ eps0 →
        (1 - δ) * lsNfoldSGD d B p ν ≤ lsNfold d B p ν beta := by
  obtain ⟨eps0, h0, h⟩ := samplecost_ge_both hδ
  exact ⟨eps0, h0, fun d B p ν beta hB hp he hε => (h d B p ν beta hB hp he hε).2⟩

end C4

/-! ### (C5), (C6) the vocabulary clauses -/

section Vocab

variable {n : ℕ} {d B : ℕ} {ν : Measure ℝ} {ps : Fin (n + 1) → unitInterval} {beta eta : ℝ}

/-- For a vocabulary with all copies stable at `(η, β)`, `0 < β < 1`: `Λ_min ≤ Λ*(p_V)`, hence
`N_1(p_V)/(B p_V) = 1/Λ*(p_V) ≤ 1/Λ_min` (`lem:helps-vocab` (iii), the comparison with the
single-feature sample cost of the slowest row). -/
theorem nfold_div_le_inv_Lmin (hB : 0 < B) (hp : ∀ j, 0 < (ps j : ℝ)) (hb0 : 0 < beta)
    (hb1 : beta < 1) (hη : 0 < eta)
    (hst : ∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) :
    lsNfold d B (ps (Fin.last n)) ν beta / ((B : ℝ) * (ps (Fin.last n) : ℝ))
      ≤ 1 / Lmin d B ν beta eta ps := by
  have hV := hp (Fin.last n)
  have hw : 0 < (copyParams d B ν beta eta ps (Fin.last n)).w := by
    rw [copyParams_w]
    have : 0 < 1 - beta := by linarith
    positivity
  have hrad0 : 0 < stepRadius (copyParams d B ν beta eta ps (Fin.last n)) :=
    lt_of_lt_of_le hb0 (beta_le_stepRadius (copyParams d B ν beta eta ps (Fin.last n)) hb0.le
      hb1.le hw.le (copyParams_noise_nonneg hp hη.le (Fin.last n)))
  have hrho0 : 0 < rhoMax d B ν beta eta ps := lt_of_lt_of_le hrad0 (le_rhoMax (Fin.last n))
  have hrho1 : rhoMax d B ν beta eta ps < 1 := rhoMax_lt_one_iff.2 hst
  have hLpos : 0 < Lmin d B ν beta eta ps := by
    unfold Lmin
    have := Real.log_neg hrho0 hrho1
    linarith
  have hLle : Lmin d B ν beta eta ps ≤ lsRate d B (ps (Fin.last n)) ν beta eta := by
    have h := Real.log_le_log hrad0 (le_rhoMax (d := d) (B := B) (ν := ν) (beta := beta)
      (eta := eta) (ps := ps) (Fin.last n))
    unfold Lmin lsRate perStepRate
    show -Real.log (rhoMax d B ν beta eta ps)
      ≤ -Real.log (stepRadius (copyParams d B ν beta eta ps (Fin.last n)))
    linarith
  have hlt : eta < criticalRate d B (ps (Fin.last n)) beta :=
    (eta_lt_critical_iff hB (ps (Fin.last n)) hb0.le hb1).2
      (copy_load_lt_one_of_stable hp hb0.le hb1 hη (hst (Fin.last n)))
  have hbdd := lsRate_bddAbove (d := d) (p := ps (Fin.last n)) hB hV ν hb0 hb1
  have hLs : lsRate d B (ps (Fin.last n)) ν beta eta ≤ lsLamStar d B (ps (Fin.last n)) ν beta :=
    le_csSup hbdd ⟨eta, ⟨hη, hlt⟩, rfl⟩
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hid : lsNfold d B (ps (Fin.last n)) ν beta / ((B : ℝ) * (ps (Fin.last n) : ℝ))
      = 1 / lsLamStar d B (ps (Fin.last n)) ν beta := by
    unfold lsNfold
    have hLs0 : lsLamStar d B (ps (Fin.last n)) ν beta ≠ 0 := (hLpos.trans_le (hLle.trans hLs)).ne'
    field_simp
  rw [hid]
  exact one_div_le_one_div_of_le hLpos (hLle.trans hLs)

/-- (C5) `v2 lem:helps-vocab` (iii), last claim, for every `s`: for every `δ > 0` there is
`ε₀ > 0` such that for every vocabulary, every `β` with `0 < 1-β ≤ ε₀`, and every `η > 0` with
all copies stable,
`(1-δ) max(N_stab, N_mem)(p_V)/(B p_V) ≤ 1/Λ_min` and `(1-δ)(d+2-p_V)/(B p_V) ≤ 1/Λ_min`.
(`Antitone ps` is not used.) -/
theorem helps_vocab_iii_coscaling {δ : ℝ} (hδ : 0 < δ) :
    ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ (n d B : ℕ) (ν : Measure ℝ) (ps : Fin (n + 1) → unitInterval) (beta eta : ℝ),
        (∀ j, 0 < (ps j : ℝ)) → Antitone ps → 0 < B → 0 < 1 - beta → 1 - beta ≤ eps0 →
        0 < eta → (∀ j, stepRadius (copyParams d B ν beta eta ps j) < 1) →
        (1 - δ) * max (lsNstab d B (ps (Fin.last n)) beta) (lsNmem B (ps (Fin.last n)) beta)
            / ((B : ℝ) * (ps (Fin.last n) : ℝ)) ≤ 1 / Lmin d B ν beta eta ps ∧
          (1 - δ) * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))
            / ((B : ℝ) * (ps (Fin.last n) : ℝ)) ≤ 1 / Lmin d B ν beta eta ps := by
  obtain ⟨eps1, h1, h⟩ := samplecost_ge_max_uniform hδ
  refine ⟨min eps1 (1 / 2), lt_min h1 (by norm_num), ?_⟩
  intro n d B ν ps beta eta hp _hanti hB he hε hη hst
  have hε1 : 1 - beta ≤ eps1 := hε.trans (min_le_left _ _)
  have hε2 : 1 - beta ≤ 1 / 2 := hε.trans (min_le_right _ _)
  have hb1 : beta < 1 := by linarith
  have hb0 : 0 < beta := by linarith
  have hV := hp (Fin.last n)
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hBp : 0 < (B : ℝ) * (ps (Fin.last n) : ℝ) := by positivity
  have hmain := h d B (ps (Fin.last n)) ν beta hB hV he hε1
  have hchain := nfold_div_le_inv_Lmin (d := d) (ν := ν) (ps := ps) hB hp hb0 hb1 hη hst
  have hfirst : (1 - δ) * max (lsNstab d B (ps (Fin.last n)) beta) (lsNmem B (ps (Fin.last n)) beta)
      / ((B : ℝ) * (ps (Fin.last n) : ℝ)) ≤ 1 / Lmin d B ν beta eta ps :=
    le_trans (div_le_div_of_nonneg_right hmain hBp.le) hchain
  refine ⟨hfirst, ?_⟩
  by_cases hδ1 : δ ≤ 1
  · refine le_trans ?_ hfirst
    apply div_le_div_of_nonneg_right _ hBp.le
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact (lsNstab_ge (d := d) (p := ps (Fin.last n)) hB hb0.le hb1).trans (le_max_left _ _)
  · push Not at hδ1
    have hV1 := (ps (Fin.last n)).2.2
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hneg : (1 - δ) * ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))
        / ((B : ℝ) * (ps (Fin.last n) : ℝ)) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith)) hBp
    exact hneg.le.trans (vv_one_div_Lmin_nonneg hst)

/-- (C6) `v2 prop:vocab_full` (i), last clause: with `External.JuryStability` (so that the
admissible set at fixed `β` is nonempty), `κ > 1`, `B ≥ 1` and `(B-1)(p_1-p_V) ≤ d+2`:
for every `δ > 0` there is `ε₀ > 0` (independent of `d, B, ν` and the vocabulary) such that
`0 < 1-β ≤ ε₀` gives `(1-δ) S_SGD(B) ≤ S_β(B)`.  (`κ > 1` is not used.) -/
theorem vocab_full_i_coscaling (jury : External.JuryStability) {δ : ℝ} (hδ : 0 < δ) :
    ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ (n d B : ℕ) (ν : Measure ℝ) (ps : Fin (n + 1) → unitInterval) (beta : ℝ),
        (∀ j, 0 < (ps j : ℝ)) → Antitone ps → 1 < kappaV ps → 1 ≤ B →
        ((B : ℝ) - 1) * ((ps 0 : ℝ) - (ps (Fin.last n) : ℝ)) ≤ (d : ℝ) + 2 →
        0 < 1 - beta → 1 - beta ≤ eps0 →
        (1 - δ) * Sfun d B ν ps sgdClass ≤ Sfun d B ν ps {beta} := by
  obtain ⟨eps1, h1, h⟩ := samplecost_ge_sgd_uniform hδ
  refine ⟨min eps1 (1 / 2), lt_min h1 (by norm_num), ?_⟩
  intro n d B ν ps beta hp hanti _hκ hB hcase he hε
  have hε1 : 1 - beta ≤ eps1 := hε.trans (min_le_left _ _)
  have hε2 : 1 - beta ≤ 1 / 2 := hε.trans (min_le_right _ _)
  have hb1 : beta < 1 := by linarith
  have hb0 : 0 < beta := by linarith
  have hB0 : 0 < B := hB
  have hV := hp (Fin.last n)
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB0
  have hBp : 0 < (B : ℝ) * (ps (Fin.last n) : ℝ) := by positivity
  have hV1 := (ps (Fin.last n)).2.2
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdp : 0 < (d : ℝ) + 2 - (ps (Fin.last n) : ℝ) := by linarith
  -- the SGD side
  have hSgd := Sfun_sgd_eq_of_le_Bx (d := d) (ν := ν) hB hp hanti hcase
  have hx : 0 < (B : ℝ) * (ps (Fin.last n) : ℝ) / ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ)) :=
    div_pos hBp hdp
  have hlogpos : 0 < Real.log (1 + (B : ℝ) * (ps (Fin.last n) : ℝ)
      / ((d : ℝ) + 2 - (ps (Fin.last n) : ℝ))) := Real.log_pos (by linarith)
  have hSgd' : lsNfoldSGD d B (ps (Fin.last n)) ν / ((B : ℝ) * (ps (Fin.last n) : ℝ))
      = Sfun d B ν ps sgdClass := by
    rw [hSgd, lsNfoldSGD_eq hB0 hV ν, mul_comm (ps (Fin.last n) : ℝ) (B : ℝ)]
    field_simp
  -- nonempty admissible set at `β`
  have hcp0 := criticalRate_pos' (d := d) (B := B) (p := ps 0) hB0 hb0.le hb1
  have hcpV := criticalRate_pos' (d := d) (B := B) (p := ps (Fin.last n)) hB0 hb0.le hb1
  have hηmin : 0 < min (criticalRate d B (ps 0) beta) (criticalRate d B (ps (Fin.last n)) beta) / 2 :=
    by positivity
  have hmem : ((min (criticalRate d B (ps 0) beta) (criticalRate d B (ps (Fin.last n)) beta) / 2,
      beta) : ℝ × ℝ) ∈ admSet d B ν ps {beta} := by
    refine ⟨hηmin, rfl, ?_⟩
    exact (all_stable_iff_lt_min jury hB0 hp hanti hb0.le hb1 hηmin).2 (by linarith [lt_min hcp0 hcpV])
  have hlb : ∀ c : ℝ, (∀ x ∈ admSet d B ν ps {beta}, c ≤ 1 / Lmin d B ν x.2 x.1 ps) →
      c ≤ Sfun d B ν ps {beta} := fun c hc =>
    le_csInf ((Set.nonempty_of_mem hmem).image _) (by rintro _ ⟨x, hx, rfl⟩; exact hc x hx)
  refine hlb _ ?_
  rintro x ⟨hη, hβ, hst⟩
  have hx2 : x.2 = beta := hβ
  rw [hx2] at hst ⊢
  have hchain := nfold_div_le_inv_Lmin (d := d) (ν := ν) (ps := ps) hB0 hp hb0 hb1 hη hst
  have hsg := h d B (ps (Fin.last n)) ν beta hB0 hV he hε1
  rw [← hSgd']
  calc (1 - δ) * (lsNfoldSGD d B (ps (Fin.last n)) ν / ((B : ℝ) * (ps (Fin.last n) : ℝ)))
      = (1 - δ) * lsNfoldSGD d B (ps (Fin.last n)) ν / ((B : ℝ) * (ps (Fin.last n) : ℝ)) := by
        ring
    _ ≤ lsNfold d B (ps (Fin.last n)) ν beta / ((B : ℝ) * (ps (Fin.last n) : ℝ)) :=
        div_le_div_of_nonneg_right hsg hBp.le
    _ ≤ 1 / Lmin d B ν beta x.1 ps := hchain

end Vocab

end

end SparseSGD.Scaling.Helps
