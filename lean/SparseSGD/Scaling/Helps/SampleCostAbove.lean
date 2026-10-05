import SparseSGD.Scaling.Helps.Limits
import SparseSGD.Scaling.Helps.Transfer
import SparseSGD.Scaling.Helps.RootPerturbation
import SparseSGD.Scaling.Helps.Stability

/-!
# Sample cost: the retention upper bound and the SGD cost (v2 `cor:sample_cost` (i), (ii) case `s → 0`, `rem:sgd_cost`)

Paper labels (v2): `cor:sample_cost = cor:samplecost`, `rem:sgd_cost`, `rem:crit_single`
(the hyperbola of `rem:crit_single` is the existing `hyperbola_relation` of `Ray.lean`).

Notation: `s = lsNu d B p β`, `N_1 = lsNfold`, `N = hyperbolaN (lsNstab d B p β) (lsNmem B p β)`,
`ε = 1 - β`.

* (A1) `lsLamStar_le_neg_log_beta`: `Λ* ≤ -ln β` for `0 < β < 1`.
* (A2) `lsNfold_ge_retention` (`cor:sample_cost` (i)): `N_1 ≥ p B / ln(1/β)`; the proof includes
  `Λ* > 0` (`lsLamStar_pos`), which uses `External.JuryStability`.
* (A3) `samplecost_above`: the case `s → 0` of `cor:sample_cost` (ii) in uniform form.
* (A4) `rem:sgd_cost`: `lsLamStar_zero_eq`, `lsNfoldSGD_eq`, `lsNfoldSGD_mono`,
  `lsNfoldSGD_le_max`.
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD SparseSGD.Probability.LeastSquares MeasureTheory

noncomputable section

section A1A2

variable {d B : ℕ} {p : unitInterval} {beta : ℝ}

/-- The LS parameters have positive `w` for every positive learning rate. -/
theorem params_w_pos_of_pos (hp : 0 < (p : ℝ)) (ν : Measure ℝ) (hb1 : beta < 1) {eta : ℝ}
    (he : 0 < eta) : 0 < (params d B p ν beta eta).w := by
  rw [params_w_eq (d := d) (B := B) hp ν hb1]
  have : 0 < 1 - beta := by linarith
  positivity

/-- The LS parameters have nonnegative noise for every nonnegative learning rate. -/
theorem params_noise_nonneg_of_nonneg (hB : 0 < B) (hp : 0 < (p : ℝ)) (ν : Measure ℝ)
    {eta : ℝ} (he : 0 ≤ eta) : 0 ≤ (params d B p ν beta eta).noise := by
  rw [params_noise_eq (d := d) hB hp ν]
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hp1 := p.2.2
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have : 0 ≤ ((d : ℝ) + 2 - p) / (2 * B) := div_nonneg (by linarith) (by positivity)
  exact mul_nonneg he this

/-- `Λ(η) ≤ -ln β` for each admissible learning rate (`lem:helps-onecopy`, LS). -/
theorem lsRate_le_neg_log_beta (hB : 0 < B) (hp : 0 < (p : ℝ)) (ν : Measure ℝ)
    (hb0 : 0 < beta) (hb1 : beta < 1) {eta : ℝ}
    (he : eta ∈ Set.Ioo 0 (criticalRate d B p beta)) :
    lsRate d B p ν beta eta ≤ -Real.log beta :=
  perStepRate_le_neg_log_beta (params d B p ν beta eta) hb0 hb1
    (params_w_pos_of_pos hp ν hb1 he.1) (params_noise_nonneg_of_nonneg hB hp ν he.1.le)

/-- The image of the rate over `(0, η_+)` is bounded above by `-ln β`. -/
theorem lsRate_bddAbove (hB : 0 < B) (hp : 0 < (p : ℝ)) (ν : Measure ℝ)
    (hb0 : 0 < beta) (hb1 : beta < 1) :
    BddAbove (lsRate d B p ν beta '' Set.Ioo 0 (criticalRate d B p beta)) :=
  ⟨-Real.log beta, by
    rintro _ ⟨eta, he, rfl⟩
    exact lsRate_le_neg_log_beta hB hp ν hb0 hb1 he⟩

/-- (A1) `v2 cor:sample_cost` (i), first half: `Λ* ≤ -ln β` for `0 < β < 1`. -/
theorem lsLamStar_le_neg_log_beta (hB : 0 < B) (hp : 0 < (p : ℝ)) (ν : Measure ℝ)
    (hb0 : 0 < beta) (hb1 : beta < 1) :
    lsLamStar d B p ν beta ≤ -Real.log beta := by
  have hcp := criticalRate_pos' (d := d) (B := B) (p := p) hB hb0.le hb1
  have hne : (lsRate d B p ν beta '' Set.Ioo 0 (criticalRate d B p beta)).Nonempty :=
    ⟨_, criticalRate d B p beta / 2, ⟨by linarith, by linarith⟩, rfl⟩
  refine csSup_le hne ?_
  rintro _ ⟨eta, he, rfl⟩
  exact lsRate_le_neg_log_beta hB hp ν hb0 hb1 he

/-- `Λ* > 0` for `0 < β < 1` (uses `External.JuryStability`): the rate at `η = η_+/2` is positive
since `u < 1` there (`lem:helps-rate`, first clause). -/
theorem lsLamStar_pos (jury : External.JuryStability) (hB : 0 < B) (hp : 0 < (p : ℝ))
    (ν : Measure ℝ) (hb0 : 0 < beta) (hb1 : beta < 1) :
    0 < lsLamStar d B p ν beta := by
  have hcp := criticalRate_pos' (d := d) (B := B) (p := p) hB hb0.le hb1
  have heta0 : criticalRate d B p beta / 2 ∈ Set.Ioo 0 (criticalRate d B p beta) :=
    ⟨by linarith, by linarith⟩
  have hbdd := lsRate_bddAbove (d := d) (p := p) hB hp ν hb0 hb1
  have hpos : 0 < lsRate d B p ν beta (criticalRate d B p beta / 2) := by
    unfold lsRate
    rw [perStepRate_pos_iff_of_beta_pos jury (params d B p ν beta (criticalRate d B p beta / 2))
      hb0 hb1 (params_w_pos_of_pos hp ν hb1 heta0.1)
      (params_noise_nonneg_of_nonneg hB hp ν heta0.1.le)]
    exact (totalLoad_lt_one_iff_eta_lt_critical d B hB p hp ν beta _ hb0.le hb1).2 heta0.2
  exact lt_of_lt_of_le hpos (le_csSup hbdd ⟨_, heta0, rfl⟩)

/-- (A2) `v2 cor:sample_cost` (i): `N_1 ≥ p B / ln(1/β)`, for `0 < β < 1`. -/
theorem lsNfold_ge_retention (jury : External.JuryStability) (hB : 0 < B) (hp : 0 < (p : ℝ))
    (ν : Measure ℝ) (hb0 : 0 < beta) (hb1 : beta < 1) :
    (p : ℝ) * B / (-Real.log beta) ≤ lsNfold d B p ν beta := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hpos := lsLamStar_pos (d := d) jury hB hp ν hb0 hb1
  have hle := lsLamStar_le_neg_log_beta (d := d) hB hp ν hb0 hb1
  unfold lsNfold
  exact div_le_div_of_nonneg_left (by positivity) hpos hle

end A1A2

/-! ### (A4) `rem:sgd_cost` -/

section A4

variable {d B : ℕ} {p : unitInterval}

/-- The SGD rate image over `(0, η_+(0))` has greatest element `-ln(1 - p η_+(0)/2)`. -/
theorem lsRate_zero_isGreatest (hB : 0 < B) (hp : 0 < (p : ℝ)) (ν : Measure ℝ) :
    IsGreatest (lsRate d B p ν 0 '' Set.Ioo 0 (criticalRate d B p 0))
      (-Real.log (1 - (p : ℝ) * criticalRate d B p 0 / 2)) := by
  obtain ⟨⟨⟨eta0, he0, hv⟩, hub⟩, hlt⟩ := ls_beta_zero_sup d B hB p hp ν
  refine ⟨⟨eta0, he0, ?_⟩, ?_⟩
  · simp only at hv
    rw [lsRate_zero_eq hB hp ν he0, hv]
  · rintro _ ⟨eta, he, rfl⟩
    rw [lsRate_zero_eq hB hp ν he]
    have hx := hub ⟨eta, he, rfl⟩
    simp only at hx
    have h1 : 0 < 1 - (p : ℝ) * criticalRate d B p 0 / 2 := by linarith
    have := Real.log_le_log h1 (show 1 - (p : ℝ) * criticalRate d B p 0 / 2
      ≤ 1 - 2 * (params d B p ν 0 eta).w * (1 - (params d B p ν 0 eta).totalLoad) by linarith)
    linarith

/-- `η_+(0) = 2B/(d+2-p+pB)`. -/
theorem criticalRate_zero_eq (hB : 0 < B) :
    criticalRate d B p 0 = 2 * B / (((d : ℝ) + 2 - p) + p * B) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hp1 := p.2.2
  have hp0 := p.2.1
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ha : 0 < ((d : ℝ) + 2 - p) + p * B := by
    have : 0 ≤ (p : ℝ) * B := by positivity
    linarith
  unfold criticalRate inverseCriticalRate
  simp only [sub_zero, add_zero, div_one, mul_one]
  field_simp

/-- (A4) `v2 rem:sgd_cost`: `Λ*_SGD = ln(1 + Bp/(d+2-p))`. -/
theorem lsLamStar_zero_eq (hB : 0 < B) (hp : 0 < (p : ℝ)) (ν : Measure ℝ) :
    lsLamStar d B p ν 0 = Real.log (1 + (p : ℝ) * B / ((d : ℝ) + 2 - p)) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hp1 := p.2.2
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ha : 0 < (d : ℝ) + 2 - p := by linarith
  have hpB : 0 < (p : ℝ) * B := by positivity
  have hg := lsRate_zero_isGreatest (d := d) hB hp ν
  unfold lsLamStar
  rw [hg.csSup_eq, criticalRate_zero_eq hB]
  have e1 : 1 - (p : ℝ) * (2 * B / (((d : ℝ) + 2 - p) + p * B)) / 2
      = ((d : ℝ) + 2 - p) / (((d : ℝ) + 2 - p) + p * B) := by
    field_simp
    ring
  have e2 : 1 + (p : ℝ) * B / ((d : ℝ) + 2 - p)
      = (((d : ℝ) + 2 - p) + p * B) / ((d : ℝ) + 2 - p) := by
    field_simp
  rw [e1, e2, ← Real.log_inv, inv_div]

/-- (A4) `v2 rem:sgd_cost`: `N_fold^SGD = Bp / ln(1 + Bp/(d+2-p))`. -/
theorem lsNfoldSGD_eq (hB : 0 < B) (hp : 0 < (p : ℝ)) (ν : Measure ℝ) :
    lsNfoldSGD d B p ν = (p : ℝ) * B / Real.log (1 + (p : ℝ) * B / ((d : ℝ) + 2 - p)) := by
  unfold lsNfoldSGD
  rw [lsLamStar_zero_eq hB hp ν]

/-- `x ↦ x / ln(1+x)` is nondecreasing on `(0, ∞)`. -/
theorem div_log_one_add_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    x / Real.log (1 + x) ≤ y / Real.log (1 + y) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hlx : 0 < Real.log (1 + x) := Real.log_pos (by linarith)
  have hly : 0 < Real.log (1 + y) := Real.log_pos (by linarith)
  rw [div_le_div_iff₀ hlx hly]
  -- concavity of log between `1` and `1 + y`
  have hc := (strictConcaveOn_log_Ioi.concaveOn).2 (x := 1) (y := 1 + y)
    (by simp : (1 : ℝ) ∈ Set.Ioi 0) (by simp only [Set.mem_Ioi]; linarith)
    (show 0 ≤ 1 - x / y by rw [sub_nonneg, div_le_one hy]; exact hxy)
    (show 0 ≤ x / y by positivity) (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hc
  have e : (1 - x / y) * 1 + x / y * (1 + y) = 1 + x := by field_simp; ring
  rw [e] at hc
  have h2 : x * Real.log (1 + y) ≤ y * Real.log (1 + x) := by
    have := mul_le_mul_of_nonneg_left hc hy.le
    have e2 : y * (x / y * Real.log (1 + y)) = x * Real.log (1 + y) := by field_simp
    linarith
  exact h2

/-- (A4) `v2 rem:sgd_cost`: `N_fold^SGD` is nondecreasing in `B ≥ 1`. -/
theorem lsNfoldSGD_mono (hp : 0 < (p : ℝ)) (ν : Measure ℝ) {B1 B2 : ℕ} (h1 : 1 ≤ B1)
    (h12 : B1 ≤ B2) : lsNfoldSGD d B1 p ν ≤ lsNfoldSGD d B2 p ν := by
  have hB1 : 0 < B1 := h1
  have hB2 : 0 < B2 := lt_of_lt_of_le hB1 h12
  have hp1 := p.2.2
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ha : 0 < (d : ℝ) + 2 - p := by linarith
  have hB1' : (0 : ℝ) < B1 := by exact_mod_cast hB1
  have hB12 : (B1 : ℝ) ≤ B2 := by exact_mod_cast h12
  rw [lsNfoldSGD_eq hB1 hp ν, lsNfoldSGD_eq hB2 hp ν]
  have key : ∀ B' : ℕ, (p : ℝ) * B' / Real.log (1 + (p : ℝ) * B' / ((d : ℝ) + 2 - p))
      = ((d : ℝ) + 2 - p) * (((p : ℝ) * B' / ((d : ℝ) + 2 - p))
        / Real.log (1 + (p : ℝ) * B' / ((d : ℝ) + 2 - p))) := by
    intro B'
    field_simp
  rw [key B1, key B2]
  refine mul_le_mul_of_nonneg_left (div_log_one_add_mono (by positivity) ?_) ha.le
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB12 hp.le) ha.le

/-- (A4) `v2 rem:sgd_cost`: for `0 ≤ β < 1`,
`N_fold^SGD ≤ N_stab + ε N_mem ≤ (1+ε) max(N_stab, N_mem)`. -/
theorem lsNfoldSGD_le_max {beta : ℝ} (hB : 0 < B) (hp : 0 < (p : ℝ)) (ν : Measure ℝ)
    (hb0 : 0 ≤ beta) (hb1 : beta < 1) :
    lsNfoldSGD d B p ν ≤ lsNstab d B p beta + (1 - beta) * lsNmem B p beta ∧
      lsNstab d B p beta + (1 - beta) * lsNmem B p beta
        ≤ (1 + (1 - beta)) * max (lsNstab d B p beta) (lsNmem B p beta) := by
  have h1 := lsNfoldSGD_le (d := d) hB hp ν
  have h2 := lsNstab_zero_sub_le (d := d) (p := p) hB hb0 hb1 hp
  have he : 0 ≤ 1 - beta := by linarith
  constructor
  · linarith
  · have ha := le_max_left (lsNstab d B p beta) (lsNmem B p beta)
    have hb := le_max_right (lsNstab d B p beta) (lsNmem B p beta)
    have := mul_le_mul_of_nonneg_left hb he
    nlinarith

end A4

/-! ### (A3) the case `s → 0` of `cor:sample_cost` (ii) -/

section A3

/-- `rayDelta ν ≤ 1/2`, hence `1 - ν/2 ≤ rayRate ν ≤ 1` (`lem:ray`). -/
theorem rayDelta_le_half {nu : ℝ} (_hnu : 0 < nu) : rayDelta nu ≤ 1 / 2 := by
  unfold rayDelta
  have h1 : 1 ≤ Real.sqrt (1 + nu ^ 2) := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + nu ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

theorem rayRate_ge_one_sub_half {nu : ℝ} (hnu : 0 < nu) : 1 - nu / 2 ≤ rayRate nu := by
  unfold rayRate
  have := rayDelta_le_half hnu
  nlinarith

/-- Lower bound for `Λ*` along the ray at small `s`: with `Δ = 1/2` and `u_n ≤ s/4`,
`Λ* ≥ ε (1 - s^{1/3}) - C₁ ε^{4/3}` and `Λ* ≥ ε/20` (`cor:sample_cost` (ii), case `s → 0`;
uses `helps_transfer_box` and `continuumPerronRate_close`). -/
theorem lsLamStar_lower_small_nu :
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 / 2 ∧ ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta : ℝ),
        0 < B → 0 < (p : ℝ) → 0 < 1 - beta → 1 - beta ≤ eps0 → lsNu d B p beta ≤ 1 →
        (1 - beta) * (1 - lsNu d B p beta ^ ((1 : ℝ) / 3)) - C1 * (1 - beta) ^ ((4 : ℝ) / 3)
            ≤ lsLamStar d B p ν beta ∧
          (1 - beta) / 20 ≤ lsLamStar d B p ν beta := by
  obtain ⟨eps1, h1, C0, hC0⟩ := helps_transfer_box (1 / 2) 1 (by norm_num) zero_le_one
  obtain ⟨C1, hC1def⟩ : ∃ C1 : ℝ, C1 = max C0 0 := ⟨_, rfl⟩
  have hC10 : 0 ≤ C1 := by rw [hC1def]; exact le_max_right _ _
  have hC1C0 : C0 ≤ C1 := by rw [hC1def]; exact le_max_left _ _
  obtain ⟨t0, ht0def⟩ : ∃ t0 : ℝ, t0 = 1 / (20 * (C1 + 1)) := ⟨_, rfl⟩
  have ht0 : 0 < t0 := by rw [ht0def]; positivity
  have hCt : C1 * t0 ≤ 1 / 20 := by
    rw [ht0def, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨min eps1 (t0 ^ 3), lt_min h1.1 (by positivity), (min_le_left _ _).trans h1.2, C1, hC10,
    ?_⟩
  intro d B p ν beta hB hp he hε hs
  have hε1 : 1 - beta ≤ eps1 := hε.trans (min_le_left _ _)
  have heps12 : 1 - beta ≤ 1 / 2 := hε1.trans h1.2
  have hb1 : beta < 1 := by linarith
  have hb0 : 0 < beta := by linarith
  have hnu := lsNu_pos (d := d) (B := B) (p := p) hB hb0.le hb1 hp
  have hnnp := lsNuNoise_pos (d := d) (B := B) (p := p) hB hb1 hp
  have hnnlt := lsNuNoise_lt (d := d) (B := B) (p := p) hB hb0.le hb1 hp
  have hDm : (1 / 2 : ℝ) ∈ Set.Ioo 0 (2 / lsNu d B p beta) := by
    refine ⟨by norm_num, ?_⟩
    rw [lt_div_iff₀ hnu]; linarith
  obtain ⟨eta0, heta0, hDe⟩ : ∃ eta0 ∈ Set.Ioo 0 (criticalRate d B p beta),
      eta0 * p / (1 - beta) = 1 / 2 := by
    rw [← ls_Delta_image hB hb0.le hb1 hp] at hDm
    obtain ⟨eta, h, e⟩ := hDm
    exact ⟨eta, h, e⟩
  obtain ⟨un, hun⟩ : ∃ un : ℝ, un = (params d B p ν beta eta0).noise := ⟨_, rfl⟩
  have hnoise := params_noise_ray (d := d) (B := B) (p := p) hB hb1 hp ν eta0
  rw [hDe, ← hun] at hnoise
  have hun0 : 0 ≤ un := by rw [hnoise]; positivity
  have hun4 : 4 * un ≤ lsNu d B p beta := by rw [hnoise]; linarith
  have hun1 : un ≤ 1 := by linarith
  have hT := (hC0 (1 - beta) ⟨he, hε1⟩ (1 / 2) ⟨by norm_num, le_rfl⟩ un ⟨hun0, hun1⟩).1
  have hrate : lsRate d B p ν beta eta0 = perStepRate (transferParams (1 - beta) (1 / 2) un) := by
    unfold lsRate
    apply perStepRate_congr
    · simp [params, oracleParams]
    · rw [params_w_eq (d := d) (B := B) hp ν hb1 eta0, hDe]
    · exact hun.symm
  have hrc : 1 - (2 * un) ^ ((1 : ℝ) / 3) ≤ continuumPerronRate (1 / 2) un := by
    have h := continuumPerronRate_close (1 / 2) un (1 / 2) 0 (by norm_num)
      (by rw [sub_zero, abs_of_nonneg hun0]; linarith)
    have h0 := continuumPerronRate_zero_load (delta := (1 / 2 : ℝ)) (by norm_num)
    have h0' : continuumPerronRate (1 / 2) 0 = 1 := by
      rw [h0]; norm_num
    have h' : |continuumPerronRate (1 / 2) un - continuumPerronRate (1 / 2) 0|
        ≤ (2 * un) ^ ((1 : ℝ) / 3) := by
      have harg : 4 * |(1 / 2 : ℝ) - 1 / 2| * rateRadius (|(1 / 2 : ℝ)| + 1) (|(0 : ℝ)| + 1)
          + 4 * |(1 / 2 : ℝ) * (1 - un) - 1 / 2 * (1 - 0)| = 2 * un := by
        have hab : |(1 / 2 : ℝ) * (1 - un) - 1 / 2 * (1 - 0)| = un / 2 := by
          rw [show (1 / 2 : ℝ) * (1 - un) - 1 / 2 * (1 - 0) = -(un / 2) by ring, abs_neg,
            abs_of_nonneg (by positivity)]
        rw [hab, sub_self, abs_zero]
        ring
      exact h.trans (le_of_eq (congrArg (fun t : ℝ => t ^ ((1 : ℝ) / 3)) harg))
    rw [h0'] at h'
    have := (abs_le.1 h').1
    linarith
  have hroot_s : (2 * un) ^ ((1 : ℝ) / 3) ≤ lsNu d B p beta ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hroot_9 : (2 * un) ^ ((1 : ℝ) / 3) ≤ 9 / 10 :=
    rpow_third_le (by positivity) (by norm_num) (by norm_num; linarith)
  have hbdd := lsRate_bddAbove (d := d) (p := p) hB hp ν hb0 hb1
  have hLam : lsRate d B p ν beta eta0 ≤ lsLamStar d B p ν beta :=
    le_csSup hbdd ⟨eta0, heta0, rfl⟩
  rw [hrate] at hLam
  have hT' := (abs_le.1 hT).1
  have h43 : (1 - beta) ^ ((4 : ℝ) / 3) = (1 - beta) * (1 - beta) ^ ((1 : ℝ) / 3) :=
    rpow_four_thirds_eq he
  have he3 : (1 - beta) ^ ((1 : ℝ) / 3) ≤ t0 :=
    rpow_third_le he.le ht0.le (hε.trans (min_le_right _ _))
  have he3pos : 0 ≤ (1 - beta) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg he.le _
  have hC0e : C0 * (1 - beta) ^ ((4 : ℝ) / 3) ≤ C1 * (1 - beta) ^ ((4 : ℝ) / 3) :=
    mul_le_mul_of_nonneg_right hC1C0 (Real.rpow_nonneg he.le _)
  have hm1 : (1 - beta) * (1 - lsNu d B p beta ^ ((1 : ℝ) / 3))
      ≤ (1 - beta) * continuumPerronRate (1 / 2) un :=
    mul_le_mul_of_nonneg_left (by linarith) he.le
  have hm2 : (1 - beta) * (1 / 10) ≤ (1 - beta) * continuumPerronRate (1 / 2) un :=
    mul_le_mul_of_nonneg_left (by linarith) he.le
  refine ⟨by linarith, ?_⟩
  have hk : C1 * (1 - beta) ^ ((4 : ℝ) / 3) ≤ (1 - beta) / 20 := by
    rw [h43]
    have : C1 * (1 - beta) ^ ((1 : ℝ) / 3) ≤ 1 / 20 :=
      (mul_le_mul_of_nonneg_left he3 hC10).trans hCt
    nlinarith
  linarith

/-- (A3) `v2 cor:sample_cost` (ii), case `s → 0`, uniform form: there are `ε₀ ∈ (0, 1/2]` and
`C ≥ 0` such that for all `(d, B, p, β)` with `ε = 1-β ≤ ε₀` and `s = ν(B,p,β) ≤ 1`,
`|Λ*/ε - 1| ≤ C (ε^{1/3} + s^{1/3})` and
`|N_1/N - 1| ≤ C (ε^{1/3} + s^{1/3})`, with `N = hyperbolaN N_stab N_mem`.
(`s` is the paper's `s = N_stab/N_mem`; the bounds are uniform, there is no `ε → 0` taken
along a fixed ray.) -/
theorem samplecost_above :
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 / 2 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta : ℝ),
        0 < B → 0 < (p : ℝ) → 0 < 1 - beta → 1 - beta ≤ eps0 → lsNu d B p beta ≤ 1 →
        |lsLamStar d B p ν beta / (1 - beta) - 1|
            ≤ C * ((1 - beta) ^ ((1 : ℝ) / 3) + lsNu d B p beta ^ ((1 : ℝ) / 3)) ∧
        |lsNfold d B p ν beta / hyperbolaN (lsNstab d B p beta) (lsNmem B p beta) - 1|
            ≤ C * ((1 - beta) ^ ((1 : ℝ) / 3) + lsNu d B p beta ^ ((1 : ℝ) / 3)) := by
  obtain ⟨eps0, he0, he0h, C1, hC10, hC1⟩ := lsLamStar_lower_small_nu
  refine ⟨eps0, he0, he0h, 20 * (C1 + 3), by positivity, ?_⟩
  intro d B p ν beta hB hp he hε hs
  obtain ⟨hlow, h20⟩ := hC1 d B p ν beta hB hp he hε hs
  have heps12 : 1 - beta ≤ 1 / 2 := hε.trans he0h
  have hb1 : beta < 1 := by linarith
  have hb0 : 0 < beta := by linarith
  have hnu := lsNu_pos (d := d) (B := B) (p := p) hB hb0.le hb1 hp
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hpB : 0 < (p : ℝ) * B := by positivity
  obtain ⟨e3, he3def⟩ : ∃ e3 : ℝ, e3 = (1 - beta) ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ, f = lsNu d B p beta ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  rw [← he3def, ← hfdef]
  have he3pos : 0 ≤ e3 := by rw [he3def]; exact Real.rpow_nonneg he.le _
  have hf0 : 0 ≤ f := by rw [hfdef]; exact Real.rpow_nonneg hnu.le _
  have hε_le : 1 - beta ≤ e3 := by
    rw [he3def]; exact le_rpow_third he.le (by linarith)
  have hs_le : lsNu d B p beta ≤ f := by
    rw [hfdef]; exact le_rpow_third hnu.le hs
  have h43 : (1 - beta) ^ ((4 : ℝ) / 3) = (1 - beta) * e3 := by
    rw [he3def]; exact rpow_four_thirds_eq he
  rw [h43] at hlow
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = lsLamStar d B p ν beta / (1 - beta) := ⟨_, rfl⟩
  have hLx : lsLamStar d B p ν beta = x * (1 - beta) := by rw [hxdef]; field_simp
  rw [hLx] at hlow h20
  rw [← hfdef] at hlow
  have hx_lo : 1 - f - C1 * e3 ≤ x := by
    have : (1 - f - C1 * e3) * (1 - beta) ≤ x * (1 - beta) := by linarith
    exact le_of_mul_le_mul_right this he
  have hx20 : 1 / 20 ≤ x := by
    have : (1 / 20) * (1 - beta) ≤ x * (1 - beta) := by linarith
    exact le_of_mul_le_mul_right this he
  -- upper bound
  have hLam_up := lsLamStar_le_neg_log_beta (d := d) hB hp ν hb0 hb1
  have hlog := neg_log_one_sub_le (x := 1 - beta) (by linarith)
  have hbeta_eq : 1 - (1 - beta) = beta := by ring
  rw [hbeta_eq] at hlog
  have hx_up : x ≤ 1 + 2 * e3 := by
    rw [hxdef, div_le_iff₀ he]
    have h1 : -Real.log beta ≤ (1 - beta) / beta := hlog
    have h2 : (1 - beta) / beta ≤ (1 - beta) * (1 + 2 * (1 - beta)) := by
      rw [div_le_iff₀ hb0]
      nlinarith [mul_nonneg (sq_nonneg (1 - beta)) (by linarith : (0 : ℝ) ≤ 1 - 2 * (1 - beta))]
    have h3 : (1 - beta) * (1 + 2 * (1 - beta)) ≤ (1 + 2 * e3) * (1 - beta) := by
      nlinarith
    linarith
  have hxabs : |x - 1| ≤ (C1 + 2) * (e3 + f) := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hC10 he3pos, mul_nonneg hC10 hf0]
  refine ⟨?_, ?_⟩
  · rw [← hxdef]
    refine hxabs.trans ?_
    nlinarith
  · -- ratio
    set S := lsNstab d B p beta with hS
    set M := lsNmem B p beta with hM
    have hMpos : 0 < M := lsNmem_pos hB hb1 hp
    have hSpos : 0 < S := lsNstab_pos hB hb0.le hb1
    have hSM : S / M = lsNu d B p beta := by
      have h1 : S = lsNu d B p beta * M := lsNstab_eq_nu_mul hB hb0.le hb1 hp
      rw [h1, mul_div_cancel_right₀ _ hMpos.ne']
    have hN := hyperbola_eq hSpos hMpos
    rw [hSM] at hN
    have hr_pos := rayRate_pos hnu
    have hr_le := rayRate_lt_one hnu
    have hr_ge := rayRate_ge_one_sub_half hnu
    rw [← hN]
    have hx0 : 0 < x := by linarith
    have hratio : lsNfold d B p ν beta / (M / rayRate (lsNu d B p beta))
        = rayRate (lsNu d B p beta) / x := by
      unfold lsNfold
      rw [hLx, hM]
      unfold lsNmem
      field_simp
    rw [hratio]
    have e1 : rayRate (lsNu d B p beta) / x - 1 = (rayRate (lsNu d B p beta) - x) / x := by
      field_simp
    rw [e1, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    have hd1 : |rayRate (lsNu d B p beta) - x|
        ≤ |rayRate (lsNu d B p beta) - 1| + |x - 1| := by
      have := abs_sub_le (rayRate (lsNu d B p beta)) 1 x
      rwa [abs_sub_comm 1 x] at this
    have hd2 : |rayRate (lsNu d B p beta) - 1| ≤ f := by
      rw [abs_le]; constructor <;> linarith
    have hd3 : |rayRate (lsNu d B p beta) - x| ≤ f + (C1 + 2) * (e3 + f) := by linarith
    have hd4 : |rayRate (lsNu d B p beta) - x| ≤ (C1 + 3) * (e3 + f) := by
      have e : f + (C1 + 2) * (e3 + f) + e3 = (C1 + 3) * (e3 + f) := by ring
      linarith
    have hQ0 : 0 ≤ (C1 + 3) * (e3 + f) := by positivity
    have h5 : (C1 + 3) * (e3 + f) ≤ 20 * (C1 + 3) * (e3 + f) * x := by
      have h6 := mul_nonneg hQ0 (by linarith : 0 ≤ 20 * x - 1)
      have e : 20 * (C1 + 3) * (e3 + f) * x - (C1 + 3) * (e3 + f)
          = (C1 + 3) * (e3 + f) * (20 * x - 1) := by ring
      linarith
    linarith

end A3

end

end SparseSGD.Scaling.Helps
