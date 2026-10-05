import SparseSGD.Scaling.Helps.Transfer
import SparseSGD.Scaling.Helps.Ray
import SparseSGD.Scaling.Helps.ExactRate
import SparseSGD.Scaling.Helps.SpeedupExpansion

/-!
# Sample-cost and speedup limits (v2 `cor:samplecost`, `cor:helps-speedup`, `lem:helps-vocab` (iii))

Uniform quantitative forms of the `ε → 0` statements of `paper/appendix/momentum_helps.tex`.

* **(L1)** ray parametrization of LS: `Δ = η p / ε`, `u = ν Δ / 2`, `u_n = ν_n Δ / 2`,
  `N_stab = ν N_mem`, and the SGD comparison `N_fold^SGD ≤ 2B/η_+(0)`.
* **(L2)** `cor:samplecost`: for `ν ∈ [ν₀/2, 2ν₀]` and `ε ≤ ε₀`,
  `|Λ* - ε r_*(ν)| ≤ C ε^{4/3}`, `|N_fold / N - 1| ≤ C ε^{1/3}`, the hyperbola, and the
  comparisons (iii).
* **(L3)** `cor:helps-speedup`, on a compact `K ⊆ (0,∞) × [0,1)`.
* **(L4)** `lem:helps-vocab` (iii), last claim.

The tex phrase "vary so that `ε → 0` and `ν → ν₀`" is formalized as the statement with explicit
constants `ε₀, C` depending only on `ν₀` (resp. `K`), valid for all `(d, B, p, β)` with
`ε = 1-β ≤ ε₀` and `ν ∈ [ν₀/2, 2ν₀]`.  The hypothesis `β ≥ 1/2` of the tex is implied by
`ε ≤ ε₀ ≤ 1/2`.  The label-noise measure `ν` of `LeastSquares.params` is arbitrary since the
additive part of the parameters does not enter the radius.
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD SparseSGD.Probability.LeastSquares MeasureTheory

noncomputable section

/-! ### Notation for LS -/

/-- Per-step rate `Λ(η)` of LS at fixed `(d,B,p,β)` (`sec:helps-rate`). -/
def lsRate (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta eta : ℝ) : ℝ :=
  perStepRate (params d B p ν beta eta)

/-- `ν = 2 ε / (p η_+)` (`cor:samplecost`). -/
def lsNu (d B : ℕ) (p : unitInterval) (beta : ℝ) : ℝ :=
  2 * (1 - beta) / ((p : ℝ) * criticalRate d B p beta)

/-- Noise ray slope `ν_n = ε (d+2-p)/(pB)`. -/
def lsNuNoise (d B : ℕ) (p : unitInterval) (beta : ℝ) : ℝ :=
  (1 - beta) * ((d : ℝ) + 2 - p) / ((p : ℝ) * B)

/-- `Λ* = sup_{0<η<η_+} Λ(η)` (`cor:samplecost`). -/
def lsLamStar (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta : ℝ) : ℝ :=
  sSup (lsRate d B p ν beta '' Set.Ioo 0 (criticalRate d B p beta))

/-- `N_fold = pB / Λ*`. -/
def lsNfold (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta : ℝ) : ℝ :=
  (p : ℝ) * B / lsLamStar d B p ν beta

/-- `N_stab = 2B/η_+`. -/
def lsNstab (d B : ℕ) (p : unitInterval) (beta : ℝ) : ℝ :=
  2 * B / criticalRate d B p beta

/-- `N_mem = pB/ε`. -/
def lsNmem (B : ℕ) (p : unitInterval) (beta : ℝ) : ℝ :=
  (p : ℝ) * B / (1 - beta)

/-- `N_fold^SGD = pB / sup_{0<η<η_+(0)} Λ(η)` for plain SGD (`β = 0`). -/
def lsNfoldSGD (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) : ℝ :=
  (p : ℝ) * B / lsLamStar d B p ν 0

/-! ### L1: the ray parametrization -/

section L1

variable {d B : ℕ} {p : unitInterval} {beta : ℝ}

theorem lsInv_pos (hB : 0 < B) (hb0 : 0 ≤ beta) (hb1 : beta < 1) :
    0 < inverseCriticalRate d B p beta := inverseCriticalRate_pos d B hB p beta hb0 hb1

theorem criticalRate_pos' (hB : 0 < B) (hb0 : 0 ≤ beta) (hb1 : beta < 1) :
    0 < criticalRate d B p beta := inv_pos.2 (lsInv_pos hB hb0 hb1)

/-- `ν = 2 ε / (p η_+) = 2 ε η_+^{-1} / p`. -/
theorem lsNu_eq (hB : 0 < B) (hb0 : 0 ≤ beta) (hb1 : beta < 1) (hp : 0 < (p : ℝ)) :
    lsNu d B p beta = 2 * (1 - beta) * inverseCriticalRate d B p beta / p := by
  have hi := lsInv_pos (d := d) (p := p) hB hb0 hb1
  unfold lsNu criticalRate
  field_simp

theorem lsNu_pos (hB : 0 < B) (hb0 : 0 ≤ beta) (hb1 : beta < 1) (hp : 0 < (p : ℝ)) :
    0 < lsNu d B p beta := by
  rw [lsNu_eq hB hb0 hb1 hp]
  have := lsInv_pos (d := d) (p := p) hB hb0 hb1
  have : 0 < 1 - beta := by linarith
  positivity

theorem lsNstab_eq :
    lsNstab d B p beta = 2 * B * inverseCriticalRate d B p beta := by
  unfold lsNstab criticalRate
  rw [div_inv_eq_mul]

/-- `N_stab = ν N_mem`. -/
theorem lsNstab_eq_nu_mul (hB : 0 < B) (hb0 : 0 ≤ beta) (hb1 : beta < 1) (hp : 0 < (p : ℝ)) :
    lsNstab d B p beta = lsNu d B p beta * lsNmem B p beta := by
  rw [lsNstab_eq, lsNu_eq hB hb0 hb1 hp]
  unfold lsNmem
  have : 0 < 1 - beta := by linarith
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  field_simp

/-- `N_stab = d+2-p + pBε/(2-ε)`. -/
theorem lsNstab_eq_explicit (hB : 0 < B) (hb0 : 0 ≤ beta) :
    lsNstab d B p beta
      = (d : ℝ) + 2 - p + (p : ℝ) * B * (1 - beta) / (2 - (1 - beta)) := by
  rw [lsNstab_eq]
  unfold inverseCriticalRate
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have : (1 + beta) ≠ 0 := by linarith
  have h2 : (2 - (1 - beta)) = 1 + beta := by ring
  rw [h2]
  field_simp

theorem lsNstab_ge (hB : 0 < B) (hb0 : 0 ≤ beta) (hb1 : beta < 1) :
    (d : ℝ) + 2 - p ≤ lsNstab d B p beta := by
  rw [lsNstab_eq_explicit hB hb0]
  have hp0 := p.2.1
  have hB' : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have : 0 < 1 - beta := by linarith
  have : 0 ≤ (p : ℝ) * B * (1 - beta) / (2 - (1 - beta)) :=
    div_nonneg (by positivity) (by linarith)
  linarith

theorem lsNstab_pos (hB : 0 < B) (hb0 : 0 ≤ beta) (hb1 : beta < 1) :
    0 < lsNstab d B p beta := by
  have h := lsNstab_ge (d := d) (p := p) hB hb0 hb1
  have hp1 := p.2.2
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem lsNmem_pos (hB : 0 < B) (hb1 : beta < 1) (hp : 0 < (p : ℝ)) :
    0 < lsNmem B p beta := by
  unfold lsNmem
  have : 0 < 1 - beta := by linarith
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  positivity

theorem params_w_eq (hp : 0 < (p : ℝ)) (ν : Measure ℝ) (hb1 : beta < 1) (eta : ℝ) :
    (params d B p ν beta eta).w = (1 - beta) ^ 2 * (eta * p / (1 - beta)) := by
  have : 1 - beta ≠ 0 := by linarith
  simp only [params, oracleParams]
  field_simp

theorem params_noise_eq (hB : 0 < B) (hp : 0 < (p : ℝ)) (ν : Measure ℝ) (eta : ℝ) :
    (params d B p ν beta eta).noise = eta * (((d : ℝ) + 2 - p) / (2 * B)) := by
  simp only [params, oracleParams, vinc]
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  field_simp

/-- Along the ray: `u = ν Δ / 2` with `Δ = η p / ε`. -/
theorem params_totalLoad_ray (hB : 0 < B) (hb0 : 0 ≤ beta) (hb1 : beta < 1) (hp : 0 < (p : ℝ))
    (ν : Measure ℝ) (eta : ℝ) :
    (params d B p ν beta eta).totalLoad
      = lsNu d B p beta * (eta * p / (1 - beta)) / 2 := by
  rw [params_totalLoad d B p hp.ne', lsNu_eq hB hb0 hb1 hp]
  have : 1 - beta ≠ 0 := by linarith
  field_simp

/-- Along the ray: `u_n = ν_n Δ / 2`. -/
theorem params_noise_ray (hB : 0 < B) (hb1 : beta < 1) (hp : 0 < (p : ℝ))
    (ν : Measure ℝ) (eta : ℝ) :
    (params d B p ν beta eta).noise
      = lsNuNoise d B p beta * (eta * p / (1 - beta)) / 2 := by
  rw [params_noise_eq hB hp]
  unfold lsNuNoise
  have : 1 - beta ≠ 0 := by linarith
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  field_simp

/-- `ν_n = ν - ε²/(2-ε)`. -/
theorem lsNuNoise_eq (hB : 0 < B) (hb0 : 0 ≤ beta) (hb1 : beta < 1) (hp : 0 < (p : ℝ)) :
    lsNuNoise d B p beta = lsNu d B p beta - (1 - beta) ^ 2 / (2 - (1 - beta)) := by
  rw [lsNu_eq hB hb0 hb1 hp]
  unfold lsNuNoise inverseCriticalRate
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have : (1 + beta) ≠ 0 := by linarith
  have h2 : (2 - (1 - beta)) = 1 + beta := by ring
  rw [h2]
  field_simp
  ring

theorem lsNuNoise_pos (hB : 0 < B) (hb1 : beta < 1) (hp : 0 < (p : ℝ)) :
    0 < lsNuNoise d B p beta := by
  unfold lsNuNoise
  have : 0 < 1 - beta := by linarith
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hp1 := p.2.2
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have : 0 < (d : ℝ) + 2 - p := by linarith
  positivity

theorem lsNuNoise_lt (hB : 0 < B) (hb0 : 0 ≤ beta) (hb1 : beta < 1) (hp : 0 < (p : ℝ)) :
    lsNuNoise d B p beta < lsNu d B p beta := by
  rw [lsNuNoise_eq hB hb0 hb1 hp]
  have : 0 < 1 - beta := by linarith
  have : 0 < (1 - beta) ^ 2 / (2 - (1 - beta)) := div_pos (by positivity) (by linarith)
  linarith

/-- `η ↦ Δ = η p/ε` maps `(0, η_+)` onto `(0, 2/ν)`. -/
theorem ls_Delta_image (hB : 0 < B) (hb0 : 0 ≤ beta) (hb1 : beta < 1) (hp : 0 < (p : ℝ)) :
    (fun eta : ℝ => eta * p / (1 - beta)) '' Set.Ioo 0 (criticalRate d B p beta)
      = Set.Ioo 0 (2 / lsNu d B p beta) := by
  have he : 0 < 1 - beta := by linarith
  have hnu := lsNu_pos (d := d) (B := B) (p := p) hB hb0 hb1 hp
  have hnu_eq := lsNu_eq (d := d) hB hb0 hb1 hp
  have hi := lsInv_pos (d := d) (p := p) hB hb0 hb1
  -- 2/ν = p / (ε i) = (p/ε) η_+
  have key : 2 / lsNu d B p beta = (p : ℝ) / (1 - beta) * criticalRate d B p beta := by
    rw [hnu_eq]; unfold criticalRate; field_simp
  rw [key]
  ext D
  simp only [Set.mem_image, Set.mem_Ioo]
  constructor
  · rintro ⟨eta, ⟨h0, h1⟩, rfl⟩
    refine ⟨by positivity, ?_⟩
    rw [div_mul_eq_mul_div, div_lt_div_iff_of_pos_right he] 
    rw [mul_comm (p : ℝ)]
    exact mul_lt_mul_of_pos_right h1 hp
  · rintro ⟨h0, h1⟩
    refine ⟨D * (1 - beta) / p, ⟨by positivity, ?_⟩, by field_simp⟩
    rw [div_lt_iff₀ hp]
    rw [div_mul_eq_mul_div, lt_div_iff₀ he] at h1
    linarith

/-- (L1) `2B/η_+(0) - N_stab = pB (1 - ε/(2-ε)) ≤ ε N_mem`. -/
theorem lsNstab_zero_sub (hB : 0 < B) (hb0 : 0 ≤ beta) :
    2 * B / criticalRate d B p 0 - lsNstab d B p beta
      = (p : ℝ) * B * (1 - (1 - beta) / (2 - (1 - beta))) := by
  rw [lsNstab_eq_explicit hB hb0]
  unfold criticalRate inverseCriticalRate
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have : (2 - (1 - beta)) ≠ 0 := by linarith
  simp only [sub_zero, add_zero, div_one, mul_one]
  rw [div_inv_eq_mul]
  field_simp
  ring

theorem lsNstab_zero_sub_le (hB : 0 < B) (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (hp : 0 < (p : ℝ)) :
    2 * B / criticalRate d B p 0 - lsNstab d B p beta ≤ (1 - beta) * lsNmem B p beta := by
  rw [lsNstab_zero_sub hB hb0]
  unfold lsNmem
  have he : 0 < 1 - beta := by linarith
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have : 0 ≤ (1 - beta) / (2 - (1 - beta)) := div_nonneg he.le (by linarith)
  have h2 : (1 - beta) * ((p : ℝ) * B / (1 - beta)) = p * B := by field_simp
  rw [h2]
  have : 0 ≤ (p : ℝ) * B := by positivity
  nlinarith

/-- `-log(1-x) ≥ x` for `x < 1`. -/
theorem neg_log_one_sub_ge {x : ℝ} (hx : x < 1) : x ≤ -Real.log (1 - x) := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 - x by linarith)
  linarith

/-- `-log(1-x) ≤ x/(1-x)` for `x < 1`. -/
theorem neg_log_one_sub_le {x : ℝ} (hx : x < 1) : -Real.log (1 - x) ≤ x / (1 - x) := by
  have h1 : 0 < 1 - x := by linarith
  have := Real.log_le_sub_one_of_pos (inv_pos.2 h1)
  rw [Real.log_inv] at this
  have e : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
  linarith

/-- Plain SGD rate for LS: `Λ(η) = -log(1 - 2w(1-u))`, with `2w(1-u) ∈ (0, p η_+(0)/2]`
(`lem:helps-sgd`, LS part). -/
theorem lsRate_zero_eq (hB : 0 < B) (hp : 0 < (p : ℝ)) (ν : Measure ℝ) {eta : ℝ}
    (he : eta ∈ Set.Ioo 0 (criticalRate d B p 0)) :
    lsRate d B p ν 0 eta
      = -Real.log (1 - 2 * (params d B p ν 0 eta).w * (1 - (params d B p ν 0 eta).totalLoad)) := by
  have hlt : (params d B p ν 0 eta).totalLoad < 1 :=
    (totalLoad_lt_one_iff_eta_lt_critical d B hB p hp ν 0 eta le_rfl zero_lt_one).2 he.2
  have hw : 0 < (params d B p ν 0 eta).w := by
    rw [ls_params_w_beta_zero]; exact mul_pos he.1 hp
  have hn : 0 ≤ (params d B p ν 0 eta).noise := by
    rw [ls_params_noise_beta_zero d B p hp.ne']
    have hB' : (0 : ℝ) < B := by exact_mod_cast hB
    have hp1 := p.2.2
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : 0 ≤ ((d : ℝ) + 2 - p) / (2 * B) := div_nonneg (by linarith) (by positivity)
    exact mul_nonneg he.1.le this
  exact (sgd_coeff_bounds (params d B p ν 0 eta) (by simp [params, oracleParams]) hw hn hlt).2.2

/-- (L1) `p η_+(0)/2 ≤ Λ*_SGD`, in particular `Λ*_SGD > 0`. -/
theorem lsLamStar_zero_ge (hB : 0 < B) (hp : 0 < (p : ℝ)) (ν : Measure ℝ) :
    (p : ℝ) * criticalRate d B p 0 / 2 ≤ lsLamStar d B p ν 0 := by
  obtain ⟨⟨eta0, he0, hv⟩, hub⟩ := (ls_beta_zero_sup d B hB p hp ν).1
  have hlt := (ls_beta_zero_sup d B hB p hp ν).2
  set xm : ℝ := (p : ℝ) * criticalRate d B p 0 / 2 with hxm
  have hbdd : BddAbove (lsRate d B p ν 0 '' Set.Ioo 0 (criticalRate d B p 0)) := by
    refine ⟨-Real.log (1 - xm), ?_⟩
    rintro _ ⟨eta, he, rfl⟩
    rw [lsRate_zero_eq hB hp ν he]
    have hx := hub ⟨eta, he, rfl⟩
    have h1 : 0 < 1 - xm := by linarith
    have := Real.log_le_log h1 (show 1 - xm ≤ 1 - 2 * (params d B p ν 0 eta).w
      * (1 - (params d B p ν 0 eta).totalLoad) by simp only at hx; linarith)
    linarith
  have h1 : lsRate d B p ν 0 eta0 ≤ lsLamStar d B p ν 0 := le_csSup hbdd ⟨eta0, he0, rfl⟩
  rw [lsRate_zero_eq hB hp ν he0] at h1
  simp only at hv
  rw [hv] at h1
  have := neg_log_one_sub_ge hlt
  linarith

/-- (L1) `N_fold^SGD ≤ 2B/η_+(0)`. -/
theorem lsNfoldSGD_le (hB : 0 < B) (hp : 0 < (p : ℝ)) (ν : Measure ℝ) :
    lsNfoldSGD d B p ν ≤ 2 * B / criticalRate d B p 0 := by
  have hcp := criticalRate_pos' (d := d) (B := B) (p := p) hB le_rfl zero_lt_one
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hge := lsLamStar_zero_ge (d := d) hB hp ν
  have hpos : 0 < (p : ℝ) * criticalRate d B p 0 / 2 := by positivity
  unfold lsNfoldSGD
  calc (p : ℝ) * B / lsLamStar d B p ν 0
      ≤ (p : ℝ) * B / ((p : ℝ) * criticalRate d B p 0 / 2) :=
        div_le_div_of_nonneg_left (by positivity) hpos hge
    _ = 2 * B / criticalRate d B p 0 := by field_simp

/-- `N_fold^SGD ≥ 0`. -/
theorem lsNfoldSGD_nonneg (hB : 0 < B) (hp : 0 < (p : ℝ)) (ν : Measure ℝ) :
    0 ≤ lsNfoldSGD d B p ν := by
  have hcp := criticalRate_pos' (d := d) (B := B) (p := p) hB le_rfl zero_lt_one
  have hge := lsLamStar_zero_ge (d := d) hB hp ν
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hpos : 0 < (p : ℝ) * criticalRate d B p 0 / 2 := by positivity
  unfold lsNfoldSGD
  exact div_nonneg (by positivity) (by linarith)

end L1

/-! ### L2: the sample cost -/

section L2

/-- `perStepRate` depends only on `(β, w, u_n)`. -/
theorem perStepRate_congr {p q : Params} (h1 : p.beta = q.beta) (h2 : p.w = q.w)
    (h3 : p.noise = q.noise) : perStepRate p = perStepRate q := by
  obtain ⟨b, w, n, a⟩ := p
  obtain ⟨b', w', n', a'⟩ := q
  simp only at h1 h2 h3
  subst h1 h2 h3
  simp [perStepRate, stepRadius, stepRoots]

/-- Transfer along the ray (Tr2, second bound, `D = 4/ν₀`, `c = ν₀`), for LS
(`cor:samplecost`, Step 2). -/
theorem lsRate_close (nu0 : ℝ) (hnu0 : 0 < nu0) :
    ∃ eps1 : ℝ, eps1 ∈ Set.Ioc (0 : ℝ) (1 / 2) ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta : ℝ),
        0 < B → 0 < (p : ℝ) → 1 - beta ∈ Set.Ioc (0 : ℝ) eps1 →
        lsNu d B p beta ∈ Set.Icc (nu0 / 2) (2 * nu0) →
        ∀ eta ∈ Set.Ioo 0 (criticalRate d B p beta),
          |lsRate d B p ν beta eta
              - (1 - beta) * continuumPerronRate (eta * p / (1 - beta))
                  (lsNu d B p beta * (eta * p / (1 - beta)) / 2)|
            ≤ C * (1 - beta) ^ ((4 : ℝ) / 3) := by
  obtain ⟨eps1, h1, C0, hC0⟩ := helps_transfer (4 / nu0) nu0 (by positivity) hnu0
  refine ⟨eps1, h1, max C0 0, le_max_right _ _, ?_⟩
  intro d B p ν beta hB hp hε hν eta heta
  have hb1 : beta < 1 := by linarith [hε.1]
  have hb0 : 0 ≤ beta := by linarith [hε.2, h1.2]
  have he : 0 < 1 - beta := hε.1
  set eps : ℝ := 1 - beta with heps
  set Delta : ℝ := eta * p / eps with hDelta
  have hnu := lsNu_pos (d := d) (B := B) (p := p) hB hb0 hb1 hp
  have hDmem : Delta ∈ Set.Ioo 0 (2 / lsNu d B p beta) := by
    rw [← ls_Delta_image hB hb0 hb1 hp]; exact ⟨eta, heta, rfl⟩
  have hD2 : Delta ≤ 4 / nu0 := by
    have : 2 / lsNu d B p beta ≤ 4 / nu0 := by
      rw [div_le_div_iff₀ hnu hnu0]; nlinarith [hν.1]
    linarith [hDmem.2]
  have hnoise := params_noise_ray (d := d) (B := B) (p := p) hB hb1 hp ν eta
  have hnnp := lsNuNoise_pos (d := d) (B := B) (p := p) hB hb1 hp
  have hnnlt := lsNuNoise_lt (d := d) (B := B) (p := p) hB hb0 hb1 hp
  set un : ℝ := (params d B p ν beta eta).noise with hun
  have hun0 : 0 ≤ un := by rw [hnoise]; have := hDmem.1; positivity
  have hun1 : un ≤ nu0 * Delta := by
    rw [hnoise]
    have := hDmem.1
    nlinarith [hν.2]
  have hT := (hC0 eps ⟨he, hε.2⟩ Delta ⟨hDmem.1, hD2⟩ un ⟨hun0, hun1⟩).2
  have hcurv : (transferParams eps Delta un).curvature = (params d B p ν beta eta).curvature := by
    have hw := params_w_eq (d := d) (B := B) hp ν hb1 eta
    have hbeta : (params d B p ν beta eta).beta = beta := rfl
    show eps ^ 2 * Delta / (2 * (1 + (1 - eps))) =
      (params d B p ν beta eta).w / (2 * (1 + (params d B p ν beta eta).beta))
    rw [hw, hbeta]
    have : 1 - eps = beta := by rw [heps]; ring
    rw [this]
  have hload : un + (transferParams eps Delta un).curvature
      = lsNu d B p beta * Delta / 2 := by
    rw [hcurv, ← params_totalLoad_ray hB hb0 hb1 hp ν eta]
    rfl
  have hrate : lsRate d B p ν beta eta = perStepRate (transferParams eps Delta un) := by
    unfold lsRate
    apply perStepRate_congr
    · simp [params, oracleParams, heps]
    · rw [params_w_eq (d := d) (B := B) hp ν hb1 eta]
    · rfl
  rw [hrate]
  rw [hload] at hT
  refine hT.trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg he.le _)

/-- `r_*(ν) ≥ 1/(1+ν)`. -/
theorem rayRate_ge {nu : ℝ} (hnu : 0 < nu) : 1 / (1 + nu) ≤ rayRate nu := by
  have h := inv_rayRate hnu
  have hr := rayRate_pos hnu
  have hs : Real.sqrt (1 + nu ^ 2) ≤ 1 + nu := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have h2 : 1 / rayRate nu ≤ 1 + nu := by rw [h]; linarith
  rw [div_le_iff₀ (by linarith)]
  rw [div_le_iff₀ hr] at h2
  linarith

/-- (L2 (i), first claim) `|Λ* - ε r_*(ν)| ≤ C ε^{4/3}` uniformly for `ν ∈ [ν₀/2, 2ν₀]`
(`cor:samplecost`, Steps 2). -/
theorem lsLamStar_close (nu0 : ℝ) (hnu0 : 0 < nu0) :
    ∃ eps1 : ℝ, eps1 ∈ Set.Ioc (0 : ℝ) (1 / 2) ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta : ℝ),
        0 < B → 0 < (p : ℝ) → 1 - beta ∈ Set.Ioc (0 : ℝ) eps1 →
        lsNu d B p beta ∈ Set.Icc (nu0 / 2) (2 * nu0) →
        |lsLamStar d B p ν beta - (1 - beta) * rayRate (lsNu d B p beta)|
            ≤ C * (1 - beta) ^ ((4 : ℝ) / 3) := by
  obtain ⟨eps1, h1, C, hC0, hC⟩ := lsRate_close nu0 hnu0
  refine ⟨eps1, h1, C, hC0, ?_⟩
  intro d B p ν beta hB hp hε hν
  have hb1 : beta < 1 := by linarith [hε.1]
  have hb0 : 0 ≤ beta := by linarith [hε.2, h1.2]
  have he : 0 < 1 - beta := hε.1
  have hnu := lsNu_pos (d := d) (B := B) (p := p) hB hb0 hb1 hp
  have hcp := criticalRate_pos' (d := d) (B := B) (p := p) hB hb0 hb1
  have hcl := hC d B p ν beta hB hp hε hν
  set eps : ℝ := 1 - beta with heps
  set nu : ℝ := lsNu d B p beta with hnudef
  set E : ℝ := C * eps ^ ((4 : ℝ) / 3) with hE
  have hne : (lsRate d B p ν beta '' Set.Ioo 0 (criticalRate d B p beta)).Nonempty :=
    ⟨_, criticalRate d B p beta / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hub : ∀ eta ∈ Set.Ioo 0 (criticalRate d B p beta),
      lsRate d B p ν beta eta ≤ eps * rayRate nu + E := by
    intro eta heta
    have h := hcl eta heta
    have hle := continuumPerronRate_ray_le hnu (eta * p / eps)
    have := mul_le_mul_of_nonneg_left hle he.le
    have := (abs_le.1 h).2
    linarith
  have hbdd : BddAbove (lsRate d B p ν beta '' Set.Ioo 0 (criticalRate d B p beta)) :=
    ⟨_, by rintro _ ⟨eta, heta, rfl⟩; exact hub eta heta⟩
  have hDm : rayDelta nu ∈ Set.Ioo 0 (2 / nu) := ⟨rayDelta_pos hnu, rayDelta_lt_two_div hnu⟩
  obtain ⟨eta0, heta0, hDe⟩ : ∃ eta0 ∈ Set.Ioo 0 (criticalRate d B p beta),
      eta0 * p / eps = rayDelta nu := by
    rw [← ls_Delta_image hB hb0 hb1 hp] at hDm
    obtain ⟨eta, h, e⟩ := hDm
    exact ⟨eta, h, e⟩
  rw [abs_le]
  constructor
  · have h := (abs_le.1 (hcl eta0 heta0)).1
    rw [hDe, continuumPerronRate_ray_at_rayDelta hnu] at h
    have h2 : lsRate d B p ν beta eta0 ≤ lsLamStar d B p ν beta :=
      le_csSup hbdd ⟨eta0, heta0, rfl⟩
    linarith
  · have := csSup_le hne (by rintro _ ⟨eta, heta, rfl⟩; exact hub eta heta)
    unfold lsLamStar
    linarith

/-- Perturbation of the hyperbola relation: if `Nfold = ρ N` with `|ρ-1| ≤ δ ≤ 1`, then
`(Nfold/S - 1)(Nfold/M - 1) - 1/2` is `O(δ)` with the bounds `N/S ≤ a`, `N/M ≤ b`. -/
theorem hyperbola_perturb {S M ρ δ a b : ℝ} (hS : 0 < S) (hM : 0 < M)
    (ha : hyperbolaN S M / S ≤ a) (hb : hyperbolaN S M / M ≤ b)
    (hρ : |ρ - 1| ≤ δ) (hδ : δ ≤ 1) :
    |(ρ * hyperbolaN S M / S - 1) * (ρ * hyperbolaN S M / M - 1) - 1 / 2| ≤ 3 * δ * a * b := by
  set N := hyperbolaN S M with hN
  have hmax := hyperbola_ge_max hS hM
  have hSN : S ≤ N := le_trans (le_max_left _ _) hmax
  have hMN : M ≤ N := le_trans (le_max_right _ _) hmax
  set α := N / S with hα
  set β' := N / M with hβ
  have hα1 : 1 ≤ α := by rw [hα, le_div_iff₀ hS]; linarith
  have hβ1 : 1 ≤ β' := by rw [hβ, le_div_iff₀ hM]; linarith
  have hrel : (α - 1) * (β' - 1) = 1 / 2 := hyperbola_relation hS hM
  have e1 : ρ * N / S = ρ * α := by rw [hα]; ring
  have e2 : ρ * N / M = ρ * β' := by rw [hβ]; ring
  rw [e1, e2]
  set t := ρ - 1 with ht
  have hρt : ρ = 1 + t := by rw [ht]; ring
  have key : (ρ * α - 1) * (ρ * β' - 1) - 1 / 2
      = t * (2 * α * β' - α - β') + t ^ 2 * (α * β') := by
    rw [← hrel, hρt]; ring
  have hab : 1 ≤ α * β' := one_le_mul_of_one_le_of_one_le hα1 hβ1
  have hα' : α ≤ α * β' := by nlinarith
  have hβ' : β' ≤ α * β' := by nlinarith
  have hg0 : 0 ≤ 2 * α * β' - α - β' := by nlinarith
  have hg1 : 2 * α * β' - α - β' ≤ 2 * (α * β') := by linarith
  have ht1 : |t| ≤ 1 := hρ.trans hδ
  have ht2 : t ^ 2 ≤ |t| := by
    rw [← sq_abs]; nlinarith [abs_nonneg t]
  have habs : |t * (2 * α * β' - α - β')| ≤ |t| * (2 * (α * β')) := by
    rw [abs_mul, abs_of_nonneg hg0]
    exact mul_le_mul_of_nonneg_left hg1 (abs_nonneg t)
  have hab0 : 0 ≤ α * β' := by linarith
  have h2 : |t ^ 2 * (α * β')| ≤ |t| * (α * β') := by
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right ht2 hab0
  have hαa : α * β' ≤ a * b := mul_le_mul ha hb (by linarith) (by linarith)
  rw [key]
  calc |t * (2 * α * β' - α - β') + t ^ 2 * (α * β')|
      ≤ |t * (2 * α * β' - α - β')| + |t ^ 2 * (α * β')| := abs_add_le _ _
    _ ≤ |t| * (2 * (α * β')) + |t| * (α * β') := add_le_add habs h2
    _ = 3 * |t| * (α * β') := by ring
    _ ≤ 3 * δ * (a * b) := by
        apply mul_le_mul (by linarith) hαa hab0 (by linarith [abs_nonneg t])
    _ = 3 * δ * a * b := by ring

/-- `ε^{4/3} = ε · ε^{1/3}`. -/
theorem rpow_four_thirds_eq {eps : ℝ} (he : 0 < eps) :
    eps ^ ((4 : ℝ) / 3) = eps * eps ^ ((1 : ℝ) / 3) := by
  rw [show (4 : ℝ) / 3 = 1 + 1 / 3 by norm_num, Real.rpow_add he, Real.rpow_one]

/-- `ε ≤ t³ ⟹ ε^{1/3} ≤ t`. -/
theorem rpow_third_le {eps t0 : ℝ} (he : 0 ≤ eps) (ht : 0 ≤ t0) (h : eps ≤ t0 ^ 3) :
    eps ^ ((1 : ℝ) / 3) ≤ t0 := by
  have h1 := Real.rpow_le_rpow he h (show (0 : ℝ) ≤ 1 / 3 by norm_num)
  have h2 : (t0 ^ 3) ^ ((1 : ℝ) / 3) = t0 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]; norm_num
  linarith

/-- `ε ≤ ε^{1/3}` for `0 ≤ ε ≤ 1`. -/
theorem le_rpow_third {eps : ℝ} (he : 0 ≤ eps) (he1 : eps ≤ 1) : eps ≤ eps ^ ((1 : ℝ) / 3) := by
  have := Real.rpow_le_rpow_of_exponent_ge' he he1 (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    (show (1 / 3 : ℝ) ≤ 1 by norm_num)
  simpa using this

/-- The real-number core of `cor:samplecost`: with `N_fold = pB/Λ`, `S = N_stab = ν M`,
`M = N_mem = pB/ε`, `|Λ - ε r_*(ν)| ≤ C ε e₃`, `C e₃ ≤ r_min/2`, the five conclusions hold. -/
theorem samplecost_real {nu0 C rmin Q K1 K2 Cf : ℝ} (hnu0 : 0 < nu0) (hC0 : 0 ≤ C)
    (hrmin : 0 < rmin) (hrmin_def : rmin = 1 / (1 + 2 * nu0)) (hQdef : Q = 1 + 2 * nu0)
    (hK1 : K1 = 2 * C / rmin) (hK2 : K2 = 3 * K1 * (2 * Q / nu0) * Q)
    (hCfK1 : K1 + 1 ≤ Cf) (hCfK2 : K2 ≤ Cf) (hCfC : C ≤ Cf)
    {nu S M X Lam eps e3 pB : ℝ} (hν : nu ∈ Set.Icc (nu0 / 2) (2 * nu0))
    (he0 : 0 < eps) (he1 : eps ≤ 1) (he3 : eps ≤ e3) (he3pos : 0 < e3) (hpB : 0 < pB)
    (hM : M = pB / eps) (hS : S = nu * M) (hCe : C * e3 ≤ rmin / 2)
    (hcl : |Lam - eps * rayRate nu| ≤ C * (eps * e3))
    (hX0 : 0 ≤ X) (hX : X ≤ S + eps * M) :
    |Lam - eps * rayRate nu| ≤ Cf * (eps * e3) ∧
      |pB / Lam / hyperbolaN S M - 1| ≤ Cf * e3 ∧
      |(pB / Lam / S - 1) * (pB / Lam / M - 1) - 1 / 2| ≤ Cf * e3 ∧
      max S M * (1 - Cf * e3) ≤ pB / Lam ∧ X * (1 - Cf * e3) ≤ pB / Lam := by
  have hnu : 0 < nu := by linarith [hν.1]
  have hQ : 0 < Q := by rw [hQdef]; positivity
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  have hCf0 : 0 ≤ Cf := by linarith
  have hMpos : 0 < M := by rw [hM]; positivity
  have hSpos : 0 < S := by rw [hS]; positivity
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = rayRate nu := ⟨_, rfl⟩
  have hrge0 := rayRate_ge hnu
  have hrpos := rayRate_pos hnu
  rw [← hrdef] at hrge0 hrpos hcl ⊢
  have hr_ge : rmin ≤ r := by
    refine le_trans ?_ hrge0
    rw [hrmin_def]
    apply one_div_le_one_div_of_le (by linarith)
    linarith [hν.2]
  have hLam_lb : eps * r / 2 ≤ Lam := by
    have h := (abs_le.1 hcl).1
    have : C * (eps * e3) ≤ eps * r / 2 := by
      have : C * e3 ≤ r / 2 := by linarith
      nlinarith
    linarith
  have hLampos : 0 < Lam := lt_of_lt_of_le (by positivity) hLam_lb
  have hrel := hyperbola_eq hSpos hMpos
  have hratio : S / M = nu := by rw [hS]; field_simp
  rw [hratio, ← hrdef] at hrel
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = hyperbolaN S M := ⟨_, rfl⟩
  rw [← hNdef] at hrel
  have hN : N = pB / (eps * r) := by
    rw [← hrel, hM]; field_simp
  have hNpos : 0 < N := by rw [hN]; positivity
  have hρN : pB / Lam = (eps * r / Lam) * N := by rw [hN]; field_simp
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = eps * r / Lam := ⟨_, rfl⟩
  rw [← hρdef] at hρN
  have hδ1 : K1 * e3 ≤ 1 := by
    rw [hK1]
    have : 2 * C / rmin * e3 = 2 * (C * e3) / rmin := by ring
    rw [this, div_le_one hrmin]; linarith
  have hρ1 : |ρ - 1| ≤ K1 * e3 := by
    have e1 : ρ - 1 = (eps * r - Lam) / Lam := by rw [hρdef]; field_simp
    rw [e1, abs_div, abs_of_pos hLampos, div_le_iff₀ hLampos]
    have habs : |eps * r - Lam| ≤ C * (eps * e3) := by
      rw [abs_sub_comm]; exact hcl
    refine habs.trans ?_
    have hr1 : 1 ≤ r / rmin := (one_le_div hrmin).2 hr_ge
    have h1' : K1 * e3 * (eps * r / 2) = C * (eps * e3) * (r / rmin) := by
      rw [hK1]; field_simp
    have h2' : C * (eps * e3) ≤ C * (eps * e3) * (r / rmin) :=
      le_mul_of_one_le_right (by positivity) hr1
    have h3' : K1 * e3 * (eps * r / 2) ≤ K1 * e3 * Lam :=
      mul_le_mul_of_nonneg_left hLam_lb (by positivity)
    linarith
  have hδ_le : K1 * e3 ≤ Cf * e3 :=
    mul_le_mul_of_nonneg_right (by linarith) he3pos.le
  have hCfe : 0 ≤ Cf * e3 := by positivity
  have hmax := hyperbola_ge_max hSpos hMpos
  rw [← hNdef] at hmax
  have hsubst : hyperbolaN S M = N := hNdef.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine hcl.trans ?_
    exact mul_le_mul_of_nonneg_right hCfC (by positivity)
  · rw [hρN, hsubst, mul_div_cancel_right₀ _ hNpos.ne']
    exact hρ1.trans hδ_le
  · -- hyperbola
    have hNM : N / M = 1 / r := by rw [hN, hM]; field_simp
    have hNS : N / S = (1 / r) * (1 / nu) := by rw [hS, ← hNM]; field_simp
    have hinv : 1 / r ≤ Q := by
      have h := one_div_le_one_div_of_le (by positivity : 0 < 1 / (1 + nu)) hrge0
      rw [one_div_one_div] at h
      rw [hQdef]; linarith [hν.2]
    have hinvnu : 1 / nu ≤ 2 / nu0 := by
      have := one_div_le_one_div_of_le (by linarith [hν.1] : 0 < nu0 / 2) hν.1
      rw [one_div_div] at this; exact this
    have hb : N / M ≤ Q := by rw [hNM]; exact hinv
    have ha : N / S ≤ 2 * Q / nu0 := by
      rw [hNS]
      have := mul_le_mul hinv hinvnu (by positivity) hQ.le
      calc _ ≤ Q * (2 / nu0) := this
        _ = 2 * Q / nu0 := by ring
    have hp := hyperbola_perturb (a := 2 * Q / nu0) (b := Q) (δ := K1 * e3) hSpos hMpos
      (by rw [hsubst]; exact ha) (by rw [hsubst]; exact hb) hρ1 hδ1
    rw [hsubst] at hp
    rw [hρN]
    refine hp.trans ?_
    calc 3 * (K1 * e3) * (2 * Q / nu0) * Q = K2 * e3 := by rw [hK2]; ring
      _ ≤ Cf * e3 := mul_le_mul_of_nonneg_right hCfK2 he3pos.le
  · rw [hρN]
    have hρlb : 1 - K1 * e3 ≤ ρ := by have := (abs_le.1 hρ1).1; linarith
    have h0 : 0 ≤ 1 - K1 * e3 := by linarith
    have h1 : max S M * (1 - Cf * e3) ≤ max S M * (1 - K1 * e3) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_max_of_le_left hSpos.le)
    have h2 : max S M * (1 - K1 * e3) ≤ N * (1 - K1 * e3) :=
      mul_le_mul_of_nonneg_right hmax h0
    have h3 : N * (1 - K1 * e3) ≤ N * ρ := mul_le_mul_of_nonneg_left hρlb hNpos.le
    linarith
  · rw [hρN]
    have hρlb : 1 - K1 * e3 ≤ ρ := by have := (abs_le.1 hρ1).1; linarith
    have h0 : 0 ≤ 1 - K1 * e3 := by linarith
    have h4 : X ≤ (1 + eps) * N := by
      have hSN : S ≤ N := le_trans (le_max_left _ _) hmax
      have hMN : M ≤ N := le_trans (le_max_right _ _) hmax
      have := mul_le_mul_of_nonneg_left hMN he0.le
      linarith
    have h5 : (1 - eps) * X ≤ N := by
      have := mul_le_mul_of_nonneg_left h4 (by linarith : 0 ≤ 1 - eps)
      have h' : 0 ≤ eps ^ 2 * N := by positivity
      nlinarith
    have h6 : (1 - K1 * e3) * ((1 - eps) * X) ≤ (1 - K1 * e3) * N :=
      mul_le_mul_of_nonneg_left h5 h0
    have h7 : (1 - K1 * e3) * N ≤ ρ * N := mul_le_mul_of_nonneg_right hρlb hNpos.le
    have h8 : 0 ≤ (K1 * e3) * eps * X := by positivity
    have h9 : K1 * e3 + eps ≤ Cf * e3 := by
      have := mul_le_mul_of_nonneg_right hCfK1 he3pos.le
      linarith [add_mul K1 1 e3]
    have h10 : X * (1 - Cf * e3) ≤ X * (1 - K1 * e3 - eps) :=
      mul_le_mul_of_nonneg_left (by linarith) hX0
    have hid : (1 - K1 * e3) * ((1 - eps) * X) = X * (1 - K1 * e3 - eps) + (K1 * e3) * eps * X := by
      ring
    linarith

/-- **`cor:samplecost`, uniform form.**  For every `ν₀ > 0` there are `ε₀ ∈ (0, 1/2]` and `C`
such that for all `(d, B, p, β)` with `ε = 1 - β ≤ ε₀` and `ν ∈ [ν₀/2, 2ν₀]`:
(i) `|Λ* - ε r_*(ν)| ≤ C ε^{4/3}` and `|N_fold/N - 1| ≤ C ε^{1/3}`, where
`N = hyperbolaN N_stab N_mem = (N_stab + N_mem + √(N_stab² + N_mem²))/2`;
(ii) `|(N_fold/N_stab - 1)(N_fold/N_mem - 1) - 1/2| ≤ C ε^{1/3}`;
(iii) `N_fold ≥ max(N_stab, N_mem)(1 - C ε^{1/3})` and
`N_fold ≥ N_fold^SGD (1 - C ε^{1/3})`.
The tex hypothesis `β ≥ 1/2` is implied by `ε ≤ ε₀ ≤ 1/2`; the label-noise measure is arbitrary.
-/
theorem cor_samplecost (nu0 : ℝ) (hnu0 : 0 < nu0) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 / 2 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta : ℝ),
        0 < B → 0 < (p : ℝ) → 0 < 1 - beta → 1 - beta ≤ eps0 →
        lsNu d B p beta ∈ Set.Icc (nu0 / 2) (2 * nu0) →
        (|lsLamStar d B p ν beta - (1 - beta) * rayRate (lsNu d B p beta)|
            ≤ C * (1 - beta) ^ ((4 : ℝ) / 3) ∧
          |lsNfold d B p ν beta / hyperbolaN (lsNstab d B p beta) (lsNmem B p beta) - 1|
            ≤ C * (1 - beta) ^ ((1 : ℝ) / 3)) ∧
        |(lsNfold d B p ν beta / lsNstab d B p beta - 1) *
            (lsNfold d B p ν beta / lsNmem B p beta - 1) - 1 / 2|
            ≤ C * (1 - beta) ^ ((1 : ℝ) / 3) ∧
        (max (lsNstab d B p beta) (lsNmem B p beta) * (1 - C * (1 - beta) ^ ((1 : ℝ) / 3))
            ≤ lsNfold d B p ν beta ∧
          lsNfoldSGD d B p ν * (1 - C * (1 - beta) ^ ((1 : ℝ) / 3)) ≤ lsNfold d B p ν beta) := by
  obtain ⟨eps1, h1, C, hC0, hC⟩ := lsLamStar_close nu0 hnu0
  have hrmin : 0 < 1 / (1 + 2 * nu0) := by positivity
  obtain ⟨rmin, hrmin_def⟩ : ∃ rmin : ℝ, rmin = 1 / (1 + 2 * nu0) := ⟨_, rfl⟩
  rw [← hrmin_def] at hrmin
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = 1 + 2 * nu0 := ⟨_, rfl⟩
  obtain ⟨t0, ht0def⟩ : ∃ t0 : ℝ, t0 = rmin / (2 * (C + 1)) := ⟨_, rfl⟩
  have ht0 : 0 < t0 := by rw [ht0def]; positivity
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = 2 * C / rmin := ⟨_, rfl⟩
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ, K2 = 3 * K1 * (2 * Q / nu0) * Q := ⟨_, rfl⟩
  have hQ : 0 < Q := by rw [hQdef]; positivity
  have hK20 : 0 ≤ K2 := by rw [hK2]; positivity
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, Cf = max C (max K1 (max K2 (K1 + 1))) := ⟨_, rfl⟩
  have hCfC : C ≤ Cf := by rw [hCf]; exact le_max_left _ _
  have hCfK1 : K1 + 1 ≤ Cf := by
    rw [hCf]; exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCfK2 : K2 ≤ Cf := by
    rw [hCf]; exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨min eps1 (t0 ^ 3), lt_min h1.1 (by positivity), (min_le_left _ _).trans h1.2, Cf,
    hC0.trans hCfC, ?_⟩
  intro d B p ν beta hB hp he hepsle hν
  have hεmem : 1 - beta ∈ Set.Ioc (0 : ℝ) eps1 := ⟨he, hepsle.trans (min_le_left _ _)⟩
  have heps12 : 1 - beta ≤ 1 / 2 := hεmem.2.trans h1.2
  have hb1 : beta < 1 := by linarith
  have hb0 : 0 ≤ beta := by linarith
  have hcl := hC d B p ν beta hB hp hεmem hν
  have hsm : (1 - beta) ^ ((1 : ℝ) / 3) ≤ t0 :=
    rpow_third_le he.le ht0.le (hepsle.trans (min_le_right _ _))
  have h43 := rpow_four_thirds_eq he
  rw [h43] at hcl
  have he3pos : 0 < (1 - beta) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos he _
  have hCe : C * (1 - beta) ^ ((1 : ℝ) / 3) ≤ rmin / 2 := by
    have h1' : C * (1 - beta) ^ ((1 : ℝ) / 3) ≤ C * t0 := mul_le_mul_of_nonneg_left hsm hC0
    have h2' : C * t0 ≤ (C + 1) * t0 := by nlinarith
    have h3' : (C + 1) * t0 = rmin / 2 := by rw [ht0def]; field_simp
    linarith
  have hgap := lsNstab_zero_sub_le (d := d) (p := p) hB hb0 hb1 hp
  have hXle := lsNfoldSGD_le (d := d) hB hp ν
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hres := samplecost_real (nu0 := nu0) (C := C) (rmin := rmin) (Q := Q) (K1 := K1)
    (K2 := K2) (Cf := Cf) hnu0 hC0 hrmin hrmin_def hQdef hK1 hK2 hCfK1 hCfK2 hCfC
    (nu := lsNu d B p beta) (S := lsNstab d B p beta) (M := lsNmem B p beta)
    (X := lsNfoldSGD d B p ν) (Lam := lsLamStar d B p ν beta) (eps := 1 - beta)
    (e3 := (1 - beta) ^ ((1 : ℝ) / 3)) (pB := (p : ℝ) * B) hν he (by linarith)
    (le_rpow_third he.le (by linarith)) he3pos (by positivity) rfl
    (lsNstab_eq_nu_mul hB hb0 hb1 hp) hCe hcl (lsNfoldSGD_nonneg hB hp ν) (by linarith)
  obtain ⟨r1, r2, r3, r4, r5⟩ := hres
  refine ⟨⟨?_, r2⟩, r3, r4, r5⟩
  rw [h43]
  exact hcl.trans (mul_le_mul_of_nonneg_right hCfC (by positivity))

end L2

/-! ### L3: speedup at a fixed learning rate -/

section L3

/-- Momentum chain parameters `⟨1-ε, ε²Δ, u_n, φ⟩` (`cor:helps-speedup`). -/
def momentumParams (eps Delta un phi : ℝ) : Params := ⟨1 - eps, eps ^ 2 * Delta, un, phi⟩

/-- SGD chain parameters `⟨0, εΔ, u_n, φ⟩` (`cor:helps-speedup`, `w = ηA = εΔ`). -/
def sgdParams (eps Delta un phi : ℝ) : Params := ⟨0, eps * Delta, un, phi⟩

/-- The floor `R_∞ = additive/(1-u)` of the chain. -/
def floorOf (p : Params) : ℝ := p.additive / (1 - p.totalLoad)

/-- Ratio perturbation: if `Λ_β = ε r (1+a)` and `Λ_0 = ε g (1+b)` with `|a| ≤ A ≤ 1/2`,
`|b| ≤ B' ≤ 1/2`, then `|Λ_β/Λ_0 - r/g| ≤ 2 (r/g)(A + B')`. -/
theorem ratio_perturb {r g eps Lb L0 A B' : ℝ} (hr : 0 < r) (hg : 0 < g) (he : 0 < eps)
    (ha : |Lb / (eps * r) - 1| ≤ A) (hb : |L0 / (eps * g) - 1| ≤ B') (hB' : B' ≤ 1 / 2) :
    |Lb / L0 - r / g| ≤ 2 * (r / g) * (A + B') := by
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = Lb / (eps * r) - 1 := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = L0 / (eps * g) - 1 := ⟨_, rfl⟩
  rw [← hadef] at ha
  rw [← hbdef] at hb
  have hb2 : -(1 / 2) ≤ b := by have := (abs_le.1 hb).1; linarith
  have hb1 : 0 < 1 + b := by linarith
  have hLb : Lb = eps * r * (1 + a) := by rw [hadef]; field_simp; ring
  have hL0 : L0 = eps * g * (1 + b) := by rw [hbdef]; field_simp; ring
  have hZ : Lb / L0 - r / g = (r / g) * ((a - b) / (1 + b)) := by
    rw [hLb, hL0]; field_simp; ring
  rw [hZ, abs_mul, abs_of_pos (by positivity : 0 < r / g), abs_div, abs_of_pos hb1]
  have h1 : |a - b| ≤ A + B' := (abs_sub a b).trans (add_le_add ha hb)
  have h2 : |a - b| / (1 + b) ≤ 2 * (A + B') := by
    rw [div_le_iff₀ hb1]
    have h3 : 0 ≤ A + B' := le_trans (abs_nonneg _) h1
    nlinarith
  have : 0 < r / g := by positivity
  nlinarith

/-- SGD rate for the LS-free chain: `|Λ_0 - ε g| ≤ 9 D² ε²` where `g = 2Δ(1-u_n)`
(`cor:helps-speedup`, via `lem:helps-sgd` and `-log(1-x) ∈ [x, x/(1-x)]`). -/
theorem sgd_rate_close {eps Delta un phi D : ℝ} (he : 0 < eps) (hD0 : 0 < Delta)
    (hDD : Delta ≤ D) (hun0 : 0 ≤ un) (hlt : un + eps * Delta / 2 < 1)
    (hsmall : 4 * eps * D ≤ 1) :
    |perStepRate (sgdParams eps Delta un phi) - eps * (2 * Delta * (1 - un))|
      ≤ 9 * D ^ 2 * eps ^ 2 := by
  have hb : (sgdParams eps Delta un phi).beta = 0 := rfl
  have hw : 0 < (sgdParams eps Delta un phi).w := mul_pos he hD0
  have hn : 0 ≤ (sgdParams eps Delta un phi).noise := hun0
  have hload : (sgdParams eps Delta un phi).totalLoad = un + eps * Delta / 2 := by
    rw [totalLoad_beta_zero _ hb]; rfl
  have hlt' : (sgdParams eps Delta un phi).totalLoad < 1 := by rw [hload]; exact hlt
  have hrate := (sgd_coeff_bounds _ hb hw hn hlt').2.2
  rw [hrate, hload]
  set x : ℝ := 1 - (1 - 2 * (sgdParams eps Delta un phi).w * (1 - (un + eps * Delta / 2)))
    with hxdef
  have hx : x = 2 * (eps * Delta) * (1 - (un + eps * Delta / 2)) := by
    rw [hxdef]; simp only [sgdParams]; ring
  have hD : 0 < D := lt_of_lt_of_le hD0 hDD
  have hx0 : 0 ≤ x := by rw [hx]; have : 0 < 1 - (un + eps * Delta / 2) := by linarith
                         positivity
  have hxg : x = eps * (2 * Delta * (1 - un)) - (eps * Delta) ^ 2 := by rw [hx]; ring
  have hxle : x ≤ eps * (2 * Delta * (1 - un)) := by nlinarith [sq_nonneg (eps * Delta)]
  have hg2 : eps * (2 * Delta * (1 - un)) ≤ 2 * eps * D := by
    have : Delta * (1 - un) ≤ D := by nlinarith
    nlinarith
  have hx12 : x ≤ 1 / 2 := by nlinarith
  have hlog : (1 - (1 - 2 * (sgdParams eps Delta un phi).w * (1 - (un + eps * Delta / 2)))) = x := rfl
  have e1 : -Real.log (1 - 2 * (sgdParams eps Delta un phi).w * (1 - (un + eps * Delta / 2)))
      = -Real.log (1 - x) := by rw [hxdef]; ring_nf
  rw [e1]
  have h1 := neg_log_one_sub_ge (show x < 1 by linarith)
  have h2 := neg_log_one_sub_le (show x < 1 by linarith)
  have h3 : x / (1 - x) - x ≤ 2 * x ^ 2 := by
    have : 0 < 1 - x := by linarith
    rw [show x / (1 - x) - x = x ^ 2 / (1 - x) by field_simp; ring, div_le_iff₀ this]
    nlinarith [sq_nonneg x]
  have h4 : x ^ 2 ≤ (2 * eps * D) ^ 2 := by
    have := pow_le_pow_left₀ hx0 (hxle.trans hg2) 2
    exact this
  have h5 : (eps * Delta) ^ 2 ≤ eps ^ 2 * D ^ 2 := by
    have : eps * Delta ≤ eps * D := mul_le_mul_of_nonneg_left hDD he.le
    nlinarith [mul_pos he hD0]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg eps, sq_nonneg D]

/-- Floors: `φ/(1-u_n) ≤ φ/(1-u) ≤ φ/(1-u_n-εΔ/2) ≤ φ/(1-u_n)(1 + (D/δ) ε)`. -/
theorem floor_chain {phi un uc s eps D dk : ℝ} (hphi : 0 ≤ phi) (hdk : 0 < dk)
    (hun : un ≤ 1 - dk) (huc0 : 0 ≤ uc) (huc : uc ≤ s) (hs : s ≤ eps * D / 2)
    (hsm : eps * D ≤ dk) (he : 0 < eps) (hD : 0 < D) :
    phi / (1 - un) ≤ phi / (1 - (un + uc)) ∧
      phi / (1 - (un + uc)) ≤ phi / (1 - (un + s)) ∧
      phi / (1 - (un + s)) ≤ phi / (1 - un) * (1 + D / dk * eps) := by
  have hs0 : 0 ≤ s := huc0.trans huc
  have hsd : s ≤ dk / 2 := by linarith
  have h1 : 0 < 1 - (un + s) := by linarith
  have h2 : 0 < 1 - (un + uc) := by linarith
  have h3 : 0 < 1 - un := by linarith
  refine ⟨?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_left hphi h2 (by linarith)
  · exact div_le_div_of_nonneg_left hphi h1 (by linarith)
  · rw [div_mul_eq_mul_div, div_le_div_iff₀ h1 h3]
    have key : (1 - un) ≤ (1 + D / dk * eps) * (1 - (un + s)) := by
      have h4 : s ≤ D / dk * eps * (1 - (un + s)) := by
        have h5 : dk / 2 ≤ 1 - (un + s) := by linarith
        have h6 : D / dk * eps * (dk / 2) = eps * D / 2 := by field_simp
        calc s ≤ eps * D / 2 := hs
          _ = D / dk * eps * (dk / 2) := h6.symm
          _ ≤ D / dk * eps * (1 - (un + s)) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
      nlinarith
    nlinarith

/-- `Λ > 0` forces `ρ < 1`. -/
theorem stepRadius_lt_one_of_rate_pos {p : Params} (h : 0 < perStepRate p) : stepRadius p < 1 := by
  by_contra hcon
  push Not at hcon
  have := Real.log_nonneg hcon
  unfold perStepRate at h
  linarith

/-- Pointwise core of `cor:helps-speedup`: all constants are explicit. -/
theorem speedup_pointwise {eps Delta un phi D dk Dmin Rm Ca' e3 : ℝ}
    (he : 0 < eps) (hep12 : eps ≤ 1 / 2) (hΔ0 : 0 < Delta) (hΔD : Delta ≤ D)
    (hΔmin : Dmin ≤ Delta) (hDmin : 0 < Dmin) (hun0 : 0 ≤ un) (hun1 : un ≤ 1 - dk)
    (hdk : 0 < dk) (hphi : 0 ≤ phi) (hD : 0 < D)
    (hD4 : eps * D ≤ dk) (hsm4 : 4 * eps * D ≤ 1)
    (hB : eps ≤ (2 * Dmin * dk) / (18 * D ^ 2))
    (hrpos : 0 < continuumPerronRate Delta un) (hr_le : continuumPerronRate Delta un ≤ Rm)
    (he3 : 0 < e3) (hee3 : eps ≤ e3) (hCa' : 0 ≤ Ca') (hA : Ca' * e3 ≤ 1 / 2)
    (hTr' : |perStepRate (transferParams eps Delta un) / (eps * continuumPerronRate Delta un) - 1|
      ≤ Ca' * e3) :
    stepRadius (momentumParams eps Delta un phi) < 1 ∧
      stepRadius (sgdParams eps Delta un phi) < 1 ∧
      |perStepRate (momentumParams eps Delta un phi) / perStepRate (sgdParams eps Delta un phi)
          - speedupRatio Delta un|
        ≤ (Rm / (2 * Dmin * dk) * 2 * (Ca' + 9 * D ^ 2 / (2 * Dmin * dk))) * e3 ∧
      phi / (1 - un) ≤ floorOf (momentumParams eps Delta un phi) ∧
      floorOf (momentumParams eps Delta un phi) ≤ floorOf (sgdParams eps Delta un phi) ∧
      floorOf (sgdParams eps Delta un phi) ≤ phi / (1 - un) * (1 + D / dk * eps) := by
  have hgm : 0 < 2 * Dmin * dk := by positivity
  have hRm0 : 0 ≤ Rm := hrpos.le.trans hr_le
  have hun1' : 0 < 1 - un := by linarith
  have hrate_m : perStepRate (momentumParams eps Delta un phi)
      = perStepRate (transferParams eps Delta un) :=
    perStepRate_congr rfl rfl rfl
  have hLb_lb : 1 / 2 ≤ perStepRate (transferParams eps Delta un) /
      (eps * continuumPerronRate Delta un) := by
    have := (abs_le.1 hTr').1; linarith
  have h0 : 0 < eps * continuumPerronRate Delta un := mul_pos he hrpos
  have hLbpos : 0 < perStepRate (transferParams eps Delta un) := by
    have := (le_div_iff₀ h0).1 hLb_lb
    linarith
  -- SGD side
  have hlt : un + eps * Delta / 2 < 1 := by
    have : eps * Delta ≤ eps * D := mul_le_mul_of_nonneg_left hΔD he.le
    linarith
  have hloadS : (sgdParams eps Delta un phi).totalLoad = un + eps * Delta / 2 := by
    rw [totalLoad_beta_zero _ rfl]; rfl
  have hradS : stepRadius (sgdParams eps Delta un phi) < 1 := by
    rw [stepRadius_lt_one_iff_beta_zero _ rfl (mul_pos he hΔ0) hun0, hloadS]; exact hlt
  have hSclose := sgd_rate_close (phi := phi) he hΔ0 hΔD hun0 hlt hsm4
  have hgpos : 0 < 2 * Delta * (1 - un) := by positivity
  have hggm : 2 * Dmin * dk ≤ 2 * Delta * (1 - un) := by
    have h1 : Dmin * dk ≤ Delta * (1 - un) := mul_le_mul hΔmin (by linarith) hdk.le hΔ0.le
    linarith
  have hL0b : |perStepRate (sgdParams eps Delta un phi) / (eps * (2 * Delta * (1 - un))) - 1|
      ≤ 9 * D ^ 2 * eps / (2 * Dmin * dk) := by
    have h0' : 0 < eps * (2 * Delta * (1 - un)) := mul_pos he hgpos
    have e1 : perStepRate (sgdParams eps Delta un phi) / (eps * (2 * Delta * (1 - un))) - 1
        = (perStepRate (sgdParams eps Delta un phi) - eps * (2 * Delta * (1 - un)))
          / (eps * (2 * Delta * (1 - un))) := by
      field_simp
    rw [e1, abs_div, abs_of_pos h0', div_le_iff₀ h0']
    refine hSclose.trans ?_
    have h1 : 9 * D ^ 2 * eps / (2 * Dmin * dk) * (eps * (2 * Delta * (1 - un)))
        ≥ 9 * D ^ 2 * eps / (2 * Dmin * dk) * (eps * (2 * Dmin * dk)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hggm he.le
    have h2 : 9 * D ^ 2 * eps / (2 * Dmin * dk) * (eps * (2 * Dmin * dk))
        = 9 * D ^ 2 * eps ^ 2 := by field_simp
    linarith
  have hB12 : 9 * D ^ 2 * eps / (2 * Dmin * dk) ≤ 1 / 2 := by
    rw [div_le_iff₀ hgm]
    have h1 := mul_le_mul_of_nonneg_right hB (by positivity : 0 ≤ 18 * D ^ 2)
    rw [div_mul_cancel₀ _ (by positivity)] at h1
    linarith
  have hratio := ratio_perturb (L0 := perStepRate (sgdParams eps Delta un phi))
    (Lb := perStepRate (transferParams eps Delta un)) hrpos hgpos he hTr' hL0b hB12
  -- floors
  have hucdef : (momentumParams eps Delta un phi).curvature
      = eps ^ 2 * Delta / (2 * (1 + (1 - eps))) := rfl
  have huc0 : 0 ≤ (momentumParams eps Delta un phi).curvature := by
    rw [hucdef]; have : 0 < 1 + (1 - eps) := by linarith
    positivity
  have huc : (momentumParams eps Delta un phi).curvature ≤ eps * Delta / 2 := by
    rw [hucdef, div_le_iff₀ (by linarith)]
    have h3 : 0 < eps * Delta := mul_pos he hΔ0
    have h4 : eps * (eps * Delta) ≤ eps * Delta := by
      have := mul_le_mul_of_nonneg_right (show eps ≤ 1 by linarith) h3.le
      linarith
    nlinarith
  have hs : eps * Delta / 2 ≤ eps * D / 2 := by
    have := mul_le_mul_of_nonneg_left hΔD he.le; linarith
  have hfl := floor_chain (phi := phi) (un := un) (uc := (momentumParams eps Delta un phi).curvature)
    (s := eps * Delta / 2) (eps := eps) (D := D) (dk := dk) hphi hdk hun1 huc0 huc hs hD4 he hD
  have hfM : floorOf (momentumParams eps Delta un phi)
      = phi / (1 - (un + (momentumParams eps Delta un phi).curvature)) := rfl
  have hfS : floorOf (sgdParams eps Delta un phi) = phi / (1 - (un + eps * Delta / 2)) := by
    unfold floorOf; rw [hloadS]; rfl
  refine ⟨?_, hradS, ?_, ?_, ?_, ?_⟩
  · apply stepRadius_lt_one_of_rate_pos
    rw [hrate_m]; exact hLbpos
  · rw [hrate_m]
    refine hratio.trans ?_
    have hrg : continuumPerronRate Delta un / (2 * Delta * (1 - un))
        ≤ Rm / (2 * Dmin * dk) :=
      div_le_div₀ (hrpos.le.trans hr_le) hr_le hgm hggm
    have h1 : 9 * D ^ 2 * eps / (2 * Dmin * dk) ≤ 9 * D ^ 2 / (2 * Dmin * dk) * e3 := by
      have : 9 * D ^ 2 * eps / (2 * Dmin * dk) = 9 * D ^ 2 / (2 * Dmin * dk) * eps := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hee3 (by positivity)
    have h2 : Ca' * e3 + 9 * D ^ 2 * eps / (2 * Dmin * dk)
        ≤ (Ca' + 9 * D ^ 2 / (2 * Dmin * dk)) * e3 := by linarith [add_mul Ca' (9 * D ^ 2 / (2 * Dmin * dk)) e3]
    calc 2 * (continuumPerronRate Delta un / (2 * Delta * (1 - un)))
          * (Ca' * e3 + 9 * D ^ 2 * eps / (2 * Dmin * dk))
        ≤ 2 * (Rm / (2 * Dmin * dk)) * ((Ca' + 9 * D ^ 2 / (2 * Dmin * dk)) * e3) := by
          have := mul_le_mul_of_nonneg_left (mul_le_mul hrg h2 (by positivity) (by positivity))
            (by norm_num : (0 : ℝ) ≤ 2)
          linarith
      _ = _ := by ring
  · rw [hfM]; exact hfl.1
  · rw [hfM, hfS]; exact hfl.2.1
  · rw [hfS]; exact hfl.2.2

/-- **`cor:helps-speedup`, uniform form.**  For `K ⊆ (0,∞) × [0,1)` compact there are `ε₀ ∈ (0,1/2]`
and `C` such that for `ε ≤ ε₀`, `(Δ, u_n) ∈ K` and `φ ≥ 0`, with momentum chain
`⟨1-ε, ε²Δ, u_n, φ⟩` and SGD chain `⟨0, εΔ, u_n, φ⟩`: both radii are `< 1`,
`|Λ_β/Λ_0 - Γ(Δ,u_n)| ≤ C ε^{1/3}`, and
`φ/(1-u_n) ≤ floor_β ≤ floor_0 ≤ φ/(1-u_n)(1 + Cε)`.  (The hypothesis `φ ≥ 0` is implicit in
the tex: the floors are variances.) -/
theorem cor_helps_speedup {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hsub : K ⊆ Set.Ioi 0 ×ˢ Set.Ico 0 1) :
    ∃ eps0 : ℝ, eps0 ∈ Set.Ioc (0 : ℝ) (1 / 2) ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ eps ∈ Set.Ioc (0 : ℝ) eps0, ∀ x ∈ K, ∀ phi : ℝ, 0 ≤ phi →
        stepRadius (momentumParams eps x.1 x.2 phi) < 1 ∧
        stepRadius (sgdParams eps x.1 x.2 phi) < 1 ∧
        |perStepRate (momentumParams eps x.1 x.2 phi) / perStepRate (sgdParams eps x.1 x.2 phi)
            - speedupRatio x.1 x.2| ≤ C * eps ^ ((1 : ℝ) / 3) ∧
        phi / (1 - x.2) ≤ floorOf (momentumParams eps x.1 x.2 phi) ∧
        floorOf (momentumParams eps x.1 x.2 phi) ≤ floorOf (sgdParams eps x.1 x.2 phi) ∧
        floorOf (sgdParams eps x.1 x.2 phi) ≤ phi / (1 - x.2) * (1 + C * eps) := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨1 / 2, ⟨by norm_num, le_refl _⟩, 0, le_refl _, by simp [he]⟩
  obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
  obtain ⟨x1, hx1, hmax⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
  obtain ⟨x2, hx2, hmaxu⟩ := hK.exists_isMaxOn hne continuous_snd.continuousOn
  obtain ⟨x3, hx3, hmaxr⟩ :=
    hK.exists_isMaxOn hne (continuous_continuumPerronRate.continuousOn)
  obtain ⟨cK, hcK, hcKle⟩ := continuumPerronRate_pos_lower_bound hK hsub
  obtain ⟨eps0a, h0a, Ca, hCa⟩ := helps_transfer_compact hK hsub
  have hs0 := hsub hx0
  have hs1 := hsub hx1
  have hs2 := hsub hx2
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = x1.1 := ⟨_, rfl⟩
  obtain ⟨Dmin, hDmindef⟩ : ∃ Dmin : ℝ, Dmin = x0.1 := ⟨_, rfl⟩
  obtain ⟨dk, hdkdef⟩ : ∃ dk : ℝ, dk = 1 - x2.2 := ⟨_, rfl⟩
  obtain ⟨Rm, hRmdef⟩ : ∃ Rm : ℝ, Rm = continuumPerronRate x3.1 x3.2 := ⟨_, rfl⟩
  have hD : 0 < D := by rw [hDdef]; exact hs1.1
  have hDmin : 0 < Dmin := by rw [hDmindef]; exact hs0.1
  have hdk : 0 < dk := by rw [hdkdef]; linarith [hs2.2.2]
  have hRm : 0 < Rm := by
    rw [hRmdef]; exact lt_of_lt_of_le hcK (hcKle x3 hx3)
  obtain ⟨gm, hgmdef⟩ : ∃ gm : ℝ, gm = 2 * Dmin * dk := ⟨_, rfl⟩
  have hgm : 0 < gm := by rw [hgmdef]; positivity
  obtain ⟨Ca', hCa'⟩ : ∃ Ca' : ℝ, Ca' = max Ca 0 := ⟨_, rfl⟩
  have hCa'0 : 0 ≤ Ca' := by rw [hCa']; exact le_max_right _ _
  obtain ⟨ta, htadef⟩ : ∃ ta : ℝ, ta = 1 / (2 * (Ca' + 1)) := ⟨_, rfl⟩
  have hta : 0 < ta := by rw [htadef]; positivity
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (Rm / gm * 2 * (Ca' + 9 * D ^ 2 / gm)) (D / dk) :=
    ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hCdef]; exact le_trans (by positivity) (le_max_right _ _)
  have hC1 : Rm / gm * 2 * (Ca' + 9 * D ^ 2 / gm) ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hC2 : D / dk ≤ C := by rw [hCdef]; exact le_max_right _ _
  refine ⟨min eps0a (min (ta ^ 3) (min (1 / (4 * D)) (min (gm / (18 * D ^ 2)) (dk / D)))),
    ⟨lt_min h0a.1 (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity)))), (min_le_left _ _).trans h0a.2⟩, C, hC0, ?_⟩
  intro eps heps x hx phi hphi
  have he : 0 < eps := heps.1
  have hep1 : eps ≤ eps0a := heps.2.trans (min_le_left _ _)
  have hep2 : eps ≤ ta ^ 3 := heps.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hep3 : eps ≤ 1 / (4 * D) :=
    heps.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hep4 : eps ≤ gm / (18 * D ^ 2) :=
    heps.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hep5 : eps ≤ dk / D :=
    heps.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hep12 : eps ≤ 1 / 2 := hep1.trans h0a.2
  have hxs := hsub hx
  have hΔ0 : 0 < x.1 := hxs.1
  have hΔD : x.1 ≤ D := by rw [hDdef]; exact hmax hx
  have hΔmin : Dmin ≤ x.1 := by rw [hDmindef]; exact hmin hx
  have hun0 : 0 ≤ x.2 := hxs.2.1
  have hun1 : x.2 ≤ 1 - dk := by
    have h : x.2 ≤ x2.2 := hmaxu hx
    rw [hdkdef]; linarith
  have hr_ge : cK ≤ continuumPerronRate x.1 x.2 := hcKle x hx
  have hr_le : continuumPerronRate x.1 x.2 ≤ Rm := by
    rw [hRmdef]; exact hmaxr hx
  have hrpos : 0 < continuumPerronRate x.1 x.2 := lt_of_lt_of_le hcK hr_ge
  have hD4 : eps * D ≤ dk := by
    have := mul_le_mul_of_nonneg_right hep5 hD.le
    rwa [div_mul_cancel₀ _ hD.ne'] at this
  have hsm4 : 4 * eps * D ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hep3 (by positivity : 0 ≤ 4 * D)
    rw [one_div, inv_mul_cancel₀ (by positivity)] at this
    linarith
  have he3pos : 0 < eps ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos he _
  have hee3 : eps ≤ eps ^ ((1 : ℝ) / 3) := le_rpow_third he.le (by linarith)
  have he3t : eps ^ ((1 : ℝ) / 3) ≤ ta := rpow_third_le he.le hta.le hep2
  have hA : Ca' * eps ^ ((1 : ℝ) / 3) ≤ 1 / 2 := by
    have h1 : Ca' * eps ^ ((1 : ℝ) / 3) ≤ Ca' * ta := mul_le_mul_of_nonneg_left he3t hCa'0
    have h2 : Ca' * ta ≤ (Ca' + 1) * ta := by nlinarith
    have h3 : (Ca' + 1) * ta = 1 / 2 := by rw [htadef]; field_simp
    linarith
  have hTr := hCa eps ⟨he, hep1⟩ x hx
  have hTr' : |perStepRate (transferParams eps x.1 x.2) / (eps * continuumPerronRate x.1 x.2) - 1|
      ≤ Ca' * eps ^ ((1 : ℝ) / 3) := by
    refine hTr.trans (mul_le_mul_of_nonneg_right ?_ he3pos.le)
    rw [hCa']; exact le_max_left _ _
  have hB : eps ≤ (2 * Dmin * dk) / (18 * D ^ 2) := by rw [← hgmdef]; exact hep4
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := speedup_pointwise (Rm := Rm) (Ca' := Ca') (D := D)
    (dk := dk) (Dmin := Dmin) he hep12 hΔ0 hΔD hΔmin hDmin hun0 hun1 hdk hphi hD hD4 hsm4 hB
    hrpos hr_le he3pos hee3 hCa'0 hA hTr'
  rw [← hgmdef] at p3
  refine ⟨p1, p2, p3.trans (mul_le_mul_of_nonneg_right hC1 he3pos.le), p4, p5, ?_⟩
  refine p6.trans ?_
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hphi (by linarith))
  have := mul_le_mul_of_nonneg_right hC2 he.le
  linarith

end L3

/-! ### L4: the asymptotic clause of `lem:helps-vocab` (iii) -/

section L4

/-- **`lem:helps-vocab` (iii), last claim, uniform form.**  For `ν_V ∈ [ν₀/2, 2ν₀]` and
`ε ≤ ε₀` there is `C` with `C ε₀^{1/3} ≤ 1/2` such that every `η ∈ (0, η_+(p_V))` has
`Λ_V(η) ≤ p_V B / ((d + 2 - p_V)(1 - C ε^{1/3}))`; in radius form, if `Λ_V(η) > 0`,
`1/Λ_V(η) ≥ (d+2-p_V)/(B p_V) · (1 - C ε^{1/3})`.  (The tex hypothesis `β ≥ 1/2` is implied by
`ε ≤ ε₀ ≤ 1/2`.) -/
theorem helps_vocab_asymptotic (nu0 : ℝ) (hnu0 : 0 < nu0) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 / 2 ∧ ∃ C : ℝ, 0 ≤ C ∧
      C * eps0 ^ ((1 : ℝ) / 3) ≤ 1 / 2 ∧
      ∀ (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta : ℝ),
        0 < B → 0 < (p : ℝ) → 0 < 1 - beta → 1 - beta ≤ eps0 →
        lsNu d B p beta ∈ Set.Icc (nu0 / 2) (2 * nu0) →
        ∀ eta ∈ Set.Ioo 0 (criticalRate d B p beta),
          lsRate d B p ν beta eta
              ≤ (p : ℝ) * B / (((d : ℝ) + 2 - p) * (1 - C * (1 - beta) ^ ((1 : ℝ) / 3))) ∧
          (0 < lsRate d B p ν beta eta →
            ((d : ℝ) + 2 - p) / (B * p) * (1 - C * (1 - beta) ^ ((1 : ℝ) / 3))
              ≤ 1 / lsRate d B p ν beta eta) := by
  obtain ⟨eps1, h1, Cr, hCr0, hCr⟩ := lsRate_close nu0 hnu0
  obtain ⟨eps2, h2pos, h2le, C, hC0, hC⟩ := cor_samplecost nu0 hnu0
  obtain ⟨t0, ht0def⟩ : ∃ t0 : ℝ, t0 = 1 / (2 * (C + 1)) := ⟨_, rfl⟩
  have ht0 : 0 < t0 := by rw [ht0def]; positivity
  refine ⟨min eps1 (min eps2 (t0 ^ 3)), lt_min h1.1 (lt_min h2pos (by positivity)),
    (min_le_left _ _).trans h1.2, C, hC0, ?_, ?_⟩
  · have := rpow_third_le (le_of_lt (lt_min h1.1 (lt_min h2pos (by positivity))) : 0 ≤ min eps1 (min eps2 (t0 ^ 3))) ht0.le
      ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : C * min eps1 (min eps2 (t0 ^ 3)) ^ ((1 : ℝ) / 3) ≤ C * t0 :=
      mul_le_mul_of_nonneg_left this hC0
    have h3 : C * t0 ≤ 1 / 2 := by
      rw [ht0def, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  intro d B p ν beta hB hp he hepsle hν eta heta
  have hε1 : 1 - beta ∈ Set.Ioc (0 : ℝ) eps1 := ⟨he, hepsle.trans (min_le_left _ _)⟩
  have hε2 : 1 - beta ≤ eps2 := hepsle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsm : (1 - beta) ^ ((1 : ℝ) / 3) ≤ t0 :=
    rpow_third_le he.le ht0.le (hepsle.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have heps12 : 1 - beta ≤ 1 / 2 := hε1.2.trans h1.2
  have hb1 : beta < 1 := by linarith
  have hb0 : 0 ≤ beta := by linarith
  have hnu := lsNu_pos (d := d) (B := B) (p := p) hB hb0 hb1 hp
  have hcp := criticalRate_pos' (d := d) (B := B) (p := p) hB hb0 hb1
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hp1 := p.2.2
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have he3pos : 0 < (1 - beta) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos he _
  have hCe : C * (1 - beta) ^ ((1 : ℝ) / 3) ≤ 1 / 2 := by
    have h2 : C * (1 - beta) ^ ((1 : ℝ) / 3) ≤ C * t0 := mul_le_mul_of_nonneg_left hsm hC0
    have h3 : C * t0 ≤ 1 / 2 := by
      rw [ht0def, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  -- Λ_V(η) ≤ Λ*
  have hcl := hCr d B p ν beta hB hp hε1 hν
  have hub : ∀ eta ∈ Set.Ioo 0 (criticalRate d B p beta),
      lsRate d B p ν beta eta
        ≤ (1 - beta) * rayRate (lsNu d B p beta) + Cr * (1 - beta) ^ ((4 : ℝ) / 3) := by
    intro eta heta
    have h := hcl eta heta
    have hle := continuumPerronRate_ray_le hnu (eta * p / (1 - beta))
    have := mul_le_mul_of_nonneg_left hle he.le
    have := (abs_le.1 h).2
    linarith
  have hbdd : BddAbove (lsRate d B p ν beta '' Set.Ioo 0 (criticalRate d B p beta)) :=
    ⟨_, by rintro _ ⟨eta, heta, rfl⟩; exact hub eta heta⟩
  have hle : lsRate d B p ν beta eta ≤ lsLamStar d B p ν beta :=
    le_csSup hbdd ⟨eta, heta, rfl⟩
  -- N_fold lower bound
  obtain ⟨_, _, hmaxb, _⟩ := hC d B p ν beta hB hp he (hepsle.trans ((min_le_right _ _).trans
    (min_le_left _ _))) hν
  have hSge := lsNstab_ge (d := d) (p := p) hB hb0 hb1
  have hdp : 0 < (d : ℝ) + 2 - p := by linarith
  have hY : 0 < 1 - C * (1 - beta) ^ ((1 : ℝ) / 3) := by linarith
  have hNf : ((d : ℝ) + 2 - p) * (1 - C * (1 - beta) ^ ((1 : ℝ) / 3)) ≤ lsNfold d B p ν beta := by
    refine le_trans ?_ hmaxb
    exact mul_le_mul_of_nonneg_right (hSge.trans (le_max_left _ _)) hY.le
  have hYpos : 0 < ((d : ℝ) + 2 - p) * (1 - C * (1 - beta) ^ ((1 : ℝ) / 3)) := by positivity
  have hNfpos : 0 < lsNfold d B p ν beta := lt_of_lt_of_le hYpos hNf
  have hpB : 0 < (p : ℝ) * B := by positivity
  have hLamStar : lsLamStar d B p ν beta = (p : ℝ) * B / lsNfold d B p ν beta := by
    have hne : lsLamStar d B p ν beta ≠ 0 := by
      intro h0
      have : lsNfold d B p ν beta = 0 := by rw [lsNfold, h0]; simp
      linarith
    rw [lsNfold]; field_simp
  have hbound : lsRate d B p ν beta eta
      ≤ (p : ℝ) * B / (((d : ℝ) + 2 - p) * (1 - C * (1 - beta) ^ ((1 : ℝ) / 3))) := by
    refine hle.trans ?_
    rw [hLamStar]
    exact div_le_div_of_nonneg_left hpB.le hYpos hNf
  refine ⟨hbound, fun hpos => ?_⟩
  have h1' := one_div_le_one_div_of_le hpos hbound
  refine le_trans (le_of_eq ?_) h1'
  field_simp

end L4

end

end SparseSGD.Scaling.Helps
