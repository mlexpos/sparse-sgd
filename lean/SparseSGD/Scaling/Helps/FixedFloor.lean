import SparseSGD.Scaling.Helps.ChiRoots
import SparseSGD.Scaling.Helps.StepSpeed
import SparseSGD.Scaling.Helps.Limits
import SparseSGD.Scaling.Helps.SpeedupExpansion

/-!
# Speed at a fixed floor (`v2 prop:fixed_floor = lem:speedup`)

Formalizes `prop:fixed_floor` of `paper/appendix/momentum_helps.tex`, the exact counterpart
paragraph after it, and the critical-damping / small-`Δ` paragraph.  Notation:
`Γ(Δ,u) = speedupRatio Δ u`, `momentumParams ε Δ u_n φ = ⟨1-ε, ε²Δ, u_n, φ⟩`,
`sgdParams ε Δ u_n φ = ⟨0, εΔ, u_n, φ⟩`.

* (P1) `fixed_floor_limit_noise`: the limit at fixed noise feedback `u_n`.
* (P2) `fixed_floor_limit_total`: the limit with the momentum chain's *total* feedback held at `u`
  (`fixedLoadNoise`, `momentumParams_totalLoad_fixedLoad`).
* (P3) `speedupRatio_le_two`, `speedupRatio_eq_two_iff` (part (i)).
* (P4) `speedupRatio_quarter_all` (part (ii), including `u = 0`).
* (P5) `fixed_floor_exact_counterpart` (the exact bound with no limit).
* (P6) `speedup_expansion_fixed_floor`, `momentum_helps_small_Delta`, `momentum_hurts_of_ge_third`.
* (P7) `critical_damping_vs_double_lr`.

**Tex correction (prop:fixed_floor).**  For `ε > 0` the total feedback of the momentum chain satisfies
`u ≥ u_c = ε²Δ/(2(2-ε)) > 0`, so no chain has "`u = 0` fixed".  Proposed fix: replace
"let `ε → 0` with `(Δ,u)` fixed" by "let `ε → 0` with `Δ` fixed and the noise feedback `u_n = u`
fixed (equivalently, the total feedback `→ u`)".  (P1) is that form and covers `u_n = 0`; (P2) is the
version with the total feedback exactly `u`.
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD Filter Topology Set

noncomputable section

/-! ### Small helpers -/

/-- Squeeze along `ε → 0+`. -/
theorem tendsto_of_abs_le_nhdsGT {f g : ℝ → ℝ} {L : ℝ}
    (hg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0))
    (h : ∀ᶠ e in 𝓝[>] (0 : ℝ), |f e - L| ≤ g e) :
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hg
  filter_upwards [h] with e he
  simpa [Real.dist_eq] using he

/-- `C ε^{1/3} → 0` as `ε → 0+`. -/
theorem tendsto_const_mul_rpow_third_nhdsGT (C : ℝ) :
    Tendsto (fun e : ℝ => C * e ^ ((1 : ℝ) / 3)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : ContinuousAt (fun e : ℝ => e ^ ((1 : ℝ) / 3)) 0 :=
    Real.continuousAt_rpow_const 0 _ (Or.inr (by norm_num))
  have h0 : Tendsto (fun e : ℝ => e ^ ((1 : ℝ) / 3)) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow (by norm_num : (1 : ℝ) / 3 ≠ 0)] using hc.tendsto
  have := (h0.const_mul C).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa using this

/-! ### (P1) the limit at fixed noise feedback -/

/-- (P1) `v2 prop:fixed_floor` (limit clause), fixed noise feedback: for `Δ > 0`, `u_n ∈ [0,1)`,
`φ ≥ 0`, the ratio of the momentum rate `Λ(⟨1-ε, ε²Δ, u_n, φ⟩)` to the SGD rate
`Λ(⟨0, εΔ, u_n, φ⟩)` tends to `Γ(Δ,u_n) = r_c(Δ,u_n)/(2Δ(1-u_n))` as `ε → 0+`.
This includes `u_n = 0`.  (Tex correction recorded in the module docstring.) -/
theorem fixed_floor_limit_noise {Delta un phi : ℝ} (hD : 0 < Delta) (hu0 : 0 ≤ un)
    (hu1 : un < 1) (hphi : 0 ≤ phi) :
    Tendsto (fun eps : ℝ =>
        perStepRate (momentumParams eps Delta un phi) / perStepRate (sgdParams eps Delta un phi))
      (𝓝[>] (0 : ℝ)) (𝓝 (speedupRatio Delta un)) := by
  have hsub : ({(Delta, un)} : Set (ℝ × ℝ)) ⊆ Set.Ioi 0 ×ˢ Set.Ico 0 1 := by
    rintro x rfl
    exact ⟨hD, hu0, hu1⟩
  obtain ⟨eps0, ⟨h0, _⟩, C, _, hC⟩ := cor_helps_speedup (K := {(Delta, un)}) isCompact_singleton hsub
  refine tendsto_of_abs_le_nhdsGT (tendsto_const_mul_rpow_third_nhdsGT C) ?_
  filter_upwards [Ioc_mem_nhdsGT h0] with e he
  exact (hC e he (Delta, un) (Set.mem_singleton _) phi hphi).2.2.1

/-! ### (P2) the limit at fixed total feedback -/

/-- The noise feedback for which the momentum chain `⟨1-ε, ε²Δ, ·, φ⟩` has total feedback exactly `u`:
`u_n(ε) = u - ε²Δ/(2(2-ε))` (the curvature feedback is `u_c = ε²Δ/(2(2-ε))`). -/
def fixedLoadNoise (eps Delta u : ℝ) : ℝ := u - eps ^ 2 * Delta / (2 * (2 - eps))

/-- The total feedback of the momentum chain with noise feedback `fixedLoadNoise ε Δ u` is `u`. -/
theorem momentumParams_totalLoad_fixedLoad (eps Delta u phi : ℝ) :
    (momentumParams eps Delta (fixedLoadNoise eps Delta u) phi).totalLoad = u := by
  simp only [Params.totalLoad, Params.curvature, momentumParams, fixedLoadNoise]
  have : (1 : ℝ) + (1 - eps) = 2 - eps := by ring
  rw [this]; ring

/-- `v2 prop:fixed_floor`: `u_n(ε) → u` as `ε → 0+`. -/
theorem tendsto_fixedLoadNoise (Delta u : ℝ) :
    Tendsto (fun e : ℝ => fixedLoadNoise e Delta u) (𝓝[>] (0 : ℝ)) (𝓝 u) := by
  have hc : ContinuousAt (fun e : ℝ => fixedLoadNoise e Delta u) 0 := by
    unfold fixedLoadNoise
    refine continuousAt_const.sub (ContinuousAt.div (by fun_prop) (by fun_prop) ?_)
    norm_num
  have h := hc.tendsto
  have h0 : fixedLoadNoise 0 Delta u = u := by simp [fixedLoadNoise]
  rw [h0] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- (P2) `v2 prop:fixed_floor` (limit clause), KE's `u` fixed: for `Δ > 0`, `u ∈ (0,1)` put
`u_n(ε) = u - ε²Δ/(2(2-ε))` so that the momentum chain's total feedback is `u`
(`momentumParams_totalLoad_fixedLoad`).  Then the ratio of the momentum rate to the SGD rate
`Λ(⟨0, εΔ, u_n(ε), φ⟩)` tends to `Γ(Δ,u)` as `ε → 0+`. -/
theorem fixed_floor_limit_total {Delta u phi : ℝ} (hD : 0 < Delta) (hu0 : 0 < u) (hu1 : u < 1)
    (hphi : 0 ≤ phi) :
    Tendsto (fun eps : ℝ =>
        perStepRate (momentumParams eps Delta (fixedLoadNoise eps Delta u) phi) /
          perStepRate (sgdParams eps Delta (fixedLoadNoise eps Delta u) phi))
      (𝓝[>] (0 : ℝ)) (𝓝 (speedupRatio Delta u)) := by
  have hsub : (({Delta} : Set ℝ) ×ˢ Set.Icc (u / 2) u : Set (ℝ × ℝ)) ⊆
      Set.Ioi 0 ×ˢ Set.Ico 0 1 := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨hD, by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨eps0, ⟨h0, h12⟩, C, _, hC⟩ :=
    cor_helps_speedup (K := ({Delta} : Set ℝ) ×ˢ Set.Icc (u / 2) u)
      (isCompact_singleton.prod isCompact_Icc) hsub
  -- `Γ(Δ, u_n(ε)) → Γ(Δ, u)`
  have hcont : ContinuousAt (fun v : ℝ => speedupRatio Delta v) u := by
    unfold speedupRatio
    have h1 : Continuous (fun v : ℝ => continuumPerronRate Delta v) := by
      have hpair : Continuous (fun v : ℝ => (Delta, v)) := by fun_prop
      have h := continuous_continuumPerronRate.comp hpair
      simpa only [Function.comp_def] using h
    have h1u : 0 < 1 - u := by linarith
    exact h1.continuousAt.div (by fun_prop) (by positivity)
  have hΓ : Tendsto (fun e : ℝ => speedupRatio Delta (fixedLoadNoise e Delta u))
      (𝓝[>] (0 : ℝ)) (𝓝 (speedupRatio Delta u)) :=
    hcont.tendsto.comp (tendsto_fixedLoadNoise Delta u)
  have hdiff : Tendsto (fun e : ℝ =>
      perStepRate (momentumParams e Delta (fixedLoadNoise e Delta u) phi) /
        perStepRate (sgdParams e Delta (fixedLoadNoise e Delta u) phi)
        - speedupRatio Delta (fixedLoadNoise e Delta u)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine tendsto_of_abs_le_nhdsGT (tendsto_const_mul_rpow_third_nhdsGT C) ?_
    have hε1 : 0 < min eps0 (min 1 (u / Delta)) :=
      lt_min h0 (lt_min one_pos (by positivity))
    filter_upwards [Ioc_mem_nhdsGT hε1] with e he
    have he0 : 0 < e := he.1
    have heA : e ≤ eps0 := he.2.trans (min_le_left _ _)
    have he1 : e ≤ 1 := he.2.trans ((min_le_right _ _).trans (min_le_left _ _))
    have heu : e ≤ u / Delta := he.2.trans ((min_le_right _ _).trans (min_le_right _ _))
    have heuD : e * Delta ≤ u := by
      rw [le_div_iff₀ hD] at heu; exact heu
    have he2 : e ^ 2 * Delta ≤ u := by
      have : e ^ 2 * Delta = e * (e * Delta) := by ring
      rw [this]
      have h3 : 0 ≤ e * Delta := by positivity
      nlinarith
    have h2e : 0 < 2 * (2 - e) := by linarith
    have hmem : (Delta, fixedLoadNoise e Delta u) ∈ ({Delta} : Set ℝ) ×ˢ Set.Icc (u / 2) u := by
      refine ⟨Set.mem_singleton _, ?_, ?_⟩
      · unfold fixedLoadNoise
        have : e ^ 2 * Delta / (2 * (2 - e)) ≤ u / 2 := by
          rw [div_le_iff₀ h2e]
          nlinarith [mul_nonneg hu0.le (sub_nonneg.2 he1)]
        linarith
      · unfold fixedLoadNoise
        have : 0 ≤ e ^ 2 * Delta / (2 * (2 - e)) := by positivity
        linarith
    have := (hC e ⟨he0, heA⟩ (Delta, fixedLoadNoise e Delta u) hmem phi hphi).2.2.1
    rw [sub_zero]
    exact this
  have := hdiff.add hΓ
  rw [zero_add] at this
  refine this.congr (fun e => ?_)
  ring

/-! ### (P3)-(P4) parts (i) and (ii) -/

/-- (P3) `v2 prop:fixed_floor (i)`: `Γ(Δ,u) ≤ 2` for `Δ > 0`, `u ∈ [0,1)` (including `u = 0`). -/
theorem speedupRatio_le_two {Delta u : ℝ} (hD : 0 < Delta) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    speedupRatio Delta u ≤ 2 := by
  rcases hu0.eq_or_lt with h | h
  · subst h
    unfold speedupRatio
    have hden : 0 < 2 * Delta * (1 - 0) := by
      have : (0 : ℝ) < 1 - 0 := by norm_num
      positivity
    rw [div_le_iff₀ hden]
    have := chi_roots_e_zero_le hD
    linarith
  · exact (speedupRatio_lt_two hD h hu1).le

/-- (P3) `v2 prop:fixed_floor (i)`, equality case: `Γ(Δ,u) = 2` iff `u = 0` and `Δ = 1/4`.
(Supersedes correction MH-2.) -/
theorem speedupRatio_eq_two_iff {Delta u : ℝ} (hD : 0 < Delta) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    speedupRatio Delta u = 2 ↔ u = 0 ∧ Delta = 1 / 4 := by
  constructor
  · intro h
    rcases hu0.eq_or_lt with h0 | h0
    · refine ⟨h0.symm, ?_⟩
      subst h0
      unfold speedupRatio at h
      have hden : 0 < 2 * Delta * (1 - 0) := by
        have : (0 : ℝ) < 1 - 0 := by norm_num
        positivity
      rw [div_eq_iff hden.ne'] at h
      exact (chi_roots_e_zero_eq_iff hD).1 (by linarith)
    · exact absurd h (speedupRatio_lt_two hD h0 hu1).ne
  · rintro ⟨rfl, rfl⟩
    unfold speedupRatio
    rw [chi_roots_b_ge (by norm_num) le_rfl]
    norm_num

/-- (P4) `v2 prop:fixed_floor (ii)`: `Γ(1/4,u) = 2/(1+a+a²)` with `a = u^{1/3}`, for every
`u ∈ [0,1)` (`u = 0` included, where both sides are `2`). -/
theorem speedupRatio_quarter_all {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    speedupRatio (1 / 4) u = 2 / (1 + u ^ ((1 : ℝ) / 3) + (u ^ ((1 : ℝ) / 3)) ^ 2) := by
  rcases hu0.eq_or_lt with h | h
  · subst h
    unfold speedupRatio
    rw [chi_roots_b_ge (by norm_num) le_rfl, Real.zero_rpow (by norm_num)]
    norm_num
  · exact speedupRatio_quarter h hu1

/-! ### (P5) the exact counterpart -/

/-- (P5) The exact counterpart of part (i), `v2 prop:fixed_floor` (paragraph after the proof,
from `lem:step_speed (ii)` and `lem:helps-sgd`).  For `β = 1-ε ∈ [0,1)`, `w = ε²Δ > 0`,
`u_n ≥ 0`, `4εΔ < 1` and SGD total feedback `u = u_n + εΔ/2 < 1`, the ratio of the momentum rate to that of
the SGD chain `⟨0, εΔ, u_n, φ⟩` is at most `2/((1-u)(1-4εΔ))`, with no limit taken. -/
theorem fixed_floor_exact_counterpart {eps Delta un phi : ℝ} (he0 : 0 < eps) (he1 : eps ≤ 1)
    (hD : 0 < Delta) (hun : 0 ≤ un) (h4 : 4 * eps * Delta < 1) (hu : un + eps * Delta / 2 < 1) :
    perStepRate (momentumParams eps Delta un phi) / perStepRate (sgdParams eps Delta un phi)
      ≤ 2 / ((1 - (un + eps * Delta / 2)) * (1 - 4 * eps * Delta)) := by
  have hpe : (momentumParams eps Delta un phi).eps = eps := by
    simp [Params.eps, momentumParams]
  have hw : 0 < eps * Delta := mul_pos he0 hD
  have hwm : 0 < eps ^ 2 * Delta := by positivity
  -- momentum side
  have hcap := (perStepRate_le_curvature_cap (momentumParams eps Delta un phi) Delta
    (by simp [momentumParams]; linarith) (by simp [momentumParams]; linarith) hwm hun
    (by rw [hpe]; rfl) (by rw [hpe]; exact h4)).2
  rw [hpe] at hcap
  have h4' : 0 < 1 - 4 * eps * Delta := by linarith
  have hlog := neg_log_one_sub_le (show 4 * eps * Delta < 1 from h4)
  have hnum : perStepRate (momentumParams eps Delta un phi) ≤ 4 * eps * Delta / (1 - 4 * eps * Delta) :=
    hcap.trans hlog
  -- SGD side
  have hb : (sgdParams eps Delta un phi).beta = 0 := rfl
  have hwS : 0 < (sgdParams eps Delta un phi).w := hw
  have hnS : 0 ≤ (sgdParams eps Delta un phi).noise := hun
  have hload : (sgdParams eps Delta un phi).totalLoad = un + eps * Delta / 2 := by
    rw [totalLoad_beta_zero _ hb]; rfl
  have hlt' : (sgdParams eps Delta un phi).totalLoad < 1 := by rw [hload]; exact hu
  have hrate := (sgd_coeff_bounds _ hb hwS hnS hlt').2.2
  rw [hload] at hrate
  have hwdef : (sgdParams eps Delta un phi).w = eps * Delta := rfl
  rw [hwdef] at hrate
  have h1u : 0 < 1 - (un + eps * Delta / 2) := by linarith
  set x : ℝ := 2 * (eps * Delta) * (1 - (un + eps * Delta / 2)) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by
    have : 1 - (un + eps * Delta / 2) ≤ 1 := by linarith
    have h5 : x ≤ 2 * (eps * Delta) * 1 :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hge := neg_log_one_sub_ge hx1
  have hden : x ≤ perStepRate (sgdParams eps Delta un phi) := by
    rw [hrate]
    have e : 1 - 2 * (eps * Delta) * (1 - (un + eps * Delta / 2)) = 1 - x := by rw [hx]
    rw [e]; exact hge
  have hcap0 : 0 ≤ 4 * eps * Delta / (1 - 4 * eps * Delta) := by positivity
  calc perStepRate (momentumParams eps Delta un phi) / perStepRate (sgdParams eps Delta un phi)
      ≤ (4 * eps * Delta / (1 - 4 * eps * Delta)) / perStepRate (sgdParams eps Delta un phi) :=
        div_le_div_of_nonneg_right hnum (hx0.trans_le hden).le
    _ ≤ (4 * eps * Delta / (1 - 4 * eps * Delta)) / x :=
        div_le_div_of_nonneg_left hcap0 hx0 hden
    _ = 2 / ((1 - (un + eps * Delta / 2)) * (1 - 4 * eps * Delta)) := by
        rw [hx]
        field_simp
        norm_num

/-! ### (P6) small `Δ` -/

/-- (P6) `v2 prop:fixed_floor`, last paragraph (restating `speedup_expansion`):
`Γ(Δ,u) = 1 + Δ(1-3u) + O(Δ²)` as `Δ → 0+`, for every `u ∈ [0,1)`. -/
theorem speedup_expansion_fixed_floor {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ D : ℝ, 0 < D → D < δ →
      |speedupRatio D u - (1 + D * (1 - 3 * u))| ≤ C * D ^ 2 := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := speedup_expansion hu0 hu1
  refine ⟨C, δ, hC, hδ, fun D hD hDδ => ?_⟩
  have := (hb D hD hDδ).2
  have e : speedupRatio D u - (1 + D * (1 - 3 * u)) = speedupRatio D u - 1 - (1 - 3 * u) * D := by
    ring
  rw [e]; exact this

/-- (P6) `v2 prop:fixed_floor`, last paragraph: for `u ∈ [0, 1/3)` there is `δ > 0` with
`Γ(Δ,u) > 1` for all `Δ ∈ (0,δ)` (`u = 0` included). -/
theorem momentum_helps_small_Delta {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1 / 3) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ D : ℝ, 0 < D → D < δ → 1 < speedupRatio D u := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := speedup_expansion hu0 (by linarith)
  have hs : 0 < 1 - 3 * u := by linarith
  refine ⟨min δ ((1 - 3 * u) / (2 * C)), lt_min hδ (by positivity), fun D hD0 hDlt => ?_⟩
  have hDδ : D < δ := lt_of_lt_of_le hDlt (min_le_left _ _)
  have hDc : D < (1 - 3 * u) / (2 * C) := lt_of_lt_of_le hDlt (min_le_right _ _)
  have hCD : C * D < (1 - 3 * u) / 2 := by
    have := (lt_div_iff₀ (by positivity : 0 < 2 * C)).1 hDc
    nlinarith
  have h := (abs_le.1 (hb D hD0 hDδ).2).1
  have : C * D ^ 2 < (1 - 3 * u) / 2 * D := by nlinarith
  nlinarith

/-- (P6) `v2 prop:fixed_floor`, last paragraph: for `u ∈ [1/3, 1)` (in particular `u ∈ (1/3,1)`),
momentum does not help at any `Δ > 0`: `Γ(Δ,u) < 1`. -/
theorem momentum_hurts_of_ge_third {Delta u : ℝ} (hD : 0 < Delta) (hu0 : 1 / 3 ≤ u)
    (hu1 : u < 1) : speedupRatio Delta u < 1 :=
  speedupRatio_lt_one hD hu0 hu1

/-! ### (P7) critical damping against doubled learning rate -/

/-- `Λ/ε → r_c(Δ,u_n)` for the momentum chain (from `helps_transfer_box`). -/
theorem momentum_rate_div_eps_tendsto {Delta un phi : ℝ} (hD : 0 < Delta) (hun : 0 ≤ un) :
    Tendsto (fun e : ℝ => perStepRate (momentumParams e Delta un phi) / e) (𝓝[>] (0 : ℝ))
      (𝓝 (continuumPerronRate Delta un)) := by
  obtain ⟨eps0, ⟨h0, _⟩, C, hC⟩ := helps_transfer_box Delta un hD hun
  refine tendsto_of_abs_le_nhdsGT (tendsto_const_mul_rpow_third_nhdsGT C) ?_
  filter_upwards [Ioc_mem_nhdsGT h0] with e he
  have he0 : 0 < e := he.1
  have hb := (hC e he Delta ⟨hD, le_rfl⟩ un ⟨hun, le_rfl⟩).1
  have hrate : perStepRate (momentumParams e Delta un phi)
      = perStepRate (transferParams e Delta un) := perStepRate_congr rfl rfl rfl
  rw [hrate]
  have h2 : e ^ ((4 : ℝ) / 3) = e * e ^ ((1 : ℝ) / 3) := by
    rw [show (4 : ℝ) / 3 = 1 + 1 / 3 by norm_num, Real.rpow_add he0, Real.rpow_one]
  have e1 : perStepRate (transferParams e Delta un) / e - continuumPerronRate Delta un
      = (perStepRate (transferParams e Delta un) - e * continuumPerronRate Delta un) / e := by
    field_simp
  rw [e1, abs_div, abs_of_pos he0, div_le_iff₀ he0]
  calc _ ≤ C * e ^ ((4 : ℝ) / 3) := hb
    _ = C * e ^ ((1 : ℝ) / 3) * e := by rw [h2]; ring

/-- `Λ(⟨0, ε/2, 2u_n, 2φ⟩)/ε → 1 - 2u_n` for `u_n ∈ [0, 1/2)`. -/
theorem double_lr_sgd_rate_div_eps_tendsto {un phi : ℝ} (hu0 : 0 ≤ un) (hu1 : un < 1 / 2) :
    Tendsto (fun e : ℝ => perStepRate (⟨0, e / 2, 2 * un, 2 * phi⟩ : Params) / e)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 - 2 * un)) := by
  have hε : 0 < min (1 / 2 : ℝ) (2 * (1 - 2 * un)) := lt_min (by norm_num) (by linarith)
  have hg : Tendsto (fun e : ℝ => (9 / 4 : ℝ) * e ^ ((1 : ℝ) / 3)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_mul_rpow_third_nhdsGT _
  refine tendsto_of_abs_le_nhdsGT hg ?_
  filter_upwards [Ioc_mem_nhdsGT hε] with e he
  have he0 : 0 < e := he.1
  have he12 : e ≤ 1 / 2 := he.2.trans (min_le_left _ _)
  have heu : e ≤ 2 * (1 - 2 * un) := he.2.trans (min_le_right _ _)
  have hsg : (⟨0, e / 2, 2 * un, 2 * phi⟩ : Params) = sgdParams e (1 / 2) (2 * un) (2 * phi) := by
    simp only [sgdParams]
    congr 1
    ring
  rw [hsg]
  have hlt : 2 * un + e * (1 / 2) / 2 < 1 := by linarith
  have hb := sgd_rate_close (phi := 2 * phi) (D := 1 / 2) he0 (by norm_num : (0 : ℝ) < 1 / 2)
    le_rfl (by linarith) hlt (by linarith)
  have e1 : perStepRate (sgdParams e (1 / 2) (2 * un) (2 * phi)) / e - (1 - 2 * un)
      = (perStepRate (sgdParams e (1 / 2) (2 * un) (2 * phi))
          - e * (2 * (1 / 2) * (1 - 2 * un))) / e := by
    field_simp
  rw [e1, abs_div, abs_of_pos he0, div_le_iff₀ he0]
  refine hb.trans ?_
  have h3 : e ≤ e ^ ((1 : ℝ) / 3) := le_rpow_third he0.le (by linarith)
  have : (9 / 4 : ℝ) * e ^ ((1 : ℝ) / 3) * e = 9 / 4 * e ^ ((1 : ℝ) / 3) * e := rfl
  have h4 : 9 * (1 / 2 : ℝ) ^ 2 * e ^ 2 = 9 / 4 * e * e := by ring
  rw [h4]
  have h5 : 9 / 4 * e * e ≤ 9 / 4 * e ^ ((1 : ℝ) / 3) * e := by
    have := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 9 / 4)
    nlinarith
  exact h5

/-- (P7) `v2 prop:fixed_floor`, critical damping against a doubled learning rate.
Let `u_n ∈ [0, 1/2)`, `a = u_n^{1/3}`.  The rate of critically damped momentum
`⟨1-ε, ε²/4, u_n, φ⟩` (learning rate `η`) divided by that of SGD at `2η`, `⟨0, ε/2, 2u_n, 2φ⟩`,
tends to `(1-a)/(1-2a³)`, which is `≥ 1 - a`; the floor of the momentum chain tends to `φ/(1-u_n)`
(that of SGD at `η`) and that of SGD at `2η` tends to `2φ/(1-2u_n)`. -/
theorem critical_damping_vs_double_lr {un phi a : ℝ} (hu0 : 0 ≤ un) (hu1 : un < 1 / 2)
    (ha : a = un ^ ((1 : ℝ) / 3)) :
    Tendsto (fun e : ℝ => perStepRate (momentumParams e (1 / 4) un phi) /
        perStepRate (⟨0, e / 2, 2 * un, 2 * phi⟩ : Params))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 - a) / (1 - 2 * a ^ 3))) ∧
    1 - a ≤ (1 - a) / (1 - 2 * a ^ 3) ∧
    Tendsto (fun e : ℝ => floorOf (momentumParams e (1 / 4) un phi)) (𝓝[>] (0 : ℝ))
      (𝓝 (phi / (1 - un))) ∧
    Tendsto (fun e : ℝ => floorOf (⟨0, e / 2, 2 * un, 2 * phi⟩ : Params)) (𝓝[>] (0 : ℝ))
      (𝓝 (2 * phi / (1 - 2 * un))) := by
  have hcube : a ^ 3 = un := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hu0]; norm_num
  have ha0 : 0 ≤ a := by rw [ha]; exact Real.rpow_nonneg hu0 _
  have hrc : continuumPerronRate (1 / 4) un = 1 - a := by
    rw [chi_roots_c hu0 (by linarith), ha]
  have hden : 0 < 1 - 2 * a ^ 3 := by rw [hcube]; linarith
  have ha1 : a < 1 := by
    by_contra h
    push Not at h
    have : 1 ≤ a ^ 3 := one_le_pow₀ h
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hM := momentum_rate_div_eps_tendsto (phi := phi) (by norm_num : (0 : ℝ) < 1 / 4) hu0
    have hS := double_lr_sgd_rate_div_eps_tendsto (phi := phi) hu0 hu1
    rw [hrc] at hM
    have := hM.div hS (by linarith)
    rw [hcube]
    refine (Tendsto.congr' ?_ this)
    filter_upwards [self_mem_nhdsWithin] with e he
    have he0 : (0 : ℝ) < e := he
    rw [Pi.div_apply, div_div_div_cancel_right₀ he0.ne']
  · rw [le_div_iff₀ hden]
    have : 0 ≤ 1 - a := by linarith
    nlinarith [pow_nonneg ha0 3]
  · have hc : ContinuousAt (fun e : ℝ => phi / (1 - (un + e ^ 2 * (1 / 4) / (2 * (1 + (1 - e))))))
        0 := by
      refine ContinuousAt.div continuousAt_const
        (continuousAt_const.sub (continuousAt_const.add (ContinuousAt.div (by fun_prop)
          (by fun_prop) ?_))) ?_
      · norm_num
      · norm_num; linarith
    have h := hc.tendsto
    have h0 : phi / (1 - (un + (0 : ℝ) ^ 2 * (1 / 4) / (2 * (1 + (1 - 0))))) = phi / (1 - un) := by
      norm_num
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  · have hc : ContinuousAt (fun e : ℝ => 2 * phi / (1 - (2 * un + (e / 2) / (2 * (1 + 0))))) 0 := by
      refine ContinuousAt.div continuousAt_const
        (continuousAt_const.sub (continuousAt_const.add (ContinuousAt.div (by fun_prop)
          continuousAt_const ?_))) ?_
      · norm_num
      · norm_num; linarith
    have h := hc.tendsto
    have h0 : 2 * phi / (1 - (2 * un + ((0 : ℝ) / 2) / (2 * (1 + 0)))) = 2 * phi / (1 - 2 * un) := by
      norm_num
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds

end
end SparseSGD.Scaling.Helps
