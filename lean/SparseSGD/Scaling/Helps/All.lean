import SparseSGD.Scaling.Helps.StepMatrix
import SparseSGD.Scaling.Helps.CubicRoots
import SparseSGD.Scaling.Helps.RootPerturbation
import SparseSGD.Scaling.Helps.Ray
import SparseSGD.Scaling.Helps.ExactRate
import SparseSGD.Scaling.Helps.SpeedupExpansion
import SparseSGD.Scaling.Helps.Transfer
import SparseSGD.Scaling.Helps.Stability
import SparseSGD.Scaling.Helps.Limits
import SparseSGD.Scaling.Helps.Vocabulary
import SparseSGD.Scaling.Helps.CriticalBatch
import SparseSGD.Scaling.Helps.ChiRoots
import SparseSGD.Scaling.Helps.StepSpeed
import SparseSGD.Scaling.Helps.StepSpectrum
import SparseSGD.Scaling.Helps.SmallDeltaSlowRoot
import SparseSGD.Scaling.Helps.SmallDeltaFactor
import SparseSGD.Scaling.Helps.SmallDelta
import SparseSGD.Scaling.Helps.SampleCostAbove
import SparseSGD.Scaling.Helps.SampleCost
import SparseSGD.Scaling.Helps.Schedule
import SparseSGD.Scaling.Helps.FixedFloor
import SparseSGD.Scaling.Helps.VocabRows
import SparseSGD.Scaling.Helps.VocabFull

/-!
# V2 momentum-helps appendix: composed results

This module imports every module of `SparseSGD/Scaling/Helps/` and bundles some of the main
statements of `source/v2/momentum_helps.tex` (section `sec:helps-app`, "Benefits of momentum";
snapshot of 2026-10-05 after the merge with KE's section and the harmonization pass).

The decay rate per step `Λ = -ln ρ(T)` (`app:rates`) is `perStepRate`, where `ρ(T) = stepRadius`
is the maximal modulus of the roots of the closed-form characteristic polynomial `stepCharPoly`
of the linear part `T` (`det_stepLinearMatrix`).  Lean's `Real.log 0 = 0`, so `Λ = ∞` (radius
`0`) is not encoded; statements that need `Λ` finite carry a hypothesis forcing a positive
radius.  `ρ(F)` is `meanRadius` (`StepSpeed`).

Map from the merged tex labels to the Lean statements (the registry `obligations.json` is the
authoritative list):

* `app:rates` (definition of `Λ`, and `Λ = ε r_c (1+o(1))`): `perStepRate`, `stepRadius`,
  `continuumPerronRate`; `helps_transfer`, `helps_transfer_compact`.
* `lem:chi_roots` (a)-(e): `lem_chi_roots` (`ChiRoots`).
* `lem:helps-sgd`: `lem_helps_sgd` below (and `ls_beta_zero_sup` for the LS part).
* `lem:step_speed` = `lem:helps-onecopy` (`β ∈ [0,1)`): `lem_step_speed`,
  `perStepRate_le_curvature_cap` (`StepSpeed`); pre-merge `perStepRate_le_onecopy`.
* `lem:step_spectrum`: `mem_stepRoots_iff_spectrumQ`, `abs_spectrumB_le`, `spectrumQ_sub_chi`
  (`StepSpectrum`).
* `lem:small_delta`: `lem_small_delta`, `lsRate_small_delta` (`SmallDelta`, with
  `SmallDeltaSlowRoot`, `SmallDeltaFactor`).
* `lem:ray`: `lem_ray_bundle` below.
* `cor:sample_cost` = `cor:samplecost`: (i) `lsNfold_ge_retention` (`SampleCostAbove`);
  (ii) `samplecost_below` (`s → ∞`), `cor_samplecost` (`s → s₀`), `samplecost_above` (`s → 0`),
  `cor_sample_cost_uniform`, `cor_sample_cost_tendsto` (`SampleCost`).
* `rem:sgd_cost`: `lsNfoldSGD_eq`, `lsNfoldSGD_mono`, `lsNfoldSGD_le_max`,
  `samplecost_ge_max_uniform`, `samplecost_ge_sgd_uniform`.
* `rem:crit_single`: `hyperbola_relation`, `hyperbola_perturb`.
* `prop:fixed_floor` = `lem:speedup`: `fixed_floor_limit_noise`, `fixed_floor_limit_total`,
  `speedupRatio_le_two`, `speedupRatio_eq_two_iff`, `speedupRatio_quarter_all`,
  `fixed_floor_exact_counterpart`, `critical_damping_vs_double_lr` (`FixedFloor`), and
  `lem_speedup` below (the pre-merge `u ∈ (0,1)` bundle with the small-`Δ` expansion).
* `rem:schedule`: `schedule_risk_asymptotic` (`Schedule`).
* `lem:vocab_rows`: `VocabRows.vocab_row_moment_trajectory_explicit`,
  `VocabRows.vocab_excess_loss_expectation` (`VocabRows`).
* `lem:helps-vocab` (i)-(v): `lem_helps_vocab_v2` (`Vocabulary`), the co-scaling clause of (iii)
  `helps_vocab_iii_coscaling` (`SampleCost`).
* `lem:helps-twocurv`: `twocurv_real`, `rhoMax_ge_twocurv` (stated through `ρ(T) ≥ ρ(F)²`).
* `prop:helps-critical` (i)-(iv): `prop_helps_critical_v2` (`CriticalBatch`; `A_O(B)` is
  `admSet`, `S_O(B)` is `Sfun`, `E_O(B)` is `Efun`, `B_O` is `Bcrit`); pre-merge
  `prop_helps_critical`.
* `prop:vocab_full` = `rem:vocab`: `prop_vocab_full` (`VocabFull`), the co-scaling clause of (i)
  `vocab_full_i_coscaling` (`SampleCost`).
* `rem:retention-cap` (a) of the live chunk `07_cor_lift`: `meanRadius_sq_le_stepRadius`,
  `beta_le_meanRadius_sq`, `meanRadius_sq_eq_beta_iff` (`StepSpeed`).

Supporting (statements dropped from the merged tex, Lean proofs kept): `lem:helps-rate`
(`perStepRate_pos_iff`), `lem:helps-roots` (`cubicRoots_match`), `lem:helps-transfer`
(`lem_helps_transfer` below), `cor:helps-speedup` (`cor_helps_speedup`).

The only external input is the 2x2 Jury criterion `External.JuryStability`, passed explicitly
to the stability statements (`stepRadius_lt_one_iff`, `all_stable_iff_lt_min`), to `Λ* > 0` in
`lsNfold_ge_retention`, and to the fixed-`β` statements `S_β = inf_B S_β(B)` (nonemptiness of
the admissible set).  The pre-merge `CriticalBatch` statements do not use it.
-/

open Filter Topology Set

namespace SparseSGD.Scaling.Helps
open SparseSGD

/-- `v2 lem:ray`, all claims.  For `ν > 0`, the supremum of `r_c(Δ, νΔ/2)` over
`Δ ∈ (0, 2/ν)` is attained and equals `r_⋆(ν) = 1 - ν Δ_ν` with `Δ_ν = 1/(1+√(1+ν²))`
(`rayRate`, `rayDelta`); it is attained only at `Δ_ν`, and
`1/r_⋆(ν) = (1 + ν + √(1+ν²))/2`. -/
theorem lem_ray_bundle {nu : ℝ} (hnu : 0 < nu) :
    IsGreatest ((fun D => continuumPerronRate D (nu * D / 2)) '' Ioo 0 (2 / nu)) (rayRate nu) ∧
    (∀ D ∈ Ioo 0 (2 / nu), continuumPerronRate D (nu * D / 2) = rayRate nu → D = rayDelta nu) ∧
    1 / rayRate nu = (1 + nu + Real.sqrt (1 + nu ^ 2)) / 2 :=
  ⟨lem_ray hnu, fun _ hD hmax => lem_ray_unique hnu hD hmax, inv_rayRate hnu⟩

/-- `v2 lem:speedup`, all four parts, for `Γ(Δ,u) = r_c(Δ,u)/(2Δ(1-u))` (`speedupRatio`).
For `u ∈ (0,1)`:

(i) `Γ(Δ,u) < 2` for every `Δ > 0`;
(ii) `Γ(1/4,u) = 2/(1+a+a²)` with `a = u^{1/3}`;
(iii) `Γ(Δ,u) = 1 + (1-3u)Δ + O(Δ²)` as `Δ → 0+`;
(iv) if `u ≥ 1/3`, `Γ(Δ,u) < 1` for every `Δ > 0` and `sup_Δ Γ = 1`; if `u < 1/3`,
`Γ(Δ,u) > 1` for all sufficiently small `Δ > 0`.

The last conjunct is the limit clause of (ii): `sup_{Δ>0} Γ(Δ,u) → 2` as `u → 0+`. -/
theorem lem_speedup :
    (∀ u : ℝ, 0 < u → u < 1 →
      (∀ D : ℝ, 0 < D → speedupRatio D u < 2) ∧
      speedupRatio (1 / 4) u = 2 / (1 + u ^ ((1 / 3 : ℝ)) + (u ^ ((1 / 3 : ℝ))) ^ 2) ∧
      (fun D => speedupRatio D u - 1 - (1 - 3 * u) * D) =O[𝓝[>] (0 : ℝ)] (fun D => D ^ 2) ∧
      (1 / 3 ≤ u →
        (∀ D : ℝ, 0 < D → speedupRatio D u < 1) ∧
        sSup ((fun D => speedupRatio D u) '' Ioi (0 : ℝ)) = 1) ∧
      (u < 1 / 3 → ∀ᶠ D in 𝓝[>] (0 : ℝ), 1 < speedupRatio D u)) ∧
    Tendsto (fun u : ℝ => sSup ((fun D => speedupRatio D u) '' Ioi (0 : ℝ)))
      (𝓝[Ioo 0 1] (0 : ℝ)) (𝓝 2) :=
  ⟨fun _ hu0 hu1 =>
    ⟨fun _ hD => speedupRatio_lt_two hD hu0 hu1, speedupRatio_quarter hu0 hu1,
      speedupRatio_isBigO hu0.le hu1,
      fun h3 => ⟨fun _ hD => speedupRatio_lt_one hD h3 hu1, sSup_speedupRatio_eq_one h3 hu1⟩,
      fun h3 => speedupRatio_gt_one_eventually hu0 h3⟩,
    tendsto_sSup_speedupRatio_zero⟩

/-- `v2 lem:helps-sgd` (chain part).  At `β = 0`, with `w > 0` and `u_n ≥ 0`:
`ρ(L) = |1 - 2w(1-u)|`; the linear part is stable iff `u < 1`; and then
`0 ≤ 1 - 2w(1-u) < 1` and `Λ = -log(1 - 2w(1-u))`.  The `(1,1)` recursion is
`step_R_beta_zero`; the LS supremum is `ls_beta_zero_sup`. -/
theorem lem_helps_sgd (p : Params) (hb : p.beta = 0) (hw : 0 < p.w) (hun : 0 ≤ p.noise) :
    stepRadius p = |1 - 2 * p.w * (1 - p.totalLoad)| ∧
    (stepRadius p < 1 ↔ p.totalLoad < 1) ∧
    (p.totalLoad < 1 →
      0 ≤ 1 - 2 * p.w * (1 - p.totalLoad) ∧ 1 - 2 * p.w * (1 - p.totalLoad) < 1 ∧
        perStepRate p = -Real.log (1 - 2 * p.w * (1 - p.totalLoad))) :=
  ⟨stepRadius_beta_zero p hb, stepRadius_lt_one_iff_beta_zero p hb hw hun,
    sgd_coeff_bounds p hb hw hun⟩

/-- `v2 lem:helps-transfer`, both forms.  For `D, c > 0` there are `ε₀ ∈ (0,1/2]` and `C`
such that, for `ε ∈ (0,ε₀]`, `Δ ∈ (0,D]`, `u_n ∈ [0,cΔ]`, the per-step rate of the chain at
`β = 1-ε`, `w = ε²Δ`, noise load `u_n` (`transferParams`) is within `C ε^{4/3}` of
`ε r_c(Δ,u_n)` and of `ε r_c(Δ,u)` with `u = u_n + u_c`.  On a compact
`K ⊆ (0,∞) × [0,1)` the relative error is `C ε^{1/3}`. -/
theorem lem_helps_transfer (D c : ℝ) (hD : 0 < D) (hc : 0 < c) :
    (∃ eps0 : ℝ, eps0 ∈ Ioc (0 : ℝ) (1 / 2) ∧ ∃ C : ℝ,
      ∀ eps ∈ Ioc (0 : ℝ) eps0, ∀ Delta ∈ Ioc (0 : ℝ) D,
        ∀ un ∈ Icc (0 : ℝ) (c * Delta),
        |perStepRate (transferParams eps Delta un) - eps * continuumPerronRate Delta un|
            ≤ C * eps ^ ((4 : ℝ) / 3) ∧
        |perStepRate (transferParams eps Delta un)
            - eps * continuumPerronRate Delta (un + (transferParams eps Delta un).curvature)|
            ≤ C * eps ^ ((4 : ℝ) / 3)) ∧
    (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Ioi 0 ×ˢ Ico 0 1 →
      ∃ eps0 : ℝ, eps0 ∈ Ioc (0 : ℝ) (1 / 2) ∧ ∃ C : ℝ,
        ∀ eps ∈ Ioc (0 : ℝ) eps0, ∀ x ∈ K,
          |perStepRate (transferParams eps x.1 x.2) / (eps * continuumPerronRate x.1 x.2) - 1|
            ≤ C * eps ^ ((1 : ℝ) / 3)) :=
  ⟨helps_transfer D c hD hc, fun _ hK hsub => helps_transfer_compact hK hsub⟩

end SparseSGD.Scaling.Helps
