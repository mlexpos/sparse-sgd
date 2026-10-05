import SparseSGD.Discrete.Stability

/-!
# Renewal layer for the momentum range `β ∈ [0,1)` (v2)

The v1 renewal declarations (`stable_kernel_masses`, `trajectory_risk_*`, ...) carry the
hypothesis `1/2 ≤ β`, used only to obtain `1 - β ≠ 0`, `1 + β > 0` and positivity of the
curvature gap.  Here they are re-proved under `0 ≤ β < 1`, as new declarations with suffix `_v2`.

* (G1) v2 `lem:L2`: `kickResponse_beta_zero` and the kernel statements.
* (G2) v2 `cor:stab` (i)-(ii) (and `cor:lift` (ii)).
* (G3) v2 `cor:stab` (iii) with the hypothesis `0 < s.R ∨ (0 < β ∧ s ≠ 0)`, and the
  dark-start counterexample at `β = 0`.
* (G4) v2 `cor:lift` (i) at `β = 0`: the noise-free covariance has rank at most one.

`lem:L1` needs no new declaration: `raw_oracle_memLp`, `raw_oracle_covariance_step` and
`raw_oracle_moment_trajectory` (Probability/RawOracle.lean) take an arbitrary real `β`, so they
already cover `β ∈ [0,1)`.  Jury stability stays an explicit hypothesis.
-/

open Filter
open scoped Topology

namespace SparseSGD

noncomputable section

/-- Under `0 ≤ β` and the stability ceiling `w < 2(1+β)`, the curvature is below one.
(Shared step of the v2 proofs, replacing `1/2 ≤ β`.) -/
theorem one_sub_curvature_pos_v2 (p : Params) (hb0 : 0 ≤ p.beta)
    (hw1 : p.w < 2 * (1 + p.beta)) : 0 < 1 - p.curvature := by
  unfold Params.curvature
  rw [sub_pos]
  apply (div_lt_iff₀ (by linarith : 0 < 2 * (1 + p.beta))).2
  linarith

/-! ### (G1) lem:L2 -/

/-- v2 `lem:L2`: at `β = 0` the kick response is `x_n = -(1-w)^n`, hence the kernel is
`K_n = η² ε² (1-w)^{2n}`.  For `β > 0` use `kickResponse_eq_chebyshev`. -/
theorem kickResponse_beta_zero (p : Params) (hb : p.beta = 0) (n : ℕ) :
    kickResponse p n = -(1 - p.w) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => rw [kickResponse_one, hb]; ring
  | more n h0 h1 =>
    rw [kickResponse_recurrence, h0, h1, hb]
    ring

/-- v2 `lem:L2` at `β = 0`: the squared kick response is `(1-w)^{2n}`. -/
theorem kickResponse_sq_beta_zero (p : Params) (hb : p.beta = 0) (n : ℕ) :
    (kickResponse p n) ^ 2 = ((1 - p.w) ^ 2) ^ n := by
  rw [kickResponse_beta_zero p hb, neg_sq, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- v2 `lem:L2` mass identities for `0 ≤ β < 1`. -/
theorem stable_kernel_masses_v2 (jury : External.JuryStability) (p : Params)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta)) :
    HasSum (fun n => 2 * p.w * p.eps * p.noise * (kickResponse p n) ^ 2)
      p.renormNoise ∧
    HasSum (fun n => 2 * p.w * p.eps * p.additive * (kickResponse p n) ^ 2)
      p.renormAdditive := by
  have heps : 1 - p.beta ≠ 0 := by linarith
  have hplus : 1 + p.beta ≠ 0 := by linarith
  have hcurv : 1 - p.curvature ≠ 0 := (one_sub_curvature_pos_v2 p hb0 hw1).ne'
  have hdecay := External.mean_powers_tendsto_zero jury p hb1 hw0 hw1
  have hmass := p.renewal_kernel_hasSum hw0.ne' heps hplus hcurv hdecay
  constructor
  · have h := hmass.mul_left p.noise
    convert h using 1
    · funext n
      ring
    · simp only [Params.renormNoise, div_eq_mul_inv, one_mul]
  · have h := hmass.mul_left p.additive
    convert h using 1
    · funext n
      ring
    · simp only [Params.renormAdditive, div_eq_mul_inv, one_mul]

/-- v2 `lem:L2`: the normalized lag kernel is nonnegative. -/
theorem normalized_kernel_lag_nonneg_v2 (_jury : External.JuryStability) (p : Params)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta)) :
    ∀ n, 0 ≤ normalizedKernelLag p n := by
  intro n
  cases n with
  | zero => simp [normalizedKernelLag]
  | succ n =>
      have hcurv : 0 < 1 - p.curvature := one_sub_curvature_pos_v2 p hb0 hw1
      simp [normalizedKernelLag]
      have heps : 0 < p.eps := by
        unfold Params.eps
        linarith
      positivity

/-- v2 `lem:L2`: the normalized lag kernel has total mass one. -/
theorem normalized_kernel_lag_hasSum_v2 (jury : External.JuryStability) (p : Params)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta)) :
    HasSum (normalizedKernelLag p) 1 := by
  have hcurv : 1 - p.curvature ≠ 0 := (one_sub_curvature_pos_v2 p hb0 hw1).ne'
  have hmass := p.renewal_kernel_hasSum hw0.ne' (by linarith : 1 - p.beta ≠ 0)
    (by linarith : 1 + p.beta ≠ 0) hcurv
    (External.mean_powers_tendsto_zero jury p hb1 hw0 hw1)
  have hscaled := hmass.mul_left (1 - p.curvature)
  have hshifted : HasSum (fun n => normalizedKernelLag p (n + 1)) 1 := by
    convert hscaled using 1
    · funext n
      simp only [normalizedKernelLag]
      ring
    · simp [hcurv]
  apply (hasSum_nat_add_iff' 1).1
  simpa only [Finset.sum_range_one, normalizedKernelLag, sub_zero] using hshifted

/-- v2 `lem:L2`: the renewal recurrence for the risk in normalized form. -/
theorem normalized_trajectory_recurrence_v2 (_jury : External.JuryStability)
    (p : Params) (s : Moments)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta))
    (k : ℕ) :
    (p.trajectory s k).R = freeRisk p s k +
      ∑ j ∈ Finset.range k,
        normalizedKernelLag p (k - j) *
          (p.renormNoise * (p.trajectory s j).R + p.renormAdditive) := by
  have hc : 0 < 1 - p.curvature := one_sub_curvature_pos_v2 p hb0 hw1
  have hrec := Params.trajectory_R_renewal p s k
  rw [hrec]
  unfold freeRisk
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j < k := Finset.mem_range.mp hj
  have hage : k - j = (k - j - 1) + 1 := by omega
  have hresp : k - 1 - j = k - j - 1 := by omega
  rw [hage]
  simp only [normalizedKernelLag]
  rw [hresp]
  unfold Params.renormNoise Params.renormAdditive
  field_simp [ne_of_gt hc]

/-- v2 `lem:L2`: partial kernel masses are at most one. -/
theorem normalized_kernel_partial_mass_le_one_v2 (jury : External.JuryStability)
    (p : Params) (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta)) (k : ℕ) :
    (∑ n ∈ Finset.range k, normalizedKernelLag p (k - n)) ≤ 1 := by
  have hnonneg := normalized_kernel_lag_nonneg_v2 jury p hb0 hb1 hw0 hw1
  have hsum := normalized_kernel_lag_hasSum_v2 jury p hb0 hb1 hw0 hw1
  have hreflect :
      (∑ n ∈ Finset.range k, normalizedKernelLag p (k - n)) =
        ∑ n ∈ Finset.range k, normalizedKernelLag p (n + 1) := by
    calc
      (∑ n ∈ Finset.range k, normalizedKernelLag p (k - n)) =
          ∑ n ∈ Finset.range k, normalizedKernelLag p ((k - 1 - n) + 1) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hnk : n < k := Finset.mem_range.mp hn
            congr 1
            omega
      _ = ∑ n ∈ Finset.range k, normalizedKernelLag p (n + 1) := by
            exact Finset.sum_range_reflect (fun n => normalizedKernelLag p (n + 1)) k
  have hzero : normalizedKernelLag p 0 = 0 := by simp [normalizedKernelLag]
  have hshift : (∑ n ∈ Finset.range k, normalizedKernelLag p (n + 1)) =
      ∑ n ∈ Finset.range (k + 1), normalizedKernelLag p n := by
    rw [Finset.sum_range_succ']
    simp [hzero]
  rw [hreflect, hshift]
  exact sum_le_hasSum (Finset.range (k + 1)) (fun n _ => hnonneg n) hsum

/-- Optional v2 `lem:L2` at `β = 0` without Jury: the mean powers decay when `0 < w < 2`
(the mean matrix then has rank one with nonzero eigenvalue `1 - w`). -/
theorem mean_powers_tendsto_zero_beta_zero (p : Params) (hb : p.beta = 0)
    (hw0 : 0 < p.w) (hw1 : p.w < 2) :
    Tendsto (fun n : ℕ => p.meanMatrix ^ n) atTop (𝓝 0) := by
  have hsq : p.meanMatrix * p.meanMatrix = (1 - p.w) • p.meanMatrix := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Params.meanMatrix, Matrix.mul_apply, Fin.sum_univ_two, hb] <;> ring
  have hpow : ∀ n : ℕ, p.meanMatrix ^ (n + 1) = (1 - p.w) ^ n • p.meanMatrix := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, smul_mul_assoc, hsq, smul_smul, pow_succ]
  have hr : |1 - p.w| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have hgeo : Tendsto (fun n : ℕ => (1 - p.w) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
  have h1 : Tendsto (fun n : ℕ => (1 - p.w) ^ n • p.meanMatrix) atTop
      (𝓝 ((0 : ℝ) • p.meanMatrix)) := hgeo.smul_const _
  rw [zero_smul] at h1
  rw [← tendsto_add_atTop_iff_nat 1]
  simpa only [hpow] using h1

/-! ### (G2) cor:stab (i)-(ii) -/

/-- v2 `cor:stab` (i): uniform bound on the risk below the renormalized threshold. -/
theorem trajectory_risk_uniform_bound_v2 (jury : External.JuryStability)
    (p : Params) (s : Moments) (A : ℝ)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta))
    (hnoise : 0 ≤ p.noise) (hadd : 0 ≤ p.additive)
    (hload : p.renormNoise < 1) (hA : 0 ≤ A)
    (hfree : ∀ k, freeRisk p s k ≤ A) :
    ∀ k, (p.trajectory s k).R ≤ (A + p.renormAdditive) / (1 - p.renormNoise) := by
  have hc : 0 < 1 - p.curvature := one_sub_curvature_pos_v2 p hb0 hw1
  have hu0 : 0 ≤ p.renormNoise := by
    unfold Params.renormNoise
    positivity
  have hphi : 0 ≤ p.renormAdditive := by
    unfold Params.renormAdditive
    positivity
  apply scalar_renewal_bound (normalizedKernelLag p)
    (fun k => freeRisk p s k) (fun k => (p.trajectory s k).R)
    p.renormNoise p.renormAdditive A
  · exact normalized_kernel_lag_nonneg_v2 jury p hb0 hb1 hw0 hw1
  · exact normalized_kernel_partial_mass_le_one_v2 jury p hb0 hb1 hw0 hw1
  · exact hu0
  · exact hload
  · exact hphi
  · exact hA
  · exact hfree
  · exact normalized_trajectory_recurrence_v2 jury p s hb0 hb1 hw0 hw1

/-- v2 `cor:stab` (i) / `cor:lift` (ii): the noise-generated excess over the free dynamics is
nonnegative and uniformly bounded. -/
theorem trajectory_risk_defect_bound_v2 (jury : External.JuryStability)
    (p : Params) (s : Moments) (A : ℝ) (hs : s.psd)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta))
    (hnoise : 0 ≤ p.noise) (hadd : 0 ≤ p.additive)
    (hload : p.renormNoise < 1) (hA : 0 ≤ A)
    (hfree : ∀ k, freeRisk p s k ≤ A) :
    ∀ k, 0 ≤ (p.trajectory s k).R - freeRisk p s k ∧
      (p.trajectory s k).R - freeRisk p s k ≤
        (p.renormNoise * A + p.renormAdditive) / (1 - p.renormNoise) := by
  have hc : 0 < 1 - p.curvature := one_sub_curvature_pos_v2 p hb0 hw1
  have hu0 : 0 ≤ p.renormNoise := by
    unfold Params.renormNoise
    positivity
  have hphi : 0 ≤ p.renormAdditive := by
    unfold Params.renormAdditive
    positivity
  have heps : 0 ≤ p.eps := by
    unfold Params.eps
    linarith
  have hnonneg := normalized_kernel_lag_nonneg_v2 jury p hb0 hb1 hw0 hw1
  have hmass := normalized_kernel_partial_mass_le_one_v2 jury p hb0 hb1 hw0 hw1
  have hR := trajectory_risk_uniform_bound_v2 jury p s A hb0 hb1 hw0 hw1
    hnoise hadd hload hA hfree
  let M : ℝ := (A + p.renormAdditive) / (1 - p.renormNoise)
  have hM : 0 ≤ M := by
    dsimp [M]
    have : 0 < 1 - p.renormNoise := by linarith
    positivity
  have hconstant : 0 ≤ p.renormNoise * M + p.renormAdditive := by positivity
  have hvalue : p.renormNoise * M + p.renormAdditive =
      (p.renormNoise * A + p.renormAdditive) / (1 - p.renormNoise) := by
    have hden : 1 - p.renormNoise ≠ 0 := by linarith
    dsimp [M]
    field_simp [hden]
    ring
  intro k
  have hdefect : (p.trajectory s k).R - freeRisk p s k =
      ∑ j ∈ Finset.range k, normalizedKernelLag p (k - j) *
        (p.renormNoise * (p.trajectory s j).R + p.renormAdditive) := by
    have hrec := normalized_trajectory_recurrence_v2 jury p s hb0 hb1 hw0 hw1 k
    linarith
  rw [hdefect]
  constructor
  · apply Finset.sum_nonneg
    intro j _
    have hjR : 0 ≤ (p.trajectory s j).R :=
      Moments.psd_R_nonneg (p.trajectory_psd s hs hw0.le heps hnoise hadd j)
    exact mul_nonneg (hnonneg (k - j)) (add_nonneg (mul_nonneg hu0 hjR) hphi)
  · calc
      (∑ j ∈ Finset.range k, normalizedKernelLag p (k - j) *
          (p.renormNoise * (p.trajectory s j).R + p.renormAdditive)) ≤
          ∑ j ∈ Finset.range k, normalizedKernelLag p (k - j) *
            (p.renormNoise * M + p.renormAdditive) := by
              apply Finset.sum_le_sum
              intro j _
              apply mul_le_mul_of_nonneg_left _ (hnonneg (k - j))
              exact add_le_add (mul_le_mul_of_nonneg_left (hR j) hu0) le_rfl
      _ = (p.renormNoise * M + p.renormAdditive) *
          (∑ j ∈ Finset.range k, normalizedKernelLag p (k - j)) := by
            rw [← Finset.sum_mul]
            ring
      _ ≤ (p.renormNoise * M + p.renormAdditive) * 1 :=
        mul_le_mul_of_nonneg_left (hmass k) hconstant
      _ = (p.renormNoise * A + p.renormAdditive) / (1 - p.renormNoise) := by
        simpa only [mul_one] using hvalue

/-- The free risk tends to zero for `0 ≤ β < 1` under Jury (v2 form of `freeRisk_tendsto_zero`,
which already carries no lower bound on `β`). -/
theorem freeRisk_tendsto_zero_v2 (jury : External.JuryStability) (p : Params) (s : Moments)
    (hb1 : p.beta < 1) (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta)) :
    Tendsto (freeRisk p s) atTop (𝓝 0) :=
  freeRisk_tendsto_zero jury p s hb1 hw0 hw1

/-- v2 `cor:lift` (ii), with the supremum justified by decay of the free mean dynamics. -/
theorem trajectory_risk_defect_sup_bound_v2 (jury : External.JuryStability)
    (p : Params) (s : Moments) (hs : s.psd)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta))
    (hnoise : 0 ≤ p.noise) (hadd : 0 ≤ p.additive)
    (hload : p.renormNoise < 1) :
    ∀ k, 0 ≤ (p.trajectory s k).R - freeRisk p s k ∧
      (p.trajectory s k).R - freeRisk p s k ≤
        (p.renormNoise * (⨆ j, freeRisk p s j) + p.renormAdditive) /
          (1 - p.renormNoise) := by
  have hbounded := (freeRisk_tendsto_zero jury p s hb1 hw0 hw1).bddAbove_range
  have hsup : ∀ k, freeRisk p s k ≤ ⨆ j, freeRisk p s j := fun k => le_ciSup hbounded k
  have hA : 0 ≤ ⨆ j, freeRisk p s j := le_trans (freeRisk_nonneg p s hs 0) (hsup 0)
  exact trajectory_risk_defect_bound_v2 jury p s _ hs hb0 hb1 hw0 hw1 hnoise hadd hload hA hsup

/-- v2 `cor:stab` (ii): strict gain at weight one persists for some exponential weight
`t > 1`.  Here `0 ≤ β` suffices: the scaled momentum `t² β` is again nonnegative, and at
`β = 0` it is identically zero. -/
theorem exists_weighted_kernel_gain_v2 (jury : External.JuryStability)
    (p : Params) (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta))
    (hload : p.renormNoise < 1) :
    ∃ t : ℝ, 1 < t ∧
      (scaledMeanParams p t).beta < 1 ∧
      0 < (scaledMeanParams p t).w ∧
      (scaledMeanParams p t).w < 2 * (1 + (scaledMeanParams p t).beta) ∧
      HasSum (fun n => normalizedKernelLag p n * (t ^ 2) ^ n) (weightedKernelMass p t) ∧
      p.renormNoise * weightedKernelMass p t < 1 := by
  have hc : 0 < 1 - p.curvature := one_sub_curvature_pos_v2 p hb0 hw1
  have hq1 : scaledMeanParams p 1 = p := by
    cases p
    simp [scaledMeanParams]
  have hm1 : weightedKernelMass p 1 = 1 := by
    unfold weightedKernelMass
    rw [hq1]
    unfold Params.eps
    field_simp [hw0.ne', hc.ne', ne_of_gt (by linarith : 0 < 1 - p.beta)]
  have hbcont : ContinuousAt (fun t : ℝ => (scaledMeanParams p t).beta) 1 := by
    unfold scaledMeanParams
    fun_prop
  have hwcont : ContinuousAt (fun t : ℝ => (scaledMeanParams p t).w) 1 := by
    unfold scaledMeanParams
    fun_prop
  have hccont : ContinuousAt (fun t : ℝ => (scaledMeanParams p t).curvature) 1 := by
    unfold Params.curvature
    apply hwcont.div
      (continuousAt_const.mul (continuousAt_const.add hbcont))
    simp [hq1]
    linarith
  have hmcont : ContinuousAt (weightedKernelMass p) 1 := by
    unfold weightedKernelMass
    apply ContinuousAt.div
    · fun_prop
    · exact ((continuousAt_const.mul hwcont).mul
        (continuousAt_const.sub hbcont)).mul (continuousAt_const.sub hccont)
    · simp only [hq1]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hw0.ne')
        (by linarith)) hc.ne'
  have hbNear : ∀ᶠ t : ℝ in 𝓝 1, (scaledMeanParams p t).beta < 1 :=
    hbcont.eventually_lt_const (by simpa [hq1] using hb1)
  have hwNear : ∀ᶠ t : ℝ in 𝓝 1, 0 < (scaledMeanParams p t).w :=
    hwcont.eventually_const_lt (by simpa [hq1] using hw0)
  have hwUpper : ∀ᶠ t : ℝ in 𝓝 1,
      (scaledMeanParams p t).w < 2 * (1 + (scaledMeanParams p t).beta) :=
    hwcont.eventually_lt (continuousAt_const.mul (continuousAt_const.add hbcont))
      (by simpa [hq1] using hw1)
  have hgain : ∀ᶠ t : ℝ in 𝓝 1, p.renormNoise * weightedKernelMass p t < 1 :=
    (continuousAt_const.mul hmcont).eventually_lt_const (by simpa [hm1] using hload)
  have hall := hbNear.and (hwNear.and (hwUpper.and hgain))
  obtain ⟨t, ht, hb, hw, hwupper, hgain⟩ := hall.exists_gt
  refine ⟨t, ht, hb, hw, hwupper, ?_, hgain⟩
  have hbnn : 0 ≤ (scaledMeanParams p t).beta := by
    simp only [scaledMeanParams]
    exact mul_nonneg (sq_nonneg t) hb0
  exact weighted_normalized_kernel_hasSum jury p t hb hw hwupper (by linarith)

/-- v2 `cor:stab` (ii): geometric convergence of the risk to the floor below the threshold. -/
theorem trajectory_risk_geometric_convergence_v2 (jury : External.JuryStability)
    (p : Params) (s : Moments)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta))
    (hnoise : 0 ≤ p.noise) (hadd : 0 ≤ p.additive)
    (hload : p.totalLoad < 1) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r < 1 ∧
      ∀ k, |(p.trajectory s k).R - p.additive / (1 - p.totalLoad)| ≤ C * r ^ k := by
  have hc : 0 < 1 - p.curvature := one_sub_curvature_pos_v2 p hb0 hw1
  have hu1 : p.renormNoise < 1 := (renormNoise_lt_one_iff p (by linarith)).2 hload
  have hu0 : 0 ≤ p.renormNoise := div_nonneg hnoise hc.le
  have hphi : 0 ≤ p.renormAdditive := div_nonneg hadd hc.le
  obtain ⟨t, ht, hb, hw, hwupper, hweight, hgain⟩ :=
    exists_weighted_kernel_gain_v2 jury p hb0 hb1 hw0 hw1 hu1
  obtain ⟨A, hA, hfree⟩ := weighted_freeRisk_bounded jury p s t (by linarith) hb hw hwupper
  let B := weightedKernelMass p t
  have hnonneg := normalized_kernel_lag_nonneg_v2 jury p hb0 hb1 hw0 hw1
  have hB : 0 ≤ B := by
    dsimp [B]
    rw [← hweight.tsum_eq]
    exact tsum_nonneg fun n => mul_nonneg (hnonneg _) (pow_nonneg (sq_nonneg _) _)
  have ht2 : 1 < t ^ 2 := by nlinarith
  have hbound := scalar_renewal_floor_geometric (normalizedKernelLag p) (freeRisk p s)
    (fun k => (p.trajectory s k).R) p.renormNoise p.renormAdditive (t ^ 2) A B
    hnonneg (by simp [normalizedKernelLag])
    (normalized_kernel_lag_hasSum_v2 jury p hb0 hb1 hw0 hw1)
    hu0 hu1 hphi ht2 hA hfree hweight hgain
    (normalized_trajectory_recurrence_v2 jury p s hb0 hb1 hw0 hw1)
  have hfloor := floor_identity p (by linarith) (ne_of_lt hload)
  rw [hfloor] at hbound
  refine ⟨(A + (p.additive / (1 - p.totalLoad)) * B) / (1 - p.renormNoise * B),
    (t ^ 2)⁻¹, ?_, inv_pos.2 (sq_pos_of_pos (by linarith)), ?_, hbound⟩
  · have hden : 0 < 1 - p.renormNoise * B := by dsimp [B]; linarith
    exact div_nonneg (add_nonneg hA (mul_nonneg (div_nonneg hadd (by linarith)) hB)) hden.le
  · exact (inv_lt_one₀ (sq_pos_of_pos (by linarith))).2 ht2

/-- v2 `cor:stab` (ii): the risk converges to the floor `additive / (1 - totalLoad)`. -/
theorem trajectory_risk_tendsto_floor_v2 (jury : External.JuryStability)
    (p : Params) (s : Moments)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta))
    (hnoise : 0 ≤ p.noise) (hadd : 0 ≤ p.additive)
    (hload : p.totalLoad < 1) :
    Tendsto (fun k => (p.trajectory s k).R) atTop
      (𝓝 (p.additive / (1 - p.totalLoad))) := by
  obtain ⟨C, r, hC, hr, hr1, hb⟩ :=
    trajectory_risk_geometric_convergence_v2 jury p s hb0 hb1 hw0 hw1 hnoise hadd hload
  have hlim : Tendsto (fun k : ℕ => C * r ^ k) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1)
  apply Metric.tendsto_atTop.2
  intro e he
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim e he
  refine ⟨N, fun k hk => ?_⟩
  have h := hN k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hC (pow_nonneg hr.le _))] at h
  rw [Real.dist_eq]
  exact (hb k).trans_lt h

/-- v2 `cor:stab` (ii): the actual normalized lag kernel has a geometric envelope below the
threshold. -/
theorem normalized_kernel_geometric_bound_v2 (jury : External.JuryStability)
    (p : Params) (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta))
    (hload : p.renormNoise < 1) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r < 1 ∧
      ∀ n, normalizedKernelLag p n ≤ C * r ^ n := by
  obtain ⟨t, ht, _, _, _, hsum, _⟩ :=
    exists_weighted_kernel_gain_v2 jury p hb0 hb1 hw0 hw1 hload
  have hh := normalized_kernel_lag_nonneg_v2 jury p hb0 hb1 hw0 hw1
  have hC : 0 ≤ weightedKernelMass p t := by
    rw [← hsum.tsum_eq]
    exact tsum_nonneg fun n => mul_nonneg (hh _) (pow_nonneg (sq_nonneg _) _)
  have ht2 : 1 < t ^ 2 := by nlinarith
  refine ⟨weightedKernelMass p t, (t ^ 2)⁻¹, hC,
    inv_pos.2 (by positivity), (inv_lt_one₀ (by positivity)).2 ht2, ?_⟩
  intro n
  have hterm : normalizedKernelLag p n * (t ^ 2) ^ n ≤ weightedKernelMass p t :=
    by
      have H := sum_le_hasSum {n}
        (fun m _ => mul_nonneg (hh m) (pow_nonneg (sq_nonneg t) m)) hsum
      simpa using H
  have hn : 0 < (t ^ 2) ^ n := pow_pos (by positivity) _
  have H := (le_div_iff₀ hn).2 hterm
  simpa [div_eq_mul_inv, inv_pow] using H

/-! ### (G3) cor:stab (iii) with the new hypothesis -/

/-- v2 `cor:stab` (iii): a PSD start with `s.R > 0`, or (for `β > 0`) any nonzero PSD start, is
visible in the free risk at time zero or one. -/
theorem freeRisk_pos_v2 (p : Params) (s : Moments) (hs : s.psd)
    (hpos : 0 < s.R ∨ (0 < p.beta ∧ s ≠ 0)) :
    0 < freeRisk p s 0 ∨ 0 < freeRisk p s 1 := by
  rcases hpos with hR | ⟨hb, hs0⟩
  · left
    simpa [freeRisk, Moments.cov] using hR
  · exact freeRisk_pos_zero_or_one p s hs hs0 hb.ne'

/-- v2 `cor:stab` (iii): above the exact renewal threshold the total risk is infinite when the
additive noise vanishes.  The hypothesis `s ≠ 0` of v1 is replaced by
`0 < s.R ∨ (0 < β ∧ s ≠ 0)` (needed at `β = 0`, see `beta_zero_dark_start`). -/
theorem trajectory_risk_not_summable_v2 (jury : External.JuryStability)
    (p : Params) (s : Moments) (hs : s.psd)
    (hpos : 0 < s.R ∨ (0 < p.beta ∧ s ≠ 0))
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta))
    (hnoise : 0 ≤ p.noise) (hadd : p.additive = 0)
    (hload : 1 ≤ p.renormNoise) :
    ¬ Summable (fun k => (p.trajectory s k).R) := by
  apply scalar_renewal_not_summable (normalizedKernelLag p) (freeRisk p s)
    (fun k => (p.trajectory s k).R) p.renormNoise
  · exact normalized_kernel_lag_nonneg_v2 jury p hb0 hb1 hw0 hw1
  · simp [normalizedKernelLag]
  · exact normalized_kernel_lag_hasSum_v2 jury p hb0 hb1 hw0 hw1
  · exact freeRisk_nonneg p s hs
  · intro k
    apply Moments.psd_R_nonneg
    apply p.trajectory_psd s hs hw0.le _ hnoise _ k
    · unfold Params.eps; linarith
    · rw [hadd]
  · exact hload
  · rcases freeRisk_pos_v2 p s hs hpos with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · intro k
    simpa [Params.renormAdditive, hadd] using
      normalized_trajectory_recurrence_v2 jury p s hb0 hb1 hw0 hw1 k

/-- v2 `cor:stab` (iii): nonsummability rules out geometric decay of the risk. -/
theorem trajectory_risk_not_geometrically_decaying_v2 (jury : External.JuryStability)
    (p : Params) (s : Moments) (hs : s.psd)
    (hpos : 0 < s.R ∨ (0 < p.beta ∧ s ≠ 0))
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta))
    (hnoise : 0 ≤ p.noise) (hadd : p.additive = 0)
    (hload : 1 ≤ p.renormNoise) :
    ¬ ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧
      ∀ k, (p.trajectory s k).R ≤ C * r ^ k := by
  rintro ⟨C, r, _, hr, hr1, hbound⟩
  apply trajectory_risk_not_summable_v2 jury p s hs hpos hb0 hb1 hw0 hw1 hnoise hadd hload
  have hsum := (summable_geometric_of_lt_one hr hr1).mul_left C
  apply hsum.of_nonneg_of_le _ hbound
  intro k
  apply Moments.psd_R_nonneg
  apply p.trajectory_psd s hs hw0.le _ hnoise _ k
  · unfold Params.eps; linarith
  · rw [hadd]

/-- v2 `cor:stab` (iii), necessity of the new hypothesis: at `β = 0` with zero additive noise,
a start with `R = C = 0` (a "dark" start `⟨0, V, 0⟩`) has identically zero risk, for any
noise level, so the risk is trivially summable even above the threshold. -/
theorem beta_zero_dark_start (p : Params) (V : ℝ) (hb : p.beta = 0) (hadd : p.additive = 0) :
    ∀ k, (p.trajectory ⟨0, V, 0⟩ k).R = 0 := by
  have key : ∀ k, (p.trajectory ⟨0, V, 0⟩ k).R = 0 ∧ (p.trajectory ⟨0, V, 0⟩ k).C = 0 := by
    intro k
    induction k with
    | zero => simp [Params.trajectory]
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [Params.trajectory, Params.step, Params.eps, h1, h2, hb, hadd]
      constructor <;> ring
  exact fun k => (key k).1

/-! ### (G4) cor:lift (i) at β = 0 -/

/-- v2 `cor:lift` (i) at every `β` including `β = 0`: a noise-free rank-one start has covariance
of rank at most one along the whole trajectory.  Rank exactly one for `β ≠ 0` and `x ≠ 0` is
`Params.noiseFree_rankOne_rank`. -/
theorem noiseFree_rankOne_rank_le_one (p : Params) (s : Moments) (x : Fin 2 → ℝ)
    (hx : s.cov = Matrix.vecMulVec x x)
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (k : ℕ) :
    (p.trajectory s k).cov.rank ≤ 1 := by
  rw [p.trajectory_cov_rankOne_noiseFree s hnoise hadd x hx k]
  exact Matrix.rank_vecMulVec_le _ _

end

end SparseSGD
