import SparseSGD.Scaling.Helps.StepMatrix
import SparseSGD.Scaling.Helps.ExactRate
import SparseSGD.Discrete.KernelMass
import SparseSGD.Discrete.Loads
import SparseSGD.External.Jury

/-!
# Stability of the per-step map for every `w > 0` (momentum-helps appendix)

Paper labels: `rem:stab-large-w` (radius form), `lem:helps-rate` (first clause: `u < 1`
gives `Lambda > 0`).

The `only if` direction of `rho(L) < 1 <-> u < 1` is `one_le_stepRadius_of_one_le_totalLoad`
(S7) of `StepMatrix.lean`.  The `if` direction is a series argument: the squared kick
response `x_n = kickResponse^2` has total mass `1/(2 w eps (1-u_c))` and satisfies the
order-three recurrence whose characteristic polynomial is the noise-free `stepCharPoly`
(it is the first coordinate of `T0^n (1,1,-1)`).  Summing it against `z^{-(n+1)}` gives the
generating function identity (St3)
`p0(z) * sum_n x_n z^{-(n+1)} = z (z + beta)`  for `|z| >= 1`.
A root `z`, `|z| >= 1`, of the noisy polynomial then satisfies `1 = kappa * sum_n x_n z^{-(n+1)}`
with `kappa = 2 w eps u_n`, so `1 <= kappa * sum_n x_n = renormNoise`, contradicting
`renormNoise < 1`.  No Jury criterion beyond the 2x2 hypothesis `External.JuryStability` is used.

Hypotheses added to the tex statement: none for `0 <= beta < 1`; the series route also covers
`beta = 0` and does not need `1/2 <= beta`.
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD Filter
open scoped Topology

noncomputable section

/-! ### The cubic recurrence of the squared kick response -/

/-- (St3) The squared kick response `x_n = kickResponse^2` satisfies the order-three
recurrence with characteristic polynomial `stepCharPoly beta w 0` (`rem:stab-large-w`). -/
theorem kickSq_recurrence (p : Params) (n : ℕ) :
    kickResponse p (n + 3) ^ 2 + stepC2 p.beta p.w 0 * kickResponse p (n + 2) ^ 2
      + stepC1 p.beta p.w 0 * kickResponse p (n + 1) ^ 2
      + stepC0 p.beta * kickResponse p n ^ 2 = 0 := by
  have h3 : kickResponse p (n + 3) =
      (1 + p.beta - p.w) * kickResponse p (n + 2) - p.beta * kickResponse p (n + 1) :=
    kickResponse_recurrence p (n + 1)
  have h2 : kickResponse p (n + 2) =
      (1 + p.beta - p.w) * kickResponse p (n + 1) - p.beta * kickResponse p n :=
    kickResponse_recurrence p n
  rw [h3, h2]
  simp only [stepC2, stepC1, stepC0]
  ring

/-- Complex-valued squared kick response. -/
def kickSqC (p : Params) (n : ℕ) : ℂ := ((kickResponse p n : ℝ) : ℂ) ^ 2

theorem kickSqC_recurrence (p : Params) (n : ℕ) :
    kickSqC p (n + 3) + (stepC2 p.beta p.w 0 : ℂ) * kickSqC p (n + 2)
      + (stepC1 p.beta p.w 0 : ℂ) * kickSqC p (n + 1)
      + (stepC0 p.beta : ℂ) * kickSqC p n = 0 := by
  have h := congrArg (fun r : ℝ => (r : ℂ)) (kickSq_recurrence p n)
  simpa [kickSqC] using h

/-- The boundary term of the partial-sum identity. -/
def kickTail (p : Params) (z : ℂ) (N : ℕ) : ℂ :=
  kickSqC p N * z ^ 2 + (kickSqC p (N + 1) + (stepC2 p.beta p.w 0 : ℂ) * kickSqC p N) * z
    + (kickSqC p (N + 2) + (stepC2 p.beta p.w 0 : ℂ) * kickSqC p (N + 1)
        + (stepC1 p.beta p.w 0 : ℂ) * kickSqC p N)

/-- Partial-sum identity (St3): for `z != 0`,
`p0(z) * sum_{n<N} x_n z^{-(n+1)} = z^2 + beta z - z^{-N} * tail_N`. -/
theorem kickSq_partial_sum (p : Params) (z : ℂ) (hz : z ≠ 0) (N : ℕ) :
    stepCharPoly p.beta p.w 0 z *
        (∑ n ∈ Finset.range N, kickSqC p n * (z ^ (n + 1))⁻¹) =
      z ^ 2 + (p.beta : ℂ) * z - (z ^ N)⁻¹ * kickTail p z N := by
  induction N with
  | zero =>
    have h0 : kickResponse p 0 = -1 := kickResponse_zero p
    have h1 : kickResponse p 1 = -(1 + p.beta - p.w) := kickResponse_one p
    have h2 : kickResponse p 2 = (1 + p.beta - p.w) * kickResponse p 1
        - p.beta * kickResponse p 0 := kickResponse_recurrence p 0
    simp only [kickTail, kickSqC, Finset.range_zero, Finset.sum_empty, mul_zero, pow_zero,
      inv_one, one_mul, zero_add]
    rw [show kickResponse p 2 = _ from h2, h1, h0]
    simp only [stepC2, stepC1]
    push_cast
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hrec := kickSqC_recurrence p N
    rw [stepCharPoly_expand]
    have hzi : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
    have hpow : (z ^ (N + 1))⁻¹ = (z ^ N)⁻¹ * z⁻¹ := by
      rw [pow_succ, mul_inv]
    rw [hpow]
    simp only [kickTail] at ih ⊢
    field_simp
    rw [show N + 1 + 2 = N + 3 from rfl]
    linear_combination hrec


/-! ### The generating function of the squared kick response -/

theorem curvature_lt_one_of_lt_ceiling (p : Params) (hb : 0 ≤ p.beta)
    (hceil : p.w < 2 * (1 + p.beta)) : p.curvature < 1 := by
  unfold Params.curvature
  rw [div_lt_one (by linarith)]
  exact hceil

/-- Total mass of the squared kick response on the stable range (`rem:stab-large-w`, via
`Discrete.KernelMass.kickResponse_sq_hasSum`). -/
theorem kickSq_hasSum_of_stable (jury : External.JuryStability) (p : Params)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hw : 0 < p.w)
    (hceil : p.w < 2 * (1 + p.beta)) :
    HasSum (fun n => kickResponse p n ^ 2)
      (1 / (2 * p.w * (1 - p.beta) * (1 - p.curvature))) := by
  have hc := curvature_lt_one_of_lt_ceiling p hb0 hceil
  exact kickResponse_sq_hasSum p hw.ne' (sub_pos.2 hb1).ne' (by linarith : 0 < 1 + p.beta).ne'
    (sub_pos.2 hc).ne' (External.mean_powers_tendsto_zero jury p hb1 hw hceil)

theorem norm_kickSqC (p : Params) (n : ℕ) : ‖kickSqC p n‖ = kickResponse p n ^ 2 := by
  simp [kickSqC, norm_pow, sq_abs]

theorem norm_inv_pow_le_one {z : ℂ} (hz : 1 ≤ ‖z‖) (n : ℕ) : ‖(z ^ n)⁻¹‖ ≤ 1 := by
  rw [norm_inv, norm_pow]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hz)

/-- (St3) For `|z| >= 1` the series `sum_n x_n z^{-(n+1)}` converges, and its sum `S`
satisfies `p0(z) * S = z (z + beta)` (`rem:stab-large-w`). -/
theorem kickSq_hasSum_mul (jury : External.JuryStability) (p : Params)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hw : 0 < p.w)
    (hceil : p.w < 2 * (1 + p.beta)) (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ∃ S : ℂ, HasSum (fun n => kickSqC p n * (z ^ (n + 1))⁻¹) S ∧
      stepCharPoly p.beta p.w 0 z * S = z * (z + p.beta) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz; linarith
  have hx := kickSq_hasSum_of_stable jury p hb0 hb1 hw hceil
  have hsumm : Summable (fun n => kickSqC p n * (z ^ (n + 1))⁻¹) := by
    refine Summable.of_norm_bounded hx.summable (fun n => ?_)
    rw [norm_mul, norm_kickSqC]
    calc kickResponse p n ^ 2 * ‖(z ^ (n + 1))⁻¹‖ ≤ kickResponse p n ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (norm_inv_pow_le_one hz _) (sq_nonneg _)
      _ = kickResponse p n ^ 2 := mul_one _
  refine ⟨_, hsumm.hasSum, ?_⟩
  set S := ∑' n, kickSqC p n * (z ^ (n + 1))⁻¹ with hS
  have h1 : Tendsto (fun N => stepCharPoly p.beta p.w 0 z *
      ∑ n ∈ Finset.range N, kickSqC p n * (z ^ (n + 1))⁻¹) atTop
      (𝓝 (stepCharPoly p.beta p.w 0 z * S)) :=
    hsumm.hasSum.tendsto_sum_nat.const_mul _
  -- the boundary term tends to zero
  have hx0 : Tendsto (fun n => kickResponse p n ^ 2) atTop (𝓝 0) := hx.summable.tendsto_atTop_zero
  have hC0 : Tendsto (fun n => kickSqC p n) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp hx0
    simpa [Function.comp_def, kickSqC] using this
  have hC1 : Tendsto (fun n => kickSqC p (n + 1)) atTop (𝓝 0) :=
    hC0.comp (tendsto_add_atTop_nat 1)
  have hC2 : Tendsto (fun n => kickSqC p (n + 2)) atTop (𝓝 0) :=
    hC0.comp (tendsto_add_atTop_nat 2)
  have hT : Tendsto (fun N => kickTail p z N) atTop (𝓝 0) := by
    have := ((hC0.mul_const (z ^ 2)).add
      (((hC1.add (hC0.const_mul (stepC2 p.beta p.w 0 : ℂ))).mul_const z))).add
      ((hC2.add (hC1.const_mul (stepC2 p.beta p.w 0 : ℂ))).add
        (hC0.const_mul (stepC1 p.beta p.w 0 : ℂ)))
    simpa [kickTail] using this
  have hE : Tendsto (fun N => (z ^ N)⁻¹ * kickTail p z N) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) (tendsto_zero_iff_norm_tendsto_zero.1 hT)
    rw [norm_mul]
    calc ‖(z ^ N)⁻¹‖ * ‖kickTail p z N‖ ≤ 1 * ‖kickTail p z N‖ :=
          mul_le_mul_of_nonneg_right (norm_inv_pow_le_one hz N) (norm_nonneg _)
      _ = ‖kickTail p z N‖ := one_mul _
  have h2 : Tendsto (fun N => stepCharPoly p.beta p.w 0 z *
      ∑ n ∈ Finset.range N, kickSqC p n * (z ^ (n + 1))⁻¹) atTop
      (𝓝 (z ^ 2 + (p.beta : ℂ) * z - 0)) := by
    have := (tendsto_const_nhds (x := z ^ 2 + (p.beta : ℂ) * z)).sub hE
    simpa only [kickSq_partial_sum p z hz0] using this
  have := tendsto_nhds_unique h1 h2
  rw [this]; ring

/-- (St3) `p0(z) != 0` for `|z| >= 1` on the stable range. -/
theorem kickSq_charPoly_ne_zero (jury : External.JuryStability) (p : Params)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hw : 0 < p.w)
    (hceil : p.w < 2 * (1 + p.beta)) (z : ℂ) (hz : 1 ≤ ‖z‖) :
    stepCharPoly p.beta p.w 0 z ≠ 0 := by
  obtain ⟨S, _, hS⟩ := kickSq_hasSum_mul jury p hb0 hb1 hw hceil z hz
  intro h0
  rw [h0, zero_mul] at hS
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz; linarith
  have hzb : z + (p.beta : ℂ) ≠ 0 := by
    intro h
    have : z = -(p.beta : ℂ) := by linear_combination h
    rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0] at hz
    linarith
  exact mul_ne_zero hz0 hzb hS.symm

/-- (St3) Generating-function identity for the squared kick response: for `|z| >= 1`,
`0 <= beta < 1` and `0 < w < 2 (1 + beta)`,
`sum_n (kickResponse^2)_n z^{-(n+1)} = z (z + beta) / p0(z)` with `p0 = stepCharPoly beta w 0`
(the noise-free characteristic polynomial; `kickResponse` does not depend on the noise
parameters, so this covers the noise-free parameters `q`).  Added hypothesis relative to the
spec: none (`beta = 0` is included; `beta > 0` is not needed). -/
theorem kickSq_generating_function (jury : External.JuryStability) (p : Params)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hw : 0 < p.w)
    (hceil : p.w < 2 * (1 + p.beta)) (z : ℂ) (hz : 1 ≤ ‖z‖) :
    HasSum (fun n => kickSqC p n * (z ^ (n + 1))⁻¹)
      (z * (z + p.beta) / stepCharPoly p.beta p.w 0 z) := by
  obtain ⟨S, hS, hid⟩ := kickSq_hasSum_mul jury p hb0 hb1 hw hceil z hz
  have hne := kickSq_charPoly_ne_zero jury p hb0 hb1 hw hceil z hz
  have : S = z * (z + p.beta) / stepCharPoly p.beta p.w 0 z := by
    rw [eq_div_iff hne, mul_comm]; exact hid
  rwa [this] at hS

/-! ### Stability -/

theorem stepCharPoly_noise_split (beta w un : ℝ) (z : ℂ) :
    stepCharPoly beta w un z =
      stepCharPoly beta w 0 z - ((2 * w * (1 - beta) * un : ℝ) : ℂ) * (z * (z + beta)) := by
  simp only [stepCharPoly]; push_cast; ring

/-- (St1, `if` direction) `rem:stab-large-w`: `u < 1` gives `rho(L) < 1`, for `0 <= beta < 1`,
`w > 0`, `u_n >= 0`. -/
theorem stepRadius_lt_one_of_totalLoad_lt_one (jury : External.JuryStability) (p : Params)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hw : 0 < p.w) (hun : 0 ≤ p.noise)
    (hu : p.totalLoad < 1) : stepRadius p < 1 := by
  have hcurv : p.curvature < 1 := by
    have : 0 ≤ p.noise := hun
    unfold Params.totalLoad at hu; linarith
  have hceil : p.w < 2 * (1 + p.beta) := by
    unfold Params.curvature at hcurv
    rw [div_lt_one (by linarith)] at hcurv
    exact hcurv
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hzroot, hzn⟩ := stepRadius_attained p
  have hz : 1 ≤ ‖z‖ := by rw [hzn]; exact hcon
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz; linarith
  have hzb : z + (p.beta : ℂ) ≠ 0 := by
    intro h
    have : z = -(p.beta : ℂ) := by linear_combination h
    rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0] at hz
    linarith
  obtain ⟨S, hS, hid⟩ := kickSq_hasSum_mul jury p hb0 hb1 hw hceil z hz
  have hroot : stepCharPoly p.beta p.w p.noise z = 0 := hzroot
  rw [stepCharPoly_noise_split] at hroot
  set κ : ℝ := 2 * p.w * (1 - p.beta) * p.noise with hκ
  have hp0 : stepCharPoly p.beta p.w 0 z = (κ : ℂ) * (z * (z + p.beta)) := sub_eq_zero.1 hroot
  rw [hp0] at hid
  have hzz : z * (z + (p.beta : ℂ)) ≠ 0 := mul_ne_zero hz0 hzb
  have hκS : (κ : ℂ) * S = 1 := by
    apply mul_left_cancel₀ hzz
    linear_combination hid
  -- bound the norm of S by the kernel mass
  have hx := kickSq_hasSum_of_stable jury p hb0 hb1 hw hceil
  have hSn : ‖S‖ ≤ 1 / (2 * p.w * (1 - p.beta) * (1 - p.curvature)) := by
    refine hS.norm_le_of_bounded hx (fun n => ?_)
    rw [norm_mul, norm_kickSqC]
    calc kickResponse p n ^ 2 * ‖(z ^ (n + 1))⁻¹‖ ≤ kickResponse p n ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (norm_inv_pow_le_one hz _) (sq_nonneg _)
      _ = kickResponse p n ^ 2 := mul_one _
  have hκ0 : 0 ≤ κ := by
    have : 0 ≤ 1 - p.beta := by linarith
    rw [hκ]; positivity
  have h1 : 1 ≤ κ * (1 / (2 * p.w * (1 - p.beta) * (1 - p.curvature))) := by
    have := congrArg norm hκS
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ0, norm_one] at this
    exact this.symm.le.trans (mul_le_mul_of_nonneg_left hSn hκ0)
  have h2 : κ * (1 / (2 * p.w * (1 - p.beta) * (1 - p.curvature))) = p.renormNoise := by
    have h3 : 1 - p.curvature ≠ 0 := (sub_pos.2 hcurv).ne'
    have h4 : 1 - p.beta ≠ 0 := (sub_pos.2 hb1).ne'
    rw [hκ]
    unfold Params.renormNoise
    field_simp [hw.ne']
  have h5 := (renormNoise_lt_one_iff p hcurv).2 hu
  linarith

/-- (St1) `rem:stab-large-w` (radius form): for `0 <= beta < 1`, `w > 0`, `u_n >= 0`,
`rho(L) < 1` if and only if `u < 1`.  The `only if` direction is (S7); the `if` direction
is the series argument above.  Requires `External.JuryStability` (2x2) and no
`1/2 <= beta`. -/
theorem stepRadius_lt_one_iff (jury : External.JuryStability) (p : Params)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hw : 0 < p.w) (hun : 0 ≤ p.noise) :
    stepRadius p < 1 ↔ p.totalLoad < 1 := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have := one_le_stepRadius_of_one_le_totalLoad p hw hb1 (by linarith) hcon
    linarith
  · exact stepRadius_lt_one_of_totalLoad_lt_one jury p hb0 hb1 hw hun

/-- (St1') `lem:stab-all` (first clause; old label `rem:stab-large-w`): if `w >= 2(1+beta)`
then `1 <= H_c <= H` and `rho(L) >= 1`, i.e. `L` is not exponentially stable
(`stepRadius p` is the spectral radius of `L`).  Hypotheses `0 <= beta < 1`, `u_n >= 0`. -/
theorem lem_stab_all_large_w (p : Params) (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1)
    (hun : 0 ≤ p.noise) (hw : 2 * (1 + p.beta) ≤ p.w) :
    1 ≤ p.curvature ∧ p.curvature ≤ p.totalLoad ∧ 1 ≤ p.totalLoad ∧ 1 ≤ stepRadius p := by
  have hpos : 0 < 2 * (1 + p.beta) := by linarith
  have hc : 1 ≤ p.curvature := by
    unfold Params.curvature
    rw [le_div_iff₀ hpos]; linarith
  have hct : p.curvature ≤ p.totalLoad := by
    unfold Params.totalLoad; linarith
  have hH : 1 ≤ p.totalLoad := hc.trans hct
  exact ⟨hc, hct, hH,
    one_le_stepRadius_of_one_le_totalLoad p (by linarith) hb1 (by linarith) hH⟩

/-- (St1'') `lem:stab-all` (old label `rem:stab-large-w`): for every `w > 0`, `0 <= beta < 1`,
`u_n >= 0`, `L` is exponentially stable (`rho(L) < 1`) if and only if `H < 1`; for
`w >= 2(1+beta)` the right side fails and so does the left (`lem_stab_all_large_w`). -/
theorem lem_stab_all (jury : External.JuryStability) (p : Params)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hw : 0 < p.w) (hun : 0 ≤ p.noise) :
    (2 * (1 + p.beta) ≤ p.w →
      1 ≤ p.curvature ∧ p.curvature ≤ p.totalLoad ∧ 1 ≤ p.totalLoad ∧ 1 ≤ stepRadius p) ∧
    (stepRadius p < 1 ↔ p.totalLoad < 1) :=
  ⟨lem_stab_all_large_w p hb0 hb1 hun, stepRadius_lt_one_iff jury p hb0 hb1 hw hun⟩

/-- (St2) `lem:helps-rate` (first clause): if the radius is positive, then
`0 < Lambda` if and only if `u < 1`. -/
theorem perStepRate_pos_iff (jury : External.JuryStability) (p : Params)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hw : 0 < p.w) (hun : 0 ≤ p.noise)
    (hrad : 0 < stepRadius p) : 0 < perStepRate p ↔ p.totalLoad < 1 := by
  rw [← stepRadius_lt_one_iff jury p hb0 hb1 hw hun, perStepRate, neg_pos]
  exact Real.log_neg_iff hrad

/-- (St2) For `0 < beta < 1` the radius positivity hypothesis is automatic, by
`beta <= stepRadius` (E1, `rem:retention-cap` (a)). -/
theorem perStepRate_pos_iff_of_beta_pos (jury : External.JuryStability) (p : Params)
    (hb0 : 0 < p.beta) (hb1 : p.beta < 1) (hw : 0 < p.w) (hun : 0 ≤ p.noise) :
    0 < perStepRate p ↔ p.totalLoad < 1 :=
  perStepRate_pos_iff jury p hb0.le hb1 hw hun
    (lt_of_lt_of_le hb0 (beta_le_stepRadius p hb0.le hb1.le hw.le hun))

end

end SparseSGD.Scaling.Helps
