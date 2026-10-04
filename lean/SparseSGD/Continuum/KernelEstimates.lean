import SparseSGD.Continuum.Renewal

open scoped Matrix.Norms.Operator Topology
open Filter Set

namespace SparseSGD

noncomputable section

/-- Second coordinate of the oscillator impulse response. -/
def continuumImpulseVelocity (delta t : ℝ) : ℝ := continuumMeanFlow delta t 1 1

private theorem continuumMeanFlow_entry_hasDerivAt (delta t : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => continuumMeanFlow delta t i j)
      ((continuumMeanGenerator delta * continuumMeanFlow delta t) i j) t := by
  let L : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ :=
    (LinearMap.proj j : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).comp
      (LinearMap.proj i : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
  exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' (continuumMeanGenerator delta) t)

theorem continuumImpulseResponse_hasDerivAt (delta t : ℝ) :
    HasDerivAt (continuumImpulseResponse delta)
      (-delta * continuumImpulseVelocity delta t) t := by
  change HasDerivAt (fun t => continuumMeanFlow delta t 0 1)
    (-delta * continuumImpulseVelocity delta t) t
  simpa [continuumImpulseResponse, continuumImpulseVelocity, continuumMeanGenerator,
    Matrix.mul_apply, Fin.sum_univ_two] using continuumMeanFlow_entry_hasDerivAt delta t 0 1

theorem continuumImpulseVelocity_hasDerivAt (delta t : ℝ) :
    HasDerivAt (continuumImpulseVelocity delta)
      (continuumImpulseResponse delta t - continuumImpulseVelocity delta t) t := by
  change HasDerivAt (fun t => continuumMeanFlow delta t 1 1)
    (continuumImpulseResponse delta t - continuumImpulseVelocity delta t) t
  simpa [continuumImpulseResponse, continuumImpulseVelocity, continuumMeanGenerator,
    Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg] using
      continuumMeanFlow_entry_hasDerivAt delta t 1 1

theorem continuumImpulseResponse_continuous (delta : ℝ) :
    Continuous (continuumImpulseResponse delta) :=
  continuous_iff_continuousAt.mpr (fun t => (continuumImpulseResponse_hasDerivAt delta t).continuousAt)

theorem continuumImpulseVelocity_continuous (delta : ℝ) :
    Continuous (continuumImpulseVelocity delta) :=
  continuous_iff_continuousAt.mpr (fun t => (continuumImpulseVelocity_hasDerivAt delta t).continuousAt)

theorem continuumRenewalKernel_continuous (delta : ℝ) : Continuous (continuumRenewalKernel delta) :=
  continuous_const.mul ((continuumImpulseResponse_continuous delta).pow 2)

/-- A Lyapunov primitive for the scalar renewal kernel. -/
def continuumKernelTail (delta t : ℝ) : ℝ :=
  (continuumImpulseResponse delta t / delta - continuumImpulseVelocity delta t) ^ 2 +
    continuumImpulseResponse delta t ^ 2 / delta

/-- A coercive oscillator energy with dissipation in both coordinates. -/
def continuumImpulseEnergy (delta t : ℝ) : ℝ :=
  continuumKernelTail delta t + continuumImpulseResponse delta t ^ 2 / delta +
    continuumImpulseVelocity delta t ^ 2

theorem continuumKernelTail_hasDerivAt {delta : ℝ} (hd : delta ≠ 0) (t : ℝ) :
    HasDerivAt (continuumKernelTail delta) (-continuumRenewalKernel delta t) t := by
  have hx := continuumImpulseResponse_hasDerivAt delta t
  have hy := continuumImpulseVelocity_hasDerivAt delta t
  convert (((hx.div_const delta).sub hy).pow 2).add ((hx.pow 2).div_const delta) using 1
  · rfl
  · dsimp [continuumRenewalKernel]
    field_simp
    ring

theorem continuumImpulseEnergy_hasDerivAt {delta : ℝ} (hd : delta ≠ 0) (t : ℝ) :
    HasDerivAt (continuumImpulseEnergy delta)
      (-(2 / delta * continuumImpulseResponse delta t ^ 2 +
        2 * continuumImpulseVelocity delta t ^ 2)) t := by
  have hx := continuumImpulseResponse_hasDerivAt delta t
  have hy := continuumImpulseVelocity_hasDerivAt delta t
  convert ((continuumKernelTail_hasDerivAt hd t).add ((hx.pow 2).div_const delta)).add
    (hy.pow 2) using 1
  · rfl
  · dsimp [continuumRenewalKernel]
    field_simp
    ring

theorem continuumKernelTail_initial (delta : ℝ) : continuumKernelTail delta 0 = 1 := by
  simp [continuumKernelTail, continuumImpulseResponse, continuumImpulseVelocity, continuumMeanFlow_zero]

theorem continuumKernelTail_nonneg {delta : ℝ} (hd : 0 < delta) (t : ℝ) :
    0 ≤ continuumKernelTail delta t := by
  unfold continuumKernelTail
  positivity

private theorem impulse_energy_bounds {delta : ℝ} (hd : 0 < delta) (t : ℝ) :
    0 ≤ continuumKernelTail delta t ∧
    continuumKernelTail delta t ≤ continuumImpulseEnergy delta t ∧
    continuumImpulseEnergy delta t ≤
      (2 / delta + 2 / delta ^ 2 + 3) *
        (continuumImpulseResponse delta t ^ 2 + continuumImpulseVelocity delta t ^ 2) := by
  let x := continuumImpulseResponse delta t
  let y := continuumImpulseVelocity delta t
  have hx := sq_nonneg x
  have hy := sq_nonneg y
  have hxy := sq_nonneg (x / delta + y)
  have hdx : 0 ≤ x ^ 2 / delta := div_nonneg hx hd.le
  have hd2 : 0 < delta ^ 2 := sq_pos_of_pos hd
  have hcoef : 0 ≤ 2 / delta + 2 / delta ^ 2 := by positivity
  refine ⟨continuumKernelTail_nonneg hd t, ?_, ?_⟩
  · dsimp [continuumImpulseEnergy]
    linarith
  · change (x / delta - y) ^ 2 + x ^ 2 / delta + x ^ 2 / delta + y ^ 2 ≤
      (2 / delta + 2 / delta ^ 2 + 3) * (x ^ 2 + y ^ 2)
    have hcross : (x / delta - y) ^ 2 ≤ 2 * x ^ 2 / delta ^ 2 + 2 * y ^ 2 := by
      field_simp at *
      nlinarith
    have hxextra : 0 ≤ 3 * x ^ 2 := by positivity
    have hyextra : 0 ≤ (2 / delta + 2 / delta ^ 2) * y ^ 2 := mul_nonneg hcoef hy
    simp only [div_eq_mul_inv] at hcross hyextra ⊢
    nlinarith

/-- Exponential comparison for a scalar dissipative energy. -/
private theorem scalar_energy_exp_bound {W : ℝ → ℝ} {lambda : ℝ}
    (hW : ∀ t, 0 ≤ t → ∃ W', HasDerivAt W W' t ∧ W' ≤ -lambda * W t)
    {t : ℝ} (ht : 0 ≤ t) : W t ≤ W 0 * Real.exp (-lambda * t) := by
  have hd (x : ℝ) (hx : 0 ≤ x) :
      ∃ d, HasDerivAt (fun x => Real.exp (lambda * x) * W x) d x ∧ d ≤ 0 := by
    obtain ⟨d, hd, hb⟩ := hW x hx
    refine ⟨lambda * Real.exp (lambda * x) * W x + Real.exp (lambda * x) * d, ?_, ?_⟩
    · convert! (((hasDerivAt_id x).const_mul lambda).exp).mul hd using 1 <;> (simp only [id_eq]; ring)
    · have := mul_le_mul_of_nonneg_left hb (Real.exp_pos (lambda * x)).le
      nlinarith
  have hanti : AntitoneOn (fun x => Real.exp (lambda * x) * W x) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro x hx
      obtain ⟨d, hd, _⟩ := hd x hx
      exact hd.continuousAt.continuousWithinAt
    · intro x hx
      obtain ⟨d, hd, _⟩ := hd x (interior_subset hx)
      exact hd.differentiableAt.differentiableWithinAt
    · intro x hx
      obtain ⟨d, hd, hb⟩ := hd x (interior_subset hx)
      rwa [hd.deriv]
  have hb := hanti (by simp) ht ht
  simp only [mul_zero, Real.exp_zero, one_mul] at hb
  have he : Real.exp (lambda * t) * Real.exp (-lambda * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hh := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-lambda * t)).le
  calc
    W t = (Real.exp (lambda * t) * W t) * Real.exp (-lambda * t) := by
      calc
        W t = W t * (Real.exp (lambda * t) * Real.exp (-lambda * t)) := by rw [he, mul_one]
        _ = (Real.exp (lambda * t) * W t) * Real.exp (-lambda * t) := by ring
    _ ≤ W 0 * Real.exp (-lambda * t) := hh

/-- The free impulse Lyapunov energy decays exponentially. -/
theorem continuumImpulseEnergy_exp_bound {delta : ℝ} (hd : 0 < delta)
    {t : ℝ} (ht : 0 ≤ t) :
    continuumImpulseEnergy delta t ≤ continuumImpulseEnergy delta 0 *
      Real.exp (-(1 / ((delta + 1) * (2 / delta + 2 / delta ^ 2 + 3))) * t) := by
  let C := 2 / delta + 2 / delta ^ 2 + 3
  let lambda := 1 / ((delta + 1) * C)
  have hC : 0 < C := by dsimp [C]; positivity
  have hl : 0 < lambda := by dsimp [lambda]; positivity
  have hlC : lambda * C = 1 / (delta + 1) := by
    dsimp [lambda]
    field_simp
  apply scalar_energy_exp_bound (lambda := lambda) ?_ ht
  intro x hx
  refine ⟨_, continuumImpulseEnergy_hasDerivAt hd.ne' x, ?_⟩
  have hb := (impulse_energy_bounds hd x).2.2
  change continuumImpulseEnergy delta x ≤ C *
    (continuumImpulseResponse delta x ^ 2 + continuumImpulseVelocity delta x ^ 2) at hb
  have hscaled := mul_le_mul_of_nonneg_left hb hl.le
  rw [← mul_assoc, hlC] at hscaled
  have h1 : 1 / (delta + 1) ≤ 2 / delta := by
    apply (div_le_div_iff₀ (by linarith) hd).mpr
    nlinarith
  have h2 : 1 / (delta + 1) ≤ 2 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  have ha := mul_le_mul_of_nonneg_right h1 (sq_nonneg (continuumImpulseResponse delta x))
  have hb := mul_le_mul_of_nonneg_right h2 (sq_nonneg (continuumImpulseVelocity delta x))
  nlinarith

/-- The kernel primitive vanishes at infinite time. -/
theorem continuumKernelTail_tendsto_zero {delta : ℝ} (hd : 0 < delta) :
    Tendsto (continuumKernelTail delta) atTop (𝓝 0) := by
  let lambda := 1 / ((delta + 1) * (2 / delta + 2 / delta ^ 2 + 3))
  have hl : 0 < lambda := by dsimp [lambda]; positivity
  have he : Tendsto (fun t : ℝ => Real.exp (-lambda * t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hl)
  have hbound : Tendsto (fun t : ℝ => continuumImpulseEnergy delta 0 *
      Real.exp (-lambda * t)) atTop (𝓝 0) := by
    simpa using he.const_mul (continuumImpulseEnergy delta 0)
  apply squeeze_zero' (Filter.Eventually.of_forall (continuumKernelTail_nonneg hd)) ?_ hbound
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (impulse_energy_bounds hd t).2.1.trans (continuumImpulseEnergy_exp_bound hd ht)

/-- The continuum renewal kernel is integrable on the positive half-line. -/
theorem continuumRenewalKernel_integrableOn {delta : ℝ} (hd : 0 < delta) :
    MeasureTheory.IntegrableOn (continuumRenewalKernel delta) (Ioi 0) := by
  have h := MeasureTheory.integrableOn_Ioi_deriv_of_nonpos' (a := (0 : ℝ))
    (fun t _ => continuumKernelTail_hasDerivAt hd.ne' t)
    (fun t _ => neg_nonpos.mpr (continuumRenewalKernel_nonneg hd t))
    (continuumKernelTail_tendsto_zero hd)
  convert h.neg using 1
  ext t
  simp

/-- The actual continuum renewal kernel has total mass exactly one. -/
theorem continuumRenewalKernel_mass {delta : ℝ} (hd : 0 < delta) :
    (∫ t in Ioi (0 : ℝ), continuumRenewalKernel delta t) = 1 := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos' (a := (0 : ℝ))
    (fun t _ => continuumKernelTail_hasDerivAt hd.ne' t)
    (fun t _ => neg_nonpos.mpr (continuumRenewalKernel_nonneg hd t))
    (continuumKernelTail_tendsto_zero hd)
  rw [MeasureTheory.integral_neg, continuumKernelTail_initial] at h
  linarith

/-- The impulse energy tends to zero at infinite time. -/
theorem continuumImpulseEnergy_tendsto_zero {delta : ℝ} (hd : 0 < delta) :
    Tendsto (continuumImpulseEnergy delta) atTop (𝓝 0) := by
  let lambda := 1 / ((delta + 1) * (2 / delta + 2 / delta ^ 2 + 3))
  have hl : 0 < lambda := by dsimp [lambda]; positivity
  have he : Tendsto (fun t : ℝ => Real.exp (-lambda * t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hl)
  have hbound : Tendsto (fun t : ℝ => continuumImpulseEnergy delta 0 *
      Real.exp (-lambda * t)) atTop (𝓝 0) := by
    simpa using he.const_mul (continuumImpulseEnergy delta 0)
  apply squeeze_zero' ?_ ?_ hbound
  · exact Filter.Eventually.of_forall (fun t =>
      (impulse_energy_bounds hd t).1.trans (impulse_energy_bounds hd t).2.1)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact continuumImpulseEnergy_exp_bound hd ht

/-- The squared impulse response is integrable. -/
theorem continuumImpulseResponse_sq_integrable {delta : ℝ} (hd : 0 < delta) :
    MeasureTheory.IntegrableOn (fun t => continuumImpulseResponse delta t ^ 2) (Ioi 0) := by
  change MeasureTheory.Integrable (fun t => continuumImpulseResponse delta t ^ 2)
    (MeasureTheory.volume.restrict (Ioi 0))
  convert (continuumRenewalKernel_integrableOn hd).const_mul (delta / 2) using 1
  funext t
  dsimp [continuumRenewalKernel]
  field_simp
  try ring

/-- The squared impulse response has integral delta/2. -/
theorem continuumImpulseResponse_sq_integral {delta : ℝ} (hd : 0 < delta) :
    (∫ t in Ioi (0 : ℝ), continuumImpulseResponse delta t ^ 2) = delta / 2 := by
  have heq : (fun t => continuumImpulseResponse delta t ^ 2) =
      fun t => delta / 2 * continuumRenewalKernel delta t := by
    funext t
    dsimp [continuumRenewalKernel]
    field_simp
    try ring
  rw [heq, MeasureTheory.integral_const_mul, continuumRenewalKernel_mass hd, mul_one]

private def impulseKineticEnergy (delta t : ℝ) : ℝ :=
  continuumImpulseResponse delta t ^ 2 / delta + continuumImpulseVelocity delta t ^ 2

private theorem impulseKineticEnergy_hasDerivAt {delta : ℝ} (hd : delta ≠ 0) (t : ℝ) :
    HasDerivAt (impulseKineticEnergy delta) (-2 * continuumImpulseVelocity delta t ^ 2) t := by
  convert ((continuumImpulseResponse_hasDerivAt delta t).pow 2 |>.div_const delta).add
    ((continuumImpulseVelocity_hasDerivAt delta t).pow 2) using 1
  · rfl
  · field_simp
    ring

private theorem impulseKineticEnergy_tendsto_zero {delta : ℝ} (hd : 0 < delta) :
    Tendsto (impulseKineticEnergy delta) atTop (𝓝 0) := by
  apply squeeze_zero (g := continuumImpulseEnergy delta) ?_ ?_
    (continuumImpulseEnergy_tendsto_zero hd)
  · intro t
    dsimp [impulseKineticEnergy]
    positivity
  · intro t
    have hF := continuumKernelTail_nonneg hd t
    dsimp [impulseKineticEnergy, continuumImpulseEnergy]
    linarith

/-- The squared impulse velocity is integrable. -/
theorem continuumImpulseVelocity_sq_integrable {delta : ℝ} (hd : 0 < delta) :
    MeasureTheory.IntegrableOn (fun t => continuumImpulseVelocity delta t ^ 2) (Ioi 0) := by
  have h := MeasureTheory.integrableOn_Ioi_deriv_of_nonpos' (a := (0 : ℝ))
    (fun t _ => impulseKineticEnergy_hasDerivAt hd.ne' t)
    (fun t _ => mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _))
    (impulseKineticEnergy_tendsto_zero hd)
  change MeasureTheory.Integrable (fun t => continuumImpulseVelocity delta t ^ 2)
    (MeasureTheory.volume.restrict (Ioi 0))
  convert h.const_mul (-1 / 2 : ℝ) using 1
  funext t
  ring

/-- The squared impulse velocity has integral one half. -/
theorem continuumImpulseVelocity_sq_integral {delta : ℝ} (hd : 0 < delta) :
    (∫ t in Ioi (0 : ℝ), continuumImpulseVelocity delta t ^ 2) = 1 / 2 := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos' (a := (0 : ℝ))
    (fun t _ => impulseKineticEnergy_hasDerivAt hd.ne' t)
    (fun t _ => mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _))
    (impulseKineticEnergy_tendsto_zero hd)
  rw [MeasureTheory.integral_const_mul] at h
  have hinit : impulseKineticEnergy delta 0 = 1 := by
    simp [impulseKineticEnergy, continuumImpulseResponse, continuumImpulseVelocity, continuumMeanFlow_zero]
  rw [hinit] at h
  linarith

/-- Derivative of the actual renewal kernel. -/
theorem continuumRenewalKernel_hasDerivAt (delta t : ℝ) (hd : delta ≠ 0) :
    HasDerivAt (continuumRenewalKernel delta)
      (-4 * continuumImpulseResponse delta t * continuumImpulseVelocity delta t) t := by
  convert ((continuumImpulseResponse_hasDerivAt delta t).pow 2).const_mul (2 / delta) using 1
  · rfl
  · field_simp
    ring

/-- The total variation of the smooth continuum renewal kernel on the positive half-line. -/
def continuumKernelTotalVariation (delta : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), |deriv (continuumRenewalKernel delta) t|

private theorem kernel_deriv_bound {delta : ℝ} (hd : 0 < delta) (t : ℝ) :
    |deriv (continuumRenewalKernel delta) t| ≤
      2 / Real.sqrt delta * continuumImpulseResponse delta t ^ 2 +
        2 * Real.sqrt delta * continuumImpulseVelocity delta t ^ 2 := by
  rw [(continuumRenewalKernel_hasDerivAt delta t hd.ne').deriv]
  let x := continuumImpulseResponse delta t
  let y := continuumImpulseVelocity delta t
  have hs : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hd
  have hs2 : Real.sqrt delta ^ 2 = delta := Real.sq_sqrt hd.le
  have hsq := sq_nonneg (|x| - Real.sqrt delta * |y|)
  have hxa := sq_abs x
  have hya := sq_abs y
  change |(-4) * x * y| ≤ 2 / Real.sqrt delta * x ^ 2 + 2 * Real.sqrt delta * y ^ 2
  rw [abs_mul, abs_mul]
  norm_num
  apply (mul_le_mul_iff_left₀ hs).mp
  have heq : (2 / Real.sqrt delta * x ^ 2 + 2 * Real.sqrt delta * y ^ 2) *
      Real.sqrt delta =
      2 * x ^ 2 + 2 * delta * y ^ 2 := by
    field_simp
    nlinarith [hs2]
  rw [heq]
  nlinarith

/-- The kernel derivative is absolutely integrable. -/
theorem continuumRenewalKernel_deriv_abs_integrable {delta : ℝ} (hd : 0 < delta) :
    MeasureTheory.IntegrableOn (fun t => |deriv (continuumRenewalKernel delta) t|) (Ioi 0) := by
  have hmajor := ((continuumImpulseResponse_sq_integrable hd).const_mul (2 / Real.sqrt delta)).add
    ((continuumImpulseVelocity_sq_integrable hd).const_mul (2 * Real.sqrt delta))
  apply hmajor.mono' ?_ (Filter.Eventually.of_forall (fun t => ?_))
  · have heq : (fun t => |deriv (continuumRenewalKernel delta) t|) =
        fun t => |-4 * continuumImpulseResponse delta t * continuumImpulseVelocity delta t| := by
      funext t
      rw [(continuumRenewalKernel_hasDerivAt delta t hd.ne').deriv]
    rw [heq]
    exact ((continuous_const.mul (continuumImpulseResponse_continuous delta)).mul
      (continuumImpulseVelocity_continuous delta)).abs.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_abs]
    exact kernel_deriv_bound hd t

/-- The actual continuum renewal kernel has total variation at most twice sqrt(delta). -/
theorem continuumKernelTotalVariation_le {delta : ℝ} (hd : 0 < delta) :
    continuumKernelTotalVariation delta ≤ 2 * Real.sqrt delta := by
  have hx := (continuumImpulseResponse_sq_integrable hd).const_mul (2 / Real.sqrt delta)
  have hy := (continuumImpulseVelocity_sq_integrable hd).const_mul (2 * Real.sqrt delta)
  have h := MeasureTheory.integral_mono (continuumRenewalKernel_deriv_abs_integrable hd)
    (hx.add hy) (fun t => kernel_deriv_bound hd t)
  change (∫ t in Ioi (0 : ℝ), |deriv (continuumRenewalKernel delta) t|) ≤
    (∫ t in Ioi (0 : ℝ), 2 / Real.sqrt delta * continuumImpulseResponse delta t ^ 2 +
      2 * Real.sqrt delta * continuumImpulseVelocity delta t ^ 2) at h
  rw [MeasureTheory.integral_add hx hy, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, continuumImpulseResponse_sq_integral hd,
    continuumImpulseVelocity_sq_integral hd] at h
  have hs : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hd
  have hs2 := Real.sq_sqrt hd.le
  have heq : 2 / Real.sqrt delta * (delta / 2) + 2 * Real.sqrt delta * (1 / 2) =
      2 * Real.sqrt delta := by
    field_simp
    nlinarith [hs2]
  rwa [heq] at h

/-- The derivative of the renewal kernel is continuous. -/
theorem continuumRenewalKernel_deriv_continuous {delta : ℝ} (hd : delta ≠ 0) :
    Continuous (deriv (continuumRenewalKernel delta)) := by
  have heq : deriv (continuumRenewalKernel delta) =
      fun t => -4 * continuumImpulseResponse delta t * continuumImpulseVelocity delta t := by
    funext t
    exact (continuumRenewalKernel_hasDerivAt delta t hd).deriv
  rw [heq]
  exact (continuous_const.mul (continuumImpulseResponse_continuous delta)).mul
    (continuumImpulseVelocity_continuous delta)

/-- Partition-based total variation is bounded by the integral of the absolute derivative. -/
theorem continuumRenewalKernel_eVariationOn_le_integral {delta : ℝ} (hd : 0 < delta) :
    eVariationOn (continuumRenewalKernel delta) (Ici 0) ≤
      ENNReal.ofReal (continuumKernelTotalVariation delta) := by
  have hdc := continuumRenewalKernel_deriv_continuous hd.ne'
  have hac := hdc.abs
  apply iSup_le
  rintro ⟨n, ⟨v, hv, hvs⟩⟩
  have hstep (i : ℕ) :
      edist (continuumRenewalKernel delta (v (i + 1))) (continuumRenewalKernel delta (v i)) ≤
        ENNReal.ofReal (∫ x in v i..v (i + 1), |deriv (continuumRenewalKernel delta) x|) := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => (continuumRenewalKernel_hasDerivAt delta x hd.ne').differentiableAt.hasDerivAt)
      (hdc.intervalIntegrable (v i) (v (i + 1)))
    rw [edist_dist, Real.dist_eq, ← hftc]
    exact ENNReal.ofReal_le_ofReal
      (intervalIntegral.abs_integral_le_integral_abs (hv (Nat.le_succ i)))
  calc
    (∑ i ∈ Finset.range n, edist (continuumRenewalKernel delta (v (i + 1)))
        (continuumRenewalKernel delta (v i))) ≤
      ∑ i ∈ Finset.range n, ENNReal.ofReal
        (∫ x in v i..v (i + 1), |deriv (continuumRenewalKernel delta) x|) :=
          Finset.sum_le_sum (fun i _ => hstep i)
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n,
        ∫ x in v i..v (i + 1), |deriv (continuumRenewalKernel delta) x|) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      exact fun i _ => intervalIntegral.integral_nonneg (hv (Nat.le_succ i))
        (fun _ _ => abs_nonneg _)
    _ = ENNReal.ofReal (∫ x in v 0..v n, |deriv (continuumRenewalKernel delta) x|) := by
      rw [intervalIntegral.sum_integral_adjacent_intervals
        (fun i _ => hac.intervalIntegrable (v i) (v (i + 1)))]
    _ ≤ ENNReal.ofReal (continuumKernelTotalVariation delta) := by
      apply ENNReal.ofReal_le_ofReal
      rw [intervalIntegral.integral_of_le (hv (Nat.zero_le n))]
      exact MeasureTheory.setIntegral_mono_set (continuumRenewalKernel_deriv_abs_integrable hd)
        (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
        (Filter.Eventually.of_forall (fun x hx => lt_of_le_of_lt (hvs 0) hx.1))

/-- The actual renewal kernel has partition-based total variation at most twice sqrt(delta). -/
theorem continuumRenewalKernel_eVariationOn_le {delta : ℝ} (hd : 0 < delta) :
    eVariationOn (continuumRenewalKernel delta) (Ici 0) ≤
      ENNReal.ofReal (2 * Real.sqrt delta) :=
  (continuumRenewalKernel_eVariationOn_le_integral hd).trans
    (ENNReal.ofReal_le_ofReal (continuumKernelTotalVariation_le hd))

end
end SparseSGD
