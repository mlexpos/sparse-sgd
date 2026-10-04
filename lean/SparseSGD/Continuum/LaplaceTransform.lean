import SparseSGD.Continuum.KernelEstimates

open Filter Set MeasureTheory
open scoped Topology

namespace SparseSGD

noncomputable section

/-- The actual kernel's real Laplace transform. -/
def continuumKernelLaplace (delta s : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * continuumRenewalKernel delta t

private def impulseR (delta t : ℝ) : ℝ := continuumImpulseResponse delta t ^ 2
private def impulseV (delta t : ℝ) : ℝ := continuumImpulseVelocity delta t ^ 2
private def impulseC (delta t : ℝ) : ℝ :=
  continuumImpulseResponse delta t * continuumImpulseVelocity delta t

private theorem impulseC_integrable {delta : ℝ} (hd : 0 < delta) :
    IntegrableOn (impulseC delta) (Ioi 0) := by
  have hmajor := (continuumImpulseResponse_sq_integrable hd).add
    (continuumImpulseVelocity_sq_integrable hd)
  apply hmajor.mono' ((continuumImpulseResponse_continuous delta).mul
    (continuumImpulseVelocity_continuous delta)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs]
    dsimp [impulseC]
    rw [abs_mul]
    nlinarith [sq_nonneg (|continuumImpulseResponse delta t| -
      |continuumImpulseVelocity delta t|), sq_abs (continuumImpulseResponse delta t),
      sq_abs (continuumImpulseVelocity delta t)])

private theorem impulseR_tendsto_zero {delta : ℝ} (hd : 0 < delta) :
    Tendsto (impulseR delta) atTop (𝓝 0) := by
  apply squeeze_zero (g := fun t => delta * continuumImpulseEnergy delta t)
    (fun t => sq_nonneg _) ?_ (by simpa using (continuumImpulseEnergy_tendsto_zero hd).const_mul delta)
  intro t
  have hF := continuumKernelTail_nonneg hd t
  have hx : 0 ≤ continuumImpulseResponse delta t ^ 2 / delta := by positivity
  have hy := sq_nonneg (continuumImpulseVelocity delta t)
  have hb : continuumImpulseResponse delta t ^ 2 / delta ≤ continuumImpulseEnergy delta t := by
    dsimp [continuumImpulseEnergy]
    linarith
  have hs := mul_le_mul_of_nonneg_left hb hd.le
  try dsimp [impulseR]
  rwa [mul_div_cancel₀ _ hd.ne'] at hs

private theorem impulseV_tendsto_zero {delta : ℝ} (hd : 0 < delta) :
    Tendsto (impulseV delta) atTop (𝓝 0) := by
  apply squeeze_zero (g := continuumImpulseEnergy delta) (fun t => sq_nonneg _) ?_
    (continuumImpulseEnergy_tendsto_zero hd)
  intro t
  have hF := continuumKernelTail_nonneg hd t
  have hx : 0 ≤ continuumImpulseResponse delta t ^ 2 / delta := by positivity
  dsimp [impulseV, continuumImpulseEnergy]
  linarith

private theorem impulseC_tendsto_zero {delta : ℝ} (hd : 0 < delta) :
    Tendsto (impulseC delta) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (g := fun t => impulseR delta t + impulseV delta t)
    (fun t => abs_nonneg _) ?_
    (by simpa using (impulseR_tendsto_zero hd).add (impulseV_tendsto_zero hd))
  intro t
  dsimp [impulseC, impulseR, impulseV]
  rw [abs_mul]
  nlinarith [sq_nonneg (|continuumImpulseResponse delta t| -
    |continuumImpulseVelocity delta t|), sq_abs (continuumImpulseResponse delta t),
    sq_abs (continuumImpulseVelocity delta t)]

private theorem impulseR_hasDerivAt (delta t : ℝ) :
    HasDerivAt (impulseR delta) (-2 * delta * impulseC delta t) t := by
  convert (continuumImpulseResponse_hasDerivAt delta t).pow 2 using 1
  · rfl
  · dsimp [impulseC]
    ring

private theorem impulseV_hasDerivAt (delta t : ℝ) :
    HasDerivAt (impulseV delta) (2 * impulseC delta t - 2 * impulseV delta t) t := by
  convert (continuumImpulseVelocity_hasDerivAt delta t).pow 2 using 1
  · rfl
  · dsimp [impulseC, impulseV]
    ring

private theorem impulseC_hasDerivAt (delta t : ℝ) :
    HasDerivAt (impulseC delta) (impulseR delta t - impulseC delta t - delta * impulseV delta t) t := by
  convert (continuumImpulseResponse_hasDerivAt delta t).mul
    (continuumImpulseVelocity_hasDerivAt delta t) using 1
  · rfl
  · dsimp [impulseR, impulseV, impulseC]
    ring

private def weightedIntegral (s : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * f t

private theorem weighted_integrable {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) :
    IntegrableOn (fun t => Real.exp (-s * t) * f t) (Ioi 0) := by
  apply hf.bdd_mul (c := 1)
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) ht.le

private theorem weighted_tendsto_zero {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℝ}
    (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun t => Real.exp (-s * t) * f t) atTop (𝓝 0) := by
  rcases eq_or_lt_of_le hs with hs | hs
  · subst s
    simpa using hf
  · have he : Tendsto (fun t : ℝ => Real.exp (-s * t)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq, neg_mul] using
        Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hs)
    simpa using he.mul hf

private theorem weightedIntegral_const_mul (s c : ℝ) (f : ℝ → ℝ) :
    weightedIntegral s (fun t => c * f t) = c * weightedIntegral s f := by
  dsimp [weightedIntegral]
  simp_rw [mul_left_comm (Real.exp (-s * _)) c]
  rw [integral_const_mul]

private theorem weightedIntegral_sub {s : ℝ} (hs : 0 ≤ s) {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hg : IntegrableOn g (Ioi 0)) :
    weightedIntegral s (fun t => f t - g t) = weightedIntegral s f - weightedIntegral s g := by
  dsimp [weightedIntegral]
  simp_rw [mul_sub]
  exact integral_sub (weighted_integrable hs hf) (weighted_integrable hs hg)

private theorem weighted_derivative_identity {s : ℝ} (hs : 0 ≤ s) {f f' : ℝ → ℝ}
    (hder : ∀ t, HasDerivAt f (f' t) t)
    (hf : IntegrableOn f (Ioi 0)) (hf' : IntegrableOn f' (Ioi 0))
    (htop : Tendsto f atTop (𝓝 0)) :
    s * weightedIntegral s f - weightedIntegral s f' = f 0 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (fun t _ => by
      have he := (((hasDerivAt_id t).const_mul (-s)).exp).mul (hder t)
      convert! he using 1 <;> first | rfl | (simp only [id_eq, Pi.add_apply, Pi.sub_apply]; ring))
    (weighted_integrable hs ((hf.const_mul (-s)).add hf'))
    (weighted_tendsto_zero hs htop)
  have hrewrite : (fun t => Real.exp (-s * t) * (s * f t - f' t)) =
      -(fun t => Real.exp (-s * t) * (-s * f t + f' t)) := by
    funext t
    simp only [Pi.neg_apply]
    ring
  have hid : weightedIntegral s (fun t => s * f t - f' t) = f 0 := by
    dsimp [weightedIntegral]
    rw [hrewrite]
    change (∫ t in Ioi (0 : ℝ), -(Real.exp (-s * t) * (-s * f t + f' t))) = f 0
    rw [integral_neg]
    simpa using congrArg Neg.neg h
  rw [weightedIntegral_sub hs (hf.const_mul s) hf', weightedIntegral_const_mul] at hid
  exact hid

/-- The real Laplace integral of the actual kernel exists throughout the closed right half-line. -/
theorem continuumKernelLaplace_integrable {delta s : ℝ} (hd : 0 < delta) (hs : 0 ≤ s) :
    IntegrableOn (fun t => Real.exp (-s * t) * continuumRenewalKernel delta t) (Ioi 0) :=
  weighted_integrable hs (continuumRenewalKernel_integrableOn hd)

/-- The actual continuum renewal kernel has the paper's rational Laplace transform. -/
theorem continuumKernelLaplace_eq {delta s : ℝ} (hd : 0 < delta) (hs : 0 ≤ s) :
    continuumKernelLaplace delta s = 4 * delta / ((s + 1) * (s ^ 2 + 2 * s + 4 * delta)) := by
  have hri : IntegrableOn (impulseR delta) (Ioi 0) := continuumImpulseResponse_sq_integrable hd
  have hvi : IntegrableOn (impulseV delta) (Ioi 0) := continuumImpulseVelocity_sq_integrable hd
  have hci := impulseC_integrable hd
  have hR := weighted_derivative_identity hs (impulseR_hasDerivAt delta) hri
    (hci.const_mul (-2 * delta)) (impulseR_tendsto_zero hd)
  have hV := weighted_derivative_identity hs (impulseV_hasDerivAt delta) hvi
    ((hci.const_mul 2).sub (hvi.const_mul 2)) (impulseV_tendsto_zero hd)
  have hC := weighted_derivative_identity hs (impulseC_hasDerivAt delta) hci
    ((hri.sub hci).sub (hvi.const_mul delta)) (impulseC_tendsto_zero hd)
  rw [weightedIntegral_const_mul] at hR
  rw [weightedIntegral_sub hs (hci.const_mul 2) (hvi.const_mul 2),
    weightedIntegral_const_mul, weightedIntegral_const_mul] at hV
  change s * weightedIntegral s (impulseC delta) -
    weightedIntegral s (fun t => (impulseR delta - impulseC delta) t - delta * impulseV delta t) =
    impulseC delta 0 at hC
  rw [weightedIntegral_sub hs (hri.sub hci) (hvi.const_mul delta)] at hC
  have hsub : weightedIntegral s (impulseR delta - impulseC delta) =
      weightedIntegral s (impulseR delta) - weightedIntegral s (impulseC delta) := by
    convert weightedIntegral_sub hs hri hci using 1
  rw [hsub, weightedIntegral_const_mul] at hC
  have hr0 : impulseR delta 0 = 0 := by
    simp [impulseR, continuumImpulseResponse, continuumMeanFlow_zero]
  have hv0 : impulseV delta 0 = 1 := by
    simp [impulseV, continuumImpulseVelocity, continuumMeanFlow_zero]
  have hc0 : impulseC delta 0 = 0 := by
    simp [impulseC, continuumImpulseResponse, continuumImpulseVelocity, continuumMeanFlow_zero]
  rw [hr0] at hR
  rw [hv0] at hV
  rw [hc0] at hC
  let R := weightedIntegral s (impulseR delta)
  let V := weightedIntegral s (impulseV delta)
  let C := weightedIntegral s (impulseC delta)
  have hReq : s * R + 2 * delta * C = 0 := by nlinarith [hR]
  have hVeq : (s + 2) * V - 2 * C = 1 := by nlinarith [hV]
  have hCeq : R - (s + 1) * C - delta * V = 0 := by nlinarith [hC]
  have hpoly : ((s + 1) * (s ^ 2 + 2 * s + 4 * delta)) * R = 2 * delta ^ 2 := by
    linear_combination ((s + 1) * (s + 2) + 2 * delta) * hReq +
      (2 * delta ^ 2) * hVeq + (2 * delta * (s + 2)) * hCeq
  have hden : 0 < (s + 1) * (s ^ 2 + 2 * s + 4 * delta) := by positivity
  have hk : continuumKernelLaplace delta s = 2 / delta * R := by
    change weightedIntegral s (fun t => 2 / delta * impulseR delta t) = 2 / delta * R
    exact weightedIntegral_const_mul s (2 / delta) (impulseR delta)
  rw [hk]
  apply (eq_div_iff hden.ne').mpr
  field_simp
  nlinarith [hpoly]

end
end SparseSGD
