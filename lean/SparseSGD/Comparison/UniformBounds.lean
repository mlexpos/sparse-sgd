import SparseSGD.Continuum.EnergyBound
import SparseSGD.Discrete.Positivity

open MeasureTheory Set

namespace SparseSGD
noncomputable section

theorem continuumRenewalKernel_partial_mass_le_one {delta : ℝ} (hd : 0 < delta)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x in (0 : ℝ)..t, continuumRenewalKernel delta x) ≤ 1 := by
  have h := intervalIntegral.integral_interval_add_Ioi
    (continuumRenewalKernel_integrableOn hd)
    ((continuumRenewalKernel_integrableOn hd).mono_set (Ioi_subset_Ioi ht))
  rw [continuumRenewalKernel_mass hd] at h
  have hp : 0 ≤ ∫ x in Ioi t, continuumRenewalKernel delta x :=
    integral_nonneg (fun x => continuumRenewalKernel_nonneg hd x)
  linarith

/-- Uniform risk bound for the actual continuum flow, obtained from the renewal equation. -/
theorem continuumFlow_risk_uniform_bound {delta u phi : ℝ} (hd : 0 < delta)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hp : 0 ≤ phi) (s : Moments) (hs : s.psd)
    {t : ℝ} (ht : 0 ≤ t) :
    (continuumFlow delta u phi s t).R ≤ (s.R + delta * s.V + phi) / (1 - u) := by
  let R := fun x => (continuumFlow delta u phi s x).R
  have hR : Continuous R := continuumFlow_R_continuous delta u phi s
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr ht) hR.continuousOn
  have hx0 : 0 ≤ R x := continuumFlow_R_nonneg hd hu0 hp s hs hx.1
  have hM : 0 ≤ u * R x + phi := by positivity
  have hint : (∫ y in (0 : ℝ)..x, continuumRenewalKernel delta (x-y) * (u*R y+phi)) ≤
      u * R x + phi := by
    have hk : Continuous (fun y => continuumRenewalKernel delta (x-y)) :=
      (continuumRenewalKernel_continuous delta).comp (continuous_const.sub continuous_id)
    calc
      _ ≤ ∫ y in (0 : ℝ)..x, continuumRenewalKernel delta (x-y) * (u*R x+phi) := by
        apply intervalIntegral.integral_mono_on hx.1
          ((hk.mul ((hR.const_mul u).add continuous_const)).intervalIntegrable 0 x)
          ((hk.mul continuous_const).intervalIntegrable 0 x)
        intro y hy
        apply mul_le_mul_of_nonneg_left _ (continuumRenewalKernel_nonneg hd _)
        have hyx := hmax ⟨hy.1, hy.2.trans hx.2⟩
        change R y ≤ R x at hyx
        change u * R y + phi ≤ u * R x + phi
        nlinarith
      _ = (∫ y in (0 : ℝ)..x, continuumRenewalKernel delta y) * (u*R x+phi) := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_comp_sub_left]
        simp
      _ ≤ 1 * (u*R x+phi) := mul_le_mul_of_nonneg_right
        (continuumRenewalKernel_partial_mass_le_one hd hx.1) hM
      _ = _ := one_mul _
  have hrenew := continuumFlow_renewal delta u phi s x
  have hfree := continuumFreeRisk_le_initial_energy delta hd s hs x hx.1
  have hbound : R x ≤ (s.R + delta*s.V+phi)/(1-u) := by
    apply (le_div_iff₀ (by linarith : 0 < 1-u)).2
    change R x = _ at hrenew
    nlinarith
  exact (hmax ⟨ht, le_rfl⟩).trans hbound

def continuumRiskBound (delta u phi : ℝ) (s : Moments) : ℝ :=
  (s.R + delta * s.V + phi) / (1-u)

def continuumEnergyBound (delta u phi : ℝ) (s : Moments) : ℝ :=
  s.R + delta*s.V + (1+u)*continuumRiskBound delta u phi s + phi

theorem continuumFlow_energy_uniform_bound {delta u phi : ℝ} (hd : 0 < delta)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hp : 0 ≤ phi) (s : Moments) (hs : s.psd)
    {t : ℝ} (ht : 0 ≤ t) :
    (continuumFlow delta u phi s t).R + delta*(continuumFlow delta u phi s t).V ≤
      continuumEnergyBound delta u phi s := by
  let E := fun t => (continuumFlow delta u phi s t).R + delta*(continuumFlow delta u phi s t).V
  let H := (1+u)*continuumRiskBound delta u phi s+phi
  have hE0 : 0 ≤ s.R+delta*s.V := by
    have := Moments.psd_R_nonneg hs
    have := Moments.psd_V_nonneg hs
    positivity
  have hH : 0 ≤ H := by
    dsimp [H, continuumRiskBound]
    positivity
  have hder (x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt (fun x => Real.exp (2*x)*(E x-H))
        (Real.exp (2*x)*(2*(1+u)*(continuumFlow delta u phi s x).R+2*phi-2*H)) x := by
    obtain ⟨hR,hV,_⟩ := continuumFlow_isMomentSolution delta u phi s x hx
    have he := (hR.add (hV.const_mul delta)).sub_const H
    have h := (((hasDerivAt_id x).const_mul 2).exp).mul he
    convert h using 1
    · rfl
    · dsimp [E, continuumField]
      field_simp
      ring
  have hanti : AntitoneOn (fun x => Real.exp (2*x)*(E x-H)) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun x hx => (hder x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hder x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hder x (interior_subset hx)).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have hb := continuumFlow_risk_uniform_bound hd hu0 hu1 hp s hs (interior_subset hx)
      change _ ≤ continuumRiskBound delta u phi s at hb
      have hu : 0 ≤ 2*(1+u) := by positivity
      have := mul_le_mul_of_nonneg_left hb hu
      dsimp [H]
      linarith
  have ha := hanti (by simp) ht ht
  have hEzero : E 0 = s.R+delta*s.V := by simp [E, continuumFlow_initial]
  simp only [mul_zero, Real.exp_zero, one_mul, hEzero] at ha
  have hexp : 1 ≤ Real.exp (2*t) := Real.one_le_exp_iff.mpr (by positivity)
  change E t ≤ s.R+delta*s.V+(1+u)*continuumRiskBound delta u phi s+phi
  by_cases he : E t ≤ H
  · dsimp [H] at he
    linarith
  · have hpE : 0 ≤ E t-H := by linarith
    have hmul := mul_le_mul_of_nonneg_right hexp hpE
    dsimp [H] at ha hmul
    nlinarith

theorem Moments.psd_cross_energy_bound (delta : ℝ) (hd : 0 < delta)
    (s : Moments) (hs : s.psd) :
    2 * Real.sqrt delta * |s.C| ≤ s.R + delta * s.V := by
  have hR := Moments.psd_R_nonneg hs
  have hV := Moments.psd_V_nonneg hs
  have hQ := Moments.psd_rankDefect_nonneg hs
  unfold Moments.rankDefect at hQ
  have hsqrt := Real.sq_sqrt hd.le
  have hprod := mul_nonneg hd.le hQ
  have hE : 0 ≤ s.R+delta*s.V := by positivity
  have hC : 0 ≤ 2*Real.sqrt delta*|s.C| := by positivity
  have heq : (2*Real.sqrt delta*|s.C|)^2 = 4*delta*s.C^2 := by
    rw [mul_pow, mul_pow, hsqrt, sq_abs]
    ring
  nlinarith [sq_nonneg (s.R-delta*s.V)]

/-- The risk derivative is bounded uniformly down to delta=0, at scale sqrt(delta). -/
theorem continuumFlow_risk_derivative_bound {delta u phi : ℝ} (hd : 0 < delta)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hp : 0 ≤ phi) (s : Moments) (hs : s.psd)
    {t : ℝ} (ht : 0 ≤ t) :
    |deriv (fun x => (continuumFlow delta u phi s x).R) t| ≤
      Real.sqrt delta * continuumEnergyBound delta u phi s := by
  rw [((continuumFlow_isMomentSolution delta u phi s t ht).1).deriv]
  change |-2*delta*(continuumFlow delta u phi s t).C| ≤ _
  have hc := Moments.psd_cross_energy_bound delta hd _ (continuumFlow_psd hd hu0 hp s hs ht)
  have he := continuumFlow_energy_uniform_bound hd hu0 hu1 hp s hs ht
  have h := mul_le_mul_of_nonneg_left (hc.trans he) (Real.sqrt_nonneg delta)
  have hsqrt := Real.sq_sqrt hd.le
  simp only [abs_mul, abs_neg, abs_of_nonneg hd.le, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have heq : Real.sqrt delta * (2 * Real.sqrt delta * |(continuumFlow delta u phi s t).C|) =
      2*delta*|(continuumFlow delta u phi s t).C| := by
    nlinarith only [congrArg (fun z => 2*z*|(continuumFlow delta u phi s t).C|) hsqrt]
  rwa [heq] at h

end
end SparseSGD
