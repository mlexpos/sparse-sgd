import SparseSGD.Comparison.RiemannBound
import SparseSGD.Comparison.ExactEmbedding

open MeasureTheory Set Filter Topology

namespace SparseSGD
noncomputable section

private theorem partial_integral_le_Ioi {f : ℝ → ℝ}
    (hi : IntegrableOn f (Ioi 0)) (hn : ∀ x, 0 ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x in (0 : ℝ)..t, f x) ≤ ∫ x in Ioi (0 : ℝ), f x := by
  have h := intervalIntegral.integral_interval_add_Ioi hi (hi.mono_set (Ioi_subset_Ioi ht))
  have hp : 0 ≤ ∫ x in Ioi t, f x := integral_nonneg hn
  linarith

/-- The continuum kernel quadrature estimate using bounded forcing and derivative. -/
theorem continuum_convolution_quadrature_bound {delta h : ℝ} (hd : 0 < delta)
    (hh : 0 < h) (k : ℕ) (f f' : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f')
    (F D : ℝ) (hF : 0 ≤ F) (hD : 0 ≤ D)
    (hbound : ∀ t ∈ Icc 0 ((k : ℝ)*h), |f t| ≤ F)
    (hderiv : ∀ t ∈ Icc 0 ((k : ℝ)*h), |f' t| ≤ D) :
    |(∫ x in (0 : ℝ)..(k : ℝ)*h, continuumRenewalKernel delta x * f ((k : ℝ)*h-x)) -
      rightEndpointSum (fun x => continuumRenewalKernel delta x * f ((k : ℝ)*h-x)) h k| ≤
        h * (2*Real.sqrt delta*F+D) := by
  let T := (k : ℝ)*h
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let q := continuumRenewalKernel delta
  let q' := deriv q
  have hq : Continuous q := continuumRenewalKernel_continuous delta
  have hq' : Continuous q' := continuumRenewalKernel_deriv_continuous hd.ne'
  have hqder (x : ℝ) : HasDerivAt q (q' x) x :=
    (continuumRenewalKernel_hasDerivAt delta x hd.ne').differentiableAt.hasDerivAt
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  let g := fun x => q x*f (T-x)
  let g' := fun x => q' x*f (T-x)-q x*f' (T-x)
  have hg (x : ℝ) : HasDerivAt g (g' x) x := by
    have hcomp := (hf (T-x)).comp x ((hasDerivAt_const x T).sub (hasDerivAt_id x))
    convert (hqder x).mul hcomp using 1
    · rfl
    · dsimp [g']; ring
  have hgc : Continuous g' := by dsimp [g']; fun_prop
  have hmono : (∫ x in (0 : ℝ)..T, ‖g' x‖) ≤
      (∫ x in (0 : ℝ)..T, |q' x|)*F + (∫ x in (0 : ℝ)..T, q x)*D := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..T, |q' x| * F+q x*D := by
        apply intervalIntegral.integral_mono_on hT (hgc.norm.intervalIntegrable 0 T)
          (((hq'.abs.mul continuous_const).add (hq.mul continuous_const)).intervalIntegrable 0 T)
        intro x hx
        have htx : T-x ∈ Icc 0 T := ⟨by linarith [hx.2],by linarith [hx.1]⟩
        have hqn : 0 ≤ q x := continuumRenewalKernel_nonneg hd x
        change |q' x*f (T-x)-q x*f' (T-x)| ≤ _
        calc
          _ ≤ |q' x*f (T-x)| + |q x*f' (T-x)| := abs_sub _ _
          _ = |q' x| * |f (T-x)| + q x * |f' (T-x)| := by rw [abs_mul,abs_mul,abs_of_nonneg hqn]
          _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hbound _ htx) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (hderiv _ htx) hqn)
      _ = _ := by
        rw [intervalIntegral.integral_add ((hq'.abs.mul_const F).intervalIntegrable 0 T)
          ((hq.mul_const D).intervalIntegrable 0 T),
          intervalIntegral.integral_mul_const,intervalIntegral.integral_mul_const]
  have hvar : (∫ x in (0 : ℝ)..T, |q' x|) ≤ 2*Real.sqrt delta := by
    exact (partial_integral_le_Ioi (continuumRenewalKernel_deriv_abs_integrable hd)
      (fun x => abs_nonneg _) hT).trans (continuumKernelTotalVariation_le hd)
  have hmass : (∫ x in (0 : ℝ)..T, q x) ≤ 1 := continuumRenewalKernel_partial_mass_le_one hd hT
  have htotal : (∫ x in (0 : ℝ)..T, ‖g' x‖) ≤ 2*Real.sqrt delta*F+D := by
    have h1 := mul_le_mul_of_nonneg_right hvar hF
    have h2 := mul_le_mul_of_nonneg_right hmass hD
    linarith
  exact (rightEndpoint_error g g' hg hgc h hh.le k).trans
    (mul_le_mul_of_nonneg_left htotal hh.le)

def Params.sampledKernelMass (p : Params) : ℝ :=
  ∑' n : ℕ, p.matchedStep*continuumRenewalKernel p.matchedDelta
    (((n+1 : ℕ) : ℝ)*p.matchedStep)

theorem Params.sampledKernelMass_hasSum (p : Params)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) (jury : External.JuryStability) :
    HasSum (fun n : ℕ => p.matchedStep*continuumRenewalKernel p.matchedDelta
      (((n+1 : ℕ) : ℝ)*p.matchedStep)) p.sampledKernelMass := by
  have H := (p.sampledImpulse_sq_hasSum hb0 hb1 hw0 hw1 jury).mul_left (p.matchedStep*(2/p.matchedDelta))
  have heq : (fun n : ℕ => p.matchedStep*continuumRenewalKernel p.matchedDelta
      (((n+1 : ℕ) : ℝ)*p.matchedStep)) =
      (fun n : ℕ => (p.matchedStep*(2/p.matchedDelta))*p.sampledImpulse (n+1)^2) := by
    funext n
    dsimp [continuumRenewalKernel,Params.sampledImpulse]
    ring
  unfold Params.sampledKernelMass
  rw [heq]
  exact H.summable.hasSum

theorem Params.sampledKernelMass_error (p : Params)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) (jury : External.JuryStability) :
    |p.sampledKernelMass-1| ≤ p.matchedStep*(2*Real.sqrt p.matchedDelta) := by
  have hd := p.matchedDelta_pos (by linarith) hb1 hw0 hw1
  have hh := p.matchedStep_pos (by linarith) hb1
  have H := rightEndpoint_infinite_error (continuumRenewalKernel p.matchedDelta)
    (deriv (continuumRenewalKernel p.matchedDelta))
    (fun x => (continuumRenewalKernel_hasDerivAt p.matchedDelta x hd.ne').differentiableAt.hasDerivAt)
    (continuumRenewalKernel_deriv_continuous hd.ne')
    (continuumRenewalKernel_integrableOn hd) (continuumRenewalKernel_deriv_abs_integrable hd)
    p.matchedStep hh p.sampledKernelMass (p.sampledKernelMass_hasSum hb0 hb1 hw0 hw1 jury)
  rw [continuumRenewalKernel_mass hd, Real.norm_eq_abs, abs_sub_comm] at H
  exact H.trans (mul_le_mul_of_nonneg_left (continuumKernelTotalVariation_le hd) hh.le)

end
end SparseSGD
