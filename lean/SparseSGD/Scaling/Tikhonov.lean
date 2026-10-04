import SparseSGD.Scaling.SmallDeltaApproximation
import SparseSGD.Scaling.GeometricRenewal
import SparseSGD.Scaling.RenewalComparison

namespace SparseSGD
open Scaling
noncomputable section
set_option maxHeartbeats 1000000

/-- Full small-Delta comparison, uniform in time and in beta. In particular,
beta may be fixed: no vanishing retention step is assumed. -/
theorem smallDelta_trajectory_learningProfile (p : Params) (Delta R : ℝ)
    (jury : External.JuryStability)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1) (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8)
    (hw : p.w=smallDeltaW p.beta Delta) (hR : 0 ≤ R)
    (hu0 : 0 ≤ p.renormNoise) (hu1 : p.renormNoise < 1) (hp : 0 ≤ p.renormAdditive) (k : ℕ) :
    |(p.trajectory ⟨R,0,0⟩ k).R-
      learningProfile p.renormNoise p.renormAdditive R ((k : ℝ)*(p.w/p.eps))| ≤
      (538/(1-p.renormNoise)+8)*Delta*(R+p.renormAdditive/(1-p.renormNoise)) := by
  let u := p.renormNoise
  let phi := p.renormAdditive
  let L := phi/(1-u)
  let rho := smallDeltaRho p.beta Delta
  let x := geometricResponse rho u phi R
  have hL : 0 ≤ L := by dsimp [L,phi,u]; positivity
  have hsize : 0 ≤ R+L := by positivity
  have hrho0 : 0 < rho := Real.exp_pos _
  have hz : 0 < smallDeltaZ p.beta Delta := by dsimp [smallDeltaZ]; positivity
  have hrho1 : rho < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hphiL : phi ≤ L := by
    have hprod : L*(1-u)=phi := by
      have hh : 1-u ≠ 0 := by dsimp [u]; linarith
      dsimp [L]
      field_simp
    have hu : 0 ≤ u := hu0
    nlinarith
  have hx (j : ℕ) : |u*x j+phi| ≤ 2*(R+L) := by
    obtain ⟨hx0,hxb⟩ := geometricResponse_bounds rho u phi R hrho0.le hrho1.le hu0 hu1 hp hR j
    change 0≤x j at hx0
    change x j≤R+L at hxb
    have hu : 0 ≤ u := hu0
    have hu' : u ≤ 1 := hu1.le
    have hp' : 0 ≤ phi := hp
    rw [abs_of_nonneg (by positivity : 0≤u*x j+phi)]
    have H := mul_le_mul_of_nonneg_right hu' hx0
    nlinarith
  obtain ⟨hw0,hw1,_,_⟩ := smallDelta_kernel_parameters p Delta hb0 hb1 hD0 hD1 hw
  obtain ⟨hkernel,hkernelBound⟩ := smallDelta_kernel_geometric p Delta jury hb0 hb1 hD0 hD1 hw
  have H := renewal_comparison (normalizedKernelLag p) (geomLag rho)
    (freeRisk p ⟨R,0,0⟩) (fun j => R*rho^j) (fun j => (p.trajectory ⟨R,0,0⟩ j).R) x
    u phi (90*Delta*R) (224*Delta) (2*(R+L))
    (normalized_kernel_lag_nonneg jury p hb0 hb1 hw0 hw1)
    (normalized_kernel_partial_mass_le_one jury p hb0 hb1 hw0 hw1)
    hu0 hu1 (by positivity) (by positivity) (by positivity) hkernel hkernelBound
    (smallDelta_freeRisk_geometric p Delta R (by linarith) hb1 hD0 hD1 hw hR) hx
    (normalized_trajectory_recurrence jury p ⟨R,0,0⟩ hb0 hb1 hw0 hw1)
    (geometricResponse_renewal rho u phi R (ne_of_lt hu1)) k
  have Hbound : |(p.trajectory ⟨R,0,0⟩ k).R-x k| ≤ 538*Delta*(R+L)/(1-u) := by
    refine H.trans ?_
    apply div_le_div_of_nonneg_right _ (by linarith : 0≤1-u)
    nlinarith [mul_nonneg hD0.le hL]
  have hz1 : smallDeltaZ p.beta Delta ≤ Delta := by dsimp [smallDeltaZ]; nlinarith
  have hzid : p.w/p.eps=smallDeltaZ p.beta Delta := by
    have he : p.eps ≠ 0 := by dsimp [Params.eps]; linarith
    rw [hw]
    dsimp [smallDeltaW,smallDeltaZ,Params.eps] at *
    field_simp
  have Hp := geometricResponse_learningProfile_error u phi R (smallDeltaZ p.beta Delta)
    hu0 hu1 hp hR hz (hz1.trans hD1) k
  change |x k-learningProfile u phi R ((k : ℝ)*smallDeltaZ p.beta Delta)|≤8*smallDeltaZ p.beta Delta*(R+L) at Hp
  rw [hzid]
  have Htri := abs_sub_le ((p.trajectory ⟨R,0,0⟩ k).R) (x k)
    (learningProfile u phi R ((k : ℝ)*smallDeltaZ p.beta Delta))
  have Hp' : |x k-learningProfile u phi R ((k : ℝ)*smallDeltaZ p.beta Delta)|≤8*Delta*(R+L) := by
    refine Hp.trans ?_
    gcongr
  change |(p.trajectory ⟨R,0,0⟩ k).R-learningProfile u phi R ((k : ℝ)*smallDeltaZ p.beta Delta)|≤
    (538/(1-u)+8)*Delta*(R+L)
  have halg : (538/(1-u)+8)*Delta*(R+L)=538*Delta*(R+L)/(1-u)+8*Delta*(R+L) := by ring
  rw [halg]
  linarith

/-- Source Corollary Tikhonov, with explicit absolute cutoff and a constant
depending only on the stability margin. -/
theorem cor_tikhonov (margin : ℝ) (hm : 0 < margin) :
    ∃ Delta1 C : ℝ, 0 < Delta1 ∧ 0 < C ∧ ∀ (p : Params) (Delta R : ℝ),
      External.JuryStability → 1/2 ≤ p.beta → p.beta < 1 →
      0 < Delta → Delta ≤ Delta1 → p.w=smallDeltaW p.beta Delta → 0 ≤ R →
      0 ≤ p.renormNoise → p.renormNoise ≤ 1-margin → 0 ≤ p.renormAdditive →
      ∀ k : ℕ, |(p.trajectory ⟨R,0,0⟩ k).R-
        learningProfile p.renormNoise p.renormAdditive R ((k : ℝ)*(p.w/p.eps))| ≤
        C*Delta*(R+p.renormAdditive/(1-p.renormNoise)) := by
  refine ⟨1/8,538/margin+8,by norm_num,by positivity,?_⟩
  intro p Delta R jury hb0 hb1 hD0 hD1 hw hR hu0 hu hp k
  have hu1 : p.renormNoise < 1 := by linarith
  have H := smallDelta_trajectory_learningProfile p Delta R jury hb0 hb1 hD0 hD1 hw hR hu0 hu1 hp k
  refine H.trans ?_
  have hL : 0 ≤ p.renormAdditive/(1-p.renormNoise) := by positivity
  have hconst : 538/(1-p.renormNoise) ≤ 538/margin :=
    div_le_div_of_nonneg_left (by norm_num) hm (by linarith)
  gcongr

end
end SparseSGD
