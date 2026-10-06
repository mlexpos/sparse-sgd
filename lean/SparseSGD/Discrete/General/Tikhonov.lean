import SparseSGD.Discrete.General.Renewal
import SparseSGD.Scaling.Tikhonov

/-!
# `cor:tikhonov` for every `ε ∈ (0,1]` (v2)

The v1 chain `smallDelta_kernel_parameters` -> `smallDelta_fast_weights` ->
`smallDelta_kernel_slow_geometric` -> `smallDelta_kernel_geometric` ->
`smallDelta_trajectory_learningProfile` -> `cor_tikhonov` carries `1/2 ≤ β`.  Here the chain is
re-proved under `0 ≤ β < 1` (plain SGD, `β = 0`, included), reusing the spectral layer
(`smallDeltaSpectrum_strong`, ... already `0 ≤ β`), `renewal_comparison`, `geometricResponse_*`,
`signed_geom_mixture_bound`, `normalizedKernelLag_geometric` unchanged, and the `_v2` kernel
lemmas of `Discrete/General/Renewal.lean`.  At `β = 0` the fast root `λ_- = 0`, `geomLag 0` is a
point mass and the weight `smallKernelWeight K β = 0`; every `q ≠ 1` hypothesis of
`weighted_geomLag` only needs `β < 1`, `a^2 < 1`, `b^2 < 1`.
-/

namespace SparseSGD
open Scaling
noncomputable section
set_option maxHeartbeats 1000000

/-- v2 `cor:tikhonov`: kernel parameters for `0 ≤ β < 1`. -/
theorem smallDelta_kernel_parameters_v2 (p : Params) (Delta : ℝ)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8)
    (hw : p.w=smallDeltaW p.beta Delta) :
    0 < p.w ∧ p.w < 2*(1+p.beta) ∧ 0 ≤ p.curvature ∧ p.curvature < 1 := by
  have he : 0 < 1-p.beta := by linarith
  have hw0 : 0 < p.w := by rw [hw]; exact mul_pos hD0 (sq_pos_of_pos he)
  have hw1 : p.w ≤ 1/8 := by
    rw [hw]
    dsimp only [smallDeltaW]
    have hs : (1-p.beta)^2 ≤ 1 := by nlinarith
    calc
      Delta*(1-p.beta)^2 ≤ Delta*1 := mul_le_mul_of_nonneg_left hs hD0.le
      _ ≤ 1/8 := by linarith
  have hwup : p.w < 2*(1+p.beta) := by linarith
  refine ⟨hw0,hwup,?_,?_⟩
  · exact div_nonneg hw0.le (by linarith)
  · exact (div_lt_one (by linarith : 0 < 2*(1+p.beta))).mpr hwup

/-- v2 `cor:tikhonov`: fast kernel weights for `0 ≤ β < 1`. -/
theorem smallDelta_fast_weights_v2 (p : Params) (Delta : ℝ)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8)
    (hw : p.w=smallDeltaW p.beta Delta) :
    let a := smallDeltaLambdaPlus p.beta Delta
    let b := smallDeltaLambdaMinus p.beta Delta
    let K := (1-p.curvature)*2*p.w*p.eps/(a-b)^2
    0 ≤ K ∧ K ≤ 8*Delta*p.eps ∧
    0 ≤ smallKernelWeight K p.beta ∧ smallKernelWeight K p.beta ≤ 8*Delta ∧
    0 ≤ smallKernelWeight K (b^2) ∧ smallKernelWeight K (b^2) ≤ 16*Delta := by
  dsimp only
  let a := smallDeltaLambdaPlus p.beta Delta
  let b := smallDeltaLambdaMinus p.beta Delta
  let K := (1-p.curvature)*2*p.w*p.eps/(a-b)^2
  change 0 ≤ K ∧ K ≤ 8*Delta*p.eps ∧ 0 ≤ smallKernelWeight K p.beta ∧
    smallKernelWeight K p.beta ≤ 8*Delta ∧ 0 ≤ smallKernelWeight K (b^2) ∧
    smallKernelWeight K (b^2) ≤ 16*Delta
  obtain ⟨_,hgap,hbpos,hbup,hapos,ha1,_,_,_,_,_,_⟩ :=
    smallDeltaSpectrum_strong p.beta Delta hb0 hb1 hD0 hD1
  have he : 0 < p.eps := by dsimp [Params.eps]; linarith
  have hgap' : p.eps/2 ≤ a-b := hgap
  have hgap0 : 0 < a-b := by linarith
  have hs : p.eps^2/4 ≤ (a-b)^2 := by nlinarith
  obtain ⟨hw0,_,hc0,hc1⟩ := smallDelta_kernel_parameters_v2 p Delta hb0 hb1 hD0 hD1 hw
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hK : K ≤ 8*Delta*p.eps := by
    apply (div_le_iff₀ (sq_pos_of_pos hgap0)).mpr
    have hcurv : (1-p.curvature)*2*p.w*p.eps ≤ 2*p.w*p.eps := by nlinarith [mul_nonneg hc0 (mul_nonneg hw0.le he.le)]
    have hw' : p.w=Delta*p.eps^2 := hw
    rw [hw'] at hcurv ⊢
    have H := mul_le_mul_of_nonneg_left hs (show 0≤8*Delta*p.eps by positivity)
    nlinarith only [hcurv,H]
  have hb1' : b < 1 := by
    have hab : b < a := by linarith
    exact hab.trans ha1
  have hb0' : 0 ≤ b := hbpos
  have hbsq : b^2 < 1 := by nlinarith
  have hbfast : 1-b^2 ≥ p.eps/2 := by
    have hD : 2*smallDeltaZ p.beta Delta ≤ p.eps/4 := by
      dsimp [smallDeltaZ,Params.eps]
      nlinarith [mul_le_mul_of_nonneg_right hD1 (show 0≤1-p.beta by linarith)]
    have hbup' : b ≤ p.beta+2*smallDeltaZ p.beta Delta := hbup
    have hbb : b^2 ≤ b := by nlinarith
    dsimp [Params.eps] at he ⊢
    dsimp [Params.eps] at hD
    linarith
  have hbweight0 : 0 ≤ smallKernelWeight K p.beta := by
    dsimp [smallKernelWeight]
    have h1 : 0 < 1-p.beta := by linarith
    exact div_nonneg (mul_nonneg hK0 hb0) h1.le
  have hbweight : smallKernelWeight K p.beta ≤ 8*Delta := by
    apply (div_le_iff₀ (show 0<1-p.beta by linarith)).mpr
    have H := mul_le_mul_of_nonneg_left hb1.le hK0
    dsimp [Params.eps] at hK
    nlinarith
  have hsqweight0 : 0 ≤ smallKernelWeight K (b^2) := by
    dsimp [smallKernelWeight]
    have h1 : 0 < 1-b^2 := by linarith
    exact div_nonneg (mul_nonneg hK0 (sq_nonneg b)) h1.le
  have hsqweight : smallKernelWeight K (b^2) ≤ 16*Delta := by
    apply (div_le_iff₀ (show 0<1-b^2 by linarith)).mpr
    have H := mul_le_mul_of_nonneg_left hbsq.le hK0
    have H2 := mul_le_mul_of_nonneg_left hbfast (show 0≤16*Delta by positivity)
    nlinarith only [hK,H,H2]
  exact ⟨hK0,hK,hbweight0,hbweight,hsqweight0,hsqweight⟩

/-- v2 `cor:tikhonov`: the actual normalized impulse kernel is within `64 Delta` of its slow
geometric component, for every `β ∈ [0,1)`. -/
theorem smallDelta_kernel_slow_geometric_v2 (p : Params) (Delta : ℝ)
    (jury : External.JuryStability)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8)
    (hw : p.w=smallDeltaW p.beta Delta) :
    Summable (fun n => |normalizedKernelLag p n-geomLag ((smallDeltaLambdaPlus p.beta Delta)^2) n|) ∧
    ∑' n, |normalizedKernelLag p n-geomLag ((smallDeltaLambdaPlus p.beta Delta)^2) n| ≤ 64*Delta := by
  let a := smallDeltaLambdaPlus p.beta Delta
  let b := smallDeltaLambdaMinus p.beta Delta
  let K := (1-p.curvature)*2*p.w*p.eps/(a-b)^2
  obtain ⟨_,hgap,hbpos,_,hapos,ha1,_,hprod,hsum,_⟩ :=
    smallDeltaSpectrum_strong p.beta Delta hb0 hb1 hD0 hD1
  have hab : a ≠ b := by
    intro h
    change a-b≥(1-p.beta)/2 at hgap
    rw [h] at hgap
    linarith
  have hb1' : b < 1 := by change a-b≥(1-p.beta)/2 at hgap; change a<1 at ha1; linarith
  have ha : a^2 < 1 := by change 0<a at hapos; change a<1 at ha1; nlinarith
  have hb : b^2 < 1 := by change 0≤b at hbpos; nlinarith
  obtain ⟨hw0,hw1,_,_⟩ := smallDelta_kernel_parameters_v2 p Delta hb0 hb1 hD0 hD1 hw
  have hsum' : a+b=1+p.beta-p.w := by rw [hw]; exact hsum
  obtain ⟨_,_,hB,hBb,hC,hCb⟩ := smallDelta_fast_weights_v2 p Delta hb0 hb1 hD0 hD1 hw
  have H := signed_geom_mixture_bound (normalizedKernelLag p) (a^2) p.beta (b^2)
    (smallKernelWeight K (a^2)) (2*smallKernelWeight K p.beta) (smallKernelWeight K (b^2))
    (sq_nonneg a) ha hb0 hb1 (sq_nonneg b) hb (by positivity) hC
    (normalized_kernel_lag_hasSum_v2 jury p hb0 hb1 hw0 hw1)
    (normalizedKernelLag_geometric p a b hab hsum' hprod (ne_of_lt ha) (ne_of_lt hb) (ne_of_lt hb1))
  refine ⟨H.1,H.2.trans ?_⟩
  change smallKernelWeight K p.beta ≤ 8*Delta at hBb
  change smallKernelWeight K (b^2) ≤ 16*Delta at hCb
  linarith

/-- v2 `cor:tikhonov`: the actual normalized renewal kernel is within `224 Delta` (total
variation) of the pure geometric law, for every `β ∈ [0,1)`. -/
theorem smallDelta_kernel_geometric_v2 (p : Params) (Delta : ℝ)
    (jury : External.JuryStability)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8)
    (hw : p.w=smallDeltaW p.beta Delta) :
    Summable (fun n => |normalizedKernelLag p n-geomLag (smallDeltaRho p.beta Delta) n|) ∧
    ∑' n, |normalizedKernelLag p n-geomLag (smallDeltaRho p.beta Delta) n| ≤ 224*Delta := by
  obtain ⟨Hs,hs⟩ := smallDelta_kernel_slow_geometric_v2 p Delta jury hb0 hb1 hD0 hD1 hw
  obtain ⟨Ht,ht⟩ := smallDelta_slow_geom_tv p.beta Delta hb0 hb1 hD0 hD1
  have hpoint (n : ℕ) : |normalizedKernelLag p n-geomLag (smallDeltaRho p.beta Delta) n| ≤
      |normalizedKernelLag p n-geomLag (smallDeltaLambdaPlus p.beta Delta^2) n|+
      |geomLag (smallDeltaLambdaPlus p.beta Delta^2) n-geomLag (smallDeltaRho p.beta Delta) n| :=
    abs_sub_le _ _ _
  have H := Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpoint (Hs.add Ht)
  refine ⟨H,?_⟩
  have Hsum := H.tsum_le_tsum hpoint (Hs.add Ht)
  rw [Hs.tsum_add Ht] at Hsum
  linarith

/-- v2 `cor:tikhonov`: full small-Delta comparison, uniform in time, for `β ∈ [0,1)` (fixed
`β`, including plain SGD at `β = 0`). -/
theorem smallDelta_trajectory_learningProfile_v2 (p : Params) (Delta R : ℝ)
    (jury : External.JuryStability)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8)
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
  obtain ⟨hw0,hw1,_,_⟩ := smallDelta_kernel_parameters_v2 p Delta hb0 hb1 hD0 hD1 hw
  obtain ⟨hkernel,hkernelBound⟩ := smallDelta_kernel_geometric_v2 p Delta jury hb0 hb1 hD0 hD1 hw
  have H := renewal_comparison (normalizedKernelLag p) (geomLag rho)
    (freeRisk p ⟨R,0,0⟩) (fun j => R*rho^j) (fun j => (p.trajectory ⟨R,0,0⟩ j).R) x
    u phi (90*Delta*R) (224*Delta) (2*(R+L))
    (normalized_kernel_lag_nonneg_v2 jury p hb0 hb1 hw0 hw1)
    (normalized_kernel_partial_mass_le_one_v2 jury p hb0 hb1 hw0 hw1)
    hu0 hu1 (by positivity) (by positivity) (by positivity) hkernel hkernelBound
    (smallDelta_freeRisk_geometric p Delta R hb0 hb1 hD0 hD1 hw hR) hx
    (normalized_trajectory_recurrence_v2 jury p ⟨R,0,0⟩ hb0 hb1 hw0 hw1)
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

/-- v2 `cor:tikhonov`, for every `ε ∈ (0,1]`: for `0 ≤ β < 1` (fixed momentum, plain SGD at
`β = 0` included), `Δ ≤ 1/8`, `w = Δ ε²`, and renormalized feedback `ũ ≤ 1 - margin`, the exact risk
trajectory stays within `C Δ (R + φ̃/(1-ũ))` of the learning profile on the clock `k w/ε`,
uniformly in `k`.  Constant `C = 538/margin + 8`. -/
theorem cor_tikhonov_v2 (margin : ℝ) (hm : 0 < margin) :
    ∃ Delta1 C : ℝ, 0 < Delta1 ∧ 0 < C ∧ ∀ (p : Params) (Delta R : ℝ),
      External.JuryStability → 0 ≤ p.beta → p.beta < 1 →
      0 < Delta → Delta ≤ Delta1 → p.w=smallDeltaW p.beta Delta → 0 ≤ R →
      0 ≤ p.renormNoise → p.renormNoise ≤ 1-margin → 0 ≤ p.renormAdditive →
      ∀ k : ℕ, |(p.trajectory ⟨R,0,0⟩ k).R-
        learningProfile p.renormNoise p.renormAdditive R ((k : ℝ)*(p.w/p.eps))| ≤
        C*Delta*(R+p.renormAdditive/(1-p.renormNoise)) := by
  refine ⟨1/8,538/margin+8,by norm_num,by positivity,?_⟩
  intro p Delta R jury hb0 hb1 hD0 hD1 hw hR hu0 hu hp k
  have hu1 : p.renormNoise < 1 := by linarith
  have H := smallDelta_trajectory_learningProfile_v2 p Delta R jury hb0 hb1 hD0 hD1 hw hR
    hu0 hu1 hp k
  refine H.trans ?_
  have hL : 0 ≤ p.renormAdditive/(1-p.renormNoise) := by positivity
  have hconst : 538/(1-p.renormNoise) ≤ 538/margin :=
    div_le_div_of_nonneg_left (by norm_num) hm (by linarith)
  gcongr

end
end SparseSGD
