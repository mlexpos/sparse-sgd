import SparseSGD.Scaling.SmallDeltaFormulas
import SparseSGD.Scaling.GeometricKernel

namespace SparseSGD
open Scaling
noncomputable section
set_option maxHeartbeats 1000000

/-- Signed geometric weights in the exact small-Delta kernel. -/
def smallKernelWeight (K q : ℝ) : ℝ := K*q/(1-q)

theorem weighted_geomLag (K q : ℝ) (hq : q ≠ 1) (n : ℕ) :
    smallKernelWeight K q*geomLag q (n+1)=K*q^(n+1) := by
  simp only [smallKernelWeight,geomLag,pow_succ]
  field_simp
  <;> ring

theorem normalizedKernelLag_geometric (p : Params) (a b : ℝ)
    (hab : a ≠ b) (hsum : a+b=1+p.beta-p.w) (hprod : a*b=p.beta)
    (ha : a^2 ≠ 1) (hb : b^2 ≠ 1) (hbeta : p.beta ≠ 1) (n : ℕ) :
    let K := (1-p.curvature)*2*p.w*p.eps/(a-b)^2
    normalizedKernelLag p n = smallKernelWeight K (a^2)*geomLag (a^2) n-
      2*smallKernelWeight K p.beta*geomLag p.beta n+
      smallKernelWeight K (b^2)*geomLag (b^2) n := by
  dsimp only
  cases n with
  | zero => simp [normalizedKernelLag,geomLag]
  | succ n =>
    rw [normalizedKernelLag_distinct_roots p a b hab hsum hprod,
      show 2*smallKernelWeight ((1-p.curvature)*2*p.w*p.eps/(a-b)^2) p.beta*geomLag p.beta (n+1)=
        2*(smallKernelWeight ((1-p.curvature)*2*p.w*p.eps/(a-b)^2) p.beta*geomLag p.beta (n+1)) by ring,
      weighted_geomLag _ _ ha,weighted_geomLag _ _ hbeta,weighted_geomLag _ _ hb,←hprod,mul_pow]
    rw [←pow_mul,←pow_mul]
    ring

theorem smallDelta_kernel_parameters (p : Params) (Delta : ℝ)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1) (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8)
    (hw : p.w=smallDeltaW p.beta Delta) :
    0 < p.w ∧ p.w < 2*(1+p.beta) ∧ 0 ≤ p.curvature ∧ p.curvature < 1 := by
  have he : 0 < 1-p.beta := by linarith
  have he1 : 1-p.beta ≤ 1 := by linarith
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

theorem smallDelta_fast_weights (p : Params) (Delta : ℝ)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1) (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8)
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
    smallDeltaSpectrum_strong p.beta Delta (by linarith) hb1 hD0 hD1
  have he : 0 < p.eps := by dsimp [Params.eps]; linarith
  have hgap' : p.eps/2 ≤ a-b := hgap
  have hgap0 : 0 < a-b := by linarith
  have hs : p.eps^2/4 ≤ (a-b)^2 := by nlinarith
  obtain ⟨hw0,_,hc0,hc1⟩ := smallDelta_kernel_parameters p Delta hb0 hb1 hD0 hD1 hw
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
    positivity
  have hbweight : smallKernelWeight K p.beta ≤ 8*Delta := by
    apply (div_le_iff₀ (show 0<1-p.beta by linarith)).mpr
    have H := mul_le_mul_of_nonneg_left hb1.le hK0
    dsimp [Params.eps] at hK
    nlinarith
  have hsqweight0 : 0 ≤ smallKernelWeight K (b^2) := by
    dsimp [smallKernelWeight]
    positivity
  have hsqweight : smallKernelWeight K (b^2) ≤ 16*Delta := by
    apply (div_le_iff₀ (show 0<1-b^2 by linarith)).mpr
    have H := mul_le_mul_of_nonneg_left hbsq.le hK0
    have H2 := mul_le_mul_of_nonneg_left hbfast (show 0≤16*Delta by positivity)
    nlinarith only [hK,H,H2]
  exact ⟨hK0,hK,hbweight0,hbweight,hsqweight0,hsqweight⟩

/-- A normalized signed mixture with small nonleading coefficients is close in
absolute sum to its leading geometric law. -/
theorem signed_geom_mixture_bound (h : ℕ → ℝ) (q r s A B C : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmass : HasSum h 1)
    (hform : ∀ n, h n=A*geomLag q n-B*geomLag r n+C*geomLag s n) :
    Summable (fun n => |h n-geomLag q n|) ∧
    ∑' n, |h n-geomLag q n| ≤ 2*(B+C) := by
  have Hq := geomLag_hasSum_one q hq0 hq1
  have Hr := geomLag_hasSum_one r hr0 hr1
  have Hs := geomLag_hasSum_one s hs0 hs1
  have H : HasSum h (A-B+C) := by
    convert ((Hq.mul_left A).sub (Hr.mul_left B)).add (Hs.mul_left C) using 1
    · ext n
      exact hform n
    · ring
  have hid : A-B+C=1 := H.unique hmass
  let major := fun n => |A-1| *geomLag q n+B*geomLag r n+C*geomLag s n
  have Hmajor : HasSum major (|A-1|+B+C) := by
    convert ((Hq.mul_left |A-1|).add (Hr.mul_left B)).add (Hs.mul_left C) using 1 <;> simp [major]
  have hpoint (n : ℕ) : |h n-geomLag q n| ≤ major n := by
    have hq := geomLag_nonneg q hq0 hq1 n
    have hr := geomLag_nonneg r hr0 hr1 n
    have hs := geomLag_nonneg s hs0 hs1 n
    rw [hform]
    have heq : A*geomLag q n-B*geomLag r n+C*geomLag s n-geomLag q n=
      (A-1)*geomLag q n-B*geomLag r n+C*geomLag s n := by ring
    rw [heq]
    calc
      _ ≤ |(A-1)*geomLag q n-B*geomLag r n|+|C*geomLag s n| := abs_add_le _ _
      _ ≤ (|(A-1)*geomLag q n|+|B*geomLag r n|)+|C*geomLag s n| := by gcongr; exact abs_sub _ _
      _ = major n := by simp [major,abs_mul,abs_of_nonneg hq,abs_of_nonneg hr,abs_of_nonneg hs,abs_of_nonneg hB,abs_of_nonneg hC]
  have habs := Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpoint Hmajor.summable
  refine ⟨habs,?_⟩
  calc
    _ ≤ ∑' n, major n := habs.tsum_le_tsum hpoint Hmajor.summable
    _ = |A-1|+B+C := Hmajor.tsum_eq
    _ ≤ 2*(B+C) := by
      have hh : |A-1| ≤ B+C := abs_le.mpr ⟨by linarith,by linarith⟩
      linarith

/-- The actual normalized impulse kernel is within 64 Delta of its slow
geometric component, uniformly in the retention parameter. -/
theorem smallDelta_kernel_slow_geometric (p : Params) (Delta : ℝ)
    (jury : External.JuryStability)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1) (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8)
    (hw : p.w=smallDeltaW p.beta Delta) :
    Summable (fun n => |normalizedKernelLag p n-geomLag ((smallDeltaLambdaPlus p.beta Delta)^2) n|) ∧
    ∑' n, |normalizedKernelLag p n-geomLag ((smallDeltaLambdaPlus p.beta Delta)^2) n| ≤ 64*Delta := by
  let a := smallDeltaLambdaPlus p.beta Delta
  let b := smallDeltaLambdaMinus p.beta Delta
  let K := (1-p.curvature)*2*p.w*p.eps/(a-b)^2
  obtain ⟨_,hgap,hbpos,_,hapos,ha1,_,hprod,hsum,_⟩ :=
    smallDeltaSpectrum_strong p.beta Delta (by linarith) hb1 hD0 hD1
  have hab : a ≠ b := by
    intro h
    change a-b≥(1-p.beta)/2 at hgap
    rw [h] at hgap
    linarith
  have hb1' : b < 1 := by change a-b≥(1-p.beta)/2 at hgap; change a<1 at ha1; linarith
  have ha : a^2 < 1 := by change 0<a at hapos; change a<1 at ha1; nlinarith
  have hb : b^2 < 1 := by change 0≤b at hbpos; nlinarith
  obtain ⟨hw0,hw1,_,_⟩ := smallDelta_kernel_parameters p Delta hb0 hb1 hD0 hD1 hw
  have hsum' : a+b=1+p.beta-p.w := by rw [hw]; exact hsum
  obtain ⟨_,_,hB,hBb,hC,hCb⟩ := smallDelta_fast_weights p Delta hb0 hb1 hD0 hD1 hw
  have H := signed_geom_mixture_bound (normalizedKernelLag p) (a^2) p.beta (b^2)
    (smallKernelWeight K (a^2)) (2*smallKernelWeight K p.beta) (smallKernelWeight K (b^2))
    (sq_nonneg a) ha (by linarith) hb1 (sq_nonneg b) hb (by positivity) hC
    (normalized_kernel_lag_hasSum jury p hb0 hb1 hw0 hw1)
    (normalizedKernelLag_geometric p a b hab hsum' hprod (ne_of_lt ha) (ne_of_lt hb) (ne_of_lt hb1))
  refine ⟨H.1,H.2.trans ?_⟩
  change smallKernelWeight K p.beta ≤ 8*Delta at hBb
  change smallKernelWeight K (b^2) ≤ 16*Delta at hCb
  linarith

end
end SparseSGD
