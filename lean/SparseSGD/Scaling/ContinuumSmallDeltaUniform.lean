import SparseSGD.Scaling.ContinuumSmallDelta
open Filter Topology
namespace SparseSGD
noncomputable section
open Scaling
set_option maxHeartbeats 1600000

/-- Uniform convergence on the entire nonnegative learning clock, including
times tending to infinity as Delta tends to zero. -/
theorem continuum_smallDelta_tendstoUniformlyOn_learningClock (u phi R : ℝ)
    (jury : External.JuryStability) (hu0 : 0≤u) (hu1 : u<1) (hp : 0≤phi) (hR : 0≤R) :
    TendstoUniformlyOn (fun D t => (continuumFlow D u phi ⟨R,0,0⟩ (t/D)).R)
      (learningProfile u phi R) (𝓝[>] 0) (Set.Ici 0) := by
  let K := (538/(1-u)+8)*(R+phi/(1-u))
  have hden : 0<1-u := by linarith
  have hK : 0≤K := by dsimp [K]; positivity
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro e he
  have hcut : 0<e/(K+1) := div_pos he (by linarith)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_le_nhds (by norm_num : (0 : ℝ)<1/8)).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds hcut).filter_mono nhdsWithin_le_nhds] with D hD hD1 hDe
  have hD0 : 0<D := hD
  intro t ht
  have htime : 0≤t/D := div_nonneg ht hD0.le
  have H := continuum_smallDelta_learningProfile D u phi R jury hD0 hD1 hu0 hu1 hp hR (t/D) htime
  rw [mul_div_cancel₀ t hD0.ne'] at H
  have hprod : D*(K+1)<e := (lt_div_iff₀ (by linarith : 0<K+1)).mp hDe
  rw [Real.dist_eq,abs_sub_comm]
  apply H.trans_lt
  have hKD : K*D<e := by nlinarith
  convert hKD using 1 <;> dsimp [K] <;> ring
end
end SparseSGD
