import SparseSGD.Scaling.ContinuumSmallDeltaUniform
import SparseSGD.Scaling.WindowReconstruction
open Filter Topology
namespace SparseSGD
noncomputable section
open Scaling
set_option maxHeartbeats 1700000

/-- The cold-start large-Delta neighbor in both actual modal coordinates,
with an error uniform over all nonnegative times. -/
theorem continuum_largeDelta_cold_two_scale (margin D u phi R : ℝ)
    (hm : 0 < margin) (hD : 4≤D) (hu0 : 0≤u) (hu : u≤1-margin)
    (hp : 0≤phi) (hR : 0≤R) (hlarge : 1≤2*margin*D) (tau : ℝ) (ht : 0≤tau) :
    let omega := Real.sqrt (D-1/4)
    let error := 2*(48+4/margin)*(R+phi/(1-u))/Real.sqrt D
    |slowEnergy D (continuumFlow D u phi ⟨R,0,0⟩ tau)-
      (2*phi/(1-u)+(R-2*phi/(1-u))*Real.exp ((u-1)*tau))|≤error ∧
    ‖oscillatoryEnergy D (oscillatoryRoot omega) (continuumFlow D u phi ⟨R,0,0⟩ tau)-
      (R : ℂ)*Complex.exp (windowOscillatoryRate u omega*(tau : ℂ))‖≤error := by
  let omega := Real.sqrt (D-1/4)
  have ho : 0<omega := Real.sqrt_pos.mpr (by linarith)
  have hosq : omega^2=D-1/4 := Real.sq_sqrt (by linarith)
  have hs := coldMoments_psd R hR
  have Hslow := continuum_window_slow_bound D u phi omega margin ⟨R,0,0⟩ hD hm hu0 hu hp hs ho hosq hlarge tau ht
  have Hosc := continuum_window_osc_bound D u phi omega margin ⟨R,0,0⟩ hD hm hu0 hu hp hs ho hosq hlarge tau ht
  have hsize : windowSize D u phi ⟨R,0,0⟩=R+phi/(1-u) := by simp [windowSize]
  have hfloor : 0≤phi/(1-u) := div_nonneg hp (by linarith)
  have hN : 0≤R+phi/(1-u) := by linarith
  have hc : 0≤48+4/margin := by positivity
  have hfreq := window_inverse_frequency_bound D omega hD ho hosq
  have herror : (48+4/margin)*windowSize D u phi ⟨R,0,0⟩/omega ≤
      2*(48+4/margin)*(R+phi/(1-u))/Real.sqrt D := by
    rw [hsize]
    have H := mul_le_mul_of_nonneg_left hfreq (mul_nonneg hc hN)
    convert H using 1 <;> ring
  constructor
  · simpa only [windowSlowProfile,slowEnergy,mul_zero,add_zero,sub_zero] using Hslow.trans herror
  · simpa only [windowOscillatoryProfile,oscillatoryEnergy,Complex.ofReal_zero,mul_zero,sub_zero,add_zero] using Hosc.trans herror

/-- The explicit neighboring-window error tends to zero as Delta grows. -/
theorem continuum_largeDelta_error_tendsto (margin u phi R : ℝ) :
    Tendsto (fun D : ℝ => 2*(48+4/margin)*(R+phi/(1-u))/Real.sqrt D)
      atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
    (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul
      (2*(48+4/margin)*(R+phi/(1-u)))

/-- Source resonance part (iii), small-Delta side: actual all-time reduction
with a constant depending only on the fixed stability margin. -/
theorem cor_resonance_neighbor_small (margin : ℝ) (hm : 0 < margin)
    (jury : External.JuryStability) :
    ∃ C>0, ∀ D u phi R : ℝ, 0<D → D≤1/8 → 0≤u → u≤1-margin →
      0≤phi → 0≤R → ∀ tau≥0,
      |(continuumFlow D u phi ⟨R,0,0⟩ tau).R-learningProfile u phi R (D*tau)| ≤
        C*D*(R+phi/(1-u)) := by
  exact ⟨538/margin+8,by positivity,fun D u phi R hD hD1 hu0 hu hp hR tau ht =>
    continuum_smallDelta_uniform_bound margin D u phi R jury hm hD hD1 hu0 hu hp hR tau ht⟩

/-- Source resonance part (iii), large-Delta side: the actual two-scale
coordinates have an all-time O(Delta^(-1/2)) error from the cold start. -/
theorem cor_resonance_neighbor_large (margin : ℝ) (hm : 0 < margin) :
    ∃ D0 C : ℝ, 0<D0 ∧ 0<C ∧ ∀ D u phi R : ℝ,
      D0≤D → 0≤u → u≤1-margin → 0≤phi → 0≤R → ∀ tau≥0,
      let omega := Real.sqrt (D-1/4)
      let error := C*(R+phi/(1-u))/Real.sqrt D
      |slowEnergy D (continuumFlow D u phi ⟨R,0,0⟩ tau)-
        (2*phi/(1-u)+(R-2*phi/(1-u))*Real.exp ((u-1)*tau))|≤error ∧
      ‖oscillatoryEnergy D (oscillatoryRoot omega) (continuumFlow D u phi ⟨R,0,0⟩ tau)-
        (R : ℂ)*Complex.exp (windowOscillatoryRate u omega*(tau : ℂ))‖≤error := by
  refine ⟨max 4 (1/(2*margin)),2*(48+4/margin),lt_max_of_lt_left (by norm_num),by positivity,?_⟩
  intro D u phi R hD hu0 hu hp hR tau ht
  have hD4 := (le_max_left 4 (1/(2*margin))).trans hD
  have hlarge : 1≤2*margin*D := by
    have H := (le_max_right 4 (1/(2*margin))).trans hD
    simpa [mul_comm] using (div_le_iff₀ (by positivity : 0<2*margin)).mp H
  exact continuum_largeDelta_cold_two_scale margin D u phi R hm hD4 hu0 hu hp hR hlarge tau ht

/-- Both window coordinate errors vanish uniformly over the entire
nonnegative time axis, despite the Delta-dependent oscillation frequency. -/
theorem continuum_largeDelta_cold_uniform_errors (margin u phi R : ℝ)
    (hm : 0 < margin) (hu0 : 0≤u) (hu : u≤1-margin) (hp : 0≤phi) (hR : 0≤R) :
    TendstoUniformlyOn
      (fun D tau => slowEnergy D (continuumFlow D u phi ⟨R,0,0⟩ tau)-
        (2*phi/(1-u)+(R-2*phi/(1-u))*Real.exp ((u-1)*tau)))
      (fun _ => 0) atTop (Set.Ici 0) ∧
    TendstoUniformlyOn
      (fun D tau => oscillatoryEnergy D (oscillatoryRoot (Real.sqrt (D-1/4)))
        (continuumFlow D u phi ⟨R,0,0⟩ tau)-
        (R : ℂ)*Complex.exp (windowOscillatoryRate u (Real.sqrt (D-1/4))*(tau : ℂ)))
      (fun _ => 0) atTop (Set.Ici 0) := by
  have herror := continuum_largeDelta_error_tendsto margin u phi R
  have hlarge : ∀ᶠ D : ℝ in atTop, 4≤D ∧ 1≤2*margin*D := by
    filter_upwards [eventually_ge_atTop (max 4 (1/(2*margin)))] with D hD
    refine ⟨(le_max_left _ _).trans hD,?_⟩
    have H := (le_max_right 4 (1/(2*margin))).trans hD
    simpa [mul_comm] using (div_le_iff₀ (by positivity : 0<2*margin)).mp H
  constructor
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro e he
    filter_upwards [hlarge,herror.eventually (eventually_lt_nhds he)] with D hD hE
    intro tau ht
    have H := (continuum_largeDelta_cold_two_scale margin D u phi R hm hD.1 hu0 hu hp hR hD.2 tau ht).1
    simpa only [Real.dist_eq,zero_sub,abs_neg] using H.trans_lt hE
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro e he
    filter_upwards [hlarge,herror.eventually (eventually_lt_nhds he)] with D hD hE
    intro tau ht
    have H := (continuum_largeDelta_cold_two_scale margin D u phi R hm hD.1 hu0 hu hp hR hD.2 tau ht).2
    simpa only [dist_zero_left] using H.trans_lt hE


/-- The cold continuum risk itself has the two-scale window expansion,
with a uniform O(Delta^(-1/2)) error. -/
theorem continuum_largeDelta_cold_risk (margin D u phi R : ℝ)
    (hm : 0 < margin) (hD : 4≤D) (hu0 : 0≤u) (hu : u≤1-margin)
    (hp : 0≤phi) (hR : 0≤R) (hlarge : 1≤2*margin*D) (tau : ℝ) (ht : 0≤tau) :
    |(continuumFlow D u phi ⟨R,0,0⟩ tau).R-
      ((2*phi/(1-u)+(R-2*phi/(1-u))*Real.exp ((u-1)*tau))/2+
        ((R : ℂ)*Complex.exp (windowOscillatoryRate u (Real.sqrt (D-1/4))*(tau : ℂ))).re/2)| ≤
      (4*(48+4/margin)+16)*(R+phi/(1-u))/Real.sqrt D := by
  let omega := Real.sqrt (D-1/4)
  let N := R+phi/(1-u)
  let C := 48+4/margin
  have ho : 0<omega := Real.sqrt_pos.mpr (by linarith)
  have hosq : omega^2=D-1/4 := Real.sq_sqrt (by linarith)
  have hN : 0≤N := by dsimp [N]; exact add_nonneg hR (div_nonneg hp (by linarith))
  have hC : 0<C := by dsimp [C]; positivity
  have hs := coldMoments_psd R hR
  have hsize : windowSize D u phi ⟨R,0,0⟩=N := by simp [windowSize,N]
  have HS := continuum_window_slow_bound D u phi omega margin ⟨R,0,0⟩ hD hm hu0 hu hp hs ho hosq hlarge tau ht
  have HZ := continuum_window_osc_bound D u phi omega margin ⟨R,0,0⟩ hD hm hu0 hu hp hs ho hosq hlarge tau ht
  rw [hsize] at HS HZ
  obtain ⟨HSB,HZB⟩ := window_profile_bounds D u phi omega ⟨R,0,0⟩ hD hu0 (by linarith) hp hs ho hosq tau ht
  rw [hsize] at HSB HZB
  have H := window_risk_reconstruction_error D omega N (C*N/omega)
    (windowSlowProfile D u phi ⟨R,0,0⟩ tau) (windowOscillatoryProfile D u omega ⟨R,0,0⟩ tau)
    (continuumFlow D u phi ⟨R,0,0⟩ tau) hD ho hosq hN (by positivity) HS HZ HSB HZB
  have hfreq := window_inverse_frequency_bound D omega hD ho hosq
  have hE : 2*(C*N/omega)+8*N/omega≤(4*C+16)*N/Real.sqrt D := by
    calc
      _ = (2*C+8)*N*(1/omega) := by ring
      _ ≤ (2*C+8)*N*(2/Real.sqrt D) := mul_le_mul_of_nonneg_left hfreq (by positivity)
      _ = _ := by ring
  simpa [windowSlowProfile,slowEnergy,windowOscillatoryProfile,oscillatoryEnergy,C,omega,N] using H.trans hE

/-- Uniform convergence of the full two-scale risk error on all forward times. -/
theorem continuum_largeDelta_cold_risk_uniform (margin u phi R : ℝ)
    (hm : 0 < margin) (hu0 : 0≤u) (hu : u≤1-margin) (hp : 0≤phi) (hR : 0≤R) :
    TendstoUniformlyOn
      (fun D tau => (continuumFlow D u phi ⟨R,0,0⟩ tau).R-
        ((2*phi/(1-u)+(R-2*phi/(1-u))*Real.exp ((u-1)*tau))/2+
          ((R : ℂ)*Complex.exp (windowOscillatoryRate u (Real.sqrt (D-1/4))*(tau : ℂ))).re/2))
      (fun _ => 0) atTop (Set.Ici 0) := by
  have herror : Tendsto (fun D : ℝ => (4*(48+4/margin)+16)*(R+phi/(1-u))/Real.sqrt D)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul
        ((4*(48+4/margin)+16)*(R+phi/(1-u)))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro e he
  filter_upwards [eventually_ge_atTop (max 4 (1/(2*margin))),
    herror.eventually (eventually_lt_nhds he)] with D hD hE
  intro tau ht
  have hD4 := (le_max_left 4 (1/(2*margin))).trans hD
  have hlarge : 1≤2*margin*D := by
    have H := (le_max_right 4 (1/(2*margin))).trans hD
    simpa [mul_comm] using (div_le_iff₀ (by positivity : 0<2*margin)).mp H
  have H := continuum_largeDelta_cold_risk margin D u phi R hm hD4 hu0 hu hp hR hlarge tau ht
  simpa only [Real.dist_eq,zero_sub,abs_neg] using H.trans_lt hE

/-- Source resonance (iii): the actual continuum flow contains both neighboring
cells, uniformly on the full nonnegative time axis in their respective clocks. -/
theorem cor_resonance_neighboring_limits (u phi R : ℝ) (jury : External.JuryStability)
    (hu0 : 0≤u) (hu1 : u<1) (hp : 0≤phi) (hR : 0≤R) :
    TendstoUniformlyOn (fun D t => (continuumFlow D u phi ⟨R,0,0⟩ (t/D)).R)
      (learningProfile u phi R) (𝓝[>] 0) (Set.Ici 0) ∧
    TendstoUniformlyOn
      (fun D tau => (continuumFlow D u phi ⟨R,0,0⟩ tau).R-
        ((2*phi/(1-u)+(R-2*phi/(1-u))*Real.exp ((u-1)*tau))/2+
          ((R : ℂ)*Complex.exp (windowOscillatoryRate u (Real.sqrt (D-1/4))*(tau : ℂ))).re/2))
      (fun _ => 0) atTop (Set.Ici 0) := by
  have hm : 0<(1-u)/2 := by linarith
  have hu : u≤1-(1-u)/2 := by linarith
  exact ⟨continuum_smallDelta_tendstoUniformlyOn_learningClock u phi R jury hu0 hu1 hp hR,
    continuum_largeDelta_cold_risk_uniform ((1-u)/2) u phi R hm hu0 hu hp hR⟩

end
end SparseSGD
