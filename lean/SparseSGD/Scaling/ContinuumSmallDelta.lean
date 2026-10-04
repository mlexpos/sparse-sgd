import SparseSGD.Scaling.ContinuumSmallDeltaAuxiliary
open Filter Topology
namespace SparseSGD
noncomputable section
open Scaling
set_option maxHeartbeats 1800000

theorem continuumAux_risk_tendsto (D u phi R tau : ℝ) (jury : External.JuryStability)
    (hD : 0<D) (hD1 : D≤1/8) (hu0 : 0≤u) (hu1 : u<1)
    (hp : 0≤phi) (hR : 0≤R) (ht : 0<tau) :
    Tendsto (fun n => ((continuumAuxParams D u phi tau n).trajectory ⟨R,0,0⟩ (n+1)).R)
      atTop (𝓝 ((continuumFlow D u phi ⟨R,0,0⟩ tau).R)) := by
  let margin := (1-u)/2
  have hm : 0 < margin := by dsimp [margin]; linarith
  have huM : u≤1-margin := by dsimp [margin]; linarith
  obtain ⟨eps0,heps0,C,hC,H⟩ := regular_cold_raw_rate D margin hD hm
  let risk := fun n => ((continuumAuxParams D u phi tau n).trajectory ⟨R,0,0⟩ (n+1)).R
  let target := (continuumFlow D u phi ⟨R,0,0⟩ tau).R
  have hb : ∀ᶠ n in atTop,
      |risk n-target|≤C*(continuumAuxParams D u phi tau n).eps*(R+phi+1) := by
    filter_upwards [continuumAux_conditions D u phi tau eps0 hD hD1 ht heps0]
      with n hn
    rcases hn with ⟨hb0,hb1,hw0,hw1,heps,hc,hn,hp'⟩
    have HH := H (continuumAuxParams D u phi tau n) R u phi hb0 hb1 hw0 hw1
      (continuumAux_raw_delta D u phi tau n) heps jury hR (by rwa [hn])
      (by rwa [hn]) hu0 huM (by rwa [hp']) (n+1)
    rw [continuumAux_step_clock D u phi tau n] at HH
    simpa [risk,target,hn,hp'] using HH
  have hupper : Tendsto (fun n => C*(continuumAuxParams D u phi tau n).eps*(R+phi+1))
      atTop (𝓝 0) := by
    simpa using ((continuumAux_step_tendsto_zero D u phi tau).const_mul C).mul_const (R+phi+1)
  have habs : Tendsto (fun n => |risk n-target|) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x:=(0:ℝ))) hupper
      (Filter.Eventually.of_forall (fun n => abs_nonneg (risk n-target))) hb
  have hd : Tendsto (fun n => dist target (risk n)) atTop (𝓝 0) := by
    simpa only [Real.dist_eq,abs_sub_comm] using habs
  exact (tendsto_const_nhds (x:=target)).congr_dist hd

/-- Genuine continuum Tikhonov bound, uniform over every nonnegative time.
It follows by taking a proved regular limit of the actual discrete estimate. -/
theorem continuum_smallDelta_learningProfile (D u phi R : ℝ) (jury : External.JuryStability)
    (hD : 0<D) (hD1 : D≤1/8) (hu0 : 0≤u) (hu1 : u<1)
    (hp : 0≤phi) (hR : 0≤R) (tau : ℝ) (ht : 0≤tau) :
    |(continuumFlow D u phi ⟨R,0,0⟩ tau).R-learningProfile u phi R (D*tau)| ≤
      (538/(1-u)+8)*D*(R+phi/(1-u)) := by
  have hden : 0<1-u := by linarith
  by_cases hz : tau=0
  · subst tau
    simp only [continuumFlow_initial,mul_zero,learningProfile_initial,sub_self,abs_zero]
    positivity
  have ht0 : 0<tau := lt_of_le_of_ne ht (Ne.symm hz)
  have hrisk := continuumAux_risk_tendsto D u phi R tau jury hD hD1 hu0 hu1 hp hR ht0
  have htime := continuumAux_learning_clock_tendsto D u phi tau ht0
  have hprofile : Tendsto (fun n => learningProfile u phi R
      (((n+1 : ℕ) : ℝ)*((continuumAuxParams D u phi tau n).w/
        (continuumAuxParams D u phi tau n).eps))) atTop (𝓝 (learningProfile u phi R (D*tau))) :=
    (learningProfile_hasDerivAt u phi R (D*tau) (by linarith)).continuousAt.tendsto.comp htime
  apply le_of_tendsto (hrisk.sub hprofile).abs
  filter_upwards [continuumAux_conditions D u phi tau 1 hD hD1 ht0 (by norm_num)] with n hn
  rcases hn with ⟨hb0,hb1,hw0,hw1,heps,hc,hn,hp'⟩
  have HH := smallDelta_trajectory_learningProfile (continuumAuxParams D u phi tau n) D R jury
    hb0 hb1 hD hD1 rfl hR (by rwa [hn]) (by rwa [hn]) (by rwa [hp']) (n+1)
  simpa only [hn,hp'] using HH

/-- Explicit stability-margin form of the all-time continuum reduction. -/
theorem continuum_smallDelta_uniform_bound (margin D u phi R : ℝ)
    (jury : External.JuryStability) (hm : 0 < margin) (hD : 0<D) (hD1 : D≤1/8)
    (hu0 : 0≤u) (hu : u≤1-margin) (hp : 0≤phi) (hR : 0≤R)
    (tau : ℝ) (ht : 0≤tau) :
    |(continuumFlow D u phi ⟨R,0,0⟩ tau).R-learningProfile u phi R (D*tau)| ≤
      (538/margin+8)*D*(R+phi/(1-u)) := by
  have hu1 : u<1 := by linarith
  have hL : 0≤phi/(1-u) := div_nonneg hp (by linarith)
  apply (continuum_smallDelta_learningProfile D u phi R jury hD hD1 hu0 hu1 hp hR tau ht).trans
  have hc : 538/(1-u)≤538/margin := div_le_div_of_nonneg_left (by norm_num) hm (by linarith)
  gcongr
end
end SparseSGD
