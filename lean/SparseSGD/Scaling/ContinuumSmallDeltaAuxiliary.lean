import SparseSGD.Scaling.ColdRegular
import SparseSGD.Scaling.Tikhonov

open Filter Topology
namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1600000

def continuumAuxBase (D tau : ℝ) (n : ℕ) : Params :=
  let beta := Real.exp (-tau/((n+1 : ℕ) : ℝ))
  ⟨beta,D*(1-beta)^2,0,0⟩

def continuumAuxParams (D u phi tau : ℝ) (n : ℕ) : Params :=
  let p := continuumAuxBase D tau n
  {p with noise := (1-p.curvature)*u, additive := (1-p.curvature)*phi}

theorem continuumAux_step_clock (D u phi tau : ℝ) (n : ℕ) :
    ((n+1 : ℕ) : ℝ)*(continuumAuxParams D u phi tau n).matchedStep=tau := by
  simp only [continuumAuxParams,continuumAuxBase,Params.matchedStep,Real.log_exp]
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem continuumAux_beta_lt_one (D u phi tau : ℝ) (ht : 0<tau) (n : ℕ) :
    (continuumAuxParams D u phi tau n).beta<1 := by
  apply Real.exp_lt_one_iff.mpr
  exact div_neg_of_neg_of_pos (neg_neg_of_pos ht) (by positivity)

theorem continuumAux_raw_delta (D u phi tau : ℝ) (n : ℕ) :
    (continuumAuxParams D u phi tau n).w=D*(continuumAuxParams D u phi tau n).eps^2 := rfl

theorem continuumAux_renorm (D u phi tau : ℝ) (n : ℕ)
    (hc : (continuumAuxParams D u phi tau n).curvature≠1) :
    (continuumAuxParams D u phi tau n).renormNoise=u ∧
      (continuumAuxParams D u phi tau n).renormAdditive=phi := by
  have hc0 : 1-(continuumAuxBase D tau n).curvature≠0 := by
    change (continuumAuxBase D tau n).curvature≠1 at hc
    exact sub_ne_zero.mpr (Ne.symm hc)
  constructor <;> simp only [continuumAuxParams,Params.renormNoise,Params.renormAdditive]
  · change (1-(continuumAuxBase D tau n).curvature)*u/(1-(continuumAuxBase D tau n).curvature)=u
    exact mul_div_cancel_left₀ u hc0
  · change (1-(continuumAuxBase D tau n).curvature)*phi/(1-(continuumAuxBase D tau n).curvature)=phi
    exact mul_div_cancel_left₀ phi hc0

theorem continuumAux_step_tendsto_zero (D u phi tau : ℝ) :
    Tendsto (fun n => (continuumAuxParams D u phi tau n).eps) atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop := by
    simpa [Function.comp_def] using (tendsto_natCast_atTop_atTop (R:=ℝ)).comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun n : ℕ => -tau/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hden
  have hb := Real.continuous_exp.continuousAt.tendsto.comp ht
  simpa [continuumAuxParams,continuumAuxBase,Params.eps] using (tendsto_const_nhds (x:=(1:ℝ))).sub hb

theorem continuumAux_beta_tendsto_one (D u phi tau : ℝ) :
    Tendsto (fun n => (continuumAuxParams D u phi tau n).beta) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x:=(1:ℝ))).sub (continuumAux_step_tendsto_zero D u phi tau)
  simpa [Params.eps] using h

theorem continuumAux_learning_clock_tendsto (D u phi tau : ℝ) (ht : 0<tau) :
    Tendsto (fun n => ((n+1 : ℕ) : ℝ)*
      ((continuumAuxParams D u phi tau n).w/(continuumAuxParams D u phi tau n).eps))
      atTop (𝓝 (D*tau)) := by
  let x := fun n : ℕ => tau/((n+1 : ℕ) : ℝ)
  have hden : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop := by
    simpa [Function.comp_def] using (tendsto_natCast_atTop_atTop (R:=ℝ)).comp (tendsto_add_atTop_nat 1)
  have hx : Tendsto x atTop (𝓝 0) := tendsto_const_nhds.div_atTop hden
  have hxp : Tendsto x atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hx,Filter.Eventually.of_forall (fun n => div_pos ht (by positivity))⟩
  have hd : HasDerivAt (fun t : ℝ => 1-Real.exp (-t)) 1 0 := by
    have hg : HasDerivAt (fun t : ℝ => -t) (-1) 0 := (hasDerivAt_id (0:ℝ)).neg
    have he : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1) 0 := by
      convert (Real.hasDerivAt_exp (-(0:ℝ))).comp (0:ℝ) hg using 1 <;> simp [Function.comp_def]
    simpa using he.const_sub (1:ℝ)
  have hratio := hd.tendsto_slope_zero_right.comp hxp
  have hscale := hratio.const_mul (D*tau)
  convert hscale using 1
  · funext n
    have hn : ((n+1 : ℕ) : ℝ)≠0 := by positivity
    have he : (continuumAuxParams D u phi tau n).eps≠0 := by
      have hb := continuumAux_beta_lt_one D u phi tau ht n
      unfold Params.eps
      linarith
    dsimp [continuumAuxParams,continuumAuxBase,Params.eps,x] at he ⊢
    simp only [zero_add,neg_zero,Real.exp_zero,sub_self]
    field_simp [he,hn,ht.ne']
    ring
  · simp
end
end SparseSGD

namespace SparseSGD
noncomputable section
/-- The auxiliary chains satisfy the actual raw and normalized hypotheses
of both the regular approximation and the discrete Tikhonov estimate. -/
theorem continuumAux_conditions (D u phi tau eps0 : ℝ)
    (hD : 0<D) (hD1 : D≤1/8) (ht : 0<tau) (heps0 : 0<eps0) :
    ∀ᶠ n in atTop,
      let p := continuumAuxParams D u phi tau n
      1/2≤p.beta ∧ p.beta<1 ∧ 0<p.w ∧ p.w≤1/16 ∧ p.eps≤eps0 ∧
        p.curvature<1 ∧ p.renormNoise=u ∧ p.renormAdditive=phi := by
  have he := continuumAux_step_tendsto_zero D u phi tau
  have hb := continuumAux_beta_tendsto_one D u phi tau
  have hw : Tendsto (fun n => (continuumAuxParams D u phi tau n).w) atTop (𝓝 0) := by
    convert (he.pow 2).const_mul D using 1
    · funext n
      exact continuumAux_raw_delta D u phi tau n
    · simp
  filter_upwards [hb.eventually (eventually_ge_nhds (by norm_num : (1/2 : ℝ)<1)),
    he.eventually (eventually_le_nhds heps0),
    hw.eventually (eventually_le_nhds (by norm_num : (0 : ℝ)<1/16))]
    with n hbn hen hwn
  let p := continuumAuxParams D u phi tau n
  have hb1 := continuumAux_beta_lt_one D u phi tau ht n
  have hwp : p.w=smallDeltaW p.beta D := rfl
  obtain ⟨hw0,hw1,hc0,hc1⟩ := smallDelta_kernel_parameters p D hbn hb1 hD hD1 hwp
  obtain ⟨hnu,hph⟩ := continuumAux_renorm D u phi tau n (by linarith : p.curvature≠1)
  exact ⟨hbn,hb1,hw0,hwn,hen,hc1,hnu,hph⟩
end
end SparseSGD
