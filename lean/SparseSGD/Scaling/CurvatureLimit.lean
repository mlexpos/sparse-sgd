import SparseSGD.Scaling.Window
import SparseSGD.Discrete.Loads

open Filter Topology
namespace SparseSGD
noncomputable section

theorem curvature_matchedStep_tendsto (p : ℕ → Params)
    (hb : Tendsto (fun n => (p n).beta) atTop (𝓝 1)) :
    Tendsto (fun n => (p n).matchedStep) atTop (𝓝 0) := by
  simpa [Params.matchedStep] using (hb.log (by norm_num : (1 : ℝ) ≠ 0)).neg

theorem curvature_traceCosine_tendsto (p : ℕ → Params) (w : ℝ)
    (hb : Tendsto (fun n => (p n).beta) atTop (𝓝 1))
    (hw : Tendsto (fun n => (p n).w) atTop (𝓝 w)) :
    Tendsto (fun n => (p n).traceCosine) atTop (𝓝 (1-w/2)) := by
  have h := ((hb.const_add 1).sub hw).div
    (tendsto_const_nhds.mul hb.sqrt) (by norm_num : (2 : ℝ)*Real.sqrt 1 ≠ 0)
  convert h using 1
  · rfl
  · norm_num
    ring

theorem curvature_foldedAngle_tendsto (p : ℕ → Params) (w : ℝ)
    (hb : Tendsto (fun n => (p n).beta) atTop (𝓝 1))
    (hw : Tendsto (fun n => (p n).w) atTop (𝓝 w)) :
    Tendsto (fun n => (p n).foldedAngle) atTop (𝓝 (Real.arccos |1-w/2|)) :=
  Real.continuous_arccos.continuousAt.tendsto.comp (curvature_traceCosine_tendsto p w hb hw).abs

theorem curvature_load_tendsto (p : ℕ → Params) (w : ℝ)
    (hb : Tendsto (fun n => (p n).beta) atTop (𝓝 1))
    (hw : Tendsto (fun n => (p n).w) atTop (𝓝 w)) :
    Tendsto (fun n => (p n).curvature) atTop (𝓝 (w/4)) := by
  convert hw.div (tendsto_const_nhds.mul (hb.const_add 1))
    (by norm_num : (2 : ℝ)*(1+1) ≠ 0) using 1
  · rfl
  · norm_num

theorem curvature_noise_tendsto (p : ℕ → Params) (w u : ℝ)
    (hb : Tendsto (fun n => (p n).beta) atTop (𝓝 1))
    (hw : Tendsto (fun n => (p n).w) atTop (𝓝 w))
    (hu : Tendsto (fun n => (p n).noise) atTop (𝓝 u)) (hw4 : w < 4) :
    Tendsto (fun n => (p n).renormNoise) atTop (𝓝 (u/(1-w/4))) :=
  hu.div (tendsto_const_nhds.sub (curvature_load_tendsto p w hb hw)) (by linarith)

theorem curvature_eventually_underdamped (p : ℕ → Params) (w : ℝ)
    (hb : Tendsto (fun n => (p n).beta) atTop (𝓝 1))
    (hw : Tendsto (fun n => (p n).w) atTop (𝓝 w)) (hw0 : 0 < w) (hw4 : w < 4) :
    ∀ᶠ n in atTop, |(p n).traceCosine| < 1 := by
  have hstar : |1-w/2| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
  exact (curvature_traceCosine_tendsto p w hb hw).abs.eventually (gt_mem_nhds hstar)

theorem curvature_angle_limit_pos (w : ℝ) (hw0 : 0 < w) (hw4 : w < 4) :
    0 < Real.arccos |1-w/2| :=
  Real.arccos_pos.mpr (abs_lt.mpr ⟨by linarith,by linarith⟩)

/-- The rescaled matched curvature has a positive finite limit. This is the
precise constant behind the source's comparison with the inverse squared step. -/
theorem curvature_scaledDelta_tendsto (p : ℕ → Params) (w : ℝ)
    (hb : Tendsto (fun n => (p n).beta) atTop (𝓝 1))
    (hw : Tendsto (fun n => (p n).w) atTop (𝓝 w)) (hw0 : 0 < w) (hw4 : w < 4)
    (hb1 : ∀ᶠ n in atTop, (p n).beta < 1) :
    Tendsto (fun n => (p n).matchedDelta*(p n).matchedStep^2)
      atTop (𝓝 ((Real.arccos |1-w/2|)^2)) := by
  have hh := curvature_matchedStep_tendsto p hb
  have ha := curvature_foldedAngle_tendsto p w hb hw
  have h := (hh.pow 2).const_mul (1/4 : ℝ) |>.add (ha.pow 2)
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero,zero_add] at h
  apply h.congr'
  filter_upwards [curvature_eventually_underdamped p w hb hw hw0 hw4,hb1,
    hb.eventually (lt_mem_nhds (show (0 : ℝ)<1 by norm_num))] with n hc hb1 hb0
  have hs := (p n).matchedStep_pos hb0 hb1
  simp only [Params.matchedDelta,hc.le,ite_true]
  field_simp

theorem curvature_matchedDelta_tendsto_atTop (p : ℕ → Params) (w : ℝ)
    (hb : Tendsto (fun n => (p n).beta) atTop (𝓝 1))
    (hw : Tendsto (fun n => (p n).w) atTop (𝓝 w)) (hw0 : 0 < w) (hw4 : w < 4)
    (hb1 : ∀ᶠ n in atTop, (p n).beta < 1) :
    Tendsto (fun n => (p n).matchedDelta) atTop atTop := by
  have hh := curvature_matchedStep_tendsto p hb
  have hs : ∀ᶠ n in atTop, 0 < (p n).matchedStep := by
    filter_upwards [hb1,hb.eventually (lt_mem_nhds (show (0:ℝ)<1 by norm_num))] with n h1 h0
    exact (p n).matchedStep_pos h0 h1
  have hg : Tendsto (fun n => (p n).matchedStep^2) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using hh.pow 2
    · filter_upwards [hs] with n hn
      exact sq_pos_of_pos hn
  have h := hg.inv_tendsto_nhdsGT_zero.atTop_mul_pos
    (sq_pos_of_pos (curvature_angle_limit_pos w hw0 hw4))
    (curvature_scaledDelta_tendsto p w hb hw hw0 hw4 hb1)
  apply h.congr'
  filter_upwards [hs] with n hn
  simp only [Pi.inv_apply]
  field_simp

theorem Params.inverse_sqrt_matchedDelta_le (p : Params) (hb0 : 0 < p.beta)
    (hb1 : p.beta < 1) (hc : |p.traceCosine| ≤ 1) (a : ℝ) (ha : 0 < a)
    (hang : a ≤ p.foldedAngle) :
    1/Real.sqrt p.matchedDelta ≤ p.matchedStep/a := by
  have hh := p.matchedStep_pos hb0 hb1
  have hsq : (p.foldedAngle/p.matchedStep)^2 ≤ p.matchedDelta := by
    simp only [Params.matchedDelta,hc,ite_true]
    linarith
  have hbound : a/p.matchedStep ≤ Real.sqrt p.matchedDelta :=
    (div_le_div_of_nonneg_right hang hh.le).trans (Real.le_sqrt_of_sq_le hsq)
  have h := one_div_le_one_div_of_le (div_pos ha hh) hbound
  convert h using 1 <;> field_simp

/-- The window comparison error becomes order one matched step at the
curvature ceiling, retaining its initial-energy and forcing factor. -/
theorem curvature_window_error_factor (p : ℕ → Params) (w : ℝ)
    (hb : Tendsto (fun n => (p n).beta) atTop (𝓝 1))
    (hw : Tendsto (fun n => (p n).w) atTop (𝓝 w)) (hw0 : 0 < w) (hw4 : w < 4)
    (hb1 : ∀ᶠ n in atTop, (p n).beta < 1) :
    ∃ C > 0, ∀ᶠ n in atTop,
      (p n).matchedStep+1/Real.sqrt (p n).matchedDelta ≤ C*(p n).matchedStep := by
  let a := Real.arccos |1-w/2|/2
  have ha : 0 < a := half_pos (curvature_angle_limit_pos w hw0 hw4)
  have hang : ∀ᶠ n in atTop, a ≤ (p n).foldedAngle :=
    (curvature_foldedAngle_tendsto p w hb hw).eventually
      (le_mem_nhds (by change Real.arccos |1-w/2|/2 < Real.arccos |1-w/2|; linarith [curvature_angle_limit_pos w hw0 hw4]))
  refine ⟨1+1/a,by positivity,?_⟩
  filter_upwards [hb1,hang,curvature_eventually_underdamped p w hb hw hw0 hw4,
    hb.eventually (lt_mem_nhds (show (0:ℝ)<1 by norm_num))] with n h1 hangle hc h0
  have h := (p n).inverse_sqrt_matchedDelta_le h0 h1 hc.le a ha hangle
  calc
    _ ≤ (p n).matchedStep+(p n).matchedStep/a := by linarith only [h]
    _ = _ := by ring

theorem curvature_angle_margin (w margin : ℝ) (hm0 : 0 ≤ margin)
    (hm : margin ≤ Real.pi/2) (hw : 2*Real.sin margin ≤ |w-2|) :
    Real.arccos |1-w/2| ≤ Real.pi/2-margin := by
  have h : Real.sin margin ≤ |1-w/2| := by
    rw [show 1-w/2=-(w-2)/2 by ring,abs_div,abs_neg]
    norm_num
    linarith
  have hh := Real.arccos_le_arccos h
  rw [← Real.cos_pi_div_two_sub margin,
    Real.arccos_cos (by linarith : 0≤Real.pi/2-margin) (by linarith [Real.pi_pos] : Real.pi/2-margin≤Real.pi)] at hh
  exact hh

/-- The actual continuum spectral rate converges to the renormalized noise cap. -/
theorem curvature_perronRate_tendsto (p : ℕ → Params) (w u : ℝ)
    (hb : Tendsto (fun n => (p n).beta) atTop (𝓝 1))
    (hw : Tendsto (fun n => (p n).w) atTop (𝓝 w))
    (hu : Tendsto (fun n => (p n).noise) atTop (𝓝 u)) (hw0 : 0 < w) (hw4 : w < 4)
    (hb1 : ∀ᶠ n in atTop, (p n).beta < 1)
    (hu0 : ∀ᶠ n in atTop, 0 ≤ (p n).renormNoise) (hu1 : u/(1-w/4) < 1) :
    Tendsto (fun n => continuumPerronRate (p n).matchedDelta (p n).renormNoise)
      atTop (𝓝 (1-u/(1-w/4))) := by
  have hdelta := curvature_matchedDelta_tendsto_atTop p w hb hw hw0 hw4 hb1
  have hlu := curvature_noise_tendsto p w u hb hw hu hw4
  have hgaps : ∀ᶠ n in atTop,
      0 ≤ (1-(p n).renormNoise)-continuumPerronRate (p n).matchedDelta (p n).renormNoise ∧
      (1-(p n).renormNoise)-continuumPerronRate (p n).matchedDelta (p n).renormNoise ≤
        (1/4)/(p n).matchedDelta := by
    filter_upwards [hdelta.eventually_ge_atTop 1,hu0,hlu.eventually (gt_mem_nhds hu1)] with n hd h0 h1
    have h := window_continuum_rate_bound (p n).matchedDelta (p n).renormNoise hd h0 h1
    convert h using 1 <;> ring
  have hgap : Tendsto (fun n => (1-(p n).renormNoise)-
      continuumPerronRate (p n).matchedDelta (p n).renormNoise) atTop (𝓝 0) :=
    squeeze_zero' (hgaps.mono fun _ h => h.1) (hgaps.mono fun _ h => h.2)
      (hdelta.const_div_atTop (1/4))
  have h := (hlu.const_sub 1).sub hgap
  simpa only [sub_sub_cancel,sub_zero] using h

end
end SparseSGD
