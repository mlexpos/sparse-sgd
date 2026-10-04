import SparseSGD.Scaling.WindowFlow

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

def windowSlowProfile (delta u phi : ℝ) (s : Moments) (t : ℝ) : ℝ :=
  2*phi/(1-u)+(slowEnergy delta s-2*phi/(1-u))*Real.exp ((u-1)*t)

def windowOscillatoryProfile (delta u omega : ℝ) (s : Moments) (t : ℝ) : ℂ :=
  oscillatoryEnergy delta (oscillatoryRoot omega) s*Complex.exp (windowOscillatoryRate u omega*(t : ℂ))

theorem continuum_window_slow_bound (delta u phi omega margin : ℝ) (s : Moments)
    (hd : 4 ≤ delta) (hm : 0 < margin) (hu0 : 0 ≤ u) (hu : u ≤ 1-margin)
    (hp : 0 ≤ phi) (hs : s.psd) (ho : 0 < omega) (hosq : omega^2 = delta-1/4)
    (hlarge : 1 ≤ 2*margin*delta) (t : ℝ) (ht : 0 ≤ t) :
    |slowEnergy delta (continuumFlow delta u phi s t)-windowSlowProfile delta u phi s t| ≤
      (48+4/margin)*windowSize delta u phi s/omega := by
  have H := continuum_window_centered_bound delta u phi omega margin s hd hm hu0 hu hp hs ho hosq hlarge t ht 0
  have hS := windowEquilibrium_slow delta u phi (by linarith)
  have he : Complex.exp (((u-1 : ℝ) : ℂ)*(t : ℂ)) = (Real.exp ((u-1)*t) : ℂ) := by
    rw [← Complex.ofReal_mul,← Complex.ofReal_exp]
  change ‖(slowEnergy delta (continuumFlow delta u phi s t) : ℂ)-
    ((slowEnergy delta (windowEquilibrium delta u phi) : ℂ)+
      ((slowEnergy delta s : ℂ)-(slowEnergy delta (windowEquilibrium delta u phi) : ℂ))*
        Complex.exp (((u-1 : ℝ) : ℂ)*(t : ℂ)))‖ ≤ _ at H
  rw [hS,he] at H
  simp only [← Complex.ofReal_sub,← Complex.ofReal_mul,← Complex.ofReal_add,
    Complex.norm_real,Real.norm_eq_abs] at H
  apply H.trans
  have hN : 0 ≤ windowSize delta u phi s := by
    have hr := Moments.psd_R_nonneg hs
    have hv := Moments.psd_V_nonneg hs
    dsimp only [windowSize]
    have hu1 : u < 1 := by linarith
    positivity
  apply div_le_div_of_nonneg_right _ ho.le
  exact mul_le_mul_of_nonneg_right (by linarith) hN

theorem continuum_window_osc_bound (delta u phi omega margin : ℝ) (s : Moments)
    (hd : 4 ≤ delta) (hm : 0 < margin) (hu0 : 0 ≤ u) (hu : u ≤ 1-margin)
    (hp : 0 ≤ phi) (hs : s.psd) (ho : 0 < omega) (hosq : omega^2 = delta-1/4)
    (hlarge : 1 ≤ 2*margin*delta) (t : ℝ) (ht : 0 ≤ t) :
    ‖oscillatoryEnergy delta (oscillatoryRoot omega) (continuumFlow delta u phi s t)-
      windowOscillatoryProfile delta u omega s t‖ ≤
      (48+4/margin)*windowSize delta u phi s/omega := by
  let Z := oscillatoryEnergy delta (oscillatoryRoot omega)
  let L := Z (windowEquilibrium delta u phi)
  let q := Complex.exp (windowOscillatoryRate u omega*(t : ℂ))
  have hu1 : u < 1 := by linarith
  have hL := windowEquilibrium_osc_bound delta u phi omega (by linarith) hu1 hp ho
  have H := continuum_window_centered_bound delta u phi omega margin s hd hm hu0 hu hp hs ho hosq hlarge t ht 1
  have hq : ‖q‖ ≤ 1 := damped_mode_norm_le_one _ (by simp [windowOscillatoryRate]; linarith) t ht
  have he : Z (continuumFlow delta u phi s t)-Z s*q =
      (Z (continuumFlow delta u phi s t)-(L+(Z s-L)*q))+L*(1-q) := by ring
  change ‖Z (continuumFlow delta u phi s t)-Z s*q‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  have hq' : ‖1-q‖ ≤ 2 := (norm_sub_le _ _).trans (by norm_num; linarith)
  have hN : phi/(1-u) ≤ windowSize delta u phi s := by
    have hr := Moments.psd_R_nonneg hs
    have hv := Moments.psd_V_nonneg hs
    dsimp only [windowSize]
    nlinarith
  have hNN : 0 ≤ windowSize delta u phi s := by
    have hfloor : 0 ≤ phi/(1-u) := by positivity
    exact hfloor.trans hN
  have hproduct : ‖L*(1-q)‖ ≤ 2*windowSize delta u phi s/omega := by
    rw [norm_mul]
    have HL : ‖L‖ ≤ windowSize delta u phi s/omega :=
      hL.trans (div_le_div_of_nonneg_right hN ho.le)
    calc
      _ ≤ (windowSize delta u phi s/omega)*2 := by gcongr
      _ = _ := by ring
  exact (add_le_add H hproduct).trans (by
    calc
      _ = (46+4/margin)*windowSize delta u phi s/omega := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hNN) ho.le)

theorem windowSize_margin_bound (delta u phi margin : ℝ) (s : Moments)
    (hd : 0 < delta) (hm : 0 < margin) (hu0 : 0 ≤ u) (hu : u ≤ 1-margin)
    (hp : 0 ≤ phi) (hs : s.psd) :
    windowSize delta u phi s ≤ (s.R+delta*s.V+|s.C|+phi)/margin := by
  have hu1 : u < 1 := by linarith
  have hE : 0 ≤ s.R+delta*s.V := by
    have hr := Moments.psd_R_nonneg hs
    have hv := Moments.psd_V_nonneg hs
    positivity
  unfold windowSize
  calc
    _ ≤ (s.R+delta*s.V+phi)/(1-u) := by
      apply (le_div_iff₀ (by linarith : 0 < 1-u)).2
      have hc := div_mul_cancel₀ phi (show 1-u ≠ 0 by linarith)
      nlinarith [mul_nonneg hu0 hE]
    _ ≤ (s.R+delta*s.V+phi)/margin := div_le_div_of_nonneg_left (by positivity) hm (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith [abs_nonneg s.C]) hm.le

theorem window_inverse_frequency_bound (delta omega : ℝ) (hd : 4 ≤ delta)
    (ho : 0 < omega) (hosq : omega^2 = delta-1/4) :
    1/omega ≤ 2/Real.sqrt delta := by
  have hs : 0 < Real.sqrt delta := Real.sqrt_pos.mpr (by linarith)
  have he := Real.sq_sqrt (by linarith : 0 ≤ delta)
  have hsq : Real.sqrt delta ≤ 2*omega := by nlinarith
  apply (div_le_div_iff₀ ho hs).2
  simpa using hsq

end
end SparseSGD
