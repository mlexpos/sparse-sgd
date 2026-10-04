import SparseSGD.Scaling.WindowChain

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

theorem window_risk_coefficients (delta omega : ℝ) (hd : 4 ≤ delta)
    (ho : 0 < omega) (hosq : omega^2 = delta-1/4) :
    0 ≤ riskSlowCoefficient delta omega ∧ riskSlowCoefficient delta omega ≤ 1 ∧
    2*‖riskOscillatoryCoefficient omega‖ ≤ 1 ∧
    |riskSlowCoefficient delta omega-1/2| ≤ 1/omega ∧
    ‖riskOscillatoryCoefficient omega-(1/4 : ℂ)‖ ≤ 1/omega := by
  have ho1 : 1 ≤ omega := by nlinarith
  have hoc : (omega : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ho.ne'
  have hrS : |riskSlowCoefficient delta omega-1/2| = 1/(8*omega^2) := by
    unfold riskSlowCoefficient
    have he : delta/(2*omega^2)-1/2 = 1/(8*omega^2) := by
      field_simp
      nlinarith
    rw [he,abs_of_pos (by positivity)]
  have hnorm : ‖1+2*Complex.I*(omega : ℂ)‖^2 = 4*delta := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    nlinarith
  have hrZ : ‖riskOscillatoryCoefficient omega‖ = delta/(4*omega^2) := by
    unfold riskOscillatoryCoefficient
    rw [norm_div,norm_neg,norm_pow,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ho,hnorm]
    norm_num
    ring
  have hclean : riskOscillatoryCoefficient omega-(1/4 : ℂ) =
      (-1/(16*omega^2) : ℝ)-Complex.I/(4*(omega : ℂ)) := by
    unfold riskOscillatoryCoefficient
    push_cast
    field_simp
    ring_nf
    simp
  refine ⟨by unfold riskSlowCoefficient; positivity,?_,?_,?_,?_⟩
  · unfold riskSlowCoefficient
    apply (div_le_iff₀ (by positivity : 0 < 2*omega^2)).2
    nlinarith
  · rw [hrZ]
    have H : delta/(4*omega^2) ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity : 0 < 4*omega^2)).2
      nlinarith
    linarith
  · rw [hrS]
    apply (div_le_div_iff₀ (by positivity : 0 < 8*omega^2) ho).2
    nlinarith
  · rw [hclean]
    calc
      _ ≤ ‖((-1/(16*omega^2) : ℝ) : ℂ)‖+‖Complex.I/(4*(omega : ℂ))‖ := norm_sub_le _ _
      _ = 1/(16*omega^2)+1/(4*omega) := by
        simp [norm_div,norm_mul,abs_div,abs_of_pos ho,abs_of_nonneg (sq_nonneg omega)]
      _ ≤ 1/omega := by
        apply (le_div_iff₀ ho).2
        field_simp
        nlinarith

theorem window_profile_bounds (delta u phi omega : ℝ) (s : Moments)
    (hd : 4 ≤ delta) (hu0 : 0 ≤ u) (hu : u < 1) (hp : 0 ≤ phi) (hs : s.psd)
    (ho : 0 < omega) (hosq : omega^2 = delta-1/4) (t : ℝ) (ht : 0 ≤ t) :
    |windowSlowProfile delta u phi s t| ≤ 4*windowSize delta u phi s ∧
    ‖windowOscillatoryProfile delta u omega s t‖ ≤ 2*windowSize delta u phi s := by
  have hL : 0 ≤ phi/(1-u) := by positivity
  have hNL : phi/(1-u) ≤ windowSize delta u phi s := by
    have hr := Moments.psd_R_nonneg hs
    have hv := Moments.psd_V_nonneg hs
    dsimp only [windowSize]
    nlinarith
  have hN : 0 ≤ windowSize delta u phi s := hL.trans hNL
  have hS := window_initial_centered_bound delta u phi omega hd hu hp ho hosq s hs 0
  change ‖(slowEnergy delta s : ℂ)-(slowEnergy delta (windowEquilibrium delta u phi) : ℂ)‖ ≤ _ at hS
  rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,windowEquilibrium_slow _ _ _ (by linarith)] at hS
  constructor
  · have hexp : Real.exp ((u-1)*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    unfold windowSlowProfile
    calc
      _ ≤ |2*phi/(1-u)|+|(slowEnergy delta s-2*phi/(1-u))*Real.exp ((u-1)*t)| := abs_add_le _ _
      _ = 2*(phi/(1-u))+|slowEnergy delta s-2*phi/(1-u)| *Real.exp ((u-1)*t) := by
        rw [abs_mul,Real.abs_exp,show 2*phi/(1-u) = 2*(phi/(1-u)) by ring,
          abs_of_nonneg (by positivity)]
      _ ≤ 2*windowSize delta u phi s+2*windowSize delta u phi s*1 := by gcongr
      _ = _ := by ring
  · unfold windowOscillatoryProfile
    rw [norm_mul]
    have hz := window_initial_osc_bound delta omega (by linarith) hosq s hs
    have hq := damped_mode_norm_le_one (windowOscillatoryRate u omega)
      (by simp [windowOscillatoryRate]; linarith) t ht
    calc
      _ ≤ (2*(s.R+delta*s.V))*1 := mul_le_mul hz hq (norm_nonneg _) ((norm_nonneg _).trans hz)
      _ ≤ _ := by dsimp only [windowSize]; nlinarith

/-- Reconstructing risk costs only the small free modal coefficient errors. -/
theorem window_risk_reconstruction_error (delta omega N E S : ℝ) (Z : ℂ) (s : Moments)
    (hd : 4 ≤ delta) (ho : 0 < omega) (hosq : omega^2 = delta-1/4)
    (hN : 0 ≤ N) (hE : 0 ≤ E) (hS : |slowEnergy delta s-S| ≤ E)
    (hZ : ‖oscillatoryEnergy delta (oscillatoryRoot omega) s-Z‖ ≤ E)
    (hSB : |S| ≤ 4*N) (hZB : ‖Z‖ ≤ 2*N) :
    |s.R-(S/2+Z.re/2)| ≤ 2*E+8*N/omega := by
  obtain ⟨hr0,hr1,hz1,hrs,hrz⟩ := window_risk_coefficients delta omega hd ho hosq
  let rS := riskSlowCoefficient delta omega
  let rZ := riskOscillatoryCoefficient omega
  have he : s.R-(S/2+Z.re/2) =
      rS*(slowEnergy delta s-S)+
      2*(rZ*(oscillatoryEnergy delta (oscillatoryRoot omega) s-Z)).re+
      (rS-1/2)*S+2*((rZ-(1/4 : ℂ))*Z).re := by
    rw [risk_modal_inversion delta omega s ho.ne' hosq]
    dsimp only [rS,rZ]
    simp only [Complex.mul_re,Complex.sub_re,Complex.sub_im]
    norm_num
    ring
  have hterm1 : |rS*(slowEnergy delta s-S)| ≤ E := by
    rw [abs_mul,abs_of_nonneg hr0]
    exact (mul_le_mul_of_nonneg_left hS hr0).trans (by nlinarith)
  have hterm2 : |2*(rZ*(oscillatoryEnergy delta (oscillatoryRoot omega) s-Z)).re| ≤ E := by
    rw [abs_mul,show |(2 : ℝ)| = 2 by norm_num]
    have H := (Complex.abs_re_le_norm _).trans (show ‖rZ*(oscillatoryEnergy delta (oscillatoryRoot omega) s-Z)‖ ≤ ‖rZ‖*E by rw [norm_mul]; gcongr)
    exact (mul_le_mul_of_nonneg_left H (by norm_num)).trans (by nlinarith)
  have hterm3 : |(rS-1/2)*S| ≤ 4*N/omega := by
    rw [abs_mul]
    calc
      _ ≤ (1/omega)*(4*N) := by gcongr
      _ = _ := by ring
  have hterm4 : |2*((rZ-(1/4 : ℂ))*Z).re| ≤ 4*N/omega := by
    rw [abs_mul,show |(2 : ℝ)| = 2 by norm_num]
    have H := (Complex.abs_re_le_norm _).trans (show ‖(rZ-(1/4 : ℂ))*Z‖ ≤ (1/omega)*(2*N) by rw [norm_mul]; gcongr)
    exact (mul_le_mul_of_nonneg_left H (by norm_num)).trans (by ring_nf; rfl)
  rw [he]
  calc
    _ ≤ |rS*(slowEnergy delta s-S)+2*(rZ*(oscillatoryEnergy delta (oscillatoryRoot omega) s-Z)).re+(rS-1/2)*S|+
        |2*((rZ-(1/4 : ℂ))*Z).re| := abs_add_le _ _
    _ ≤ (|rS*(slowEnergy delta s-S)+2*(rZ*(oscillatoryEnergy delta (oscillatoryRoot omega) s-Z)).re|+
        |(rS-1/2)*S|)+|2*((rZ-(1/4 : ℂ))*Z).re| := by gcongr; exact abs_add_le _ _
    _ ≤ ((|rS*(slowEnergy delta s-S)|+|2*(rZ*(oscillatoryEnergy delta (oscillatoryRoot omega) s-Z)).re|)+
        |(rS-1/2)*S|)+|2*((rZ-(1/4 : ℂ))*Z).re| := by gcongr; exact abs_add_le _ _
    _ ≤ E+E+4*N/omega+4*N/omega := by gcongr
    _ = 2*E+8*N/omega := by ring

end
end SparseSGD
