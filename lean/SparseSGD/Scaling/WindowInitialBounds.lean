import SparseSGD.Scaling.WindowScalars

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

def windowEquilibrium (delta u phi : ℝ) : Moments := ⟨phi/(1-u),phi/(delta*(1-u)),0⟩
def windowSize (delta u phi : ℝ) (s : Moments) : ℝ := s.R+delta*s.V+phi/(1-u)

theorem oscillatoryRoot_norm (delta omega : ℝ) (hd : 0 ≤ delta)
    (hosq : omega^2 = delta-1/4) : ‖oscillatoryRoot omega‖ = 2*Real.sqrt delta := by
  have hn : ‖oscillatoryRoot omega‖^2 = 4*delta := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply,oscillatoryRoot]
    nlinarith
  nlinarith [Real.sq_sqrt hd,Real.sqrt_nonneg delta,norm_nonneg (oscillatoryRoot omega)]

theorem window_initial_slow_bound (delta : ℝ) (hd : 1 ≤ delta) (s : Moments) (hs : s.psd) :
    |slowEnergy delta s| ≤ 2*(s.R+delta*s.V) := by
  have hr := Moments.psd_R_nonneg hs
  have hv := Moments.psd_V_nonneg hs
  have hx := Moments.psd_cross_energy_bound delta (by linarith) s hs
  have hd1 : 1 ≤ Real.sqrt delta := by nlinarith [Real.sq_sqrt (by linarith : 0 ≤ delta),Real.sqrt_nonneg delta]
  have hC : |s.C| ≤ s.R+delta*s.V := by
    nlinarith [mul_le_mul_of_nonneg_right hd1 (abs_nonneg s.C)]
  unfold slowEnergy
  calc
    _ ≤ |s.R+delta*s.V|+|s.C| := by simpa using abs_sub_le (s.R+delta*s.V) 0 s.C
    _ ≤ _ := by rw [abs_of_nonneg (by positivity)]; linarith

theorem window_initial_osc_bound (delta omega : ℝ) (hd : 1 ≤ delta)
    (hosq : omega^2 = delta-1/4) (s : Moments) (hs : s.psd) :
    ‖oscillatoryEnergy delta (oscillatoryRoot omega) s‖ ≤ 2*(s.R+delta*s.V) := by
  have hr := Moments.psd_R_nonneg hs
  have hv := Moments.psd_V_nonneg hs
  have hx := Moments.psd_cross_energy_bound delta (by linarith) s hs
  have hn := oscillatoryRoot_norm delta omega (by linarith) hosq
  have hfrac : ‖oscillatoryRoot omega^2/4‖ = delta := by
    rw [norm_div,norm_pow,hn]
    norm_num
    rw [mul_pow,Real.sq_sqrt (by linarith : 0 ≤ delta)]
    ring
  rw [oscillatoryEnergy_polynomial delta _ s (oscillatoryRoot_add_two_ne_zero omega)
    (oscillatoryRoot_quadratic delta omega hosq)]
  calc
    _ ≤ ‖(s.R : ℂ)‖+‖oscillatoryRoot omega^2/4*(s.V : ℂ)‖+‖oscillatoryRoot omega*(s.C : ℂ)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = s.R+delta*s.V+2*Real.sqrt delta*|s.C| := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,abs_of_nonneg hv,hfrac,hn]
    _ ≤ _ := by linarith

theorem windowEquilibrium_slow (delta u phi : ℝ) (hd : delta ≠ 0) :
    slowEnergy delta (windowEquilibrium delta u phi) = 2*phi/(1-u) := by
  simp only [windowEquilibrium,slowEnergy]
  field_simp
  ring

theorem windowEquilibrium_osc (delta u phi : ℝ) (hd : delta ≠ 0)
    (lambda : ℂ) (hl : lambda+2 ≠ 0) :
    oscillatoryEnergy delta lambda (windowEquilibrium delta u phi) =
      (2/(lambda+2))*((phi/(1-u) : ℝ) : ℂ) := by
  simp only [windowEquilibrium,oscillatoryEnergy]
  push_cast
  field_simp [show (delta : ℂ) ≠ 0 by exact_mod_cast hd,hl]
  ring

theorem windowEquilibrium_osc_bound (delta u phi omega : ℝ) (hd : 0 < delta)
    (hu : u < 1) (hp : 0 ≤ phi) (ho : 0 < omega) :
    ‖oscillatoryEnergy delta (oscillatoryRoot omega) (windowEquilibrium delta u phi)‖ ≤
      (phi/(1-u))/omega := by
  have hg : 2*omega ≤ ‖oscillatoryRoot omega+2‖ := by
    have H := Complex.abs_im_le_norm (oscillatoryRoot omega+2)
    simpa [oscillatoryRoot,abs_of_pos ho,abs_mul] using H
  have hn := norm_pos_iff.mpr (oscillatoryRoot_add_two_ne_zero omega)
  have hL : 0 ≤ phi/(1-u) := by positivity
  rw [windowEquilibrium_osc delta u phi hd.ne' _ (oscillatoryRoot_add_two_ne_zero omega),
    norm_mul,norm_div]
  norm_num only [Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL]
  calc
    _ ≤ (2/(2*omega))*(phi/(1-u)) := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) hg) hL
    _ = _ := by ring

end
end SparseSGD
