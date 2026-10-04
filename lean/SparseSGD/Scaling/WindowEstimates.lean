import SparseSGD.Scaling.WindowModes

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

theorem damped_mode_norm_le_one (z : ℂ) (hz : z.re ≤ 0) (t : ℝ) (ht : 0 ≤ t) :
    ‖Complex.exp (z*(t : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hz ht)

/-- A dominant mode approximates a finite modal sum when the other functional
projections are small; this estimate is uniform for all nonnegative times. -/
theorem modal_dominant_approximation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rates coeff factors : ι → ℂ) (d : ι) (w : ℂ) (epsilon B I H t : ℝ)
    (he : 0 ≤ epsilon) (hB : ∑ i, ‖coeff i‖ ≤ B)
    (hI : ‖∑ i, coeff i*factors i‖ ≤ I)
    (hr : ∀ i, (rates i).re ≤ 0) (ht : 0 ≤ t)
    (hf : ∀ i, i ≠ d → ‖factors i‖ ≤ epsilon)
    (hexp : ‖Complex.exp (rates d*(t : ℂ))-Complex.exp (w*(t : ℂ))‖ ≤ H) :
    ‖(∑ i, coeff i*factors i*Complex.exp (rates i*(t : ℂ)))-
      (∑ i, coeff i*factors i)*Complex.exp (w*(t : ℂ))‖ ≤ 2*epsilon*B+I*H := by
  have hH : 0 ≤ H := (norm_nonneg _).trans hexp
  have hsplit : (∑ i, coeff i*factors i*Complex.exp (rates i*(t : ℂ)))-
      (∑ i, coeff i*factors i)*Complex.exp (w*(t : ℂ)) =
      (∑ i, coeff i*factors i*(Complex.exp (rates i*(t : ℂ))-Complex.exp (rates d*(t : ℂ))))+
      (∑ i, coeff i*factors i)*(Complex.exp (rates d*(t : ℂ))-Complex.exp (w*(t : ℂ))) := by
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.sum_mul]
    ring
  rw [hsplit]
  apply (norm_add_le _ _).trans
  have hsum : ‖∑ i, coeff i*factors i*
      (Complex.exp (rates i*(t : ℂ))-Complex.exp (rates d*(t : ℂ)))‖ ≤ 2*epsilon*B := by
    calc
      _ ≤ ∑ i, ‖coeff i*factors i*(Complex.exp (rates i*(t : ℂ))-Complex.exp (rates d*(t : ℂ)))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i, 2*epsilon*‖coeff i‖ := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i = d
        · subst i
          simp only [sub_self,mul_zero,norm_zero]
          positivity
        · have hni := damped_mode_norm_le_one (rates i) (hr i) t ht
          have hnd := damped_mode_norm_le_one (rates d) (hr d) t ht
          have hdif : ‖Complex.exp (rates i*(t : ℂ))-Complex.exp (rates d*(t : ℂ))‖ ≤ 2 :=
            (norm_sub_le _ _).trans (by linarith)
          rw [norm_mul,norm_mul]
          calc
            _ ≤ ‖coeff i‖*epsilon*2 := by gcongr; exact hf i hi
            _ = _ := by ring
      _ = 2*epsilon*(∑ i, ‖coeff i‖) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
  rw [norm_mul]
  exact add_le_add hsum (mul_le_mul hI hexp (norm_nonneg _) (by linarith [norm_nonneg (∑ i, coeff i*factors i)]))

theorem largeModeRates_fast_gap (delta a omega : ℝ) (hd : 1 ≤ delta)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ho : 0 < omega) (hosq : omega^2 = delta-1/4)
    (i : Fin 3) (hi : i ≠ 0) :
    2*omega ≤ ‖largeModeRates delta a i+1‖ := by
  have hf := (largeModeFrequency_deviation delta a omega hd ha0 ha1 ho hosq).1
  have hb := largeModeFrequency_pos delta a hd
  fin_cases i
  · exact (hi rfl).elim
  · have H := Complex.abs_im_le_norm (largeModeRootPlus delta a+1)
    have he : (largeModeRootPlus delta a+1).im = largeModeFrequency delta a := by simp [largeModeRootPlus]
    rw [he,abs_of_pos hb] at H
    exact (by linarith : 2*omega ≤ largeModeFrequency delta a).trans H
  · have H := Complex.abs_im_le_norm (star (largeModeRootPlus delta a)+1)
    have he : (star (largeModeRootPlus delta a)+1).im = -largeModeFrequency delta a := by simp [largeModeRootPlus]
    rw [he,abs_neg,abs_of_pos hb] at H
    exact (by linarith : 2*omega ≤ largeModeFrequency delta a).trans H

theorem largeModeRates_osc_gap (delta a omega : ℝ) (hd : 1 ≤ delta)
    (ho : 0 < omega) (i : Fin 3) (hi : i ≠ 1) :
    2*omega ≤ ‖largeModeRates delta a i-oscillatoryRoot omega‖ := by
  have hb := largeModeFrequency_pos delta a hd
  fin_cases i
  · change 2*omega ≤ ‖((a-1 : ℝ) : ℂ)-oscillatoryRoot omega‖
    have H := Complex.abs_im_le_norm (((a-1 : ℝ) : ℂ)-oscillatoryRoot omega)
    have he : (((a-1 : ℝ) : ℂ)-oscillatoryRoot omega).im = -2*omega := by simp [oscillatoryRoot]
    rw [he,abs_mul,abs_of_pos ho] at H
    norm_num at H
    simpa only [Complex.ofReal_sub,Complex.ofReal_one] using H
  · exact (hi rfl).elim
  · have H := Complex.abs_im_le_norm (star (largeModeRootPlus delta a)-oscillatoryRoot omega)
    have he : (star (largeModeRootPlus delta a)-oscillatoryRoot omega).im =
        -(largeModeFrequency delta a+2*omega) := by simp [largeModeRootPlus,oscillatoryRoot]; ring
    rw [he,abs_neg,abs_of_pos (by positivity)] at H
    exact (by linarith : 2*omega ≤ largeModeFrequency delta a+2*omega).trans H

theorem windowSlowFactor_fast_bound (delta u a omega : ℝ) (hd : 1 ≤ delta)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : a^3+(4*delta-1)*a-4*delta*u = 0) (ho : 0 < omega)
    (hosq : omega^2 = delta-1/4) (i : Fin 3) (hi : i ≠ 0) :
    ‖windowModeFactor (windowSlowWeights delta) delta (largeModeRates delta a i)‖ ≤ 1/omega := by
  have H := congrArg norm (windowSlowFactor_eigenrelation delta u (largeModeRates delta a i)
    (by linarith) (largeModeRates_is_root delta u a hd ha i))
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu0] at H
  norm_num only [Complex.norm_ofNat] at H
  have hgap := largeModeRates_fast_gap delta a omega hd ha0 ha1 ho hosq i hi
  apply (le_div_iff₀ ho).2
  nlinarith [mul_le_mul_of_nonneg_right hgap
    (norm_nonneg (windowModeFactor (windowSlowWeights delta) delta (largeModeRates delta a i)))]

theorem windowOscFactor_wrong_bound (delta u a omega : ℝ) (hd : 1 ≤ delta)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ha : a^3+(4*delta-1)*a-4*delta*u = 0)
    (ho : 0 < omega) (hosq : omega^2 = delta-1/4) (i : Fin 3) (hi : i ≠ 1) :
    ‖windowModeFactor (windowOscWeights delta (oscillatoryRoot omega)) delta (largeModeRates delta a i)‖ ≤
      1/omega := by
  have H := congrArg norm (windowOscFactor_eigenrelation delta u (oscillatoryRoot omega)
    (largeModeRates delta a i) (by linarith) (oscillatoryRoot_add_two_ne_zero omega)
    (oscillatoryRoot_quadratic delta omega hosq) (largeModeRates_is_root delta u a hd ha i))
  have hg : ‖-(2*oscillatoryRoot omega/(oscillatoryRoot omega+2))‖ = 2 := energyModeGain_norm omega 1
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu0,hg] at H
  have hgap := largeModeRates_osc_gap delta a omega hd ho i hi
  apply (le_div_iff₀ ho).2
  nlinarith [mul_le_mul_of_nonneg_right hgap
    (norm_nonneg (windowModeFactor (windowOscWeights delta (oscillatoryRoot omega)) delta (largeModeRates delta a i)))]

end
end SparseSGD
