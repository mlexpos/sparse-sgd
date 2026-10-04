import SparseSGD.Scaling.WindowScalars

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

def windowModeCoordinate (delta : ℝ) (z : ℂ) : Fin 3 → ℂ :=
  ![1,modeVelocityFactor delta z,modeCrossFactor delta z]

def windowLinearFunctional (w : Fin 3 → ℂ) (s : Moments) : ℂ :=
  w 0*(s.R : ℂ)+w 1*(s.V : ℂ)+w 2*(s.C : ℂ)

def windowModeFactor (w : Fin 3 → ℂ) (delta : ℝ) (z : ℂ) : ℂ :=
  w 0+w 1*modeVelocityFactor delta z+w 2*modeCrossFactor delta z

def windowSlowWeights (delta : ℝ) : Fin 3 → ℂ := ![1,(delta : ℂ),-1]
def windowOscWeights (delta : ℝ) (lambda : ℂ) : Fin 3 → ℂ :=
  ![1,-lambda*(delta : ℂ)/(lambda+2),lambda]

theorem windowLinearFunctional_slow (delta : ℝ) (s : Moments) :
    windowLinearFunctional (windowSlowWeights delta) s = (slowEnergy delta s : ℂ) := by
  simp [windowLinearFunctional,windowSlowWeights,slowEnergy]
  ring

theorem windowLinearFunctional_osc (delta : ℝ) (lambda : ℂ) (s : Moments) :
    windowLinearFunctional (windowOscWeights delta lambda) s = oscillatoryEnergy delta lambda s := by
  simp [windowLinearFunctional,windowOscWeights,oscillatoryEnergy]
  ring

private theorem window_re_decomposition (z : ℂ) : (z.re : ℂ) = (z+star z)/2 := by
  apply Complex.ext <;> simp <;> ring

private theorem window_modeCoordinate_star (delta : ℝ) (z : ℂ) (j : Fin 3) :
    star (windowModeCoordinate delta z j) = windowModeCoordinate delta (star z) j := by
  fin_cases j <;> simp [windowModeCoordinate,modeVelocityFactor,modeCrossFactor]

private theorem window_exp_star (z : ℂ) (t : ℝ) :
    star (Complex.exp (z*(t : ℂ))) = Complex.exp (star z*(t : ℂ)) := by
  change (starRingEnd ℂ) (Complex.exp (z*(t : ℂ))) =
    Complex.exp ((starRingEnd ℂ) z*(t : ℂ))
  rw [← Complex.exp_conj,map_mul,Complex.conj_ofReal]

theorem continuumFlow_window_coordinates (delta u phi a : ℝ) (s : Moments)
    (hd : 1 ≤ delta) (hu : u ≠ 1) (ha : a^3+(4*delta-1)*a-4*delta*u = 0)
    (t : ℝ) (ht : 0 ≤ t) (j : Fin 3) :
    ![((continuumFlow delta u phi s t).R : ℂ),((continuumFlow delta u phi s t).V : ℂ),
      ((continuumFlow delta u phi s t).C : ℂ)] j =
      ![((phi/(1-u) : ℝ) : ℂ),((phi/(delta*(1-u)) : ℝ) : ℂ),0] j+
      ∑ i : Fin 3, largeModeCoefficients delta u phi a s i*
        windowModeCoordinate delta (largeModeRates delta a i) j*
        Complex.exp (largeModeRates delta a i*(t : ℂ)) := by
  have H := continuum_solution_unique delta u phi s (largeModeFlow delta u phi a s)
    (largeModeFlow_initial delta u phi a s hd)
    (largeModeFlow_isMomentSolution delta u phi a s hd hu ha) t ht
  rw [← H]
  let z0 : ℂ := ((a-1 : ℝ) : ℂ)
  let c0 : ℂ := (largeModeSlowCoefficient delta a (largeModeCenteredInitial delta u phi s) : ℂ)
  let c1 := largeModeOscCoefficient delta a (largeModeCenteredInitial delta u phi s)
  have hreal : star (windowModeCoordinate delta z0 j*c0*Complex.exp (z0*(t : ℂ))) =
      windowModeCoordinate delta z0 j*c0*Complex.exp (z0*(t : ℂ)) := by
    rw [star_mul,star_mul,window_modeCoordinate_star,window_exp_star]
    simp [z0,c0]
    ring
  have hr : ((windowModeCoordinate delta z0 j*c0*Complex.exp (z0*(t : ℂ))).re : ℂ) =
      windowModeCoordinate delta z0 j*c0*Complex.exp (z0*(t : ℂ)) := by
    rw [window_re_decomposition,hreal]
    ring
  have he : ((windowModeCoordinate delta (largeModeRootPlus delta a) j*c1*
      Complex.exp (largeModeRootPlus delta a*(t : ℂ))).re : ℂ) =
      (windowModeCoordinate delta (largeModeRootPlus delta a) j*c1*
        Complex.exp (largeModeRootPlus delta a*(t : ℂ))+
      windowModeCoordinate delta (star (largeModeRootPlus delta a)) j*star c1*
        Complex.exp (star (largeModeRootPlus delta a)*(t : ℂ)))/2 := by
    rw [window_re_decomposition,star_mul,star_mul,window_modeCoordinate_star,window_exp_star]
    ring
  have hj : ![((largeModeFlow delta u phi a s t).R : ℂ),((largeModeFlow delta u phi a s t).V : ℂ),
      ((largeModeFlow delta u phi a s t).C : ℂ)] j =
      ![((phi/(1-u) : ℝ) : ℂ),((phi/(delta*(1-u)) : ℝ) : ℂ),0] j+
      ((windowModeCoordinate delta z0 j*c0*Complex.exp (z0*(t : ℂ))).re : ℂ)+
      ((windowModeCoordinate delta (largeModeRootPlus delta a) j*c1*
        Complex.exp (largeModeRootPlus delta a*(t : ℂ))).re : ℂ) := by
    fin_cases j <;> simp [largeModeFlow,largeModeHomogeneousFlow,exponentialModeMoments,
      windowModeCoordinate,z0,c0,c1,Complex.mul_re,Complex.mul_im] <;> ring
  rw [hj,hr,he]
  simp only [largeModeCoefficients,largeModeRates,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  dsimp only [z0,c0,c1]
  ring

/-- Every linear functional has the actual, explicitly inverted three-mode expansion. -/
theorem continuumFlow_window_functional (delta u phi a : ℝ) (s : Moments)
    (hd : 1 ≤ delta) (hu : u ≠ 1) (ha : a^3+(4*delta-1)*a-4*delta*u = 0)
    (t : ℝ) (ht : 0 ≤ t) (w : Fin 3 → ℂ) :
    windowLinearFunctional w (continuumFlow delta u phi s t) =
      windowLinearFunctional w ⟨phi/(1-u),phi/(delta*(1-u)),0⟩+
      ∑ i : Fin 3, largeModeCoefficients delta u phi a s i*
        windowModeFactor w delta (largeModeRates delta a i)*
        Complex.exp (largeModeRates delta a i*(t : ℂ)) := by
  have h0 := continuumFlow_window_coordinates delta u phi a s hd hu ha t ht 0
  have h1 := continuumFlow_window_coordinates delta u phi a s hd hu ha t ht 1
  have h2 := continuumFlow_window_coordinates delta u phi a s hd hu ha t ht 2
  simp only [Matrix.cons_val] at h0 h1 h2
  unfold windowLinearFunctional
  rw [h0,h1,h2]
  simp [windowModeFactor,windowModeCoordinate,Fin.sum_univ_succ]
  ring

theorem largeModeRates_is_root (delta u a : ℝ) (hd : 1 ≤ delta)
    (ha : a^3+(4*delta-1)*a-4*delta*u = 0) (i : Fin 3) :
    (largeModeRates delta a i)^3+3*(largeModeRates delta a i)^2+
      (2+4*(delta : ℂ))*largeModeRates delta a i+4*(delta : ℂ)*(1-(u : ℂ)) = 0 := by
  fin_cases i
  · rw [largeMode_cubic_factor delta u a hd ha]
    simp [largeModeRates]
  · exact largeModeRootPlus_is_root delta u a hd ha
  · have H := congrArg star (largeModeRootPlus_is_root delta u a hd ha)
    simpa [largeModeRates] using H

theorem windowSlowFactor_eigenrelation (delta u : ℝ) (z : ℂ) (hd : delta ≠ 0)
    (hz : z^3+3*z^2+(2+4*(delta : ℂ))*z+4*(delta : ℂ)*(1-(u : ℂ)) = 0) :
    (z+1)*windowModeFactor (windowSlowWeights delta) delta z = 2*(u : ℂ) := by
  obtain ⟨hR,hV,hC⟩ := mode_factors_eigenrelations delta u z hd hz
  simp only [windowModeFactor,windowSlowWeights,Matrix.cons_val,one_mul,neg_one_mul]
  have hdc : (delta : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  linear_combination (norm := ring_nf) hR+(delta : ℂ)*hV-hC
  field_simp [hdc]
  ring

theorem windowOscFactor_eigenrelation (delta u : ℝ) (lambda z : ℂ) (hd : delta ≠ 0)
    (hl : lambda+2 ≠ 0) (hq : lambda^2+2*lambda+4*(delta : ℂ) = 0)
    (hz : z^3+3*z^2+(2+4*(delta : ℂ))*z+4*(delta : ℂ)*(1-(u : ℂ)) = 0) :
    (z-lambda)*windowModeFactor (windowOscWeights delta lambda) delta z =
      -(2*lambda/(lambda+2))*(u : ℂ) := by
  obtain ⟨hR,hV,hC⟩ := mode_factors_eigenrelations delta u z hd hz
  have hdc : (delta : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  simp only [windowModeFactor,windowOscWeights,Matrix.cons_val,one_mul]
  linear_combination (norm := ring_nf) hR-(lambda*(delta : ℂ)/(lambda+2))*hV+lambda*hC-
    ((lambda+1)/(lambda+2))*modeCrossFactor delta z*hq
  field_simp [hdc,show 2+lambda ≠ 0 by simpa [add_comm] using hl]
  ring

end
end SparseSGD
