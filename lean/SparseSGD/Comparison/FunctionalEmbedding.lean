import SparseSGD.Comparison.MomentComparison

open MeasureTheory Set

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

/-- Scalar integrating factor identity for a complex classical linear ODE. -/
theorem scalar_complex_duhamel (z f : ℝ → ℂ) (lambda b : ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hz : ∀ t, 0 ≤ t → HasDerivAt z (lambda*z t+b*f t) t)
    (hf : Continuous f) :
    z T = Complex.exp (lambda*(T : ℂ))*z 0+
      ∫ x in (0 : ℝ)..T, Complex.exp (lambda*((T-x : ℝ) : ℂ))*b*f x := by
  have hexp (l : ℂ) (t : ℝ) : HasDerivAt (fun x : ℝ => Complex.exp (l*(x : ℂ)))
      (l*Complex.exp (l*(t : ℂ))) t := by
    convert ((hasDerivAt_id t).ofReal_comp.const_mul l).cexp using 1 <;> simp <;> ring
  have hder (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt (fun x : ℝ => Complex.exp (-lambda*(x : ℂ))*z x)
        (Complex.exp (-lambda*(t : ℂ))*b*f t) t := by
    convert (hexp (-lambda) t).mul (hz t ht) using 1 <;> ring
  have hc : Continuous (fun x : ℝ => Complex.exp (-lambda*(x : ℂ))*b*f x) := by fun_prop
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hder x (by rw [uIcc_of_le hT] at hx; exact hx.1))
    (hc.intervalIntegrable 0 T)
  have hexpcancel : Complex.exp (lambda*(T : ℂ))*Complex.exp (-lambda*(T : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  have H' := congrArg (fun w : ℂ => Complex.exp (lambda*(T : ℂ))*w) H
  rw [← intervalIntegral.integral_const_mul] at H'
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul,mul_sub,← mul_assoc,hexpcancel] at H'
  have heq : (fun x : ℝ => Complex.exp (lambda*(T : ℂ))*
      Complex.exp (-lambda*(x : ℂ))*b*f x) =
      (fun x : ℝ => Complex.exp (lambda*((T-x : ℝ) : ℂ))*b*f x) := by
    funext x
    rw [← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [heq] at H'
  linear_combination -H'


theorem scalar_complex_duhamel_reversed (z f : ℝ → ℂ) (lambda b : ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hz : ∀ t, 0 ≤ t → HasDerivAt z (lambda*z t+b*f t) t)
    (hf : Continuous f) :
    z T = Complex.exp (lambda*(T : ℂ))*z 0+
      b*(∫ x in (0 : ℝ)..T, Complex.exp (lambda*(x : ℂ))*f (T-x)) := by
  rw [scalar_complex_duhamel z f lambda b T hT hz hf]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  have hint := intervalIntegral.integral_comp_sub_left
    (fun x : ℝ => Complex.exp (lambda*(x : ℂ))*f (T-x)) (a := (0 : ℝ)) (b := T) T
  simp only [sub_sub_cancel,sub_self,sub_zero] at hint
  have hintb := congrArg (fun z : ℂ => b*z) hint
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul] at hintb
  rw [← hintb]
  apply intervalIntegral.integral_congr
  intro x _
  ring

theorem continuumFlow_slowEnergy_duhamel (delta u phi : ℝ) (hd : delta ≠ 0)
    (s : Moments) (T : ℝ) (hT : 0 ≤ T) :
    (slowEnergy delta (continuumFlow delta u phi s T) : ℂ) =
      Complex.exp (-(T : ℂ))*(slowEnergy delta s : ℂ)+
        2*(∫ x in (0 : ℝ)..T, Complex.exp (-(x : ℂ))*
          ((u*(continuumFlow delta u phi s (T-x)).R+phi : ℝ) : ℂ)) := by
  have H := scalar_complex_duhamel_reversed
    (fun t => (slowEnergy delta (continuumFlow delta u phi s t) : ℂ))
    (fun t => ((u*(continuumFlow delta u phi s t).R+phi : ℝ) : ℂ)) (-1) 2 T hT
    (fun x hx => by
      have D := (slowEnergy_hasDerivAt (continuumFlow_isMomentSolution delta u phi s) hd hx).ofReal_comp
      simpa using D) (Complex.continuous_ofReal.comp (((continuumFlow_R_continuous delta u phi s).const_mul u).add continuous_const))
  simpa [continuumFlow_initial] using H

theorem continuumFlow_oscillatoryEnergy_duhamel (delta u phi : ℝ) (hd : delta ≠ 0)
    (lambda : ℂ) (hl : lambda+2 ≠ 0)
    (hq : lambda^2+2*lambda+4*(delta : ℂ) = 0)
    (s : Moments) (T : ℝ) (hT : 0 ≤ T) :
    oscillatoryEnergy delta lambda (continuumFlow delta u phi s T) =
      Complex.exp (lambda*(T : ℂ))*oscillatoryEnergy delta lambda s-
        (2*lambda/(lambda+2))*(∫ x in (0 : ℝ)..T, Complex.exp (lambda*(x : ℂ))*
          ((u*(continuumFlow delta u phi s (T-x)).R+phi : ℝ) : ℂ)) := by
  have H := scalar_complex_duhamel_reversed
    (fun t => oscillatoryEnergy delta lambda (continuumFlow delta u phi s t))
    (fun t => ((u*(continuumFlow delta u phi s t).R+phi : ℝ) : ℂ)) lambda
    (-2*lambda/(lambda+2)) T hT
    (fun x hx => by
      convert oscillatoryEnergy_hasDerivAt (continuumFlow_isMomentSolution delta u phi s)
        hd lambda hl hq hx using 1 <;> push_cast <;> ring)
    (Complex.continuous_ofReal.comp (((continuumFlow_R_continuous delta u phi s).const_mul u).add continuous_const))
  simpa [continuumFlow_initial,sub_eq_add_neg,neg_mul,neg_div] using H

/-- Free continuum covariance transport at every real time. -/
theorem continuumFlow_free_covariance (delta : ℝ) (s : Moments) (t : ℝ) :
    (continuumFlow delta 0 0 s t).cov =
      continuumMeanFlow delta t*s.cov*(continuumMeanFlow delta t).transpose := by
  have H := continuumCovarianceFlow_variation_of_constants delta 0 0 s t
  simpa [continuumCovarianceFlow,continuumCovarianceSource] using H

theorem continuumFlow_free_slowEnergy (delta : ℝ) (hd : delta ≠ 0)
    (s : Moments) (t : ℝ) (ht : 0 ≤ t) :
    slowEnergy delta (continuumFlow delta 0 0 s t) = Real.exp (-t)*slowEnergy delta s := by
  have H := scalar_complex_duhamel
    (fun t => (slowEnergy delta (continuumFlow delta 0 0 s t) : ℂ)) (fun _ => 0) (-1) 0 t ht
    (fun x hx => by
      have D := (slowEnergy_hasDerivAt (continuumFlow_isMomentSolution delta 0 0 s) hd hx).ofReal_comp
      simpa using D) continuous_const
  simp only [zero_mul,mul_zero,intervalIntegral.integral_zero,add_zero,continuumFlow_initial] at H
  have H' := congrArg Complex.re H
  simpa [Complex.mul_re,Complex.exp_re] using H'

theorem continuumFlow_free_oscillatoryEnergy (delta : ℝ) (hd : delta ≠ 0)
    (lambda : ℂ) (hl : lambda+2 ≠ 0)
    (hq : lambda^2+2*lambda+4*(delta : ℂ) = 0)
    (s : Moments) (t : ℝ) (ht : 0 ≤ t) :
    oscillatoryEnergy delta lambda (continuumFlow delta 0 0 s t) =
      Complex.exp (lambda*(t : ℂ))*oscillatoryEnergy delta lambda s := by
  have H := scalar_complex_duhamel
    (fun t => oscillatoryEnergy delta lambda (continuumFlow delta 0 0 s t))
    (fun _ => 0) lambda 0 t ht
    (fun x hx => by
      simpa using oscillatoryEnergy_hasDerivAt (continuumFlow_isMomentSolution delta 0 0 s)
        hd lambda hl hq hx) continuous_const
  simpa [continuumFlow_initial] using H

def impulsedMoments (s : Moments) (c : ℝ) : Moments := ⟨s.R,s.V+c,s.C⟩

theorem impulsedMoments_cov (s : Moments) (c : ℝ) :
    (impulsedMoments s c).cov = s.cov+c • continuumKickCovariance := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [impulsedMoments,Moments.cov,continuumKickCovariance]

variable (p : Params) (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
  (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) (jury : External.JuryStability)

include hb0 hb1 hw0 hw1 jury

/-- Exact moment embedding in matched coordinates, including the V impulse. -/
theorem Params.matchedMoments_step (s : Moments) :
    p.matchedMoments (p.step s) = continuumFlow p.matchedDelta 0 0
      (impulsedMoments (p.matchedMoments s)
        (p.gridImpulseFactor*(p.renormNoise*s.R+p.renormAdditive))) p.matchedStep := by
  have H := p.exact_embedding_step hb0 hb1 hw0 hw1 jury s
  rw [← p.matchedMoments_cov,← p.matchedMoments_cov] at H
  have hk : Matrix.vecMulVec (![0,1] : Fin 2 → ℝ) ![0,1] = continuumKickCovariance := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec,continuumKickCovariance]
  rw [hk,← impulsedMoments_cov] at H
  unfold Params.matchedMeanFlow at H
  rw [← continuumFlow_free_covariance] at H
  apply Moments.ext
  · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) H
  · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) H
  · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) H

/-- Exact slow-eigenfunctional update in matched coordinates. -/
theorem Params.matched_slowEnergy_step (s : Moments) :
    slowEnergy p.matchedDelta (p.matchedMoments (p.step s)) = Real.exp (-p.matchedStep)*
      (slowEnergy p.matchedDelta (p.matchedMoments s)+p.matchedDelta*p.gridImpulseFactor*
        (p.renormNoise*s.R+p.renormAdditive)) := by
  rw [p.matchedMoments_step hb0 hb1 hw0 hw1 jury,
    continuumFlow_free_slowEnergy p.matchedDelta
      (p.matchedDelta_pos (by linarith) hb1 hw0 hw1).ne' _ _
      (p.matchedStep_pos (by linarith) hb1).le]
  unfold slowEnergy impulsedMoments
  ring

/-- Exact oscillatory-eigenfunctional update in matched coordinates. -/
theorem Params.matched_oscillatoryEnergy_step (lambda : ℂ) (hl : lambda+2 ≠ 0)
    (hq : lambda^2+2*lambda+4*(p.matchedDelta : ℂ) = 0) (s : Moments) :
    oscillatoryEnergy p.matchedDelta lambda (p.matchedMoments (p.step s)) =
      Complex.exp (lambda*(p.matchedStep : ℂ))*
        (oscillatoryEnergy p.matchedDelta lambda (p.matchedMoments s)-
          lambda*p.matchedDelta/(lambda+2)*(p.gridImpulseFactor : ℂ)*
            ((p.renormNoise*s.R+p.renormAdditive : ℝ) : ℂ)) := by
  rw [p.matchedMoments_step hb0 hb1 hw0 hw1 jury,
    continuumFlow_free_oscillatoryEnergy p.matchedDelta
      (p.matchedDelta_pos (by linarith) hb1 hw0 hw1).ne' lambda hl hq _ _
      (p.matchedStep_pos (by linarith) hb1).le]
  unfold oscillatoryEnergy impulsedMoments
  push_cast
  ring

end
end SparseSGD
