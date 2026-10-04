import SparseSGD.Comparison.FunctionalEmbedding
import SparseSGD.Comparison.NormalizationBound

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

theorem scalar_grid_unroll (q f : ℕ → ℂ) (r b : ℂ)
    (hq : ∀ k, q (k+1) = r*(q k+b*f k)) (k : ℕ) :
    q k = r^k*q 0+b*(∑ j ∈ Finset.range k, r^(k-j)*f j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hq,ih,Finset.sum_range_succ]
    have hsum : (∑ j ∈ Finset.range k, r^(k+1-j)*f j) =
        r*(∑ j ∈ Finset.range k, r^(k-j)*f j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk := Finset.mem_range.mp hj
      rw [show k+1-j = (k-j)+1 by omega,pow_succ]
      ring
    rw [hsum,show k+1-k = 1 by omega,pow_one,pow_succ]
    ring

def sampledFunctionalConvolution (lambda : ℂ) (h : ℝ) (f : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range k, (h : ℂ)*Complex.exp (lambda*((k-j : ℕ) : ℂ)*(h : ℂ))*f j

theorem scalar_exponential_grid_unroll (q f : ℕ → ℂ) (lambda b : ℂ) (h : ℝ)
    (hh : h ≠ 0) (hq : ∀ k, q (k+1) = Complex.exp (lambda*(h : ℂ))*(q k+b*f k)) (k : ℕ) :
    q k = Complex.exp (lambda*(k : ℂ)*(h : ℂ))*q 0+
      (b/(h : ℂ))*sampledFunctionalConvolution lambda h f k := by
  rw [scalar_grid_unroll q f (Complex.exp (lambda*(h : ℂ))) b hq k]
  have hexp (n : ℕ) : Complex.exp (lambda*(h : ℂ))^n =
      Complex.exp (lambda*(n : ℂ)*(h : ℂ)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  simp_rw [hexp]
  unfold sampledFunctionalConvolution
  rw [Finset.mul_sum,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hhc : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  field_simp

/-- Exact equality between the functional grid sum and right-endpoint sampling. -/
theorem sampledFunctionalConvolution_eq_rightEndpoint (lambda : ℂ) (h : ℝ) (f : ℝ → ℂ) (k : ℕ) :
    sampledFunctionalConvolution lambda h (fun j => f ((j : ℝ)*h)) k =
      rightEndpointSum (fun x => Complex.exp (lambda*(x : ℂ))*f ((k : ℝ)*h-x)) h k := by
  unfold sampledFunctionalConvolution rightEndpointSum
  conv_rhs => rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk := Finset.mem_range.mp hj
  have hlag : k-1-j+1 = k-j := by omega
  have htime : (k : ℝ)*h-((k-j : ℕ) : ℝ)*h = (j : ℝ)*h := by
    rw [Nat.cast_sub hjk.le]
    ring
  rw [hlag]
  dsimp only
  rw [htime]
  simp [Complex.real_smul]
  push_cast
  ring

variable (p : Params) (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
  (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) (jury : External.JuryStability)
include hb0 hb1 hw0 hw1 jury

theorem Params.gridImpulseFactor_eq_normalized_step :
    p.gridImpulseFactor = 2*p.matchedStep/(p.matchedDelta*p.sampledKernelMass) := by
  have hs := p.sampledImpulse_sq_tsum_pos hb0 hb1 hw0 hw1 jury
  have hd := p.matchedDelta_pos (by linarith) hb1 hw0 hw1
  have hm : p.sampledKernelMass = p.matchedStep*(2/p.matchedDelta)*
      (∑' n : ℕ, p.sampledImpulse (n+1)^2) := by
    unfold Params.sampledKernelMass Params.sampledImpulse continuumRenewalKernel
    simp only [tsum_mul_left]
    ring
  have hh := p.matchedStep_pos (by linarith) hb1
  rw [hm]
  unfold Params.gridImpulseFactor
  field_simp [hs.ne',hd.ne',hh.ne']

/-- Exact slow functional grid formula in actual matched coordinates. -/
theorem Params.matched_slowEnergy_grid (s : Moments) (k : ℕ) :
    (slowEnergy p.matchedDelta (p.matchedMoments (p.trajectory s k)) : ℂ) =
      Complex.exp (-((k : ℝ)*p.matchedStep : ℝ))*
        (slowEnergy p.matchedDelta (p.matchedMoments s) : ℂ)+
      (2/(p.sampledKernelMass : ℂ))*sampledFunctionalConvolution (-1) p.matchedStep
        (fun j => ((p.renormNoise*(p.trajectory s j).R+p.renormAdditive : ℝ) : ℂ)) k := by
  have hh := p.matchedStep_pos (by linarith) hb1
  have H := scalar_exponential_grid_unroll
    (fun j => (slowEnergy p.matchedDelta (p.matchedMoments (p.trajectory s j)) : ℂ))
    (fun j => ((p.renormNoise*(p.trajectory s j).R+p.renormAdditive : ℝ) : ℂ)) (-1)
    ((p.matchedDelta*p.gridImpulseFactor : ℝ) : ℂ) p.matchedStep hh.ne'
    (fun j => by
      rw [Params.trajectory]
      have J := congrArg Complex.ofReal (p.matched_slowEnergy_step hb0 hb1 hw0 hw1 jury (p.trajectory s j))
      simpa using J) k
  simp only [Params.trajectory,neg_mul,one_mul] at H
  rw [p.gridImpulseFactor_eq_normalized_step hb0 hb1 hw0 hw1 jury] at H
  have hdc : (p.matchedDelta : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (p.matchedDelta_pos (by linarith) hb1 hw0 hw1).ne'
  have hhc : (p.matchedStep : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hmc : (p.sampledKernelMass : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (p.sampledKernelMass_pos hb0 hb1 hw0 hw1 jury).ne'
  convert H using 1 <;> push_cast <;> field_simp [hdc,hhc,hmc] <;> ring

/-- Exact oscillatory functional grid formula in actual matched coordinates. -/
theorem Params.matched_oscillatoryEnergy_grid (lambda : ℂ) (hl : lambda+2 ≠ 0)
    (hq : lambda^2+2*lambda+4*(p.matchedDelta : ℂ) = 0) (s : Moments) (k : ℕ) :
    oscillatoryEnergy p.matchedDelta lambda (p.matchedMoments (p.trajectory s k)) =
      Complex.exp (lambda*((k : ℝ)*p.matchedStep : ℝ))*
        oscillatoryEnergy p.matchedDelta lambda (p.matchedMoments s)-
      ((2*lambda/(lambda+2))/(p.sampledKernelMass : ℂ))*
        sampledFunctionalConvolution lambda p.matchedStep
          (fun j => ((p.renormNoise*(p.trajectory s j).R+p.renormAdditive : ℝ) : ℂ)) k := by
  have hh := p.matchedStep_pos (by linarith) hb1
  have H := scalar_exponential_grid_unroll
    (fun j => oscillatoryEnergy p.matchedDelta lambda (p.matchedMoments (p.trajectory s j)))
    (fun j => ((p.renormNoise*(p.trajectory s j).R+p.renormAdditive : ℝ) : ℂ)) lambda
    (-lambda*p.matchedDelta/(lambda+2)*(p.gridImpulseFactor : ℂ)) p.matchedStep hh.ne'
    (fun j => by
      rw [Params.trajectory]
      convert p.matched_oscillatoryEnergy_step hb0 hb1 hw0 hw1 jury lambda hl hq (p.trajectory s j)
        using 1 <;> ring) k
  simp only [Params.trajectory] at H
  rw [p.gridImpulseFactor_eq_normalized_step hb0 hb1 hw0 hw1 jury] at H
  have hdc : (p.matchedDelta : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (p.matchedDelta_pos (by linarith) hb1 hw0 hw1).ne'
  have hhc : (p.matchedStep : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hmc : (p.sampledKernelMass : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (p.sampledKernelMass_pos hb0 hb1 hw0 hw1 jury).ne'
  convert H using 1 <;> push_cast <;> field_simp [hdc,hhc,hmc] <;> ring

end
end SparseSGD
