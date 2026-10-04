import SparseSGD.Comparison.ConvolutionQuadrature

namespace SparseSGD
noncomputable section

def Params.matchedMoments (p : Params) (s : Moments) : Moments :=
  ⟨p.matchedCovariance s 0 0, p.matchedCovariance s 1 1, p.matchedCovariance s 0 1⟩

theorem Params.matchedCovariance_symmetric (p : Params) (s : Moments) :
    (p.matchedCovariance s).transpose = p.matchedCovariance s := by
  have hs : s.cov.transpose = s.cov := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  simp only [Params.matchedCovariance, Matrix.transpose_mul, Matrix.transpose_transpose, hs]
  rw [Matrix.mul_assoc]

theorem Params.matchedMoments_cov (p : Params) (s : Moments) :
    (p.matchedMoments s).cov = p.matchedCovariance s := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1)
    (p.matchedCovariance_symmetric s)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Params.matchedMoments,Moments.cov] <;> exact h.symm

theorem Params.matchedMoments_psd (p : Params) (s : Moments) (hs : s.psd) :
    (p.matchedMoments s).psd := by
  change (p.matchedMoments s).cov.PosSemidef
  rw [p.matchedMoments_cov]
  simpa only [Params.matchedCovariance, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hs.mul_mul_conjTranspose_same p.matchingMatrix⁻¹

theorem Params.matchedFreeRisk_eq_continuumFreeRisk (p : Params) (s : Moments) (t : ℝ) :
    p.matchedFreeRisk s t = continuumFreeRisk p.matchedDelta (p.matchedMoments s) t := by
  simp only [Params.matchedFreeRisk, continuumFreeRisk, p.matchedMoments_cov]

/-- The concrete continuum solution at the paper's matched parameters and initial covariance. -/
def Params.comparisonFlow (p : Params) (s : Moments) (t : ℝ) : Moments :=
  continuumFlow p.matchedDelta p.renormNoise p.renormAdditive (p.matchedMoments s) t

def Params.comparisonInitialSize (p : Params) (s : Moments) : ℝ :=
  (p.matchedMoments s).R + p.matchedDelta*(p.matchedMoments s).V + |(p.matchedMoments s).C|

end
end SparseSGD
