import SparseSGD.Continuum.Flow

open scoped Matrix.Norms.Operator
open NormedSpace

namespace SparseSGD

noncomputable section

/-- The covariance matrix along the concrete matrix-exponential continuum flow. -/
def continuumCovarianceFlow (delta u phi : ℝ) (s : Moments) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (continuumFlow delta u phi s t).cov

/-- Generator of the free two-coordinate oscillator. -/
def continuumMeanGenerator (delta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -delta; 1, -1]

/-- Fundamental matrix of the free oscillator. -/
def continuumMeanFlow (delta t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  NormedSpace.exp (t • continuumMeanGenerator delta)

/-- The covariance of a unit kick in the second coordinate. -/
def continuumKickCovariance : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

/-- Covariance injection rate in the continuum moment equations. -/
def continuumCovarianceSource (delta u phi : ℝ) (s : Moments) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (2 / delta * (u * s.R + phi)) • continuumKickCovariance

theorem continuumCovarianceFlow_initial (delta u phi : ℝ) (s : Moments) :
    continuumCovarianceFlow delta u phi s 0 = s.cov := by
  simp [continuumCovarianceFlow, continuumFlow_initial]

theorem continuumCovarianceFlow_hasDerivAt_R (delta u phi : ℝ) (s : Moments) (t : ℝ) :
    HasDerivAt (fun t => (continuumCovarianceFlow delta u phi s t) 0 0)
      (continuumField delta u phi (continuumFlow delta u phi s t)).R t := by
  simpa [continuumCovarianceFlow, Moments.cov] using
    (continuumFlow_hasDerivAt delta u phi s t).1

theorem continuumField_covariance (delta u phi : ℝ) (s : Moments) :
    (continuumField delta u phi s).cov =
      continuumMeanGenerator delta * s.cov + s.cov * (continuumMeanGenerator delta).transpose +
        continuumCovarianceSource delta u phi s := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [continuumField, Moments.cov, continuumMeanGenerator,
      continuumCovarianceSource, continuumKickCovariance] <;> ring

/-- The concrete covariance flow solves the inhomogeneous Lyapunov differential equation. -/
theorem continuumCovarianceFlow_hasDerivAt (delta u phi : ℝ) (s : Moments) (t : ℝ) :
    HasDerivAt (continuumCovarianceFlow delta u phi s)
      (continuumMeanGenerator delta * continuumCovarianceFlow delta u phi s t +
        continuumCovarianceFlow delta u phi s t * (continuumMeanGenerator delta).transpose +
        continuumCovarianceSource delta u phi (continuumFlow delta u phi s t)) t := by
  change HasDerivAt (continuumCovarianceFlow delta u phi s)
    (continuumMeanGenerator delta * (continuumFlow delta u phi s t).cov +
      (continuumFlow delta u phi s t).cov * (continuumMeanGenerator delta).transpose +
      continuumCovarianceSource delta u phi (continuumFlow delta u phi s t)) t
  rw [← continuumField_covariance]
  obtain ⟨hR, hV, hC⟩ := continuumFlow_hasDerivAt delta u phi s t
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [continuumCovarianceFlow, Moments.cov] using hR
  · simpa [continuumCovarianceFlow, Moments.cov] using hC
  · simpa [continuumCovarianceFlow, Moments.cov] using hC
  · simpa [continuumCovarianceFlow, Moments.cov] using hV

theorem continuumMeanFlow_zero (delta : ℝ) : continuumMeanFlow delta 0 = 1 := by
  simp [continuumMeanFlow]

theorem continuumMeanFlow_hasDerivAt (delta t : ℝ) :
    HasDerivAt (continuumMeanFlow delta)
      (continuumMeanFlow delta t * continuumMeanGenerator delta) t := by
  exact hasDerivAt_exp_smul_const (continuumMeanGenerator delta) t

/-- Differentiation commutes with matrix transpose. -/
private theorem hasDerivAt_matrix_transpose {f : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {f' : Matrix (Fin 2) (Fin 2) ℝ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun x => (f x).transpose) f'.transpose t := by
  let L := (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) ℝ ℝ).toLinearMap.toContinuousLinearMap
  exact L.hasFDerivAt.comp_hasDerivAt t h

/-- Covariance transported back from a fixed terminal time has only the noise derivative. -/
theorem continuumCovarianceFlow_transport_hasDerivAt
    (delta u phi : ℝ) (s : Moments) (t x : ℝ) :
    HasDerivAt (fun x => continuumMeanFlow delta (t - x) *
        continuumCovarianceFlow delta u phi s x * (continuumMeanFlow delta (t - x)).transpose)
      (continuumMeanFlow delta (t - x) *
        continuumCovarianceSource delta u phi (continuumFlow delta u phi s x) *
        (continuumMeanFlow delta (t - x)).transpose) x := by
  have hP := (continuumMeanFlow_hasDerivAt delta (t - x)).scomp x
    ((hasDerivAt_const x t).sub (hasDerivAt_id x))
  have hPT := hasDerivAt_matrix_transpose hP
  have hS := continuumCovarianceFlow_hasDerivAt delta u phi s x
  convert (hP.mul hS).mul hPT using 1 <;>
    first | rfl | (simp only [Function.comp_apply, Pi.mul_apply, zero_sub, neg_smul,
      one_smul, Matrix.transpose_neg, Matrix.transpose_mul]; noncomm_ring)

/-- The matrix-exponential oscillator flow is continuous. -/
theorem continuumMeanFlow_continuous (delta : ℝ) : Continuous (continuumMeanFlow delta) :=
  continuous_iff_continuousAt.mpr (fun t => (continuumMeanFlow_hasDerivAt delta t).continuousAt)

/-- The explicit continuum moment risk is continuous on the whole real line. -/
theorem continuumFlow_R_continuous (delta u phi : ℝ) (s : Moments) :
    Continuous (fun t => (continuumFlow delta u phi s t).R) :=
  continuous_iff_continuousAt.mpr
    (fun t => (continuumFlow_hasDerivAt delta u phi s t).1.continuousAt)

/-- Variation of constants for the actual continuum covariance flow. -/
theorem continuumCovarianceFlow_variation_of_constants
    (delta u phi : ℝ) (s : Moments) (t : ℝ) :
    continuumCovarianceFlow delta u phi s t =
      continuumMeanFlow delta t * s.cov * (continuumMeanFlow delta t).transpose +
        ∫ x in (0 : ℝ)..t, continuumMeanFlow delta (t - x) *
          continuumCovarianceSource delta u phi (continuumFlow delta u phi s x) *
          (continuumMeanFlow delta (t - x)).transpose := by
  have hint : Continuous (fun x => continuumMeanFlow delta (t - x) *
      continuumCovarianceSource delta u phi (continuumFlow delta u phi s x) *
      (continuumMeanFlow delta (t - x)).transpose) := by
    have hP : Continuous (fun x : ℝ => continuumMeanFlow delta (t - x)) :=
      (continuumMeanFlow_continuous delta).comp (continuous_const.sub continuous_id)
    have hQ : Continuous (fun x => continuumCovarianceSource delta u phi
        (continuumFlow delta u phi s x)) := by
      exact (continuous_const.mul
        ((continuous_const.mul (continuumFlow_R_continuous delta u phi s)).add continuous_const)).smul
          continuous_const
    exact (hP.mul hQ).mul hP.matrix_transpose
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => continuumCovarianceFlow_transport_hasDerivAt delta u phi s t x)
    (hint.intervalIntegrable 0 t)
  simp only [sub_self, continuumMeanFlow_zero, one_mul, Matrix.transpose_one, mul_one,
    sub_zero, continuumCovarianceFlow_initial] at h
  rw [h]
  abel

end
end SparseSGD
