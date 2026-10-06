import SparseSGD.Comparison.ExactEmbedding
import SparseSGD.Discrete.FreeRisk
import SparseSGD.Comparison.MatchedFlow
import Mathlib.LinearAlgebra.Matrix.Rank

open scoped Matrix.Norms.Operator Matrix

namespace SparseSGD
noncomputable section

/-- Noise-free deterministic transport of a rank-one covariance. -/
theorem Params.noiseFree_rankOne_transport (p : Params) (s : Moments)
    (x : Fin 2 → ℝ) (hx : s.cov = Matrix.vecMulVec x x)
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (k : ℕ) :
    (p.trajectory s k).cov =
      Matrix.vecMulVec ((p.meanMatrix ^ k).mulVec x)
        ((p.meanMatrix ^ k).mulVec x) :=
  p.trajectory_cov_rankOne_noiseFree s hnoise hadd x hx k

/-- The risk is the square of the deterministic first coordinate, and is the
exact matched free risk on every grid point. -/
theorem Params.noiseFree_rankOne_square_root_lift (p : Params) (s : Moments)
    (x : Fin 2 → ℝ) (hx : s.cov = Matrix.vecMulVec x x)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (k : ℕ) :
    (p.trajectory s k).R = ((p.meanMatrix ^ k).mulVec x 0)^2 ∧
      (p.trajectory s k).R = p.matchedFreeRisk s ((k : ℝ)*p.matchedStep) := by
  exact ⟨p.trajectory_R_rankOne_noiseFree s hnoise hadd x hx k,
    p.noiseFree_risk_eq_matched_grid hb0 hb1 hw0 hw1 s hnoise hadd k⟩

/-- The source's uniform defect bound, with the supremum of the actual free risk. -/
theorem Params.squareRootLift_defect (jury : External.JuryStability)
    (p : Params) (s : Moments) (hs : s.psd)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))
    (hnoise : 0 ≤ p.noise) (hadd : 0 ≤ p.additive)
    (hload : p.renormNoise < 1) :
    ∀ k, 0 ≤ (p.trajectory s k).R - freeRisk p s k ∧
      (p.trajectory s k).R - freeRisk p s k ≤
        (p.renormNoise * (⨆ j, freeRisk p s j) + p.renormAdditive) /
          (1-p.renormNoise) :=
  trajectory_risk_defect_sup_bound jury p s hs hb0 hb1 hw0 hw1 hnoise hadd hload


/-- Deterministic matched-coordinate state from the actual inverse matching map. -/
def Params.squareRootLiftVector (p : Params) (x : Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  (continuumMeanFlow p.matchedDelta t).mulVec (p.matchingMatrix⁻¹.mulVec x)

def Params.squareRootLiftX (p : Params) (x : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  p.squareRootLiftVector x t 0

def Params.squareRootLiftY (p : Params) (x : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  p.squareRootLiftVector x t 1

private theorem liftMeanFlow_entry_hasDerivAt (delta t : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => continuumMeanFlow delta t i j)
      ((continuumMeanGenerator delta * continuumMeanFlow delta t) i j) t := by
  let L : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ :=
    (LinearMap.proj j : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).comp
      (LinearMap.proj i : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
  exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' (continuumMeanGenerator delta) t)

/-- The matched error coordinate solves the actual free oscillator equation. -/
theorem Params.squareRootLiftX_hasDerivAt (p : Params) (x : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (p.squareRootLiftX x) (-p.matchedDelta * p.squareRootLiftY x t) t := by
  let z := p.matchingMatrix⁻¹.mulVec x
  have h := ((liftMeanFlow_entry_hasDerivAt p.matchedDelta t 0 0).mul_const (z 0)).add
    ((liftMeanFlow_entry_hasDerivAt p.matchedDelta t 0 1).mul_const (z 1))
  convert h using 1
  · funext r
    simp [Params.squareRootLiftX, Params.squareRootLiftVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, z]
  · simp [Params.squareRootLiftY, Params.squareRootLiftVector, continuumMeanGenerator,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, z]
    ring

/-- The matched momentum coordinate solves the actual free oscillator equation. -/
theorem Params.squareRootLiftY_hasDerivAt (p : Params) (x : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (p.squareRootLiftY x) (p.squareRootLiftX x t - p.squareRootLiftY x t) t := by
  let z := p.matchingMatrix⁻¹.mulVec x
  have h := ((liftMeanFlow_entry_hasDerivAt p.matchedDelta t 1 0).mul_const (z 0)).add
    ((liftMeanFlow_entry_hasDerivAt p.matchedDelta t 1 1).mul_const (z 1))
  convert h using 1
  · funext r
    simp [Params.squareRootLiftY, Params.squareRootLiftVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, z]
  · simp [Params.squareRootLiftX, Params.squareRootLiftY, Params.squareRootLiftVector,
      continuumMeanGenerator, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, z]
    ring

/-- Elimination of the momentum gives the damped oscillator at every real time. -/
theorem Params.squareRootLift_oscillator (p : Params) (x : Fin 2 → ℝ) (t : ℝ) :
    deriv (deriv (p.squareRootLiftX x)) t + deriv (p.squareRootLiftX x) t +
      p.matchedDelta * p.squareRootLiftX x t = 0 := by
  have hX : deriv (p.squareRootLiftX x) = fun r => -p.matchedDelta * p.squareRootLiftY x r :=
    funext fun r => (p.squareRootLiftX_hasDerivAt x r).deriv
  have hXX := ((p.squareRootLiftY_hasDerivAt x t).const_mul (-p.matchedDelta)).deriv
  rw [hX, hXX]
  ring

/-- The initial matched vector is exactly the inverse image of the discrete initial vector. -/
theorem Params.squareRootLift_initial (p : Params) (x : Fin 2 → ℝ) :
    p.squareRootLiftVector x 0 = p.matchingMatrix⁻¹.mulVec x := by
  simp [Params.squareRootLiftVector, continuumMeanFlow_zero]

/-- A rank-one discrete start has the matching rank-one initial covariance. -/
theorem Params.matchedCovariance_rankOne (p : Params) (s : Moments) (x : Fin 2 → ℝ)
    (hx : s.cov = Matrix.vecMulVec x x) :
    p.matchedCovariance s = Matrix.vecMulVec (p.matchingMatrix⁻¹.mulVec x)
      (p.matchingMatrix⁻¹.mulVec x) := by
  rw [Params.matchedCovariance, hx, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

/-- The matched free risk is the square of the deterministic lift at every real time. -/
theorem Params.matchedFreeRisk_squareRootLift (p : Params) (s : Moments) (x : Fin 2 → ℝ)
    (hx : s.cov = Matrix.vecMulVec x x) (t : ℝ) :
    p.matchedFreeRisk s t = (p.squareRootLiftX x t)^2 := by
  rw [Params.matchedFreeRisk, p.matchedCovariance_rankOne s x hx,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  simp [Params.squareRootLiftX, Params.squareRootLiftVector, Matrix.vecMulVec, pow_two]

/-- Source corollary 7(i): exact squared oscillator risk on the retention grid. -/
theorem Params.noiseFree_risk_squareRootLift_grid (p : Params) (s : Moments) (x : Fin 2 → ℝ)
    (hx : s.cov = Matrix.vecMulVec x x)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (k : ℕ) :
    (p.trajectory s k).R = (p.squareRootLiftX x ((k : ℝ)*p.matchedStep))^2 := by
  rw [p.noiseFree_risk_eq_matched_grid hb0 hb1 hw0 hw1 s hnoise hadd,
    p.matchedFreeRisk_squareRootLift s x hx]

private theorem rank_outer_product_nonzero (x : Fin 2 → ℝ) (hx : x ≠ 0) :
    (Matrix.vecMulVec x x).rank = 1 := by
  have hupper := Matrix.rank_vecMulVec_le x x
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hx
    funext i
    exact hn i
  let B : Matrix (Fin 1) (Fin 1) ℝ := (Matrix.vecMulVec x x).submatrix (fun _ => i) (fun _ => i)
  have hdet : B.det ≠ 0 := by simpa [B, Matrix.det_fin_one, Matrix.vecMulVec] using mul_ne_zero hi hi
  have hlower := Matrix.rank_submatrix_le (Matrix.vecMulVec x x) (fun _ : Fin 1 => i) (fun _ : Fin 1 => i)
  have hrank : B.rank = 1 := by simpa using Matrix.rank_of_det_ne_zero hdet
  change B.rank ≤ _ at hlower
  rw [hrank] at hlower
  omega

/-- Noise-free covariance transport preserves its exact matrix rank. -/
theorem Params.noiseFree_covariance_rank (p : Params) (s : Moments) (hb : p.beta ≠ 0)
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (k : ℕ) :
    (p.trajectory s k).cov.rank = s.cov.rank := by
  have hdet : (p.meanMatrix^k).det ≠ 0 := by rw [Matrix.det_pow,p.det_meanMatrix]; exact pow_ne_zero _ hb
  rw [p.trajectory_cov_noiseFree s hnoise hadd,
    Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (by simpa using hdet),
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hdet]

/-- A nonzero rank-one start stays of exact rank one, including every grid point. -/
theorem Params.noiseFree_rankOne_rank (p : Params) (s : Moments) (x : Fin 2 → ℝ)
    (hx : s.cov = Matrix.vecMulVec x x) (hne : x ≠ 0) (hb : p.beta ≠ 0)
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (k : ℕ) :
    (p.trajectory s k).cov.rank = 1 := by
  rw [p.noiseFree_covariance_rank s hb hnoise hadd, hx]
  exact rank_outer_product_nonzero x hne

/-- The zero outer-product start remains rank zero. -/
theorem Params.noiseFree_zero_rank (p : Params) (s : Moments)
    (hx : s.cov = Matrix.vecMulVec (0 : Fin 2 → ℝ) 0)
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (k : ℕ) :
    (p.trajectory s k).cov.rank = 0 := by
  rw [p.noiseFree_rankOne_transport s 0 hx hnoise hadd]
  simp


/-- The actual matched free moment flow is the second moment of the deterministic lift. -/
theorem Params.continuumFreeFlow_squareRootLift_cov (p : Params) (s : Moments) (x : Fin 2 → ℝ)
    (hx : s.cov = Matrix.vecMulVec x x) (t : ℝ) :
    (continuumFlow p.matchedDelta 0 0 (p.matchedMoments s) t).cov =
      Matrix.vecMulVec (p.squareRootLiftVector x t) (p.squareRootLiftVector x t) := by
  have h := continuumCovarianceFlow_variation_of_constants p.matchedDelta 0 0 (p.matchedMoments s) t
  simp only [continuumCovarianceSource, zero_mul, add_zero, mul_zero, zero_smul,
    Matrix.mul_zero, Matrix.zero_mul, intervalIntegral.integral_zero, add_zero] at h
  change _ = _ at h
  rw [p.matchedMoments_cov, p.matchedCovariance_rankOne s x hx,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose] at h
  exact h

/-- With zero feedback and temperature, the actual comparison flow has the deterministic lifted covariance. -/
theorem Params.comparisonFlow_squareRootLift_cov (p : Params) (s : Moments) (x : Fin 2 → ℝ)
    (hx : s.cov = Matrix.vecMulVec x x) (hnoise : p.noise = 0) (hadd : p.additive = 0)
    (t : ℝ) : (p.comparisonFlow s t).cov =
      Matrix.vecMulVec (p.squareRootLiftVector x t) (p.squareRootLiftVector x t) := by
  simpa only [Params.comparisonFlow, Params.renormNoise, Params.renormAdditive,
    hnoise, hadd, zero_div] using p.continuumFreeFlow_squareRootLift_cov s x hx t

/-- The actual noise-free comparison risk is a squared oscillator at every real time. -/
theorem Params.comparisonFlow_squareRootLift_R (p : Params) (s : Moments) (x : Fin 2 → ℝ)
    (hx : s.cov = Matrix.vecMulVec x x) (hnoise : p.noise = 0) (hadd : p.additive = 0)
    (t : ℝ) : (p.comparisonFlow s t).R = (p.squareRootLiftX x t)^2 := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0)
    (p.comparisonFlow_squareRootLift_cov s x hx hnoise hadd t)
  simpa [Moments.cov, Matrix.vecMulVec, Params.squareRootLiftX, pow_two] using h

/-- An invertible matching map and fundamental matrix preserve nonzero initial vectors. -/
theorem Params.squareRootLiftVector_ne_zero (p : Params) (x : Fin 2 → ℝ) (hx : x ≠ 0)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) (t : ℝ) :
    p.squareRootLiftVector x t ≠ 0 := by
  have hP : IsUnit p.matchingMatrix.det :=
    isUnit_iff_ne_zero.mpr (p.matchingMatrix_det_ne_zero hb0 hb1 hw0 hw1)
  have hPi := Matrix.mulVec_injective_of_det_ne_zero
    ((p.matchingMatrix.isUnit_nonsing_inv_det hP).ne_zero)
  have hE : IsUnit (continuumMeanFlow p.matchedDelta t) :=
    NormedSpace.isUnit_exp (t • continuumMeanGenerator p.matchedDelta)
  have hEi := Matrix.mulVec_injective_of_isUnit hE
  have hinj : Function.Injective (fun z => p.squareRootLiftVector z t) := hEi.comp hPi
  intro hz
  apply hx
  apply hinj
  simpa [Params.squareRootLiftVector] using hz

/-- A nonzero noise-free comparison covariance stays of exact rank one at every real time. -/
theorem Params.comparisonFlow_squareRootLift_rank (p : Params) (s : Moments) (x : Fin 2 → ℝ)
    (hx : s.cov = Matrix.vecMulVec x x) (hne : x ≠ 0)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (t : ℝ) :
    (p.comparisonFlow s t).cov.rank = 1 := by
  rw [p.comparisonFlow_squareRootLift_cov s x hx hnoise hadd]
  exact rank_outer_product_nonzero _ (p.squareRootLiftVector_ne_zero x hne hb0 hb1 hw0 hw1 t)

/-- The zero lift remains rank zero at every real time. -/
theorem Params.comparisonFlow_zero_rank (p : Params) (s : Moments)
    (hx : s.cov = Matrix.vecMulVec (0 : Fin 2 → ℝ) 0)
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (t : ℝ) :
    (p.comparisonFlow s t).cov.rank = 0 := by
  rw [p.comparisonFlow_squareRootLift_cov s 0 hx hnoise hadd]
  simp [Params.squareRootLiftVector]


/-- The derivative of the lifted error is itself differentiable with the oscillator acceleration. -/
theorem Params.squareRootLiftX_second_hasDerivAt (p : Params) (x : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (deriv (p.squareRootLiftX x))
      (-deriv (p.squareRootLiftX x) t - p.matchedDelta * p.squareRootLiftX x t) t := by
  have hX : deriv (p.squareRootLiftX x) = fun r => -p.matchedDelta * p.squareRootLiftY x r :=
    funext fun r => (p.squareRootLiftX_hasDerivAt x r).deriv
  rw [hX]
  convert (p.squareRootLiftY_hasDerivAt x t).const_mul (-p.matchedDelta) using 1 <;>
    first | rfl | ring

/-- Source corollary 7(ii), measured directly against the squared matched oscillator
from the same rank-one start. The estimate holds at every discrete time. -/
theorem Params.squareRootLift_oscillator_defect (jury : External.JuryStability)
    (p : Params) (s : Moments) (hs : s.psd) (x : Fin 2 → ℝ)
    (hx : s.cov = Matrix.vecMulVec x x)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))
    (hnoise : 0 ≤ p.noise) (hadd : 0 ≤ p.additive) (hload : p.renormNoise < 1) :
    ∀ k, 0 ≤ (p.trajectory s k).R - (p.squareRootLiftX x ((k : ℝ)*p.matchedStep))^2 ∧
      (p.trajectory s k).R - (p.squareRootLiftX x ((k : ℝ)*p.matchedStep))^2 ≤
        (p.renormNoise * (⨆ j : ℕ, (p.squareRootLiftX x ((j : ℝ)*p.matchedStep))^2) +
          p.renormAdditive) / (1-p.renormNoise) := by
  have hfree (j : ℕ) : freeRisk p s j = (p.squareRootLiftX x ((j : ℝ)*p.matchedStep))^2 := by
    rw [p.freeRisk_eq_matched_grid hb0 hb1 hw0 hw1 s j,
      p.matchedFreeRisk_squareRootLift s x hx]
  have H := squareRootLift_defect jury p s hs hb0 hb1 hw0 hw1 hnoise hadd hload
  simp_rw [hfree] at H
  exact H

end
end SparseSGD
