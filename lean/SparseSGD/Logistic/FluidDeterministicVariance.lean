import SparseSGD.Logistic.FluidDeterministicPhysical
open MeasureTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000
def scalarFrameMu (rr : ℝ) : Vec 2 := WithLp.toLp 2 ![rr,0]
def scalarFrameTheta (t R : ℝ) : Vec 2 := WithLp.toLp 2 ![t,Real.sqrt R]
theorem scalarFrameMu_norm (rr : ℝ) (hr : 0≤rr) : r (scalarFrameMu rr)=rr := by
  have H : ‖scalarFrameMu rr‖^2=rr^2 := by
    simp [EuclideanSpace.real_norm_sq_eq,scalarFrameMu,Fin.sum_univ_succ]
  unfold r
  nlinarith [norm_nonneg (scalarFrameMu rr)]
theorem scalarFrameTheta_norm (t R : ℝ) (hR : 0≤R) :
    ‖scalarFrameTheta t R‖^2=t^2+R := by
  simp [EuclideanSpace.real_norm_sq_eq,scalarFrameTheta,Fin.sum_univ_succ,Real.sq_sqrt hR]
theorem scalarFrameTheta_signal (rr t R : ℝ) (hr : 0<rr) :
    signalCoord (scalarFrameMu rr) (scalarFrameTheta t R)=t := by
  unfold signalCoord
  rw [scalarFrameMu_norm rr hr.le]
  have hi : inner ℝ (scalarFrameTheta t R) (scalarFrameMu rr)=t*rr := by
    simp [EuclideanSpace.inner_eq_star_dotProduct,scalarFrameMu,scalarFrameTheta,
      dotProduct,Fin.sum_univ_succ,mul_comm]
  rw [hi,mul_div_cancel_right₀ t hr.ne']
theorem scalar_bulk_variance_nonneg
    (S : SparseSGD.External.GaussianSteinCertificate 2) (p : unitInterval)
    (rr t R : ℝ) (hr : 0<rr) (hR : 0≤R) :
    0 ≤ scalarCoefD0 p rr t (t^2+R)+R*(scalarCoefDtheta p rr t (t^2+R)-(scalarCoefA p rr t (t^2+R))^2) := by
  let mu := scalarFrameMu rr
  let theta := scalarFrameTheta t R
  have hmu : r mu=rr := scalarFrameMu_norm rr hr.le
  have htheta : ‖theta‖^2=t^2+R := scalarFrameTheta_norm t R hR
  have hsignal : signalCoord mu theta=t := scalarFrameTheta_signal rr t R hr
  have hbulk : ‖bulkPart mu theta‖^2=R := by
    have H := bulkPart_norm_sq mu theta (by simpa [hmu] using hr)
    rw [← div_pow] at H
    change ‖bulkPart mu theta‖^2=‖theta‖^2-(signalCoord mu theta)^2 at H
    rw [htheta,hsignal] at H
    linarith
  have H := bulkResidual_norm_sq_integral (B:=1) S (by norm_num) p mu theta (by simpa [hmu] using hr)
  have h0 : 0≤∫ a : Batch 2 1, ‖bulkResidual p mu theta a‖^2 ∂batchLaw 2 1 p := integral_nonneg (fun _ =>sq_nonneg _)
  rw [H,coefA_eq_scalar p mu theta (by simpa [hmu] using hr),
    coefD0_eq_scalar p mu theta (by simpa [hmu] using hr),
    coefDtheta_eq_scalar p mu theta (by simpa [hmu] using hr),hmu,htheta,hsignal,hbulk] at h0
  norm_num at h0
  nlinarith
theorem scalarCoefD0_nonneg (p : unitInterval) (rr t q : ℝ) :
    0 ≤ scalarCoefD0 p rr t q := by
  unfold scalarCoefD0 SparseSGD.Probability.gaussianAverage
  exact add_nonneg (mul_nonneg (by linarith [p.property.2]) (integral_nonneg (fun _ =>sq_nonneg _)))
    (mul_nonneg p.property.1 (integral_nonneg (fun _ =>sq_nonneg _)))

/-- The actual scalar bulk variance is nonnegative on the physical cone.
A two-dimensional Gaussian realization discharges the variance assertion. -/
theorem matchedDriftMap_physical {d B : ℕ}
    (S : SparseSGD.External.GaussianSteinCertificate 2) (hd : 2≤d) (hB : 0<B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (hr : 0<r mu)
    {y : Fin 5 → ℝ} (hy : matchedPhysical y) :
    matchedPhysical (matchedDriftMap (B:=B) eta beta p mu y) := by
  unfold matchedDriftMap
  apply matchedCoefficientStep_physical _ _ _ _ _ _ hy
  apply div_nonneg _ (by positivity : (0:ℝ)≤(B:ℝ))
  have hvar := scalar_bulk_variance_nonneg S p (r mu) (y 0) (y 2) hr hy.1
  have hD := scalarCoefD0_nonneg p (r mu) (y 0) ((y 0)^2+y 2)
  have hd' : (2:ℝ)≤(d:ℝ) := by exact_mod_cast hd
  nlinarith [mul_nonneg (by linarith : 0≤(d:ℝ)-2) hD]

theorem matchedDriftOrbit_physical {d B : ℕ}
    (S : SparseSGD.External.GaussianSteinCertificate 2) (hd : 2≤d) (hB : 0<B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (hr : 0<r mu)
    (y : ℕ→Fin 5→ℝ) (h0 : matchedPhysical (y 0))
    (hstep : ∀ n, y (n+1)=matchedDriftMap (B:=B) eta beta p mu (y n)) :
    ∀ n, matchedPhysical (y n) := by
  intro n
  induction n with
  | zero =>exact h0
  | succ n ih =>rw [hstep];exact matchedDriftMap_physical S hd hB eta beta p mu hr ih
end
end SparseSGD.Logistic
