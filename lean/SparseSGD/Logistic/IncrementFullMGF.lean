import SparseSGD.Logistic.IncrementBulkBounds
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

def lrIncrementVariance {d : ℕ} (eta : ℝ) (p : unitInterval) (mu : Vec d)
    (Q K L : ℝ) (B : ℕ) : ℝ :=
  4*((eta*stoppedDirectionBound Q K L)^2*projectionVariance p mu Q/(B : ℝ)+
    (3*eta^2)^2*bulkQuadraticVariance Q p d B)

def lrIncrementScale {d : ℕ} (eta : ℝ) (mu : Vec d) (Q K L : ℝ) (B : ℕ) : ℝ :=
  2*((eta*stoppedDirectionBound Q K L)*projectionScale mu/(B : ℝ)+
    (3*eta^2)*bulkQuadraticScale Q d B)

/-- The full actual five-coordinate LR increment satisfies the two-sided
unit-dual Bernstein bound on a bounded stopped neighborhood. The effective
learning-step correction is the explicit hypothesis `eta*p ≤ L`. -/
theorem tame_matchedIncrement_dual_mgf {d B : ℕ}
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (J : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : SparseSGD.External.GaussianSteinCertificate d)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d)
    (ell : (Fin 5 → ℝ) →L[ℝ] ℝ) (Q K L t : ℝ)
    (hB : 0 < B) (hp : 0 < (p : ℝ)) (hr : 0 < r mu)
    (heta : 0 ≤ eta) (hbeta : 0 ≤ beta) (hbeta1 : beta < 1) (hell : ‖ell‖ ≤ 1)
    (htame : tameError p mu s.1 ≤ 1/2) (hθ : ‖s.1‖ ≤ Q)
    (hm : ‖(eta/(1-beta)) • bulkPart mu s.2‖ ≤ K) (hstep : eta*(p : ℝ) ≤ L)
    (ht : |t| * lrIncrementScale eta mu Q K L B < 1) :
    Integrable (fun a : Batch d B => Real.exp (t*ell (matchedIncrement eta beta p mu s a))) (batchLaw d B p) ∧
    (∫ a : Batch d B, Real.exp (t*ell (matchedIncrement eta beta p mu s a)) ∂batchLaw d B p) ≤
      Real.exp (t^2*lrIncrementVariance eta p mu Q K L B/(2*(1-|t| * lrIncrementScale eta mu Q K L B))) := by
  let u := matchedDualLinearDirection (B := B) eta beta p mu (fun i => ell (Pi.single i 1)) s
  let c := matchedDualQuadraticCoefficient eta beta (fun i => ell (Pi.single i 1))
  let D := eta*stoppedDirectionBound Q K L
  let f := fun a : Batch d B => inner ℝ u (centeredBatchGradient p mu s.1 a)
  let g := centeredBulkSquare (B := B) p mu s.1
  have hQ : 0 ≤ Q := (norm_nonneg _).trans hθ
  have hK : 0 ≤ K := (norm_nonneg _).trans hm
  have hL : 0 ≤ L := (mul_nonneg heta hp.le).trans hstep
  have hD : 0 ≤ D := by dsimp [D, stoppedDirectionBound]; positivity
  have hu : ‖u‖ ≤ D := matchedDualLinearDirection_norm_le_bounded_learning_step S eta beta p mu ell s
    Q K L hB hr heta hbeta hbeta1 hell hp htame hθ hm hstep
  have hc : |c| ≤ 3*eta^2 := matchedDualQuadraticCoefficient_abs_le _ hbeta hbeta1
    (fun i => (matched_dual_coordinate_abs_le ell i).trans hell)
  have hδm : Measurable (fun a : Batch d B => centeredBatchGradient p mu s.1 a) :=
    (measurable_centeredBatchGradient p mu).comp
      (f := fun a : Batch d B => (s.1,a)) (measurable_const.prodMk measurable_id)
  have hfm : Measurable f := measurable_const.inner hδm
  have hgm : Measurable g := ((measurable_bulkPart mu).comp hδm).norm.pow_const 2 |>.sub measurable_const
  have hv1 : 0 ≤ D^2*projectionVariance p mu Q/(B : ℝ) := by
    dsimp [projectionVariance, rareProjectionConstant]
    positivity
  have hv2 : 0 ≤ bulkQuadraticVariance Q p d B := by
    dsimp [bulkQuadraticVariance, bulkQuadraticConstant, complementQuadraticVariance, symmetricProjectionConstant]
    positivity
  have hM1 : 0 ≤ D*projectionScale mu/(B : ℝ) := by dsimp [projectionScale]; positivity
  have hM2 : 0 ≤ bulkQuadraticScale Q d B := by dsimp [bulkQuadraticScale,symmetricProjectionConstant]; positivity
  have h1 (x : ℝ) (hx : |x| * (D*projectionScale mu/(B : ℝ)) < 1) :=
    tame_batch_direction_mgf (H d) p mu s.1 u Q D x hB hp htame hθ hD hu hx
  have h2 (x : ℝ) (hx : |x| * bulkQuadraticScale Q d B < 1) :=
    tame_bulk_square_mgf H J G S p mu s.1 s.2 Q x hB hp hr htame hθ hx
  have hh := increment_two_component_bernstein (batchLaw d B p) f g hfm hgm
    (D^2*projectionVariance p mu Q/(B : ℝ)) (bulkQuadraticVariance Q p d B)
    (D*projectionScale mu/(B : ℝ)) (bulkQuadraticScale Q d B) c (3*eta^2) t
    hv1 hv2 hM1 hM2 (by positivity) hc h1 h2 ht
  have he (a : Batch d B) : ell (matchedIncrement eta beta p mu s a) = f a+c*g a :=
    matchedIncrement_continuousDual_decomposition eta beta p mu ell s a hr (ne_of_lt hbeta1)
  simp_rw [he]
  exact hh
end
end SparseSGD.Logistic
