import SparseSGD.Logistic.Coefficients
import SparseSGD.Logistic.GaussianSigmoid
import SparseSGD.Probability.GaussianCalculus
import SparseSGD.Logistic.GaussianDerivativeBounds

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
open SparseSGD.Probability
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

/-- The intercept of the negative-class logit at signal norm `r`. -/
def scalarBias (p : unitInterval) (r : ℝ) : ℝ :=
  Real.log ((p : ℝ) / (1 - (p : ℝ))) - r ^ 2 / 2

/-- Logistic coefficients written in terms of the scalar signal coordinate and
the independent Gaussian variance. -/
def scalarCoefA (p : unitInterval) (r t q : ℝ) : ℝ :=
  (1 - (p : ℝ)) *
      SparseSGD.Probability.gaussianAverage sigmaPrime (scalarBias p r) q +
    (p : ℝ) * SparseSGD.Probability.gaussianAverage sigmaPrime
      (r * t + scalarBias p r) q

def scalarCoefB (p : unitInterval) (r t q : ℝ) : ℝ :=
  (p : ℝ) * (SparseSGD.Probability.gaussianAverage sigma
    (r * t + scalarBias p r) q - 1)

def scalarCoefD0 (p : unitInterval) (r t q : ℝ) : ℝ :=
  (1 - (p : ℝ)) * SparseSGD.Probability.gaussianAverage
      (fun x => sigma x ^ 2) (scalarBias p r) q +
    (p : ℝ) * SparseSGD.Probability.gaussianAverage
      (fun x => (1 - sigma x) ^ 2) (r * t + scalarBias p r) q

def scalarCoefDtheta (p : unitInterval) (r t q : ℝ) : ℝ :=
  (1 - (p : ℝ)) * SparseSGD.Probability.gaussianAverage sigmaSqSecond
      (scalarBias p r) q +
    (p : ℝ) * SparseSGD.Probability.gaussianAverage oneMinusSigmaSqSecond
      (r * t + scalarBias p r) q

private theorem avg_sigmaSq_continuous : Continuous (fun x : ℝ => sigma x ^ 2) := by
  fun_prop

private theorem avg_oneMinusSigmaSq_continuous : Continuous (fun x : ℝ => (1-sigma x)^2) := by
  fun_prop

private theorem signal_product {d : ℕ} (mu theta : Vec d) (hr : 0 < r mu) :
    r mu * signalCoord mu theta = inner ℝ theta mu := by
  unfold signalCoord
  field_simp [ne_of_gt hr]

theorem coefA_eq_scalar {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hr : 0 < r mu) :
    coefA p mu theta = scalarCoefA p (r mu) (signalCoord mu theta) (‖theta‖^2) := by
  unfold coefA scalarCoefA
  have h0 := SparseSGD.Probability.gaussian_projected_average theta (bias p mu)
    sigmaPrime sigmaPrime_continuous
  have h1 := SparseSGD.Probability.gaussian_projected_average theta
    (inner ℝ theta mu + bias p mu) sigmaPrime sigmaPrime_continuous
  simp only [classLogit0, classLogit1, add_assoc]
  rw [h0, h1]
  simp only [bias, scalarBias]
  rw [signal_product mu theta hr]
  rfl

theorem coefB_eq_scalar {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hr : 0 < r mu) :
    coefB p mu theta = scalarCoefB p (r mu) (signalCoord mu theta) (‖theta‖^2) := by
  unfold coefB scalarCoefB
  have h1 := SparseSGD.Probability.gaussian_projected_average theta
    (inner ℝ theta mu + bias p mu) sigma sigma_continuous
  simp only [classLogit1, add_assoc]
  rw [h1]
  simp only [bias, scalarBias]
  rw [signal_product mu theta hr]
  rfl

theorem coefD0_eq_scalar {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hr : 0 < r mu) :
    coefD0 p mu theta = scalarCoefD0 p (r mu) (signalCoord mu theta) (‖theta‖^2) := by
  unfold coefD0 scalarCoefD0
  have h0 := SparseSGD.Probability.gaussian_projected_average theta (bias p mu)
    (fun x => sigma x ^ 2) avg_sigmaSq_continuous
  have h1 := SparseSGD.Probability.gaussian_projected_average theta
    (inner ℝ theta mu + bias p mu)
    (fun x => (1-sigma x)^2) avg_oneMinusSigmaSq_continuous
  simp only [classLogit0, classLogit1, add_assoc]
  rw [h0, h1]
  simp only [bias, scalarBias]
  rw [signal_product mu theta hr]
  rfl

theorem coefDtheta_eq_scalar {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hr : 0 < r mu) :
    coefDtheta p mu theta = scalarCoefDtheta p (r mu) (signalCoord mu theta) (‖theta‖^2) := by
  unfold coefDtheta scalarCoefDtheta
  have h0 := SparseSGD.Probability.gaussian_projected_average theta (bias p mu)
    sigmaSqSecond sigmaSqSecond_continuous
  have h1 := SparseSGD.Probability.gaussian_projected_average theta
    (inner ℝ theta mu + bias p mu)
    oneMinusSigmaSqSecond oneMinusSigmaSqSecond_continuous
  simp only [classLogit0, classLogit1, add_assoc]
  rw [h0, h1]
  simp only [bias, scalarBias]
  rw [signal_product mu theta hr]
  rfl

/-- The actual mixed signal/variance derivatives of a class mixture.
Signal differentiation suppresses the negative class, raises the sigmoid
derivative order by one, and supplies `r`. Variance differentiation raises
the order by two and supplies `1/2`. -/
def scalarGaussianJet (f0 f1 : ℕ → ℝ → ℝ) (base a b : ℕ)
    (p : unitInterval) (r t q : ℝ) : ℝ :=
  (r^a * (1/2 : ℝ)^b) *
    ((if a = 0 then (1-(p : ℝ)) * gaussianAverage (f0 (base+a+2*b)) (scalarBias p r) q else 0) +
      (p : ℝ) * gaussianAverage (f1 (base+a+2*b)) (r*t+scalarBias p r) q)

theorem scalarGaussianJet_signal {f0 f1 : ℕ → ℝ → ℝ}
    (H1 : BoundedDerivativeSequence f1) (base a b : ℕ)
    (p : unitInterval) (r t q : ℝ) :
    HasDerivAt (fun t => scalarGaussianJet f0 f1 base a b p r t q)
      (scalarGaussianJet f0 f1 base (a+1) b p r t q) t := by
  have hp : HasDerivAt (fun t => gaussianAverage (f1 (base+a+2*b)) (r*t+scalarBias p r) q)
      (gaussianAverage (f1 (base+a+2*b+1)) (r*t+scalarBias p r) q * r) t := by
    simpa only [Function.comp_def, mul_one, id_eq] using
      (H1.average_mean (base+a+2*b) (r*t+scalarBias p r) q).comp t
      (((hasDerivAt_id t).const_mul r).add_const (scalarBias p r))
  have h := ((hasDerivAt_const t
      (if a = 0 then (1-(p : ℝ))*gaussianAverage (f0 (base+a+2*b)) (scalarBias p r) q else 0)).add
      (hp.const_mul (p : ℝ))).const_mul (r^a*(1/2 : ℝ)^b)
  convert h using 1
  · rfl
  · simp only [scalarGaussianJet, Nat.add_one_ne_zero, if_false, zero_add,
      show base+(a+1)+2*b = base+a+2*b+1 by omega, pow_succ]
    ring

theorem scalarGaussianJet_variance {f0 f1 : ℕ → ℝ → ℝ}
    (H0 : BoundedDerivativeSequence f0) (H1 : BoundedDerivativeSequence f1)
    (S : SparseSGD.External.GaussianSteinCertificate 1) (base a b : ℕ)
    (p : unitInterval) (r t q : ℝ) (hq : 0 ≤ q) :
    HasDerivWithinAt (fun q => scalarGaussianJet f0 f1 base a b p r t q)
      (scalarGaussianJet f0 f1 base a (b+1) p r t q) (Set.Ici 0) q := by
  have h0 := (H0.average_variance S (base+a+2*b) (scalarBias p r) q hq).const_mul (1-(p : ℝ))
  have h1 := (H1.average_variance S (base+a+2*b) (r*t+scalarBias p r) q hq).const_mul (p : ℝ)
  by_cases ha : a = 0
  · have h := (h0.add h1).const_mul (r^a*(1/2 : ℝ)^b)
    convert h using 1
    · simp only [scalarGaussianJet, ha, if_true, Pi.add_apply]
    · unfold scalarGaussianJet
      rw [show base+a+2*(b+1) = base+a+2*b+2 by omega]
      simp only [ha, if_true, pow_succ]
      ring
  · have h := h1.const_mul (r^a*(1/2 : ℝ)^b)
    convert h using 1
    · simp only [scalarGaussianJet, ha, if_false, zero_add]
    · unfold scalarGaussianJet
      rw [show base+a+2*(b+1) = base+a+2*b+2 by omega]
      simp only [ha, if_false, zero_add, pow_succ]
      ring

theorem scalarGaussianJet_variance_pos {f0 f1 : ℕ → ℝ → ℝ}
    (H0 : BoundedDerivativeSequence f0) (H1 : BoundedDerivativeSequence f1)
    (S : SparseSGD.External.GaussianSteinCertificate 1) (base a b : ℕ)
    (p : unitInterval) (r t q : ℝ) (hq : 0 < q) :
    HasDerivAt (fun q => scalarGaussianJet f0 f1 base a b p r t q)
      (scalarGaussianJet f0 f1 base a (b+1) p r t q) q :=
  (scalarGaussianJet_variance H0 H1 S base a b p r t q hq.le).hasDerivAt
    (Ici_mem_nhds hq)

/-- Expansion at an actual vector-model state, exposing exactly the Gaussian
averages used in the dimension-independent tame derivative bounds. -/
theorem scalarGaussianJet_eq_actual {d : ℕ} (f0 f1 : ℕ → ℝ → ℝ)
    (base a b : ℕ) (p : unitInterval) (mu theta : Vec d) (hr : 0 < r mu) :
    scalarGaussianJet f0 f1 base a b p (r mu) (signalCoord mu theta) (‖theta‖^2) =
      ((r mu)^a * (1/2 : ℝ)^b) *
        ((if a = 0 then (1-(p : ℝ)) * gaussianAverage (f0 (base+a+2*b))
          (bias p mu) (‖theta‖^2) else 0) +
          (p : ℝ) * gaussianAverage (f1 (base+a+2*b))
            (inner ℝ theta mu+bias p mu) (‖theta‖^2)) := by
  simp only [scalarGaussianJet, scalarBias, bias]
  rw [signal_product mu theta hr]
  rfl

def scalarCoefAJet (a b : ℕ) (p : unitInterval) (r t q : ℝ) : ℝ :=
  scalarGaussianJet sigmaDerivative sigmaDerivative 1 a b p r t q

def scalarCoefBJet (a b : ℕ) (p : unitInterval) (r t q : ℝ) : ℝ :=
  scalarGaussianJet (fun _ _ => 0) sigmaDerivative 0 a b p r t q -
    if a+b = 0 then (p : ℝ) else 0

def scalarCoefD0Jet (a b : ℕ) (p : unitInterval) (r t q : ℝ) : ℝ :=
  scalarGaussianJet sigmaSquareDerivative oneMinusSigmaSquareDerivative 0 a b p r t q

def scalarCoefDthetaJet (a b : ℕ) (p : unitInterval) (r t q : ℝ) : ℝ :=
  scalarGaussianJet sigmaSquareDerivative oneMinusSigmaSquareDerivative 2 a b p r t q

@[simp] theorem scalar_sigmaDerivative_zero_fun : sigmaDerivative 0 = sigma := funext sigmaDerivative_zero
@[simp] theorem scalar_sigmaDerivative_one_fun : sigmaDerivative 1 = sigmaPrime := funext sigmaDerivative_one
@[simp] theorem scalar_sigmaSquareDerivative_zero_fun : sigmaSquareDerivative 0 = fun x => sigma x^2 :=
  funext sigmaSquareDerivative_zero
@[simp] theorem scalar_oneMinusSquareDerivative_zero_fun : oneMinusSigmaSquareDerivative 0 = fun x => (1-sigma x)^2 :=
  funext oneMinusSigmaSquareDerivative_zero
@[simp] theorem scalar_sigmaSquareDerivative_two_fun : sigmaSquareDerivative 2 = sigmaSqSecond :=
  funext sigmaSquareDerivative_two
@[simp] theorem scalar_oneMinusSquareDerivative_two_fun : oneMinusSigmaSquareDerivative 2 = oneMinusSigmaSqSecond :=
  funext oneMinusSigmaSquareDerivative_two

@[simp] theorem scalar_gaussianAverage_zero (c q : ℝ) : gaussianAverage (fun _ => 0) c q = 0 := by
  simp [gaussianAverage]

@[simp] theorem scalarCoefAJet_zero (p : unitInterval) (r t q : ℝ) :
    scalarCoefAJet 0 0 p r t q = scalarCoefA p r t q := by
  simp [scalarCoefAJet, scalarGaussianJet, scalarCoefA]

@[simp] theorem scalarCoefBJet_zero (p : unitInterval) (r t q : ℝ) :
    scalarCoefBJet 0 0 p r t q = scalarCoefB p r t q := by
  simp [scalarCoefBJet, scalarGaussianJet, scalarCoefB]
  ring

@[simp] theorem scalarCoefD0Jet_zero (p : unitInterval) (r t q : ℝ) :
    scalarCoefD0Jet 0 0 p r t q = scalarCoefD0 p r t q := by
  simp [scalarCoefD0Jet, scalarGaussianJet, scalarCoefD0]

@[simp] theorem scalarCoefDthetaJet_zero (p : unitInterval) (r t q : ℝ) :
    scalarCoefDthetaJet 0 0 p r t q = scalarCoefDtheta p r t q := by
  simp [scalarCoefDthetaJet, scalarGaussianJet, scalarCoefDtheta]

private theorem scalar_zero_boundedDerivativeSequence : BoundedDerivativeSequence (fun _ _ => 0) where
  derivative n x := hasDerivAt_const x 0
  bounded n := ⟨0, fun x => by simp⟩

theorem scalarCoefAJet_signal (a b : ℕ) (p : unitInterval) (r t q : ℝ) :
    HasDerivAt (fun t => scalarCoefAJet a b p r t q) (scalarCoefAJet (a+1) b p r t q) t :=
  scalarGaussianJet_signal sigma_boundedDerivativeSequence 1 a b p r t q

theorem scalarCoefAJet_variance (S : SparseSGD.External.GaussianSteinCertificate 1)
    (a b : ℕ) (p : unitInterval) (r t q : ℝ) (hq : 0 ≤ q) :
    HasDerivWithinAt (fun q => scalarCoefAJet a b p r t q) (scalarCoefAJet a (b+1) p r t q) (Set.Ici 0) q :=
  scalarGaussianJet_variance sigma_boundedDerivativeSequence sigma_boundedDerivativeSequence S 1 a b p r t q hq

theorem scalarCoefAJet_variance_pos (S : SparseSGD.External.GaussianSteinCertificate 1)
    (a b : ℕ) (p : unitInterval) (r t q : ℝ) (hq : 0 < q) :
    HasDerivAt (fun q => scalarCoefAJet a b p r t q) (scalarCoefAJet a (b+1) p r t q) q :=
  scalarGaussianJet_variance_pos sigma_boundedDerivativeSequence sigma_boundedDerivativeSequence S 1 a b p r t q hq

theorem scalarCoefD0Jet_signal (a b : ℕ) (p : unitInterval) (r t q : ℝ) :
    HasDerivAt (fun t => scalarCoefD0Jet a b p r t q) (scalarCoefD0Jet (a+1) b p r t q) t :=
  scalarGaussianJet_signal oneMinusSigmaSquare_boundedDerivativeSequence 0 a b p r t q

theorem scalarCoefD0Jet_variance (S : SparseSGD.External.GaussianSteinCertificate 1)
    (a b : ℕ) (p : unitInterval) (r t q : ℝ) (hq : 0 ≤ q) :
    HasDerivWithinAt (fun q => scalarCoefD0Jet a b p r t q) (scalarCoefD0Jet a (b+1) p r t q) (Set.Ici 0) q :=
  scalarGaussianJet_variance sigmaSquare_boundedDerivativeSequence oneMinusSigmaSquare_boundedDerivativeSequence S 0 a b p r t q hq

theorem scalarCoefD0Jet_variance_pos (S : SparseSGD.External.GaussianSteinCertificate 1)
    (a b : ℕ) (p : unitInterval) (r t q : ℝ) (hq : 0 < q) :
    HasDerivAt (fun q => scalarCoefD0Jet a b p r t q) (scalarCoefD0Jet a (b+1) p r t q) q :=
  scalarGaussianJet_variance_pos sigmaSquare_boundedDerivativeSequence oneMinusSigmaSquare_boundedDerivativeSequence S 0 a b p r t q hq

theorem scalarCoefDthetaJet_signal (a b : ℕ) (p : unitInterval) (r t q : ℝ) :
    HasDerivAt (fun t => scalarCoefDthetaJet a b p r t q) (scalarCoefDthetaJet (a+1) b p r t q) t :=
  scalarGaussianJet_signal oneMinusSigmaSquare_boundedDerivativeSequence 2 a b p r t q

theorem scalarCoefDthetaJet_variance (S : SparseSGD.External.GaussianSteinCertificate 1)
    (a b : ℕ) (p : unitInterval) (r t q : ℝ) (hq : 0 ≤ q) :
    HasDerivWithinAt (fun q => scalarCoefDthetaJet a b p r t q) (scalarCoefDthetaJet a (b+1) p r t q) (Set.Ici 0) q :=
  scalarGaussianJet_variance sigmaSquare_boundedDerivativeSequence oneMinusSigmaSquare_boundedDerivativeSequence S 2 a b p r t q hq

theorem scalarCoefDthetaJet_variance_pos (S : SparseSGD.External.GaussianSteinCertificate 1)
    (a b : ℕ) (p : unitInterval) (r t q : ℝ) (hq : 0 < q) :
    HasDerivAt (fun q => scalarCoefDthetaJet a b p r t q) (scalarCoefDthetaJet a (b+1) p r t q) q :=
  scalarGaussianJet_variance_pos sigmaSquare_boundedDerivativeSequence oneMinusSigmaSquare_boundedDerivativeSequence S 2 a b p r t q hq

theorem scalarCoefBJet_signal (a b : ℕ) (p : unitInterval) (r t q : ℝ) :
    HasDerivAt (fun t => scalarCoefBJet a b p r t q) (scalarCoefBJet (a+1) b p r t q) t := by
  have h := (scalarGaussianJet_signal (f0 := fun _ _ => 0)
    sigma_boundedDerivativeSequence 0 a b p r t q).sub_const
      (if a+b = 0 then (p : ℝ) else 0)
  simpa [scalarCoefBJet, show a+1+b ≠ 0 by omega] using h

theorem scalarCoefBJet_variance (S : SparseSGD.External.GaussianSteinCertificate 1)
    (a b : ℕ) (p : unitInterval) (r t q : ℝ) (hq : 0 ≤ q) :
    HasDerivWithinAt (fun q => scalarCoefBJet a b p r t q) (scalarCoefBJet a (b+1) p r t q) (Set.Ici 0) q := by
  have h := (scalarGaussianJet_variance scalar_zero_boundedDerivativeSequence
    sigma_boundedDerivativeSequence S 0 a b p r t q hq).sub_const
      (if a+b = 0 then (p : ℝ) else 0)
  simpa [scalarCoefBJet, show a+(b+1) ≠ 0 by omega] using h

theorem scalarCoefBJet_variance_pos (S : SparseSGD.External.GaussianSteinCertificate 1)
    (a b : ℕ) (p : unitInterval) (r t q : ℝ) (hq : 0 < q) :
    HasDerivAt (fun q => scalarCoefBJet a b p r t q) (scalarCoefBJet a (b+1) p r t q) q :=
  (scalarCoefBJet_variance S a b p r t q hq.le).hasDerivAt (Ici_mem_nhds hq)

/-- Actual signal derivative of scalarCoefA; the jet definition expands its Gaussian formula. -/
theorem scalarCoefA_signal_hasDerivAt (p : unitInterval) (r t q : ℝ) :
    HasDerivAt (fun t => scalarCoefA p r t q) (scalarCoefAJet 1 0 p r t q) t := by
  simpa only [scalarCoefAJet_zero] using scalarCoefAJet_signal 0 0 p r t q

/-- Actual variance derivative, including the one-sided derivative at zero. -/
theorem scalarCoefA_variance_hasDerivWithinAt (S : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r t q : ℝ) (hq : 0 ≤ q) :
    HasDerivWithinAt (fun q => scalarCoefA p r t q) (scalarCoefAJet 0 1 p r t q) (Set.Ici 0) q := by
  simpa only [scalarCoefAJet_zero] using scalarCoefAJet_variance S 0 0 p r t q hq

theorem scalarCoefA_variance_hasDerivAt (S : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r t q : ℝ) (hq : 0 < q) :
    HasDerivAt (fun q => scalarCoefA p r t q) (scalarCoefAJet 0 1 p r t q) q := by
  simpa only [scalarCoefAJet_zero] using scalarCoefAJet_variance_pos S 0 0 p r t q hq

/-- The two pure and two mixed second derivatives of the actual coefficient.
Both mixed derivatives have exactly the same Gaussian jet. -/
theorem scalarCoefA_second_derivatives (S : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r t q : ℝ) (hq : 0 ≤ q) :
    HasDerivAt (fun t => scalarCoefAJet 1 0 p r t q) (scalarCoefAJet 2 0 p r t q) t ∧
    HasDerivWithinAt (fun q => scalarCoefAJet 1 0 p r t q) (scalarCoefAJet 1 1 p r t q) (Set.Ici 0) q ∧
    HasDerivAt (fun t => scalarCoefAJet 0 1 p r t q) (scalarCoefAJet 1 1 p r t q) t ∧
    HasDerivWithinAt (fun q => scalarCoefAJet 0 1 p r t q) (scalarCoefAJet 0 2 p r t q) (Set.Ici 0) q :=
  ⟨scalarCoefAJet_signal 1 0 p r t q, scalarCoefAJet_variance S 1 0 p r t q hq,
    scalarCoefAJet_signal 0 1 p r t q, scalarCoefAJet_variance S 0 1 p r t q hq⟩

/-- Actual signal derivative of scalarCoefB; the jet definition expands its Gaussian formula. -/
theorem scalarCoefB_signal_hasDerivAt (p : unitInterval) (r t q : ℝ) :
    HasDerivAt (fun t => scalarCoefB p r t q) (scalarCoefBJet 1 0 p r t q) t := by
  simpa only [scalarCoefBJet_zero] using scalarCoefBJet_signal 0 0 p r t q

/-- Actual variance derivative, including the one-sided derivative at zero. -/
theorem scalarCoefB_variance_hasDerivWithinAt (S : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r t q : ℝ) (hq : 0 ≤ q) :
    HasDerivWithinAt (fun q => scalarCoefB p r t q) (scalarCoefBJet 0 1 p r t q) (Set.Ici 0) q := by
  simpa only [scalarCoefBJet_zero] using scalarCoefBJet_variance S 0 0 p r t q hq

theorem scalarCoefB_variance_hasDerivAt (S : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r t q : ℝ) (hq : 0 < q) :
    HasDerivAt (fun q => scalarCoefB p r t q) (scalarCoefBJet 0 1 p r t q) q := by
  simpa only [scalarCoefBJet_zero] using scalarCoefBJet_variance_pos S 0 0 p r t q hq

/-- The two pure and two mixed second derivatives of the actual coefficient.
Both mixed derivatives have exactly the same Gaussian jet. -/
theorem scalarCoefB_second_derivatives (S : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r t q : ℝ) (hq : 0 ≤ q) :
    HasDerivAt (fun t => scalarCoefBJet 1 0 p r t q) (scalarCoefBJet 2 0 p r t q) t ∧
    HasDerivWithinAt (fun q => scalarCoefBJet 1 0 p r t q) (scalarCoefBJet 1 1 p r t q) (Set.Ici 0) q ∧
    HasDerivAt (fun t => scalarCoefBJet 0 1 p r t q) (scalarCoefBJet 1 1 p r t q) t ∧
    HasDerivWithinAt (fun q => scalarCoefBJet 0 1 p r t q) (scalarCoefBJet 0 2 p r t q) (Set.Ici 0) q :=
  ⟨scalarCoefBJet_signal 1 0 p r t q, scalarCoefBJet_variance S 1 0 p r t q hq,
    scalarCoefBJet_signal 0 1 p r t q, scalarCoefBJet_variance S 0 1 p r t q hq⟩

/-- Actual signal derivative of scalarCoefD0; the jet definition expands its Gaussian formula. -/
theorem scalarCoefD0_signal_hasDerivAt (p : unitInterval) (r t q : ℝ) :
    HasDerivAt (fun t => scalarCoefD0 p r t q) (scalarCoefD0Jet 1 0 p r t q) t := by
  simpa only [scalarCoefD0Jet_zero] using scalarCoefD0Jet_signal 0 0 p r t q

/-- Actual variance derivative, including the one-sided derivative at zero. -/
theorem scalarCoefD0_variance_hasDerivWithinAt (S : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r t q : ℝ) (hq : 0 ≤ q) :
    HasDerivWithinAt (fun q => scalarCoefD0 p r t q) (scalarCoefD0Jet 0 1 p r t q) (Set.Ici 0) q := by
  simpa only [scalarCoefD0Jet_zero] using scalarCoefD0Jet_variance S 0 0 p r t q hq

theorem scalarCoefD0_variance_hasDerivAt (S : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r t q : ℝ) (hq : 0 < q) :
    HasDerivAt (fun q => scalarCoefD0 p r t q) (scalarCoefD0Jet 0 1 p r t q) q := by
  simpa only [scalarCoefD0Jet_zero] using scalarCoefD0Jet_variance_pos S 0 0 p r t q hq

/-- The two pure and two mixed second derivatives of the actual coefficient.
Both mixed derivatives have exactly the same Gaussian jet. -/
theorem scalarCoefD0_second_derivatives (S : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r t q : ℝ) (hq : 0 ≤ q) :
    HasDerivAt (fun t => scalarCoefD0Jet 1 0 p r t q) (scalarCoefD0Jet 2 0 p r t q) t ∧
    HasDerivWithinAt (fun q => scalarCoefD0Jet 1 0 p r t q) (scalarCoefD0Jet 1 1 p r t q) (Set.Ici 0) q ∧
    HasDerivAt (fun t => scalarCoefD0Jet 0 1 p r t q) (scalarCoefD0Jet 1 1 p r t q) t ∧
    HasDerivWithinAt (fun q => scalarCoefD0Jet 0 1 p r t q) (scalarCoefD0Jet 0 2 p r t q) (Set.Ici 0) q :=
  ⟨scalarCoefD0Jet_signal 1 0 p r t q, scalarCoefD0Jet_variance S 1 0 p r t q hq,
    scalarCoefD0Jet_signal 0 1 p r t q, scalarCoefD0Jet_variance S 0 1 p r t q hq⟩

/-- Actual signal derivative of scalarCoefDtheta; the jet definition expands its Gaussian formula. -/
theorem scalarCoefDtheta_signal_hasDerivAt (p : unitInterval) (r t q : ℝ) :
    HasDerivAt (fun t => scalarCoefDtheta p r t q) (scalarCoefDthetaJet 1 0 p r t q) t := by
  simpa only [scalarCoefDthetaJet_zero] using scalarCoefDthetaJet_signal 0 0 p r t q

/-- Actual variance derivative, including the one-sided derivative at zero. -/
theorem scalarCoefDtheta_variance_hasDerivWithinAt (S : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r t q : ℝ) (hq : 0 ≤ q) :
    HasDerivWithinAt (fun q => scalarCoefDtheta p r t q) (scalarCoefDthetaJet 0 1 p r t q) (Set.Ici 0) q := by
  simpa only [scalarCoefDthetaJet_zero] using scalarCoefDthetaJet_variance S 0 0 p r t q hq

theorem scalarCoefDtheta_variance_hasDerivAt (S : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r t q : ℝ) (hq : 0 < q) :
    HasDerivAt (fun q => scalarCoefDtheta p r t q) (scalarCoefDthetaJet 0 1 p r t q) q := by
  simpa only [scalarCoefDthetaJet_zero] using scalarCoefDthetaJet_variance_pos S 0 0 p r t q hq

/-- The two pure and two mixed second derivatives of the actual coefficient.
Both mixed derivatives have exactly the same Gaussian jet. -/
theorem scalarCoefDtheta_second_derivatives (S : SparseSGD.External.GaussianSteinCertificate 1)
    (p : unitInterval) (r t q : ℝ) (hq : 0 ≤ q) :
    HasDerivAt (fun t => scalarCoefDthetaJet 1 0 p r t q) (scalarCoefDthetaJet 2 0 p r t q) t ∧
    HasDerivWithinAt (fun q => scalarCoefDthetaJet 1 0 p r t q) (scalarCoefDthetaJet 1 1 p r t q) (Set.Ici 0) q ∧
    HasDerivAt (fun t => scalarCoefDthetaJet 0 1 p r t q) (scalarCoefDthetaJet 1 1 p r t q) t ∧
    HasDerivWithinAt (fun q => scalarCoefDthetaJet 0 1 p r t q) (scalarCoefDthetaJet 0 2 p r t q) (Set.Ici 0) q :=
  ⟨scalarCoefDthetaJet_signal 1 0 p r t q, scalarCoefDthetaJet_variance S 1 0 p r t q hq,
    scalarCoefDthetaJet_signal 0 1 p r t q, scalarCoefDthetaJet_variance S 0 1 p r t q hq⟩

end
end SparseSGD.Logistic
