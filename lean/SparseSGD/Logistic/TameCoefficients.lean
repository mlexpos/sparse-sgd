import SparseSGD.Logistic.GaussianSigmoid

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1000000

def gaussianAlpha {d : ℕ} (mu theta : Vec d) : ℝ :=
  Real.exp ((‖theta‖^2-‖mu‖^2)/2)

def tameError {d : ℕ} (p : unitInterval) (mu theta : Vec d) : ℝ :=
  (p : ℝ)*(Real.exp (2*‖theta‖^2-‖mu‖^2)+
    Real.exp ((3*‖theta‖^2-‖mu‖^2)/2)+
    (1+gaussianAlpha mu theta)*Real.exp |inner ℝ theta mu|)

theorem gaussianAlpha_pos {d : ℕ} (mu theta : Vec d) : 0 < gaussianAlpha mu theta :=
  Real.exp_pos _

theorem tameError_source_formula {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hr : 0 < r mu) :
    tameError p mu theta = (p : ℝ)*(Real.exp (2*‖theta‖^2-(r mu)^2)+
      Real.exp ((3*‖theta‖^2-(r mu)^2)/2)+
      (1+gaussianAlpha mu theta)*Real.exp (r mu*|signalCoord mu theta|)) := by
  have h : r mu*|signalCoord mu theta| = |inner ℝ theta mu| := by
    rw [signalCoord, abs_div, abs_of_pos hr, mul_div_cancel₀ _ hr.ne']
  rw [h]
  rfl

theorem tameError_ge_probability {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    (p : ℝ) ≤ tameError p mu theta := by
  have ha := (gaussianAlpha_pos mu theta).le
  have he : 1 ≤ Real.exp |inner ℝ theta mu| := Real.one_le_exp (abs_nonneg _)
  have hp := p.property.1
  have hsum : 1 ≤ Real.exp (2*‖theta‖^2-‖mu‖^2)+
      Real.exp ((3*‖theta‖^2-‖mu‖^2)/2)+(1+gaussianAlpha mu theta)*Real.exp |inner ℝ theta mu| := by
    nlinarith [Real.exp_pos (2*‖theta‖^2-‖mu‖^2),
      Real.exp_pos ((3*‖theta‖^2-‖mu‖^2)/2)]
  exact (mul_one (p : ℝ)).symm ▸ mul_le_mul_of_nonneg_left hsum hp

theorem bias_first_exponential {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Real.exp (bias p mu+‖theta‖^2/2) = (p : ℝ)/(1-(p : ℝ))*gaussianAlpha mu theta := by
  unfold bias gaussianAlpha
  rw [show Real.log ((p : ℝ)/(1-(p : ℝ)))-‖mu‖^2/2+‖theta‖^2/2 =
    Real.log ((p : ℝ)/(1-(p : ℝ)))+(‖theta‖^2-‖mu‖^2)/2 by ring,
    Real.exp_add, Real.exp_log (div_pos hp0 (by linarith))]

theorem bias_second_exponential {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Real.exp (2*bias p mu+2*‖theta‖^2) =
      (p : ℝ)^2/(1-(p : ℝ))^2*Real.exp (2*‖theta‖^2-‖mu‖^2) := by
  unfold bias
  rw [show 2*(Real.log ((p : ℝ)/(1-(p : ℝ)))-‖mu‖^2/2)+2*‖theta‖^2 =
    (Real.log ((p : ℝ)/(1-(p : ℝ)))+Real.log ((p : ℝ)/(1-(p : ℝ))))+
      (2*‖theta‖^2-‖mu‖^2) by ring, Real.exp_add, Real.exp_add,
    Real.exp_log (div_pos hp0 (by linarith))]
  field_simp

theorem coefA_exponential_error {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    |coefA p mu theta-(p : ℝ)*gaussianAlpha mu theta| ≤
      2*(1-(p : ℝ))*Real.exp (2*bias p mu+2*‖theta‖^2)+
        (p : ℝ)*Real.exp (inner ℝ theta mu+bias p mu+‖theta‖^2/2) := by
  have H0 := gaussian_sigmaPrime_error_bound theta (bias p mu)
  have H1 := (gaussian_sigmaPrime_integral_bound theta (inner ℝ theta mu+bias p mu)).2
  have hm : (1-(p : ℝ))*Real.exp (bias p mu+‖theta‖^2/2) =
      (p : ℝ)*gaussianAlpha mu theta := by
    rw [bias_first_exponential p mu theta hp0 hp1]
    field_simp [show 1-(p : ℝ) ≠ 0 by linarith]
  rw [← hm]
  unfold coefA classLogit0 classLogit1
  simp only [add_assoc] at *
  rw [show (1-(p : ℝ))*(∫ z, sigmaPrime (inner ℝ theta (WithLp.toLp 2 z)+bias p mu)
      ∂SparseSGD.Probability.standardGaussianProduct d)+
      (p : ℝ)*(∫ z, sigmaPrime (inner ℝ theta (WithLp.toLp 2 z)+(inner ℝ theta mu+bias p mu))
      ∂SparseSGD.Probability.standardGaussianProduct d)-
      (1-(p : ℝ))*Real.exp (bias p mu+‖theta‖^2/2) =
      (1-(p : ℝ))*((∫ z, sigmaPrime (inner ℝ theta (WithLp.toLp 2 z)+bias p mu)
      ∂SparseSGD.Probability.standardGaussianProduct d)-Real.exp (bias p mu+‖theta‖^2/2))+
      (p : ℝ)*(∫ z, sigmaPrime (inner ℝ theta (WithLp.toLp 2 z)+(inner ℝ theta mu+bias p mu))
      ∂SparseSGD.Probability.standardGaussianProduct d) by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1-(p : ℝ)), abs_of_pos hp0]
  have h0 := mul_le_mul_of_nonneg_left H0 (by linarith : 0 ≤ 1-(p : ℝ))
  have h1 := mul_le_mul_of_nonneg_left H1 hp0.le
  nlinarith

theorem coefB_exponential_error {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    |coefB p mu theta+(p : ℝ)| ≤
      (p : ℝ)*Real.exp (inner ℝ theta mu+bias p mu+‖theta‖^2/2) := by
  have H := (gaussian_sigma_integral_bound theta (inner ℝ theta mu+bias p mu)).2
  unfold coefB classLogit1
  simp only [add_assoc] at *
  rw [show (p : ℝ)*((∫ z, sigma (inner ℝ theta (WithLp.toLp 2 z)+(inner ℝ theta mu+bias p mu))
    ∂SparseSGD.Probability.standardGaussianProduct d)-1)+(p : ℝ) =
    (p : ℝ)*(∫ z, sigma (inner ℝ theta (WithLp.toLp 2 z)+(inner ℝ theta mu+bias p mu))
    ∂SparseSGD.Probability.standardGaussianProduct d) by ring,
    abs_mul, abs_of_nonneg p.property.1]
  exact mul_le_mul_of_nonneg_left H p.property.1

theorem coefD0_exponential_error {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    |coefD0 p mu theta-(p : ℝ)| ≤
      (1-(p : ℝ))*Real.exp (2*bias p mu+2*‖theta‖^2)+
        2*(p : ℝ)*Real.exp (inner ℝ theta mu+bias p mu+‖theta‖^2/2) := by
  have H0 := (gaussian_sigma_sq_integral_bound theta (bias p mu)).2
  have H1 := gaussian_oneMinusSigma_sq_error_bound theta (inner ℝ theta mu+bias p mu)
  have hp0 := p.property.1
  have hp1 : 0 ≤ 1-(p : ℝ) := sub_nonneg.mpr p.property.2
  unfold coefD0 classLogit0 classLogit1
  simp only [add_assoc] at *
  rw [show (1-(p : ℝ))*(∫ z, sigma (inner ℝ theta (WithLp.toLp 2 z)+bias p mu)^2
    ∂SparseSGD.Probability.standardGaussianProduct d)+
    (p : ℝ)*(∫ z, (1-sigma (inner ℝ theta (WithLp.toLp 2 z)+(inner ℝ theta mu+bias p mu)))^2
    ∂SparseSGD.Probability.standardGaussianProduct d)-(p : ℝ) =
    (1-(p : ℝ))*(∫ z, sigma (inner ℝ theta (WithLp.toLp 2 z)+bias p mu)^2
    ∂SparseSGD.Probability.standardGaussianProduct d)+
    (p : ℝ)*((∫ z, (1-sigma (inner ℝ theta (WithLp.toLp 2 z)+(inner ℝ theta mu+bias p mu)))^2
    ∂SparseSGD.Probability.standardGaussianProduct d)-1) by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg hp1, abs_of_nonneg hp0]
  have h0 := mul_le_mul_of_nonneg_left H0 hp1
  have h1 := mul_le_mul_of_nonneg_left H1 hp0
  nlinarith

theorem coefDtheta_exponential_bound {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    |coefDtheta p mu theta| ≤
      4*(1-(p : ℝ))*Real.exp (2*bias p mu+2*‖theta‖^2)+
        2*(p : ℝ)*Real.exp (inner ℝ theta mu+bias p mu+‖theta‖^2/2) := by
  have H0 := (gaussian_sigmaSqSecond_integral_bound theta (bias p mu)).2
  have H1 := (gaussian_oneMinusSigmaSqSecond_integral_bound theta (inner ℝ theta mu+bias p mu)).2
  have hp0 := p.property.1
  have hp1 : 0 ≤ 1-(p : ℝ) := sub_nonneg.mpr p.property.2
  unfold coefDtheta classLogit0 classLogit1
  simp only [add_assoc] at *
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg hp1, abs_of_nonneg hp0]
  have h0 := mul_le_mul_of_nonneg_left H0 hp1
  have h1 := mul_le_mul_of_nonneg_left H1 hp0
  nlinarith


/-- Explicit controls of the two Gaussian exponential errors by the source
small parameter. All constants below are universal. -/
theorem tame_exponential_controls_of_probability_le_half {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hp0 : 0 < (p : ℝ)) (hphalf : (p : ℝ) ≤ 1/2) :
    (1-(p : ℝ))*Real.exp (2*bias p mu+2*‖theta‖^2) ≤ 2*(p : ℝ)*tameError p mu theta ∧
    (1-(p : ℝ))*Real.exp (2*bias p mu+2*‖theta‖^2) ≤ 2*(p : ℝ)*gaussianAlpha mu theta*tameError p mu theta ∧
    (p : ℝ)*Real.exp (inner ℝ theta mu+bias p mu+‖theta‖^2/2) ≤ 2*(p : ℝ)*tameError p mu theta ∧
    (p : ℝ)*Real.exp (inner ℝ theta mu+bias p mu+‖theta‖^2/2) ≤ 2*(p : ℝ)*gaussianAlpha mu theta*tameError p mu theta := by
  have hp1 : (p : ℝ) < 1 := by linarith
  have hden : 0 < 1-(p : ℝ) := by linarith
  let X := Real.exp (2*‖theta‖^2-‖mu‖^2)
  let Y := Real.exp ((3*‖theta‖^2-‖mu‖^2)/2)
  let E := Real.exp |inner ℝ theta mu|
  let a := gaussianAlpha mu theta
  let eps := tameError p mu theta
  have hX : 0 < X := Real.exp_pos _
  have hY : 0 < Y := Real.exp_pos _
  have hE : 0 < E := Real.exp_pos _
  have ha : 0 < a := gaussianAlpha_pos _ _
  have hXY : X = a*Y := by
    dsimp [X,Y,a,gaussianAlpha]
    rw [← Real.exp_add]
    congr 1
    ring
  have heq : eps = (p : ℝ)*(X+Y+(1+a)*E) := rfl
  have hx : (p : ℝ)*X ≤ eps := by
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ hp0.le
    have H : 0 ≤ (1+a)*E := by positivity
    linarith
  have hy : (p : ℝ)*Y ≤ eps := by
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ hp0.le
    have H : 0 ≤ (1+a)*E := by positivity
    linarith
  have he : (p : ℝ)*E ≤ eps := by nlinarith
  have hae : (p : ℝ)*a*E ≤ eps := by nlinarith
  have hratio : (p : ℝ)^2/(1-(p : ℝ)) ≤ 2*(p : ℝ)^2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg (p : ℝ)]
  have H0 : (1-(p : ℝ))*Real.exp (2*bias p mu+2*‖theta‖^2) ≤ 2*(p : ℝ)^2*X := by
    rw [bias_second_exponential p mu theta hp0 hp1]
    calc
      _ = ((p : ℝ)^2/(1-(p : ℝ)))*X := by dsimp [X]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hratio hX.le
  have H1 : (p : ℝ)*Real.exp (inner ℝ theta mu+bias p mu+‖theta‖^2/2) ≤ 2*(p : ℝ)^2*a*E := by
    rw [show inner ℝ theta mu+bias p mu+‖theta‖^2/2 =
      (bias p mu+‖theta‖^2/2)+inner ℝ theta mu by ring, Real.exp_add,
      bias_first_exponential p mu theta hp0 hp1]
    have hm : Real.exp (inner ℝ theta mu) ≤ E := Real.exp_le_exp.mpr (le_abs_self _)
    calc
      _ = ((p : ℝ)^2/(1-(p : ℝ)))*a*Real.exp (inner ℝ theta mu) := by dsimp [a]; ring
      _ ≤ (2*(p : ℝ)^2)*a*E := mul_le_mul
        (mul_le_mul_of_nonneg_right hratio ha.le) hm (Real.exp_pos _).le (by positivity)
  refine ⟨H0.trans ?_,H0.trans ?_,H1.trans ?_,H1.trans ?_⟩
  · have H := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2*(p : ℝ) by positivity)
    nlinarith
  · rw [hXY]
    have H := mul_le_mul_of_nonneg_left hy (show 0 ≤ 2*(p : ℝ)*a by positivity)
    change 2*(p : ℝ)^2*(a*Y) ≤ 2*(p : ℝ)*a*eps
    nlinarith
  · have H := mul_le_mul_of_nonneg_left hae (show 0 ≤ 2*(p : ℝ) by positivity)
    nlinarith
  · have H := mul_le_mul_of_nonneg_left he (show 0 ≤ 2*(p : ℝ)*a by positivity)
    nlinarith

theorem tame_exponential_controls {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hp0 : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2) :
    (1-(p : ℝ))*Real.exp (2*bias p mu+2*‖theta‖^2) ≤ 2*(p : ℝ)*tameError p mu theta ∧
    (1-(p : ℝ))*Real.exp (2*bias p mu+2*‖theta‖^2) ≤ 2*(p : ℝ)*gaussianAlpha mu theta*tameError p mu theta ∧
    (p : ℝ)*Real.exp (inner ℝ theta mu+bias p mu+‖theta‖^2/2) ≤ 2*(p : ℝ)*tameError p mu theta ∧
    (p : ℝ)*Real.exp (inner ℝ theta mu+bias p mu+‖theta‖^2/2) ≤ 2*(p : ℝ)*gaussianAlpha mu theta*tameError p mu theta :=
  tame_exponential_controls_of_probability_le_half p mu theta hp0
    ((tameError_ge_probability p mu theta).trans htame)

/-- The actual Gaussian-mixture coefficients satisfy the paper's tame
asymptotics, with numerical constants and the actual small parameter. -/
theorem tame_coefficients_of_probability_le_half {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hp0 : 0 < (p : ℝ)) (hphalf : (p : ℝ) ≤ 1/2) :
    |coefA p mu theta-(p : ℝ)*gaussianAlpha mu theta| ≤
      6*(p : ℝ)*gaussianAlpha mu theta*tameError p mu theta ∧
    |coefB p mu theta+(p : ℝ)| ≤ 2*(p : ℝ)*tameError p mu theta ∧
    |coefD0 p mu theta-(p : ℝ)| ≤ 6*(p : ℝ)*tameError p mu theta ∧
    |coefDtheta p mu theta| ≤ 12*(p : ℝ)*tameError p mu theta := by
  obtain ⟨h0,h0a,h1,h1a⟩ := tame_exponential_controls_of_probability_le_half p mu theta hp0 hphalf
  have hp1 : (p : ℝ) < 1 := by linarith
  refine ⟨?_,coefB_exponential_error p mu theta |>.trans h1,?_,?_⟩
  · have H := coefA_exponential_error p mu theta hp0 hp1
    nlinarith
  · have H := coefD0_exponential_error p mu theta
    nlinarith
  · have H := coefDtheta_exponential_bound p mu theta
    nlinarith

theorem tame_coefficients {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hp0 : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2) :
    |coefA p mu theta-(p : ℝ)*gaussianAlpha mu theta| ≤
      6*(p : ℝ)*gaussianAlpha mu theta*tameError p mu theta ∧
    |coefB p mu theta+(p : ℝ)| ≤ 2*(p : ℝ)*tameError p mu theta ∧
    |coefD0 p mu theta-(p : ℝ)| ≤ 6*(p : ℝ)*tameError p mu theta ∧
    |coefDtheta p mu theta| ≤ 12*(p : ℝ)*tameError p mu theta :=
  tame_coefficients_of_probability_le_half p mu theta hp0
    ((tameError_ge_probability p mu theta).trans htame)

end
end SparseSGD.Logistic
