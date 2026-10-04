import SparseSGD.Logistic.TameCoefficients
import SparseSGD.Logistic.GaussianDerivativeBounds

open SparseSGD.Probability
namespace SparseSGD.Logistic
noncomputable section

/-- Every derivative order in the class-zero/class-one sigmoid mixture has
its exponential main term, with a dimension-independent tame remainder. -/
theorem tame_sigma_mixture_derivative (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d : ℕ} (p : unitInterval) (mu theta : Vec d),
      0 < (p : ℝ) → tameError p mu theta ≤ 1/2 →
      |(1-(p : ℝ))*gaussianAverage (sigmaDerivative n) (bias p mu) (‖theta‖^2)+
        (p : ℝ)*gaussianAverage (sigmaDerivative n) (inner ℝ theta mu+bias p mu) (‖theta‖^2)-
        (p : ℝ)*gaussianAlpha mu theta| ≤ C*(p : ℝ)*gaussianAlpha mu theta*tameError p mu theta := by
  obtain ⟨C,hC,h⟩ := gaussian_sigmaDerivative_bounds n
  refine ⟨4*C, by linarith, fun {d} p mu theta hp ht => ?_⟩
  have hp1 : (p : ℝ) < 1 := by linarith [tameError_ge_probability p mu theta]
  have hd : 0 ≤ 1-(p : ℝ) := by linarith
  have hm : (1-(p : ℝ))*Real.exp (bias p mu+‖theta‖^2/2) = (p : ℝ)*gaussianAlpha mu theta := by
    rw [bias_first_exponential p mu theta hp hp1]
    field_simp [show 1-(p : ℝ) ≠ 0 by linarith]
  have hs := tame_exponential_controls p mu theta hp ht
  have h0 := (h (bias p mu) (‖theta‖^2) (sq_nonneg _)).2
  have h1 := (h (inner ℝ theta mu+bias p mu) (‖theta‖^2) (sq_nonneg _)).1
  rw [← hm]
  rw [show (1-(p : ℝ))*gaussianAverage (sigmaDerivative n) (bias p mu) (‖theta‖^2)+
      (p : ℝ)*gaussianAverage (sigmaDerivative n) (inner ℝ theta mu+bias p mu) (‖theta‖^2)-
      (1-(p : ℝ))*Real.exp (bias p mu+‖theta‖^2/2) =
      (1-(p : ℝ))*(gaussianAverage (sigmaDerivative n) (bias p mu) (‖theta‖^2)-Real.exp (bias p mu+‖theta‖^2/2))+
      (p : ℝ)*gaussianAverage (sigmaDerivative n) (inner ℝ theta mu+bias p mu) (‖theta‖^2) by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_of_nonneg hd,abs_of_pos hp]
  have H0 := mul_le_mul_of_nonneg_left h0 hd
  have H1 := mul_le_mul_of_nonneg_left h1 hp.le
  have H2 := mul_le_mul_of_nonneg_left hs.2.1 (show 0≤C by linarith)
  have H3 := mul_le_mul_of_nonneg_left hs.2.2.2 (show 0≤C by linarith)
  nlinarith

/-- Signal derivatives only differentiate the positive-class mean. -/
theorem tame_sigma_positive_derivative (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d : ℕ} (p : unitInterval) (mu theta : Vec d),
      0 < (p : ℝ) → tameError p mu theta ≤ 1/2 →
      |(p : ℝ)*gaussianAverage (sigmaDerivative n) (inner ℝ theta mu+bias p mu) (‖theta‖^2)| ≤
        C*(p : ℝ)*tameError p mu theta := by
  obtain ⟨C,hC,h⟩ := gaussian_sigmaDerivative_bounds n
  refine ⟨2*C, by linarith, fun {d} p mu theta hp ht => ?_⟩
  rw [abs_mul,abs_of_pos hp]
  have h1 := mul_le_mul_of_nonneg_left
    (h (inner ℝ theta mu+bias p mu) (‖theta‖^2) (sq_nonneg _)).1 hp.le
  have hs := mul_le_mul_of_nonneg_left (tame_exponential_controls p mu theta hp ht).2.2.1
    (show 0≤C by linarith)
  nlinarith

/-- Positive-order derivatives of the quadratic residual mixture have no
constant main term. The bound is uniform over dimensions and tame states. -/
theorem tame_square_mixture_derivative (n : ℕ) (hn : n ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d : ℕ} (p : unitInterval) (mu theta : Vec d),
      0 < (p : ℝ) → tameError p mu theta ≤ 1/2 →
      |(1-(p : ℝ))*gaussianAverage (sigmaSquareDerivative n) (bias p mu) (‖theta‖^2)+
        (p : ℝ)*gaussianAverage (oneMinusSigmaSquareDerivative n) (inner ℝ theta mu+bias p mu) (‖theta‖^2)| ≤
        C*(p : ℝ)*tameError p mu theta := by
  obtain ⟨C,hC,h⟩ := gaussian_sigmaSquareDerivative_bound n
  obtain ⟨D,hD,h'⟩ := gaussian_oneMinusSigmaSquareDerivative_bound n hn
  refine ⟨2*(C+D), by positivity, fun {d} p mu theta hp ht => ?_⟩
  have hd : 0 ≤ 1-(p : ℝ) := sub_nonneg.mpr p.property.2
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_of_nonneg hd,abs_of_pos hp]
  have h0 := mul_le_mul_of_nonneg_left (h (bias p mu) (‖theta‖^2) (sq_nonneg _)) hd
  have h1 := mul_le_mul_of_nonneg_left (h' (inner ℝ theta mu+bias p mu) (‖theta‖^2) (sq_nonneg _)) hp.le
  have hs := tame_exponential_controls p mu theta hp ht
  have h2 := mul_le_mul_of_nonneg_left hs.1 hC
  have h3 := mul_le_mul_of_nonneg_left hs.2.2.1 hD
  nlinarith

theorem tame_square_positive_derivative (n : ℕ) (hn : n ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d : ℕ} (p : unitInterval) (mu theta : Vec d),
      0 < (p : ℝ) → tameError p mu theta ≤ 1/2 →
      |(p : ℝ)*gaussianAverage (oneMinusSigmaSquareDerivative n) (inner ℝ theta mu+bias p mu) (‖theta‖^2)| ≤
        C*(p : ℝ)*tameError p mu theta := by
  obtain ⟨C,hC,h⟩ := gaussian_oneMinusSigmaSquareDerivative_bound n hn
  refine ⟨2*C, by positivity, fun {d} p mu theta hp ht => ?_⟩
  rw [abs_mul,abs_of_pos hp]
  have h1 := mul_le_mul_of_nonneg_left
    (h (inner ℝ theta mu+bias p mu) (‖theta‖^2) (sq_nonneg _)) hp.le
  have hs := mul_le_mul_of_nonneg_left (tame_exponential_controls p mu theta hp ht).2.2.1 hC
  nlinarith

end
end SparseSGD.Logistic
