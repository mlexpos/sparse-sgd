import SparseSGD.Logistic.SigmoidDerivatives
import SparseSGD.Probability.GaussianBounds

open SparseSGD.Probability
namespace SparseSGD.Logistic
noncomputable section

/-- A hierarchy of actual derivatives with a global bound at every order. -/
structure BoundedDerivativeSequence (f : ℕ → ℝ → ℝ) : Prop where
  derivative : ∀ n x, HasDerivAt (f n) (f (n+1) x) x
  bounded : ∀ n, ∃ C : ℝ, ∀ x, |f n x| ≤ C

theorem BoundedDerivativeSequence.continuous {f : ℕ → ℝ → ℝ}
    (H : BoundedDerivativeSequence f) (n : ℕ) : Continuous (f n) :=
  continuous_iff_continuousAt.mpr fun x => (H.derivative n x).continuousAt

theorem BoundedDerivativeSequence.average_mean {f : ℕ → ℝ → ℝ}
    (H : BoundedDerivativeSequence f) (n : ℕ) (c q : ℝ) :
    HasDerivAt (fun c => gaussianAverage (f n) c q) (gaussianAverage (f (n+1)) c q) c := by
  obtain ⟨F,hF⟩ := H.bounded n
  obtain ⟨D,hD⟩ := H.bounded (n+1)
  exact gaussianAverage_mean_hasDerivAt (f n) (f (n+1)) (H.derivative n)
    (H.continuous (n+1)) F D hF hD c q

theorem BoundedDerivativeSequence.average_variance {f : ℕ → ℝ → ℝ}
    (H : BoundedDerivativeSequence f) (S : SparseSGD.External.GaussianSteinCertificate 1)
    (n : ℕ) (c q : ℝ) (hq : 0 ≤ q) :
    HasDerivWithinAt (gaussianAverage (f n) c) (gaussianAverage (f (n+2)) c q/2) (Set.Ici 0) q := by
  obtain ⟨F,hF⟩ := H.bounded n
  obtain ⟨D,hD⟩ := H.bounded (n+1)
  obtain ⟨E,hE⟩ := H.bounded (n+2)
  exact gaussianAverage_variance_hasDerivWithinAt S (f n) (f (n+1)) (f (n+2))
    (H.derivative n) (H.derivative (n+1)) (H.continuous (n+2)) F D E hF hD hE c q hq

theorem BoundedDerivativeSequence.average_variance_pos {f : ℕ → ℝ → ℝ}
    (H : BoundedDerivativeSequence f) (S : SparseSGD.External.GaussianSteinCertificate 1)
    (n : ℕ) (c q : ℝ) (hq : 0 < q) :
    HasDerivAt (gaussianAverage (f n) c) (gaussianAverage (f (n+2)) c q/2) q := by
  obtain ⟨F,hF⟩ := H.bounded n
  obtain ⟨D,hD⟩ := H.bounded (n+1)
  obtain ⟨E,hE⟩ := H.bounded (n+2)
  exact gaussianAverage_variance_hasDerivAt S (f n) (f (n+1)) (f (n+2))
    (H.derivative n) (H.derivative (n+1)) (H.continuous (n+2)) F D E hF hD hE c q hq

theorem sigma_boundedDerivativeSequence : BoundedDerivativeSequence sigmaDerivative where
  derivative := hasDerivAt_sigmaDerivative
  bounded n := by
    obtain ⟨C,_,hC⟩ := sigmaDerivative_bounds n
    exact ⟨C,fun x => (hC x).1⟩

theorem sigmaSquare_boundedDerivativeSequence : BoundedDerivativeSequence sigmaSquareDerivative where
  derivative := hasDerivAt_sigmaSquareDerivative
  bounded n := by
    obtain ⟨C,_,hC⟩ := sigmaSquareDerivative_bounds n
    exact ⟨C,fun x => (hC x).1⟩

theorem oneMinusSigmaSquare_boundedDerivativeSequence : BoundedDerivativeSequence oneMinusSigmaSquareDerivative where
  derivative := hasDerivAt_oneMinusSigmaSquareDerivative
  bounded n := by
    obtain ⟨C,_,hC⟩ := oneMinusSigmaSquareDerivative_bounded n
    exact ⟨C,hC⟩

theorem gaussian_sigmaDerivative_bounds (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ c q : ℝ, 0 ≤ q →
      |gaussianAverage (sigmaDerivative n) c q| ≤ C*Real.exp (c+q/2) ∧
      |gaussianAverage (sigmaDerivative n) c q-Real.exp (c+q/2)| ≤ C*Real.exp (2*c+2*q) := by
  obtain ⟨C,hC,h⟩ := sigmaDerivative_bounds n
  refine ⟨C,hC,fun c q hq => ⟨?_,?_⟩⟩
  · simpa using (gaussianAverage_exponential_bound _ (sigmaDerivative_continuous n)
      C 1 (by simpa using fun x => (h x).2.1) c q hq).2
  · exact gaussianAverage_exponential_error _ (sigmaDerivative_continuous n)
      C C (fun x => (h x).2.1) (fun x => (h x).2.2) c q hq

theorem gaussian_sigmaSquareDerivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c q : ℝ, 0 ≤ q →
      |gaussianAverage (sigmaSquareDerivative n) c q| ≤ C*Real.exp (2*c+2*q) := by
  obtain ⟨C,hC,h⟩ := sigmaSquareDerivative_bounds n
  refine ⟨C,hC,fun c q hq => ?_⟩
  have hh := (gaussianAverage_exponential_bound _ (sigmaSquareDerivative_continuous n)
    C 2 (fun x => (h x).2) c q hq).2
  convert hh using 1 <;> ring

theorem gaussian_oneMinusSigmaSquareDerivative_bound (n : ℕ) (hn : n ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c q : ℝ, 0 ≤ q →
      |gaussianAverage (oneMinusSigmaSquareDerivative n) c q| ≤ C*Real.exp (c+q/2) := by
  obtain ⟨C,hC,h⟩ := oneMinusSigmaSquareDerivative_exp_bound n hn
  refine ⟨C,hC,fun c q hq => ?_⟩
  simpa using (gaussianAverage_exponential_bound _ (oneMinusSigmaSquareDerivative_continuous n)
    C 1 (by simpa using h) c q hq).2

end
end SparseSGD.Logistic
