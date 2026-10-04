import SparseSGD.Probability.GaussianProduct

open MeasureTheory

namespace SparseSGD.External

/-! A reusable interface to the two standard Gaussian integration-by-parts
identities.  This is a *certificate*, rather than an axiom: callers must
provide the first- and second-order identities for the standard product
Gaussian.  The hypotheses below leave the test functions arbitrary and state
only the integrability needed for each integral. -/

noncomputable section

structure GaussianSteinCertificate (d : ℕ) : Prop where
  first_order : ∀ (θ : Fin d → ℝ) (c : ℝ) (f f' : ℝ → ℝ) (i : Fin d),
    (∀ t, HasDerivAt f (f' t) t) →
    Continuous f' →
    Integrable (fun z : Fin d → ℝ => f (∑ j, θ j * z j + c) * z i)
        (SparseSGD.Probability.standardGaussianProduct d)
    → Integrable (fun z : Fin d → ℝ => f' (∑ j, θ j * z j + c))
        (SparseSGD.Probability.standardGaussianProduct d)
    → (∫ z, f (∑ j, θ j * z j + c) * z i ∂SparseSGD.Probability.standardGaussianProduct d) =
        θ i * ∫ z, f' (∑ j, θ j * z j + c) ∂SparseSGD.Probability.standardGaussianProduct d
  second_order : ∀ (θ : Fin d → ℝ) (c : ℝ) (f f' f'' : ℝ → ℝ) (i j : Fin d),
    (∀ t, HasDerivAt f (f' t) t) →
    (∀ t, HasDerivAt f' (f'' t) t) →
    Continuous f' →
    Continuous f'' →
    Integrable (fun z : Fin d → ℝ => f (∑ k, θ k * z k + c) * z i * z j)
      (SparseSGD.Probability.standardGaussianProduct d)
    → Integrable (fun z : Fin d → ℝ => f (∑ k, θ k * z k + c))
      (SparseSGD.Probability.standardGaussianProduct d)
    → Integrable (fun z : Fin d → ℝ => f'' (∑ k, θ k * z k + c))
      (SparseSGD.Probability.standardGaussianProduct d)
    → (∫ z, f (∑ k, θ k * z k + c) * z i * z j ∂SparseSGD.Probability.standardGaussianProduct d) =
        (if i = j then ∫ z, f (∑ k, θ k * z k + c)
          ∂SparseSGD.Probability.standardGaussianProduct d else 0) +
        θ i * θ j * ∫ z, f'' (∑ k, θ k * z k + c)
          ∂SparseSGD.Probability.standardGaussianProduct d

end
end SparseSGD.External
