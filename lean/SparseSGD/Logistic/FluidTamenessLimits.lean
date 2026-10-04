import SparseSGD.Logistic.IncrementStoppedDomain

open Filter Topology
namespace SparseSGD.Logistic
noncomputable section

/-- The vanishing tame-error hypothesis in the source implies a vanishing
rare-class probability; this is already forced at any one reference state. -/
theorem probability_tendsto_zero_of_tame_error
    (p : (d : ℕ) → unitInterval) (mu theta : (d : ℕ) → Vec d)
    (h : Tendsto (fun d => tameError (p d) (mu d) (theta d)) atTop (𝓝 0)) :
    Tendsto (fun d => (p d : ℝ)) atTop (𝓝 0) := by
  exact squeeze_zero (fun d => (p d).property.1)
    (fun d => tameError_ge_probability (p d) (mu d) (theta d)) h

/-- On a uniformly bounded state family with a fixed teacher norm,
vanishing rare probability supplies the source's vanishing tame error. -/
theorem tame_error_tendsto_zero_of_bounded_parameters
    (p : (d : ℕ) → unitInterval) (mu theta : (d : ℕ) → Vec d) (teacherNorm Q : ℝ)
    (hQ : 0 ≤ Q) (hr : ∀ᶠ d in atTop, r (mu d)=teacherNorm)
    (htheta : ∀ᶠ d in atTop, ‖theta d‖≤Q)
    (hp : Tendsto (fun d => (p d : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun d => tameError (p d) (mu d) (theta d)) atTop (𝓝 0) := by
  let C := Real.exp (2*Q^2)+Real.exp (3*Q^2/2)+(1+Real.exp (Q^2/2))*Real.exp (Q*teacherNorm)
  have hc : Tendsto (fun d => (p d : ℝ)*C) atTop (𝓝 0) := by simpa using hp.mul_const C
  apply squeeze_zero' (Filter.Eventually.of_forall (fun d =>
    (p d).property.1.trans (tameError_ge_probability (p d) (mu d) (theta d)))) _ hc
  filter_upwards [hr,htheta] with d hd hn
  simpa only [stoppedTameConstant,hd,C] using tameError_le_stoppedNorm (p d) (mu d) (theta d) Q hQ hn

end
end SparseSGD.Logistic
