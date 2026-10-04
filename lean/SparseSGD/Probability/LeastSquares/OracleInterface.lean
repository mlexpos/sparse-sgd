import SparseSGD.Probability.LeastSquares.Model

open MeasureTheory
namespace SparseSGD.Probability.LeastSquares
noncomputable section

def residual {d B : ℕ} (p : unitInterval) (e : Vec d) (a : Batch d B) : Vec d :=
  batchGradient e a - (p : ℝ) • e

/-- An internal assembly interface. The public model theorem must construct this
record from the sample law, rather than accept it as a model assumption. -/
structure BatchOracle (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) : Prop where
  memLp : ∀ e : Vec d, MemLp (batchGradient (B := B) e) 2 (batchLaw d B p ν)
  mean : ∀ e : Vec d, (∫ a, batchGradient e a ∂batchLaw d B p ν) = (p : ℝ) • e
  second : ∀ e : Vec d, (∫ a, ‖batchGradient e a‖ ^ 2 ∂batchLaw d B p ν) =
    ((p : ℝ)^2 + vinc d B p) * ‖e‖ ^ 2 + vadd d B p ν
  centered_mean : ∀ e : Vec d, (∫ a, residual p e a ∂batchLaw d B p ν) = 0
  centered_second : ∀ e : Vec d, (∫ a, ‖residual p e a‖ ^ 2 ∂batchLaw d B p ν) =
    vinc d B p * ‖e‖ ^ 2 + vadd d B p ν

end
end SparseSGD.Probability.LeastSquares
