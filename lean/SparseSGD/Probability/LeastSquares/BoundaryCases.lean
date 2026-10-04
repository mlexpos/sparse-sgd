import SparseSGD.Probability.LeastSquares.BatchOracle
import SparseSGD.Probability.LeastSquares.Process

open MeasureTheory

namespace SparseSGD.Probability.LeastSquares
noncomputable section

theorem batchGradient_mean_p_zero {d B : ℕ} (hB : 0 < B)
    (p : unitInterval) (hp : (p : ℝ) = 0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0)
    (e : Vec d) :
    (∫ a, batchGradient e a ∂batchLaw d B p ν) = 0 := by
  have O := batchOracle (d := d) (B := B) hB p ν hz hmean
  rw [O.mean]
  simp [hp]

theorem batchGradient_norm_sq_p_zero {d B : ℕ} (hB : 0 < B)
    (p : unitInterval) (hp : (p : ℝ) = 0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0)
    (e : Vec d) :
    (∫ a, ‖batchGradient e a‖ ^ 2 ∂batchLaw d B p ν) = 0 := by
  have O := batchOracle (d := d) (B := B) hB p ν hz hmean
  rw [O.second]
  simp [vinc, vadd, hp]

theorem centered_variance_p_one {d B : ℕ} (hB : 0 < B)
    (p : unitInterval) (hp : (p : ℝ) = 1) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0)
    (e : Vec d) :
    (∫ a, ‖residual p e a‖ ^ 2 ∂batchLaw d B p ν) =
      ((d + 1 : ℕ) : ℝ) * ‖e‖ ^ 2 / B + labelVariance ν * d / B := by
  have O := batchOracle (d := d) (B := B) hB p ν hz hmean
  rw [O.centered_second]
  simp [vinc, vadd, hp]
  ring

theorem centered_variance_p_one_batch_one {d : ℕ}
    (p : unitInterval) (hp : (p : ℝ) = 1) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0)
    (e : Vec d) :
    (∫ a, ‖residual p e a‖ ^ 2 ∂batchLaw d 1 p ν) =
      ((d + 1 : ℕ) : ℝ) * ‖e‖ ^ 2 + labelVariance ν * d := by
  simpa using centered_variance_p_one (d := d) (B := 1) (by omega)
    p hp ν hz hmean e

theorem labelVariance_dirac_zero :
    labelVariance (Measure.dirac (0 : ℝ)) = 0 := by
  simp [labelVariance]

theorem label_memLp_dirac_zero : MemLp id 2 (Measure.dirac (0 : ℝ)) := by
  have hEq : id =ᵐ[Measure.dirac (0 : ℝ)] (fun _ : ℝ => 0) := by
    exact ae_eq_dirac id
  exact (memLp_congr_ae hEq).2 (memLp_const (0 : ℝ))

theorem label_mean_dirac_zero :
    (∫ z, z ∂Measure.dirac (0 : ℝ)) = 0 := by
  simp

theorem dirac_zero_batchOracle {d B : ℕ} (hB : 0 < B) (p : unitInterval) :
    BatchOracle d B p (Measure.dirac (0 : ℝ)) := by
  exact batchOracle hB p (Measure.dirac (0 : ℝ))
    label_memLp_dirac_zero label_mean_dirac_zero

end
end SparseSGD.Probability.LeastSquares
