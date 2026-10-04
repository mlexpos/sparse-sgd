import SparseSGD.Scaling.SmallDeltaKernel
import SparseSGD.Scaling.SmallDeltaForcing
import SparseSGD.Scaling.SmallDeltaExponential

namespace SparseSGD
open Scaling
noncomputable section

/-- Actual normalized renewal kernel on the learning clock. -/
theorem smallDelta_kernel_geometric (p : Params) (Delta : ℝ)
    (jury : External.JuryStability)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1) (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8)
    (hw : p.w=smallDeltaW p.beta Delta) :
    Summable (fun n => |normalizedKernelLag p n-geomLag (smallDeltaRho p.beta Delta) n|) ∧
    ∑' n, |normalizedKernelLag p n-geomLag (smallDeltaRho p.beta Delta) n| ≤ 224*Delta := by
  obtain ⟨Hs,hs⟩ := smallDelta_kernel_slow_geometric p Delta jury hb0 hb1 hD0 hD1 hw
  obtain ⟨Ht,ht⟩ := smallDelta_slow_geom_tv p.beta Delta (by linarith) hb1 hD0 hD1
  have hpoint (n : ℕ) : |normalizedKernelLag p n-geomLag (smallDeltaRho p.beta Delta) n| ≤
      |normalizedKernelLag p n-geomLag (smallDeltaLambdaPlus p.beta Delta^2) n|+
      |geomLag (smallDeltaLambdaPlus p.beta Delta^2) n-geomLag (smallDeltaRho p.beta Delta) n| :=
    abs_sub_le _ _ _
  have H := Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpoint (Hs.add Ht)
  refine ⟨H,?_⟩
  have Hsum := H.tsum_le_tsum hpoint (Hs.add Ht)
  rw [Hs.tsum_add Ht] at Hsum
  linarith

/-- Actual cold-start forcing on the learning clock, with no limit assumption
on the retention parameter. -/
theorem smallDelta_freeRisk_geometric (p : Params) (Delta R : ℝ)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8)
    (hw : p.w=smallDeltaW p.beta Delta) (hR : 0 ≤ R) (k : ℕ) :
    |freeRisk p ⟨R,0,0⟩ k-R*(smallDeltaRho p.beta Delta)^k| ≤ 90*Delta*R := by
  have H := smallDelta_freeRisk_slow p Delta R hb0 hb1 hD0 hD1 hw hR k
  have Hp := smallDelta_slow_power_error p.beta Delta hb0 hb1 hD0 hD1 k
  have HH : |R*(smallDeltaLambdaPlus p.beta Delta^2)^k-R*(smallDeltaRho p.beta Delta)^k| ≤ 80*Delta*R := by
    rw [←mul_sub,abs_mul,abs_of_nonneg hR]
    nlinarith [mul_le_mul_of_nonneg_left Hp hR]
  have ht := abs_sub_le (freeRisk p ⟨R,0,0⟩ k) (R*(smallDeltaLambdaPlus p.beta Delta^2)^k)
    (R*(smallDeltaRho p.beta Delta)^k)
  linarith

end
end SparseSGD
