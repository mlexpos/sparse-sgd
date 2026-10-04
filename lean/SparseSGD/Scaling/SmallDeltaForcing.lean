import SparseSGD.Scaling.SmallDeltaFormulas
import SparseSGD.Scaling.GeometricKernel

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1000000

/-- The cold-start free risk differs from the slow eigenmode by at most ten
Delta times the initial risk, uniformly over every discrete time. -/
theorem smallDelta_freeRisk_slow (p : Params) (Delta R : ℝ)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8)
    (hw : p.w=smallDeltaW p.beta Delta) (hR : 0 ≤ R) (k : ℕ) :
    |freeRisk p ⟨R,0,0⟩ k-R*((smallDeltaLambdaPlus p.beta Delta)^2)^k| ≤ 10*Delta*R := by
  let a := smallDeltaLambdaPlus p.beta Delta
  let b := smallDeltaLambdaMinus p.beta Delta
  obtain ⟨_,hgap,hbpos,hbup,hapos,ha1,_,hprod,hsum,_,_,hblo⟩ :=
    smallDeltaSpectrum_strong p.beta Delta hb0 hb1 hD0 hD1
  change a-b≥(1-p.beta)/2 at hgap
  change 0≤b at hbpos
  change b≤p.beta+2*smallDeltaZ p.beta Delta at hbup
  change 0<a at hapos
  change a<1 at ha1
  change p.beta≤b at hblo
  have hgap0 : 0 < a-b := by linarith
  have hab : b ≤ a := by linarith
  have hsum' : a+b=1+p.beta-p.w := by rw [hw]; exact hsum
  let t := (b-p.beta)/(a-b)
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hgap0.le
  have ht : t ≤ 4*Delta := by
    apply (div_le_iff₀ hgap0).mpr
    have H := mul_le_mul_of_nonneg_left hgap (show 0≤4*Delta by positivity)
    dsimp [smallDeltaZ] at hbup
    nlinarith only [hbup,H]
  have hpa : 0 ≤ a^k := pow_nonneg hapos.le k
  have hpa1 : a^k ≤ 1 := pow_le_one₀ hapos.le ha1.le
  have hpb : 0 ≤ b^k := pow_nonneg hbpos k
  have hpba : b^k ≤ a^k := pow_le_pow_left₀ hbpos hab k
  have hdiff : 0 ≤ a^k-b^k := by linarith
  have hdiff1 : a^k-b^k ≤ 1 := by linarith
  have hresponse : (p.meanMatrix^k) 0 0=a^k+t*(a^k-b^k) := by
    rw [p.meanPower00_distinct_roots a b (ne_of_gt hgap0 |> sub_ne_zero.mp) hsum' hprod]
    dsimp [t]
    field_simp
    <;> ring
  have herror : 0 ≤ t*(a^k-b^k) ∧ t*(a^k-b^k) ≤ 4*Delta := by
    constructor
    · positivity
    · calc
        _ ≤ t*1 := mul_le_mul_of_nonneg_left hdiff1 ht0
        _ ≤ _ := by simpa using ht
  have herrsmall : t*(a^k-b^k) ≤ 1/2 := by linarith
  have hprodsmall : (t*(a^k-b^k))^2 ≤ (1/2)*(t*(a^k-b^k)) := by nlinarith
  have hcross : 2*a^k*(t*(a^k-b^k)) ≤ 2*(t*(a^k-b^k)) := by nlinarith
  have hsq : |((p.meanMatrix^k) 0 0)^2-(a^k)^2| ≤ 10*Delta := by
    rw [hresponse,abs_of_nonneg (by nlinarith : 0≤(a^k+t*(a^k-b^k))^2-(a^k)^2)]
    nlinarith only [hprodsmall,hcross,herror.2]
  rw [cold_freeRisk,show (a^2)^k=(a^k)^2 by rw [←pow_mul,←pow_mul,Nat.mul_comm 2 k],←mul_sub,abs_mul,abs_of_nonneg hR]
  nlinarith [mul_le_mul_of_nonneg_left hsq hR]

end
end SparseSGD
