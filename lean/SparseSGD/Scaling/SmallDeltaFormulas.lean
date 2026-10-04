import SparseSGD.Scaling.SmallDeltaSpectrum
import SparseSGD.Discrete.StableKernel
import SparseSGD.Discrete.RiskBound

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1000000

/-- Exact impulse formula for distinct real roots of the actual mean recurrence. -/
theorem kickResponse_distinct_roots (p : Params) (a b : ℝ) (hab : a ≠ b)
    (hsum : a+b=1+p.beta-p.w) (hprod : a*b=p.beta) (n : ℕ) :
    kickResponse p n = -(a^(n+1)-b^(n+1))/(a-b) := by
  have hn : a-b ≠ 0 := sub_ne_zero.mpr hab
  refine Nat.twoStepInduction ?_ ?_ ?_ n
  · simp only [Nat.zero_add, pow_one, kickResponse_zero]
    apply (eq_div_iff hn).mpr
    ring
  · rw [kickResponse_one,←hsum]
    field_simp
    ring
  · intro k hk hk1
    rw [kickResponse_recurrence,hk1,hk,←hsum,←hprod]
    simp only [pow_succ]
    field_simp
    ring

theorem Params.meanPower_entry_recurrence (p : Params) (i j : Fin 2) (n : ℕ) :
    (p.meanMatrix^(n+2)) i j =
      (1+p.beta-p.w)*(p.meanMatrix^(n+1)) i j-p.beta*(p.meanMatrix^n) i j := by
  have hp : p.meanMatrix ^ (n+2) = (1+p.beta-p.w) • p.meanMatrix^(n+1)-p.beta • p.meanMatrix^n := by
    rw [pow_add,p.meanMatrix_cayleyHamilton,mul_sub,mul_smul_comm,mul_smul_comm,mul_one,←pow_succ]
  rw [hp]
  simp

/-- Exact cold-start mean response, including the signed fast-mode amplitude. -/
theorem Params.meanPower00_distinct_roots (p : Params) (a b : ℝ) (hab : a ≠ b)
    (hsum : a+b=1+p.beta-p.w) (hprod : a*b=p.beta) (n : ℕ) :
    (p.meanMatrix^n) 0 0 = ((a-p.beta)*a^n+(p.beta-b)*b^n)/(a-b) := by
  have hn : a-b ≠ 0 := sub_ne_zero.mpr hab
  refine Nat.twoStepInduction ?_ ?_ ?_ n
  · simp only [pow_zero, Matrix.one_apply_eq]
    apply (eq_div_iff hn).mpr
    ring
  · simp only [pow_one,Params.meanMatrix,Matrix.of_apply,Matrix.cons_val_zero]
    apply (eq_div_iff hn).mpr
    have hh := congrArg (fun x : ℝ => x*(a-b)) hsum
    nlinarith only [hh]
  · intro k hk hk1
    rw [p.meanPower_entry_recurrence,hk1,hk,←hsum,←hprod]
    simp only [pow_succ]
    field_simp
    ring

theorem cold_freeRisk (p : Params) (R : ℝ) (n : ℕ) :
    freeRisk p ⟨R,0,0⟩ n = R*((p.meanMatrix^n) 0 0)^2 := by
  simp [freeRisk,Moments.cov,Matrix.mul_apply,Fin.sum_univ_two,←Matrix.transpose_pow]
  ring

theorem cold_freeRisk_distinct_roots (p : Params) (a b R : ℝ) (hab : a ≠ b)
    (hsum : a+b=1+p.beta-p.w) (hprod : a*b=p.beta) (n : ℕ) :
    freeRisk p ⟨R,0,0⟩ n = R*(((a-p.beta)*a^n+(p.beta-b)*b^n)/(a-b))^2 := by
  rw [cold_freeRisk,p.meanPower00_distinct_roots a b hab hsum hprod]

theorem normalizedKernelLag_distinct_roots (p : Params) (a b : ℝ) (hab : a ≠ b)
    (hsum : a+b=1+p.beta-p.w) (hprod : a*b=p.beta) (n : ℕ) :
    normalizedKernelLag p (n+1) =
      ((1-p.curvature)*2*p.w*p.eps/(a-b)^2)*(a^(n+1)-b^(n+1))^2 := by
  rw [normalizedKernelLag,kickResponse_distinct_roots p a b hab hsum hprod]
  field_simp

/-- The small-Delta roots are the roots of the actual `Params` mean recurrence. -/
theorem smallDelta_actual_roots (p : Params) (Delta : ℝ)
    (hb0 : 0 ≤ p.beta) (hb1 : p.beta < 1) (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8)
    (hw : p.w=smallDeltaW p.beta Delta) :
    smallDeltaLambdaMinus p.beta Delta < smallDeltaLambdaPlus p.beta Delta ∧
    smallDeltaLambdaPlus p.beta Delta+smallDeltaLambdaMinus p.beta Delta=1+p.beta-p.w ∧
    smallDeltaLambdaPlus p.beta Delta*smallDeltaLambdaMinus p.beta Delta=p.beta := by
  have H := smallDeltaSpectrum p.beta Delta hb0 hb1 hD0 hD1
  exact ⟨by linarith [H.2.1],by rw [hw]; exact H.2.2.2.2.2.2.2.2,H.2.2.2.2.2.2.2.1⟩

end
end SparseSGD
