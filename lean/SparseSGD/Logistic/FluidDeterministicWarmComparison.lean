import SparseSGD.Logistic.FluidDeterministicFree
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000

private theorem warm_sequence_duhamel
    (F : (Fin 5→ℝ)→L[ℝ](Fin 5→ℝ)) (x e : ℕ→Fin 5→ℝ)
    (hrec : ∀ n, x (n+1)=F (x n)+e n) (n : ℕ) :
    x n=(F^n) (x 0)+∑ j∈Finset.range n, (F^(n-1-j)) (e j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hrec,ih,map_add,map_sum,Finset.sum_range_succ]
    have H : ∑ j∈Finset.range n, F ((F^(n-1-j)) (e j)) =
        ∑ j∈Finset.range n, (F^(n+1-1-j)) (e j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [show n+1-1-j=(n-1-j)+1 by omega,pow_succ']
      rfl
    rw [H,pow_succ']
    simp [add_assoc]

private theorem warm_scalar_forcing (A b beta : ℝ) (u : ℕ→ℝ) (n : ℕ)
    (hA : 0≤A) (hb : 0≤b) (hbeta : 0≤beta) (hbeta1 : beta<1)
    (hu : ∀ k≤n, u k≤A*beta^k+b*∑ j∈Finset.range k, u j) :
    u n≤A*beta^n+(b*A/(1-beta))*(1+b)^n := by
  have hh : 0<1-beta := by linarith
  have hAh : 0≤A/(1-beta) := div_nonneg hA hh.le
  have hs : ∀ k≤n, (∑ j∈Finset.range k, u j)≤A/(1-beta)*((1+b)^k-beta^k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hhprev := ih (by omega)
      rw [Finset.sum_range_succ]
      have H := hu k (by omega)
      have Hsum := mul_le_mul_of_nonneg_left hhprev (show 0≤1+b by positivity)
      have hid : (A/(1-beta))*(1-beta)=A := div_mul_cancel₀ _ hh.ne'
      have hn := mul_nonneg (mul_nonneg hb hAh) (pow_nonneg hbeta k)
      rw [pow_succ,pow_succ]
      have hidp := congrArg (fun t : ℝ=>t*beta^k) hid
      nlinarith only [H,Hsum,hidp,hn]
  have H := hu n le_rfl
  have HS := mul_le_mul_of_nonneg_left (hs n le_rfl) hb
  have hn := mul_nonneg (mul_nonneg hb hAh) (pow_nonneg hbeta n)
  have heq : b*A/(1-beta)=b*(A/(1-beta)) := by ring
  rw [heq]
  nlinarith only [H,HS,hn]

/-- A bounded stable fast initial layer remains bounded after a locally
Lipschitz slow perturbation. Its integrated effect is proportional to the
learning/retention ratio, while its instantaneous size is retained. -/
theorem warm_local_perturbation_bound
    (F : (Fin 5→ℝ)→L[ℝ](Fin 5→ℝ)) (x e : ℕ→Fin 5→ℝ)
    (beta z C A T : ℝ) (N : ℕ)
    (hb0 : 0≤beta) (hb1 : beta<1) (hz : 0≤z) (hC : 0≤C) (hA : 0≤A)
    (hclock : (N:ℝ)*z≤T)
    (hF : ∀ n : ℕ, ‖F^n‖≤4)
    (hinit : ∀ n : ℕ, ‖(F^n) (x 0)‖≤A*beta^n)
    (hrec : ∀ n, x (n+1)=F (x n)+e n)
    (he : ∀ n<N, ‖x n‖≤A+1 → ‖e n‖≤C*z*‖x n‖)
    (hsmall : (4*C*z*A/(1-beta))*Real.exp (4*C*T)≤1) :
    ∀ n≤N, ‖x n‖≤A*beta^n+(4*C*z*A/(1-beta))*Real.exp (4*C*T) := by
  have hh : 0<1-beta := by linarith
  have hcz : 0≤C*z := mul_nonneg hC hz
  have hcoeff : 0≤4*C*z*A/(1-beta) := by positivity
  have hT : 0≤T := (mul_nonneg (Nat.cast_nonneg _) hz).trans hclock
  have hpow (n : ℕ) (hn : n≤N) : (1+4*C*z)^n≤Real.exp (4*C*T) := by
    calc
      _ ≤ (Real.exp (4*C*z))^n := by
        apply pow_le_pow_left₀ (by positivity) _ n
        simpa [add_comm] using Real.add_one_le_exp (4*C*z)
      _ = Real.exp ((n:ℝ)*(4*C*z)) := by rw [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hnR : (n:ℝ)≤N := by exact_mod_cast hn
        have H := mul_le_mul_of_nonneg_left
          ((mul_le_mul_of_nonneg_right hnR hz).trans hclock)
          (show 0≤4*C by positivity)
        nlinarith only [H])
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hlocal : ∀ j<n, ‖e j‖≤C*z*‖x j‖ := by
      intro j hj
      apply he j (by omega)
      have H := ih j hj (by omega)
      have hp := pow_le_one₀ (n:=j) hb0 hb1.le
      have HB := mul_le_mul_of_nonneg_left hp hA
      nlinarith only [H,HB,hsmall]
    have hineq : ∀ k≤n, ‖x k‖≤A*beta^k+(4*C*z)*(∑ j∈Finset.range k, ‖x j‖) := by
      intro k hk
      rw [warm_sequence_duhamel F x e hrec k]
      apply (norm_add_le _ _).trans
      apply add_le_add (hinit k)
      rw [Finset.mul_sum]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have H := ((F^(k-1-j)).le_opNorm (e j)).trans
        (mul_le_mul (hF _) (hlocal j (by omega)) (norm_nonneg _) (by norm_num : (0:ℝ)≤4))
      convert H using 1 <;> ring
    have H := warm_scalar_forcing A (4*C*z) beta (fun k=>‖x k‖) n hA (by positivity) hb0 hb1 hineq
    apply H.trans
    apply add_le_add_right _ (A*beta^n)
    exact mul_le_mul_of_nonneg_left (hpow n hn) hcoeff
end
end SparseSGD.Logistic
