import SparseSGD.Logistic.FluidDeterministicProducts
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1500000

theorem jacobianResponse_eq_matchedProduct
    (J : ℕ→(Fin 5→ℝ) →L[ℝ] (Fin 5→ℝ)) (k j : ℕ) (hjk : j<k) :
    jacobianResponse J k j = matchedJacobianProduct (fun n =>J (j+1+n)) (k-j-1) := by
  induction k generalizing j with
  | zero =>omega
  | succ k ih =>
    by_cases hj : j=k
    · subst j; simp [jacobianResponse_new,matchedJacobianProduct]; rfl
    · have hj' : j<k := by omega
      rw [jacobianResponse_old J hj',ih j hj']
      have he : k+1-j-1=(k-j-1)+1 := by omega
      rw [he,matchedJacobianProduct]
      have he2 : j+1+(k-j-1)=k := by omega
      rw [he2]
      rfl

/-- Actual response products have a uniform finite-clock bound whenever
individual Jacobians are small perturbations of the explicit fast block. -/
theorem matchedJacobianResponse_bound
    (beta e T : ℝ) (hb0 : 0≤beta) (hb1 : beta≤1) (he : 0≤e)
    (K : ℕ) (hclock : (K:ℝ)*e≤T)
    (J : ℕ→(Fin 5→ℝ) →L[ℝ] (Fin 5→ℝ))
    (hJ : ∀ n<K, ‖J n-matchedFreeOperator beta‖≤e) :
    ∀ k≤K, ∀ j<k, ‖jacobianResponse J k j‖≤4*Real.exp (4*T) := by
  intro k hk j hj
  rw [jacobianResponse_eq_matchedProduct J k j hj]
  let Js := fun n =>if j+1+n<K then J (j+1+n) else matchedFreeOperator beta
  have hJs : ∀ n, ‖Js n-matchedFreeOperator beta‖≤e := by
    intro n
    dsimp [Js]
    split_ifs with hn
    · exact hJ _ hn
    · simpa using he
  have hprod : matchedJacobianProduct (fun n=>J (j+1+n)) (k-j-1)=
      matchedJacobianProduct Js (k-j-1) := by
    have H : ∀ m≤k-j-1, matchedJacobianProduct (fun n=>J (j+1+n)) m=matchedJacobianProduct Js m := by
      intro m
      induction m with
      | zero =>simp [matchedJacobianProduct]
      | succ m ih =>
        intro hm
        rw [matchedJacobianProduct,matchedJacobianProduct,ih (by omega)]
        have hm' : j+1+m<K := by omega
        simp [Js,hm']
    exact H _ le_rfl
  rw [hprod]
  have H := matchedJacobianProduct_perturbation_bound (matchedFreeOperator beta) Js 4 e
    (by norm_num) he (matchedFreeOperator_pow_norm_le_four beta hb0 hb1) hJs (k-j-1)
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤4)
  apply Real.exp_le_exp.mpr
  have hn : ((k-j-1:ℕ):ℝ)≤(K:ℝ) := by exact_mod_cast (show k-j-1≤K by omega)
  have HH := (mul_le_mul_of_nonneg_right hn he).trans hclock
  nlinarith
end
end SparseSGD.Logistic
