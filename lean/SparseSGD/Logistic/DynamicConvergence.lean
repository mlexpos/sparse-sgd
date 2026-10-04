import SparseSGD.Logistic.DynamicParameters
namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 1800000

/-- Finite-horizon convergence from a local residual estimate. Compact
containment of the recursion is proved by bootstrap, not assumed. -/
theorem dynamic_grid_error_of_local_residual (r delta Phi M F h E T : ℝ)
    (L : ℝ≥0) (N : ℕ) (x : ℕ → DynamicState) (y : ℝ → DynamicState)
    (hh : 0 ≤ h) (hE : 0 ≤ E) (hF : 0 ≤ F) (hT : (N:ℝ)*h ≤ T)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hyM : ∀ t ∈ Set.Icc 0 T, ‖y t‖ ≤ M-1)
    (hL : LipschitzOnWith L (dynamicField r delta Phi) (Metric.closedBall 0 M))
    (hb : ∀ z, ‖z‖ ≤ M → ‖dynamicField r delta Phi z‖ ≤ F)
    (hstep : ∀ k < N, ‖x k‖ ≤ M →
      ‖x (k+1)-(x k+h • dynamicField r delta Phi (x k))‖ ≤ h*E)
    (hsmall : (‖x 0-y 0‖+T*(E+(L:ℝ)*F*h))*Real.exp (T*(L:ℝ)) ≤ 1) :
    ∀ n ≤ N, ‖x n-y ((n:ℝ)*h)‖ ≤
      (‖x 0-y 0‖+T*(E+(L:ℝ)*F*h))*Real.exp (T*(L:ℝ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hnt : (n:ℝ)*h ≤ T :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hh).trans hT
    have hJ : 0 ≤ E+(L:ℝ)*F*h := by positivity
    have hrec : ∀ k < n,
        ‖x (k+1)-y (((k+1:ℕ):ℝ)*h)‖ ≤
          (1+h*(L:ℝ))*‖x k-y ((k:ℝ)*h)‖+h*(E+(L:ℝ)*F*h) := by
      intro k hk
      have hkN : k < N := hk.trans_le hn
      have hkt : (k:ℝ)*h ≤ T :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hk.le) hh).trans hnt
      have hk0 : 0 ≤ (k:ℝ)*h := by positivity
      have hk1 : ((k+1:ℕ):ℝ)*h ≤ T :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hk) hh).trans hnt
      have hxM : ‖x k‖ ≤ M := by
        have hi := ih k hk (hk.le.trans hn)
        calc
          _ = ‖(x k-y ((k:ℝ)*h))+y ((k:ℝ)*h)‖ := by simp
          _ ≤ ‖x k-y ((k:ℝ)*h)‖+‖y ((k:ℝ)*h)‖ := norm_add_le _ _
          _ ≤ 1+(M-1) := add_le_add (hi.trans hsmall) (hyM _ ⟨hk0,hkt⟩)
          _ = M := by ring
      have hyball : ‖y ((k:ℝ)*h)‖ ≤ M := by linarith [hyM _ ⟨hk0,hkt⟩]
      have hs := hstep k hkN hxM
      have htend : (k:ℝ)*h+h=((k+1:ℕ):ℝ)*h := by push_cast; ring
      have hseg : Set.Icc ((k:ℝ)*h) ((k:ℝ)*h+h) ⊆ Set.Icc 0 T := by
        intro t ht
        rw [htend] at ht
        exact ⟨hk0.trans ht.1,ht.2.trans hk1⟩
      have heuler := dynamic_ode_euler_error r delta Phi M F ((k:ℝ)*h) h L y hh hF
        (fun t ht => hy t (hseg ht))
        (fun t ht => by linarith [hyM t (hseg ht)]) hb hL
      rw [htend] at heuler
      have he := dynamic_one_step_error (dynamicField r delta Phi) h (h*E)
        ((L:ℝ)*F*h^2) L (x k) (y ((k:ℝ)*h)) (x (k+1)) (y (((k+1:ℕ):ℝ)*h)) hh
        (hL.norm_sub_le (by simpa using hxM) (by simpa using hyball)) hs heuler
      apply he.trans
      ring_nf
      exact le_rfl
    have hg := dynamic_discrete_gronwall (fun k => ‖x k-y ((k:ℝ)*h)‖) n h
      (E+(L:ℝ)*F*h) (L:ℝ) T (fun _ _ => norm_nonneg _) hh hJ L.coe_nonneg hrec hnt n le_rfl
    simpa using hg

end
end SparseSGD.Logistic
