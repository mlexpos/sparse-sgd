import SparseSGD.Logistic.Equilibrium

namespace SparseSGD.Logistic
noncomputable section

/-- A positive root cannot lie below this exponential scale. -/
theorem root_lower_bound (r Phi theta : ℝ) (hr : 0 < r) (hPhi : 0 ≤ Phi)
    (hθ : 0 < theta) (hroot : g r Phi theta = r) :
    r / Real.exp (Phi / 2) ≤ theta := by
  have htheta_le := positive_root_le_r r Phi theta hr hPhi hθ hroot
  have hexp_arg :
      (theta ^ 2 - r ^ 2 + Phi * theta / r) / 2 ≤ Phi / 2 := by
    have hsq : theta ^ 2 ≤ r ^ 2 := by nlinarith
    have hterm : Phi * theta / r ≤ Phi := by
      rw [div_le_iff₀ hr]
      nlinarith
    nlinarith
  have hexp : Real.exp ((theta ^ 2 - r ^ 2 + Phi * theta / r) / 2) ≤
      Real.exp (Phi / 2) := Real.exp_le_exp.mpr hexp_arg
  have hroot' : theta * Real.exp ((theta ^ 2 - r ^ 2 + Phi * theta / r) / 2) = r := by
    exact hroot
  have hmul : r ≤ theta * Real.exp (Phi / 2) := by
    rw [← hroot']
    exact mul_le_mul_of_nonneg_left hexp (le_of_lt hθ)
  exact (div_le_iff₀ (Real.exp_pos _)).2 (by simpa [mul_comm] using hmul)

/-- A uniform upper bound on the load gives a uniform root lower bound. -/
theorem root_lower_bound_of_phi_le (r Phi theta P : ℝ) (hr : 0 < r)
    (hPhi : 0 ≤ Phi) (hθ : 0 < theta) (hroot : g r Phi theta = r)
    (hPhiP : Phi ≤ P) :
    r / Real.exp (P / 2) ≤ theta := by
  have hbase := root_lower_bound r Phi theta hr hPhi hθ hroot
  have hexp : Real.exp (Phi / 2) ≤ Real.exp (P / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hdiv : r / Real.exp (P / 2) ≤ r / Real.exp (Phi / 2) := by
    exact div_le_div_of_nonneg_left hr.le (Real.exp_pos _) hexp
  exact le_trans hdiv hbase

/-- The bulk coordinate is uniformly comparable when the load is bounded. -/
theorem bulk_bounds_of_phi_le (r Phi theta P : ℝ) (hr : 0 < r)
    (hPhi : 0 ≤ Phi) (hθ : 0 < theta) (hroot : g r Phi theta = r)
    (hPhiP : Phi ≤ P) :
    Phi / Real.exp (P / 2) ≤ Phi * theta / r ∧ Phi * theta / r ≤ Phi := by
  have hthetaLower := root_lower_bound_of_phi_le r Phi theta P hr hPhi hθ hroot hPhiP
  have hthetaUpper := positive_root_le_r r Phi theta hr hPhi hθ hroot
  constructor
  · rw [le_div_iff₀ hr]
    calc
      Phi / Real.exp (P / 2) * r = Phi * (r / Real.exp (P / 2)) := by ring
      _ ≤ Phi * theta := mul_le_mul_of_nonneg_left hthetaLower hPhi
  · rw [div_le_iff₀ hr]
    exact mul_le_mul_of_nonneg_left hthetaUpper hPhi

end
end SparseSGD.Logistic
