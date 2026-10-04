import SparseSGD.Logistic.FluidScaling

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

/-- A horizon on min(learning step, retention step) controls the accumulated
learning step with exactly the source max(1,Delta) factor. -/
theorem min_clock_learning_horizon (z eps T : ℝ) (N : ℕ)
    (hz : 0 < z) (he : 0 < eps)
    (hN : (N : ℝ)*min z eps ≤ T) :
    (N : ℝ)*z ≤ T*max 1 (z/eps) := by
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg _) (le_min hz.le he.le)).trans hN
  rcases le_total z eps with h | h
  · rw [min_eq_left h] at hN
    exact hN.trans (by nlinarith [le_max_left (1 : ℝ) (z/eps)])
  · rw [min_eq_right h] at hN
    have H := mul_le_mul hN (le_max_right (1 : ℝ) (z/eps)) (div_nonneg hz.le he.le) hT
    convert H using 1 <;> field_simp

/-- Actual accumulated variance on the clock used by source cor:fluid. -/
theorem lrIncrementVariance_min_clock_bound {d B : ℕ}
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (Q K L T : ℝ) (N : ℕ)
    (hd : 2 ≤ d) (hB : 0 < B) (hp : 0 < (p : ℝ)) (heta : 0 < eta)
    (hbeta : beta < 1) (hz : eta*(p : ℝ) ≤ 1)
    (hN : (N : ℝ)*min (eta*(p : ℝ)) (1-beta) ≤ T) :
    (N : ℝ)*lrIncrementVariance eta p mu Q K L B ≤
      (10*lrSourceVarianceConstant Q K L)*T*max 1 (eta*(p : ℝ)/(1-beta))*
        (1+logisticPhi d B eta)^3*(1+(r mu)^2)/(d : ℝ) := by
  have hclock := min_clock_learning_horizon (eta*(p : ℝ)) (1-beta) T N
    (mul_pos heta hp) (by linarith) hN
  have H := lrSourceVariance_horizon_bound eta p mu N (T*max 1 (eta*(p : ℝ)/(1-beta)))
    hd hB hp heta.le hz hclock
  have hC : 0 ≤ lrSourceVarianceConstant Q K L := by
    dsimp [lrSourceVarianceConstant,rareProjectionConstant,bulkQuadraticConstant,symmetricProjectionConstant]
    positivity
  calc
    _ ≤ (N : ℝ)*(lrSourceVarianceConstant Q K L*lrSourceVariance d B eta p mu) :=
      mul_le_mul_of_nonneg_left (lrIncrementVariance_le_source eta p mu Q K L hd hB hp) (Nat.cast_nonneg _)
    _ = lrSourceVarianceConstant Q K L*((N : ℝ)*lrSourceVariance d B eta p mu) := by ring
    _ ≤ lrSourceVarianceConstant Q K L*(10*(T*max 1 (eta*(p : ℝ)/(1-beta)))*
        (1+logisticPhi d B eta)^3*(1+(r mu)^2)/(d : ℝ)) := mul_le_mul_of_nonneg_left H hC
    _ = _ := by ring

/-- The actual Bernstein scale in source variables, retaining its eta term. -/
theorem lrIncrementScale_dimension_bound {d B : ℕ}
    (eta : ℝ) (mu : Vec d) (Q K L : ℝ)
    (hd : 2 ≤ d) (hB : 0 < B) (heta : 0 ≤ eta)
    (hQ : 0 ≤ Q) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    lrIncrementScale eta mu Q K L B ≤
      4*lrSourceScaleConstant Q K L*logisticPhi d B eta*(1+r mu)*
        (1+logisticPhi d B eta+eta)/(d : ℝ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdm : 0 ≤ (d : ℝ)-1 := by linarith
  have hphi : 0 ≤ logisticPhi d B eta := by dsimp [logisticPhi]; positivity
  have hC : 0 ≤ lrSourceScaleConstant Q K L := by
    dsimp [lrSourceScaleConstant,stoppedDirectionBound,symmetricProjectionConstant]
    positivity
  apply (lrIncrementScale_le_source eta mu Q K L hd hB heta hQ hK hL).trans
  unfold lrSourceScale
  have H := mul_le_mul_of_nonneg_right (eta_div_batch_le_phi eta hd hB heta)
    (show 0 ≤ (1+r mu)*(1+logisticPhi d B eta+eta) by dsimp [r]; positivity)
  have H' := mul_le_mul_of_nonneg_left H hC
  convert H' using 1 <;> ring

end
end SparseSGD.Logistic
