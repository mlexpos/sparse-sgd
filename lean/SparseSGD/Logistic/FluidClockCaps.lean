import SparseSGD.Logistic.FluidClock
namespace SparseSGD.Logistic
noncomputable section

/-- A bounded raw Delta gives a uniform learning horizon on the min clock. -/
theorem min_clock_learning_horizon_le_cap (z eps T D : ℝ) (N : ℕ)
    (hz : 0 < z) (he : 0 < eps) (hN : (N : ℝ)*min z eps ≤ T)
    (hD : z/eps ≤ D) : (N : ℝ)*z ≤ T*max 1 D := by
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg _) (le_min hz.le he.le)).trans hN
  exact (min_clock_learning_horizon z eps T N hz he hN).trans
    (mul_le_mul_of_nonneg_left (max_le_max_left 1 hD) hT)

/-- A positive lower raw-Delta bound gives a uniform retention horizon. -/
theorem min_clock_retention_horizon_le_cap (z eps T deltaMin : ℝ) (N : ℕ)
    (hz : 0 < z) (he : 0 < eps) (hN : (N : ℝ)*min z eps ≤ T)
    (hd : 0 < deltaMin) (hD : deltaMin ≤ z/eps) :
    (N : ℝ)*eps ≤ T*max 1 (1/deltaMin) := by
  apply min_clock_learning_horizon_le_cap eps z T (1/deltaMin) N he hz (by simpa [min_comm] using hN)
  rw [div_le_div_iff₀ hz hd]
  have h := (le_div_iff₀ he).1 hD
  nlinarith

/-- In the small-Delta cell the min clock is exactly the learning clock. -/
theorem min_clock_learning_of_small_delta (z eps T : ℝ) (N : ℕ)
    (hD : z ≤ eps) (hN : (N : ℝ)*min z eps ≤ T) : (N : ℝ)*z ≤ T := by
  simpa only [min_eq_left hD] using hN

end
end SparseSGD.Logistic
