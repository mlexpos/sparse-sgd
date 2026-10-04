import SparseSGD.Scaling.FluidHorizon
open Filter Topology
namespace SparseSGD.Scaling
noncomputable section
/-- The polynomial degree is explicit and independent of the rarity prefactor. -/
theorem fluidGridHorizon_eventually_le_degree
    (T etaStar pStar alpha kappa epsStar gamma : ℝ)
    (hT : 0 ≤ T) (heta : 0 < etaStar) (hp : 0 < pStar) (heps : 0 < epsStar)
    (ha : 0 ≤ alpha+kappa) (hg : 0 ≤ gamma) :
    ∀ᶠ d : ℕ in atTop,
      (fluidGridHorizon T etaStar pStar alpha kappa epsStar gamma d : ℝ) ≤ (d:ℝ)^(fluidHorizonDegree alpha kappa gamma) := by
  let m := max (alpha+kappa) gamma
  let c := min (etaStar*pStar) epsStar
  let q := fluidHorizonDegree alpha kappa gamma
  have hm : 0 ≤ m := le_trans hg (le_max_right _ _)
  have hc : 0 < c := lt_min (mul_pos heta hp) heps
  have hlarge : ∀ᶠ d : ℕ in atTop, max (T/c) 1 ≤ (d:ℝ) := by
    exact (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d:ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (max (T/c) 1))
  filter_upwards [fluidClock_lower_bound_eventually etaStar pStar alpha kappa epsStar gamma heta hp heps ha hg,
    eventually_gt_atTop (0:ℕ), hlarge] with d hclock hd hlarge
  have hdR : 1 ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : 0 < (d:ℝ) := by linarith
  have hpow : (d:ℝ)^(-(alpha+kappa))=(d:ℝ)^(-alpha)*(d:ℝ)^(-kappa) := by
    rw [show -(alpha+kappa)=(-alpha)+(-kappa) by ring, Real.rpow_add hdpos]
  have hstepEq : fluidLearningStep etaStar pStar alpha kappa d =
      etaStar*pStar*(d:ℝ)^(-(alpha+kappa)) := by
    unfold fluidLearningStep scaledLearningRate scaledSparsity
    rw [hpow]
    ring
  have hclockpos : 0 < fluidClock etaStar pStar alpha kappa epsStar gamma d := by
    unfold fluidClock
    apply lt_min
    · unfold fluidLearningStep scaledLearningRate scaledSparsity
      positivity
    · unfold scaledRetention
      positivity
  have hpowpos : 0 < (d:ℝ)^(-m) := Real.rpow_pos_of_pos hdpos _
  have hclocklb : c*(d:ℝ)^(-m) ≤ fluidClock etaStar pStar alpha kappa epsStar gamma d := by
    simpa [c,m] using hclock
  have hfloor := Nat.floor_le (div_nonneg hT hclockpos.le)
  have hN : (fluidGridHorizon T etaStar pStar alpha kappa epsStar gamma d:ℝ)
      ≤ T / fluidClock etaStar pStar alpha kappa epsStar gamma d := hfloor
  have hdiv : T / fluidClock etaStar pStar alpha kappa epsStar gamma d
      ≤ T / (c*(d:ℝ)^(-m)) :=
    div_le_div_of_nonneg_left hT (mul_pos hc hpowpos) hclocklb
  have hrewrite : T / (c*(d:ℝ)^(-m)) = (T/c)*(d:ℝ)^m := by
    rw [Real.rpow_neg (le_of_lt hdpos), div_eq_mul_inv]
    field_simp
  have hTle : T/c ≤ (d:ℝ) := le_trans (le_max_left _ _) hlarge
  have hq : (T/c)*(d:ℝ)^m ≤ (d:ℝ)^q := by
    have hqpow : (d:ℝ)^q=(d:ℝ)^m*(d:ℝ) := by
      dsimp [q,fluidHorizonDegree,m]
      rw [Real.rpow_add hdpos]
      simp [Real.rpow_one]
    rw [hqpow]
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hTle
      (Real.rpow_nonneg (by positivity : 0 ≤ (d:ℝ)) m)
  calc
    (fluidGridHorizon T etaStar pStar alpha kappa epsStar gamma d:ℝ)
        ≤ T / fluidClock etaStar pStar alpha kappa epsStar gamma d := hN
    _ ≤ T / (c*(d:ℝ)^(-m)) := hdiv
    _ = (T/c)*(d:ℝ)^m := hrewrite
    _ ≤ (d:ℝ)^q := hq

end
end SparseSGD.Scaling
