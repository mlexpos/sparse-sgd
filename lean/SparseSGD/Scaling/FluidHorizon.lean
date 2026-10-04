import SparseSGD.Scaling.PowerParameters
import SparseSGD.Scaling.IntegerFamilies

open Filter Topology

namespace SparseSGD.Scaling
noncomputable section

/-- The power-law learning-time increment `eta*p`. -/
def fluidLearningStep (etaStar pStar alpha kappa : ℝ) (d : ℕ) : ℝ :=
  scaledLearningRate etaStar alpha d * scaledSparsity pStar kappa d

/-- The smaller learning/retention increment used as the fluid mesh. -/
def fluidClock (etaStar pStar alpha kappa epsStar gamma : ℝ) (d : ℕ) : ℝ :=
  min (fluidLearningStep etaStar pStar alpha kappa d) (scaledRetention epsStar gamma d)

/-- Number of actual grid points through physical time `T`. -/
def fluidGridHorizon (T etaStar pStar alpha kappa epsStar gamma : ℝ) (d : ℕ) : ℕ :=
  ⌊T / fluidClock etaStar pStar alpha kappa epsStar gamma d⌋₊

/-- Explicit degree covering the reciprocal of both candidate fluid clocks. -/
def fluidHorizonDegree (alpha kappa gamma : ℝ) : ℝ := max (alpha+kappa) gamma + 1

/-- For positive constants and nonnegative power exponents, the fluid mesh is
bounded below by the slower of the learning and retention powers. -/
theorem fluidClock_lower_bound_eventually
    (etaStar pStar alpha kappa epsStar gamma : ℝ)
    (heta : 0 < etaStar) (hp : 0 < pStar) (heps : 0 < epsStar)
    (ha : 0 ≤ alpha+kappa) (hg : 0 ≤ gamma) :
    ∀ᶠ d : ℕ in atTop,
      fluidClock etaStar pStar alpha kappa epsStar gamma d ≥
          min (etaStar*pStar) epsStar * (d:ℝ)^(-(max (alpha+kappa) gamma)) := by
  filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
  have hdR : 1 ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : 0 < (d:ℝ) := by linarith
  have hp1 : (d:ℝ)^(-(max (alpha+kappa) gamma)) ≤ (d:ℝ)^(-(alpha+kappa)) :=
    Real.rpow_le_rpow_of_exponent_le hdR (neg_le_neg (le_max_left _ _))
  have hp2 : (d:ℝ)^(-(max (alpha+kappa) gamma)) ≤ (d:ℝ)^(-gamma) :=
    Real.rpow_le_rpow_of_exponent_le hdR (neg_le_neg (le_max_right _ _))
  have hpow : (d:ℝ)^(-(alpha+kappa)) = (d:ℝ)^(-alpha)*(d:ℝ)^(-kappa) := by
    rw [show -(alpha+kappa)=(-alpha)+(-kappa) by ring, Real.rpow_add hdpos]
  have hstepEq : fluidLearningStep etaStar pStar alpha kappa d =
      etaStar*pStar*(d:ℝ)^(-(alpha+kappa)) := by
    unfold fluidLearningStep scaledLearningRate scaledSparsity
    rw [hpow]
    ring
  have hfirst : min (etaStar*pStar) epsStar * (d:ℝ)^(-(max (alpha+kappa) gamma)) ≤
      fluidLearningStep etaStar pStar alpha kappa d := by
    rw [hstepEq]
    exact mul_le_mul (min_le_left _ _) hp1 (Real.rpow_nonneg (by positivity) _) (by positivity)
  have hsecond : min (etaStar*pStar) epsStar * (d:ℝ)^(-(max (alpha+kappa) gamma)) ≤
      scaledRetention epsStar gamma d := by
    change min (etaStar*pStar) epsStar * (d:ℝ)^(-(max (alpha+kappa) gamma)) ≤
      epsStar * (d:ℝ)^(-gamma)
    exact mul_le_mul (min_le_right _ _) hp2 (Real.rpow_nonneg (by positivity) _) (by positivity)
  exact le_min hfirst hsecond

/-- The number of actual time-grid points up to any fixed `T` is eventually
bounded by `d^q` for the explicit exponent `q=max(alpha+kappa,gamma)+1`.
The batch exponent does not enter because this clock is `min(z,eps)`. -/
theorem fluidGridHorizon_eventually_le_polynomial
    (T etaStar pStar alpha kappa epsStar gamma : ℝ)
    (hT : 0 ≤ T) (heta : 0 < etaStar) (hp : 0 < pStar) (heps : 0 < epsStar)
    (ha : 0 ≤ alpha+kappa) (hg : 0 ≤ gamma) :
    ∃ q : ℝ, 0 ≤ q ∧ ∀ᶠ d : ℕ in atTop,
      (fluidGridHorizon T etaStar pStar alpha kappa epsStar gamma d : ℝ) ≤ (d:ℝ)^q := by
  let m := max (alpha+kappa) gamma
  let c := min (etaStar*pStar) epsStar
  let q := fluidHorizonDegree alpha kappa gamma
  have hm : 0 ≤ m := le_trans hg (le_max_right _ _)
  have hc : 0 < c := lt_min (mul_pos heta hp) heps
  have hlarge : ∀ᶠ d : ℕ in atTop, max (T/c) 1 ≤ (d:ℝ) := by
    exact (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d:ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (max (T/c) 1))
  refine ⟨q, by dsimp [q,fluidHorizonDegree]; linarith, ?_⟩
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

/-- In cells with vanishing learning and retention increments, the actual
fluid mesh tends to zero. -/
theorem fluidClock_tendsto_zero
    (etaStar pStar alpha kappa epsStar gamma : ℝ)
    (heta : 0 < etaStar) (hp : 0 < pStar) (heps : 0 < epsStar)
    (ha : 0 < alpha+kappa) (hg : 0 < gamma) :
    Tendsto (fun d : ℕ => fluidClock etaStar pStar alpha kappa epsStar gamma d)
      atTop (𝓝 0) := by
  have hstep : Tendsto (fun d : ℕ => fluidLearningStep etaStar pStar alpha kappa d)
      atTop (𝓝 0) := by
    have hpow : Tendsto (fun d : ℕ => (d:ℝ)^(-(alpha+kappa))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
    have hconst := hpow.const_mul (etaStar*pStar)
    have hpowid : ∀ᶠ d : ℕ in atTop,
        fluidLearningStep etaStar pStar alpha kappa d = etaStar*pStar*(d:ℝ)^(-(alpha+kappa)) := by
      filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
      have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
      have hpw : (d:ℝ)^(-(alpha+kappa))=(d:ℝ)^(-alpha)*(d:ℝ)^(-kappa) := by
        rw [show -(alpha+kappa)=(-alpha)+(-kappa) by ring, Real.rpow_add hdR]
      simp only [fluidLearningStep,scaledLearningRate,scaledSparsity]
      rw [hpw]
      ring
    have hconst' : Tendsto (fun d : ℕ => etaStar*pStar*(d:ℝ)^(-(alpha+kappa)))
        atTop (𝓝 0) := by simpa using hconst
    exact hconst'.congr' (hpowid.mono fun _ h => h.symm)
  have hret : Tendsto (fun d : ℕ => scaledRetention epsStar gamma d) atTop (𝓝 0) :=
    scaledRetention_tendsto_zero epsStar gamma hg
  have hmin := hstep.min hret
  simpa [fluidClock] using hmin


end
end SparseSGD.Scaling
