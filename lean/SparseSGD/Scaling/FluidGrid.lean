import SparseSGD.Scaling.FluidHorizon

open Filter Topology

namespace SparseSGD.Scaling
noncomputable section

/-- The minimum of a vanishing positive mesh and any eventually positive
second mesh also vanishes; the second mesh need not tend to zero. -/
theorem tendsto_min_zero_of_tendsto_zero
    (z e : ℕ → ℝ) (hz : Tendsto z atTop (𝓝 0))
    (he : ∀ᶠ d : ℕ in atTop, 0 < e d) :
    Tendsto (fun d => min (z d) (e d)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    filter_upwards [hz.eventually (Ioi_mem_nhds hb), he] with d hzd hed
    exact lt_min hzd (by linarith)
  · intro b hb
    filter_upwards [hz.eventually (Iio_mem_nhds hb), he] with d hzd hed
    exact lt_of_le_of_lt (min_le_left _ _) hzd

/-- A floor horizon fits under its physical horizon whenever the mesh is
positive. -/
theorem fluid_grid_floor_le (T h : ℝ) (hT : 0 ≤ T) (hh : 0 < h) :
    (⌊T / h⌋₊ : ℝ) * h ≤ T :=
  gridHorizon_le T h hT hh

/-- If a positive mesh tends to zero, every fixed positive time interval
eventually contains at least one grid step. -/
theorem floor_horizon_eventually_pos (T : ℝ) (hT : 0 < T) (h : ℕ → ℝ)
    (hh : ∀ᶠ d : ℕ in atTop, 0 < h d)
    (hlim : Tendsto h atTop (𝓝 0)) :
    ∀ᶠ d : ℕ in atTop, 0 < ⌊T / h d⌋₊ := by
  filter_upwards [hh, hlim.eventually (Iio_mem_nhds hT)] with d hpos hsmall
  have hratio : 1 ≤ T / h d := (le_div_iff₀ hpos).2 (by linarith)
  exact Nat.floor_pos.mpr hratio

/-- The actual power-law fluid clock vanishes whenever the learning increment
does. This includes gamma=0, since the retention increment stays positive. -/
theorem actual_fluidClock_tendsto_zero
    (etaStar pStar alpha kappa epsStar gamma : ℝ)
    (heta : 0 < etaStar) (hp : 0 < pStar) (heps : 0 < epsStar)
    (ha : 0 < alpha+kappa) :
    Tendsto (fun d : ℕ => fluidClock etaStar pStar alpha kappa epsStar gamma d)
      atTop (𝓝 0) := by
  have hz : Tendsto (fun d : ℕ => fluidLearningStep etaStar pStar alpha kappa d)
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
  have hepos : ∀ᶠ d : ℕ in atTop, 0 < scaledRetention epsStar gamma d := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    unfold scaledRetention
    positivity
  exact tendsto_min_zero_of_tendsto_zero _ _ hz hepos

/-- The actual fluid grid horizon is eventually nonzero for every positive
physical horizon whenever alpha+kappa>0. -/
theorem actual_fluidGridHorizon_eventually_pos
    (T etaStar pStar alpha kappa epsStar gamma : ℝ)
    (hT : 0 < T) (heta : 0 < etaStar) (hp : 0 < pStar)
    (heps : 0 < epsStar) (ha : 0 < alpha+kappa) :
    ∀ᶠ d : ℕ in atTop,
      0 < fluidGridHorizon T etaStar pStar alpha kappa epsStar gamma d := by
  apply floor_horizon_eventually_pos T hT
    (fluidClock etaStar pStar alpha kappa epsStar gamma)
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    unfold fluidClock fluidLearningStep scaledLearningRate scaledSparsity scaledRetention
    positivity
  · exact actual_fluidClock_tendsto_zero etaStar pStar alpha kappa epsStar gamma heta hp heps ha

/-- Every positive actual fluid clock gives a floor grid horizon staying at
or before the requested time. -/
theorem actual_fluidGridHorizon_le
    (T etaStar pStar alpha kappa epsStar gamma : ℝ) (d : ℕ)
    (hT : 0 ≤ T)
    (hclock : 0 < fluidClock etaStar pStar alpha kappa epsStar gamma d) :
    (fluidGridHorizon T etaStar pStar alpha kappa epsStar gamma d : ℝ) *
      fluidClock etaStar pStar alpha kappa epsStar gamma d ≤ T := by
  exact fluid_grid_floor_le T _ hT hclock

end
end SparseSGD.Scaling
