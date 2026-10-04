import SparseSGD.Scaling.Exponents
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

namespace SparseSGD.Scaling
noncomputable section

/-- A positive, integer-valued batch family. Its power-law interpretation below
requires a positive exponent; exponent zero is represented by a fixed integer. -/
def integerBatch (scale exponent : ℝ) (d : ℕ) : ℕ :=
  max 1 ⌊scale * (d : ℝ) ^ exponent⌋₊

theorem integerBatch_pos (scale exponent : ℝ) (d : ℕ) :
    0 < integerBatch scale exponent d :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem powerLaw_tendsto_atTop (scale exponent : ℝ) (hs : 0 < scale)
    (he : 0 < exponent) :
    Tendsto (fun d : ℕ => scale * (d : ℝ) ^ exponent) atTop atTop :=
  ((tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop).const_mul_atTop hs

theorem integerBatch_eventually_floor (scale exponent : ℝ) (hs : 0 < scale)
    (he : 0 < exponent) :
    ∀ᶠ d : ℕ in atTop, integerBatch scale exponent d =
      ⌊scale * (d : ℝ) ^ exponent⌋₊ := by
  filter_upwards [(powerLaw_tendsto_atTop scale exponent hs he).eventually
    (eventually_ge_atTop 1)] with d hd
  exact max_eq_right ((Nat.le_floor_iff (by positivity)).2 (by simpa using hd))

/-- Rounding does not change the asymptotic batch prefactor. -/
theorem integerBatch_ratio_tendsto (scale exponent : ℝ) (hs : 0 < scale)
    (he : 0 < exponent) :
    Tendsto (fun d : ℕ => (integerBatch scale exponent d : ℝ) /
      (scale * (d : ℝ) ^ exponent)) atTop (𝓝 1) := by
  apply (tendsto_nat_floor_div_atTop.comp
    (powerLaw_tendsto_atTop scale exponent hs he)).congr'
  filter_upwards [integerBatch_eventually_floor scale exponent hs he] with d hd
  rw [hd]
  rfl

theorem integerBatch_tendsto_atTop (scale exponent : ℝ) (hs : 0 < scale)
    (he : 0 < exponent) :
    Tendsto (integerBatch scale exponent) atTop atTop := by
  apply (tendsto_nat_floor_atTop.comp
    (powerLaw_tendsto_atTop scale exponent hs he)).congr'
  filter_upwards [integerBatch_eventually_floor scale exponent hs he] with d hd
  exact hd.symm

theorem fixedBatch_ratio (B : ℕ) (hB : 0 < B) (d : ℕ) :
    (B : ℝ) / ((B : ℝ) * (d : ℝ) ^ (0 : ℝ)) = 1 := by
  simp [Real.rpow_zero, Nat.cast_ne_zero.mpr hB.ne']

/-- A positive natural batch size cannot have a negative power-law exponent. -/
theorem no_positive_integer_batch_negative_exponent (B : ℕ → ℕ)
    (hB : ∀ d, 0 < B d) (scale exponent : ℝ) (he : exponent < 0) :
    ¬ Tendsto (fun d : ℕ => (B d : ℝ) / (scale * (d : ℝ) ^ exponent))
      atTop (𝓝 1) := by
  intro hlim
  have hp : Tendsto (fun d : ℕ => scale * (d : ℝ) ^ exponent) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (neg_pos.mpr he)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa using h.const_mul scale
  by_cases hs : scale = 0
  · subst scale
    simp only [zero_mul, div_zero] at hlim
    have := tendsto_nhds_unique hlim tendsto_const_nhds
    norm_num at this
  have hbzero : Tendsto (fun d : ℕ => (B d : ℝ)) atTop (𝓝 0) := by
    have h := hlim.mul hp
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
    exact div_mul_cancel₀ _ (mul_ne_zero hs (Real.rpow_pos_of_pos (by exact_mod_cast hd) _).ne')
  have hone : (1 : ℝ) ≤ 0 := ge_of_tendsto hbzero (Filter.Eventually.of_forall
    (fun d => by exact_mod_cast hB d))
  norm_num at hone

/-- Integer grid horizons never exceed the requested physical horizon. -/
theorem gridHorizon_le (T h : ℝ) (hT : 0 ≤ T) (hh : 0 < h) :
    (⌊T / h⌋₊ : ℝ) * h ≤ T := by
  have := Nat.floor_le (div_nonneg hT hh.le)
  exact (le_div_iff₀ hh).mp this

theorem gridHorizon_gap (T h : ℝ) (hh : 0 < h) :
    T - (⌊T / h⌋₊ : ℝ) * h < h := by
  have := Nat.lt_floor_add_one (T / h)
  have hmul := (div_lt_iff₀ hh).mp this
  nlinarith

end
end SparseSGD.Scaling
