import SparseSGD.Scaling.IntegerFamilies

open Filter Topology Asymptotics

namespace SparseSGD.Scaling
noncomputable section

theorem integerBatch_eq_floor_of_one_le (scale exponent : ℝ) (d : ℕ)
    (hx : 1 ≤ scale * (d : ℝ) ^ exponent) :
    integerBatch scale exponent d = ⌊scale * (d : ℝ) ^ exponent⌋₊ := by
  unfold integerBatch
  exact max_eq_right ((Nat.le_floor_iff (by positivity)).2 (by simpa using hx))

theorem integerBatch_floor_error (scale exponent : ℝ) (d : ℕ)
    (hx : 1 ≤ scale * (d : ℝ) ^ exponent) :
    0 ≤ scale * (d : ℝ) ^ exponent - (integerBatch scale exponent d : ℝ) ∧
    scale * (d : ℝ) ^ exponent - (integerBatch scale exponent d : ℝ) < 1 := by
  rw [integerBatch_eq_floor_of_one_le scale exponent d hx]
  constructor
  · have h := Nat.floor_le (by positivity : 0 ≤ scale * (d : ℝ) ^ exponent)
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · have h := Nat.lt_floor_add_one (scale * (d : ℝ) ^ exponent)
    have h' : scale * (d : ℝ) ^ exponent <
        (⌊scale * (d : ℝ) ^ exponent⌋₊ : ℝ) + 1 := by exact_mod_cast h
    linarith

theorem integerBatch_relative_error (scale exponent : ℝ) (d : ℕ)
    (hx : 1 ≤ scale * (d : ℝ) ^ exponent) :
    |(integerBatch scale exponent d : ℝ) /
      (scale * (d : ℝ) ^ exponent) - 1| ≤
        1 / (scale * (d : ℝ) ^ exponent) := by
  let x := scale * (d : ℝ) ^ exponent
  let b := (integerBatch scale exponent d : ℝ)
  have hxpos : 0 < x := by dsimp [x]; linarith
  obtain ⟨hlo, hhi⟩ := integerBatch_floor_error scale exponent d (by simpa [x] using hx)
  have hgaplo : 0 ≤ x-b := by simpa [x,b] using hlo
  have hgaphi : x-b < 1 := by simpa [x,b] using hhi
  have hratio : b/x-1 = -(x-b)/x := by field_simp; ring
  calc
    |b/x-1| = (x-b)/x := by
      rw [hratio, abs_div]
      rw [abs_neg, abs_of_nonneg hgaplo, abs_of_pos hxpos]
    _ ≤ 1/x := (div_le_div_iff₀ hxpos hxpos).2 (by nlinarith [hgaphi])

theorem integerBatch_inverse_relative_error (scale exponent : ℝ) (d : ℕ)
    (hx : 2 ≤ scale * (d : ℝ) ^ exponent) :
    |(scale * (d : ℝ) ^ exponent) /
      (integerBatch scale exponent d : ℝ) - 1| ≤
        2 / (scale * (d : ℝ) ^ exponent) := by
  let x := scale * (d : ℝ) ^ exponent
  let b := (integerBatch scale exponent d : ℝ)
  have hxpos : 0 < x := by dsimp [x]; linarith
  obtain ⟨hlo, hhi⟩ := integerBatch_floor_error scale exponent d (by linarith)
  have hgaplo : 0 ≤ x-b := by simpa [x,b] using hlo
  have hgaphi : x-b < 1 := by simpa [x,b] using hhi
  have hBpos : 0 < b := by
    linarith
  have hBhalf : x/2 ≤ b := by linarith [hgaphi]
  have hratio : x/b-1 = (x-b)/b := by field_simp
  calc
    |x/b-1| = (x-b)/b := by
      rw [hratio, abs_div]
      rw [abs_of_nonneg hgaplo, abs_of_pos hBpos]
    _ ≤ 2/x := by
      rw [div_le_div_iff₀ hBpos hxpos]
      have hm : (x-b)*x ≤ x := by nlinarith [hgaplo, hgaphi, hxpos]
      have hm2 : x ≤ 2*b := by linarith
      nlinarith

theorem integerBatch_rounding_eventually (scale exponent : ℝ)
    (hs : 0 < scale) (he : 0 < exponent) :
    ∀ᶠ d : ℕ in atTop,
      |(integerBatch scale exponent d : ℝ) /
        (scale * (d : ℝ) ^ exponent) - 1| ≤
          1 / (scale * (d : ℝ) ^ exponent) ∧
      |(scale * (d : ℝ) ^ exponent) /
        (integerBatch scale exponent d : ℝ) - 1| ≤
          2 / (scale * (d : ℝ) ^ exponent) := by
  filter_upwards [(powerLaw_tendsto_atTop scale exponent hs he).eventually
    (eventually_ge_atTop (2 : ℝ))] with d hd
  exact ⟨integerBatch_relative_error scale exponent d (by linarith),
    integerBatch_inverse_relative_error scale exponent d (by linarith)⟩

theorem integerBatch_relative_error_isBigO (scale exponent : ℝ)
    (hs : 0 < scale) (he : 0 < exponent) :
    (fun d : ℕ => |(integerBatch scale exponent d : ℝ) /
      (scale * (d : ℝ) ^ exponent) - 1|) =O[atTop]
      (fun d : ℕ => (d : ℝ) ^ (-exponent)) := by
  rw [isBigO_iff]
  refine ⟨1/scale, ?_⟩
  filter_upwards [integerBatch_rounding_eventually scale exponent hs he,
    eventually_gt_atTop (0 : ℕ)] with d hd hpos
  have hp : 0 < (d : ℝ) ^ exponent := Real.rpow_pos_of_pos (by exact_mod_cast hpos) _
  have heq : 1/(scale * (d : ℝ)^exponent) =
      (1/scale) * (d : ℝ)^(-exponent) := by
    rw [Real.rpow_neg (by positivity : 0 ≤ (d : ℝ))]
    field_simp
  have hnorm : ‖(d : ℝ)^(-exponent)‖ = (d : ℝ)^(-exponent) := by
    rw [Real.norm_eq_abs, abs_of_pos
      (Real.rpow_pos_of_pos (by exact_mod_cast hpos) (-exponent))]
  calc
    ‖|(integerBatch scale exponent d : ℝ)/(scale * (d : ℝ)^exponent)-1|‖ =
        |(integerBatch scale exponent d : ℝ)/(scale * (d : ℝ)^exponent)-1| := by
      rw [Real.norm_eq_abs, abs_abs]
    _ ≤ 1/(scale * (d : ℝ)^exponent) := hd.1
    _ = (1/scale) * ‖(d : ℝ)^(-exponent)‖ := by rw [heq, hnorm]

theorem integerBatch_zero_exponent_eq_fixed (scale : ℝ) (d : ℕ) :
    integerBatch scale 0 d = integerBatch scale 0 0 := by
  simp [integerBatch]

end
end SparseSGD.Scaling
