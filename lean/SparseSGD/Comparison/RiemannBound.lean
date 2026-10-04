import SparseSGD.Comparison.UniformBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

open MeasureTheory Set Filter Topology

namespace SparseSGD
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def rightEndpointSum (f : ℝ → E) (h : ℝ) (k : ℕ) : E :=
  ∑ n ∈ Finset.range k, h • f ((n+1 : ℕ)*h)

theorem rightEndpoint_cell_error (f f' : ℝ → E)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hc : Continuous f')
    (a b : ℝ) (hab : a ≤ b) :
    ‖(∫ x in a..b, f x) - (b-a) • f b‖ ≤
      (b-a) * ∫ x in a..b, ‖f' x‖ := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) :
      ‖f x - f b‖ ≤ ∫ x in a..b, ‖f' x‖ := by
    rw [norm_sub_rev]
    calc
      ‖f b-f x‖ ≤ ∫ y in x..b, ‖f' y‖ := by
        apply norm_sub_le_integral_of_norm_deriv_le_of_le hx.2
          hfc.continuousOn (fun y _ => (hf y).differentiableAt.differentiableWithinAt)
        · exact Eventually.of_forall fun y _ => by rw [(hf y).deriv]
        · exact hc.norm.intervalIntegrable x b
      _ ≤ ∫ y in a..b, ‖f' y‖ := by
        apply intervalIntegral.integral_mono_interval hx.1 hx.2 le_rfl
        · exact Eventually.of_forall fun y => norm_nonneg _
        · exact hc.norm.intervalIntegrable a b
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun x => f x-f b)
    (fun x hx => hpoint x (by rw [uIoc_of_le hab] at hx; exact ⟨hx.1.le,hx.2⟩))
  rw [intervalIntegral.integral_sub (hfc.intervalIntegrable a b) (intervalIntegrable_const),
    intervalIntegral.integral_const, abs_of_nonneg (sub_nonneg.mpr hab)] at h
  simpa only [mul_comm] using h

/-- Right-endpoint quadrature controlled by the integral of the derivative norm. -/
theorem rightEndpoint_error (f f' : ℝ → E)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hc : Continuous f')
    (h : ℝ) (hh : 0 ≤ h) (k : ℕ) :
    ‖(∫ x in (0 : ℝ)..(k : ℝ)*h, f x) - rightEndpointSum f h k‖ ≤
      h * ∫ x in (0 : ℝ)..(k : ℝ)*h, ‖f' x‖ := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume)
    (a := fun n : ℕ => (n : ℝ)*h) (n := k)
    (fun n _ => hfc.intervalIntegrable ((n : ℝ)*h) ((n+1 : ℕ)*h))
  have hsum' := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume)
    (a := fun n : ℕ => (n : ℝ)*h) (n := k)
    (fun n _ => hc.norm.intervalIntegrable ((n : ℝ)*h) ((n+1 : ℕ)*h))
  simp only [Nat.cast_zero, zero_mul] at hsum hsum'
  rw [← hsum, rightEndpointSum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.range k,
        ‖(∫ x in (n : ℝ)*h..(n+1 : ℕ)*h, f x) - h • f ((n+1 : ℕ)*h)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range k, h * ∫ x in (n : ℝ)*h..(n+1 : ℕ)*h, ‖f' x‖ := by
      apply Finset.sum_le_sum
      intro n hn
      have hstep : ((n+1 : ℕ) : ℝ)*h-(n : ℝ)*h = h := by push_cast; ring
      have hle : (n : ℝ)*h ≤ ((n+1 : ℕ) : ℝ)*h := by nlinarith
      simpa only [hstep] using rightEndpoint_cell_error f f' hf hc
        ((n : ℝ)*h) (((n+1 : ℕ) : ℝ)*h) hle
    _ = _ := by rw [← Finset.mul_sum, hsum']

/-- The same quadrature estimate on the positive half-line, for summable samples. -/
theorem rightEndpoint_infinite_error (f f' : ℝ → E)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hc : Continuous f')
    (hi : IntegrableOn f (Ioi 0)) (hi' : IntegrableOn (fun x => ‖f' x‖) (Ioi 0))
    (h : ℝ) (hh : 0 < h) (S : E)
    (hsum : HasSum (fun n : ℕ => h • f ((n+1 : ℕ)*h)) S) :
    ‖(∫ x in Ioi (0 : ℝ), f x)-S‖ ≤ h * ∫ x in Ioi (0 : ℝ), ‖f' x‖ := by
  have hgrid : Tendsto (fun n : ℕ => (n : ℝ)*h) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hh
  have hleft := (intervalIntegral_tendsto_integral_Ioi 0 hi hgrid).sub
    hsum.tendsto_sum_nat
  have hright := (intervalIntegral_tendsto_integral_Ioi 0 hi' hgrid).const_mul h
  exact le_of_tendsto_of_tendsto' hleft.norm hright
    (fun k => rightEndpoint_error f f' hf hc h hh.le k)

end
end SparseSGD
