import SparseSGD.Logistic.IncrementSquareMGF

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section

theorem exp_add_le_average_doubles (x y : ℝ) :
    Real.exp (x+y) ≤ (Real.exp (2*x)+Real.exp (2*y))/2 := by
  rw [Real.exp_add]
  have hx : Real.exp (2*x) = (Real.exp x)^2 := by
    rw [show 2*x = x+x by ring, Real.exp_add]
    ring
  have hy : Real.exp (2*y) = (Real.exp y)^2 := by
    rw [show 2*y = y+y by ring, Real.exp_add]
    ring
  rw [hx, hy]
  nlinarith [sq_nonneg (Real.exp x-Real.exp y)]

/-- Two possibly dependent exponentials can be combined from their
doubled MGF bounds. Measurability and integrability precede the integral. -/
theorem exp_add_integrable_bound {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] (f g : X → ℝ)
    (hfm : Measurable f) (hgm : Measurable g) (Cf Cg : ℝ) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : Integrable (fun x => Real.exp (2*f x)) κ)
    (hg : Integrable (fun x => Real.exp (2*g x)) κ)
    (hfe : (∫ x, Real.exp (2*f x) ∂κ) ≤ Real.exp Cf)
    (hge : (∫ x, Real.exp (2*g x) ∂κ) ≤ Real.exp Cg) :
    Integrable (fun x => Real.exp (f x+g x)) κ ∧
    (∫ x, Real.exp (f x+g x) ∂κ) ≤ Real.exp (Cf+Cg) := by
  have hmajor := (hf.add hg).div_const 2
  have hi : Integrable (fun x => Real.exp (f x+g x)) κ := by
    apply hmajor.mono' (Real.measurable_exp.comp (hfm.add hgm)).aestronglyMeasurable
    filter_upwards with x
    change ‖Real.exp (f x+g x)‖ ≤ (Real.exp (2*f x)+Real.exp (2*g x))/2
    rw [Real.norm_eq_abs, Real.abs_exp]
    exact exp_add_le_average_doubles _ _
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi hmajor (fun x => exp_add_le_average_doubles (f x) (g x))
  simp only [Pi.add_apply] at hh
  rw [integral_div, integral_add hf hg] at hh
  have hxf : Real.exp Cf ≤ Real.exp (Cf+Cg) := Real.exp_le_exp.mpr (by linarith)
  have hxg : Real.exp Cg ≤ Real.exp (Cf+Cg) := Real.exp_le_exp.mpr (by linarith)
  linarith

end
end SparseSGD.Logistic
