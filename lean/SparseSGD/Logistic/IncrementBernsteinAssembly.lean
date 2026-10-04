import SparseSGD.Logistic.IncrementEffectiveStep
import SparseSGD.Logistic.IncrementComplementMean
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

/-- Two dependent Bernstein components can be combined with an explicitly
bounded coefficient. This is proved by exponential Jensen domination. -/
theorem increment_two_component_bernstein {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] (f g : X → ℝ)
    (hf : Measurable f) (hg : Measurable g) (v1 v2 M1 M2 c C t : ℝ)
    (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hC : 0 ≤ C) (hc : |c| ≤ C)
    (hmgf1 : ∀ s : ℝ, |s| * M1 < 1 → Integrable (fun x => Real.exp (s*f x)) κ ∧
      (∫ x, Real.exp (s*f x) ∂κ) ≤ Real.exp (s^2*v1/(2*(1-|s| * M1))))
    (hmgf2 : ∀ s : ℝ, |s| * M2 < 1 → Integrable (fun x => Real.exp (s*g x)) κ ∧
      (∫ x, Real.exp (s*g x) ∂κ) ≤ Real.exp (s^2*v2/(2*(1-|s| * M2))))
    (ht : |t| * (2*(M1+C*M2)) < 1) :
    Integrable (fun x => Real.exp (t*(f x+c*g x))) κ ∧
    (∫ x, Real.exp (t*(f x+c*g x)) ∂κ) ≤
      Real.exp (t^2*(4*(v1+C^2*v2))/(2*(1-|t| * (2*(M1+C*M2))))) := by
  have hdom1 : |2*t| * M1 < 1 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [mul_nonneg (abs_nonneg t) (mul_nonneg hC hM2)]
  have hdom2 : |2*t*c| * M2 < 1 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*|t| * M2 by positivity)
    nlinarith [mul_nonneg (abs_nonneg t) hM1]
  have h1 := hmgf1 (2*t) hdom1
  have h2 := hmgf2 (2*t*c) hdom2
  let Cf := (2*t)^2*v1/(2*(1-|2*t| * M1))
  let Cg := (2*t*c)^2*v2/(2*(1-|2*t*c| * M2))
  have hCf : 0 ≤ Cf := by dsimp [Cf]; positivity
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have he1 (x : X) : 2*(t*f x) = (2*t)*f x := by ring
  have he2 (x : X) : 2*(t*c*g x) = (2*t*c)*g x := by ring
  have hh := exp_add_integrable_bound κ (fun x => t*f x) (fun x => t*c*g x)
    (hf.const_mul _) (hg.const_mul _) Cf Cg hCf hCg
    (by simp_rw [he1]; exact h1.1) (by simp_rw [he2]; exact h2.1)
    (by simp_rw [he1]; exact h1.2) (by simp_rw [he2]; exact h2.2)
  have he (x : X) : t*(f x+c*g x) = t*f x+t*c*g x := by ring
  simp_rw [he]
  refine ⟨hh.1, hh.2.trans ?_⟩
  apply Real.exp_le_exp.mpr
  let D := 2*(1-|t| * (2*(M1+C*M2)))
  have hD : 0 < D := by dsimp [D]; linarith
  have hDf : D ≤ 2*(1-|2*t| * M1) := by
    dsimp [D]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [mul_nonneg (abs_nonneg t) (mul_nonneg hC hM2)]
  have hDg : D ≤ 2*(1-|2*t*c| * M2) := by
    dsimp [D]
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*|t| * M2 by positivity)
    nlinarith [mul_nonneg (abs_nonneg t) hM1]
  have hfbound := div_le_div_of_nonneg_left (show 0 ≤ (2*t)^2*v1 by positivity) hD hDf
  have hgbound := div_le_div_of_nonneg_left (show 0 ≤ (2*t*c)^2*v2 by positivity) hD hDg
  have hc2 : c^2 ≤ C^2 := by
    have hh := mul_self_le_mul_self (abs_nonneg c) hc
    simpa only [← pow_two, sq_abs] using hh
  have hn := mul_le_mul_of_nonneg_left hc2 (show 0 ≤ 4*t^2*v2 by positivity)
  have hnum : (2*t*c)^2*v2 ≤ 4*t^2*C^2*v2 := by nlinarith
  have hdiv := div_le_div_of_nonneg_right hnum hD.le
  have hgfinal := hgbound.trans hdiv
  have htotal := add_le_add hfbound hgfinal
  dsimp [Cf, Cg]
  exact htotal.trans_eq (by dsimp [D]; ring)
end
end SparseSGD.Logistic
