import SparseSGD.Logistic.IncrementBatchFourthRemainder
import SparseSGD.Logistic.IncrementSquareMGF

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

theorem gaussian_quartic_tilt_majorant (z : ℝ) :
    z^4*Real.exp (z^2/8) ≤ 8*z^2*Real.exp (z^2/4) := by
  have h : z^2/8 ≤ Real.exp (z^2/8) := by linarith [Real.add_one_le_exp (z^2/8)]
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 8*z^2*Real.exp (z^2/8) by positivity)
  have he : Real.exp (z^2/8)*Real.exp (z^2/8) = Real.exp (z^2/4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ 8*z^2*(Real.exp (z^2/8)*Real.exp (z^2/8)) := by nlinarith
    _ = _ := by rw [he]

/-- A fourth-order global MGF remainder gives a square-exponential
remainder with the same small variance coefficient. This uses actual
Gaussian auxiliary integration, not a squared-Bernstein assumption. -/
theorem square_fourth_remainder_of_global {X : Type*} [MeasurableSpace X]
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ) (hfm : Measurable f)
    (hf2 : Integrable (fun x => f x^2) κ)
    (V k A : ℝ) (hV : 0 ≤ V) (hA : 0 ≤ A) (hkA : 2*k*A ≤ 1/8)
    (hint : ∀ s : ℝ, Integrable (fun x => Real.exp (s*f x)) κ)
    (hrem : ∀ s : ℝ, (∫ x, Real.exp (s*f x) ∂κ)-1-(s^2/2)*(∫ x, f x^2 ∂κ) ≤
      V*s^4*Real.exp (k*s^2)) :
    Integrable (fun x => Real.exp (A*f x^2)) κ ∧
    (∫ x, Real.exp (A*f x^2) ∂κ)-1-A*(∫ x, f x^2 ∂κ) ≤ 128*V*A^2 := by
  let v := ∫ x, f x^2 ∂κ
  have hv : 0 ≤ v := integral_nonneg (fun _ => sq_nonneg _)
  let F : ℝ × X → ℝ := fun z => Real.exp (Real.sqrt (2*A)*z.1*f z.2)
  have hmF : Measurable F := Real.measurable_exp.comp
    ((measurable_const.mul measurable_fst).mul (hfm.comp measurable_snd))
  have hs (x : X) : (∫ z : ℝ, F (z,x) ∂gaussianReal 0 1) = Real.exp (A*f x^2) := by
    have hg := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) (Real.sqrt (2*A)*f x)
    simp only [mgf, zero_mul, NNReal.coe_one, one_mul, zero_add] at hg
    have he (z : ℝ) : F (z,x) = Real.exp ((Real.sqrt (2*A)*f x)*z) := by dsimp [F]; congr 1; ring
    simp_rw [he]
    rw [hg]
    congr 1
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2*A)]
    ring
  let M := fun z : ℝ => 1+(A*v)*z^2+(32*V*A^2)*(z^2*Real.exp (z^2/4))
  have hbound (z : ℝ) : (∫ x, F (z,x) ∂κ) ≤ M z := by
    have hh := hrem (Real.sqrt (2*A)*z)
    have he2 : (Real.sqrt (2*A)*z)^2 = 2*A*z^2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2*A)]
    have he4 : (Real.sqrt (2*A)*z)^4 = 4*A^2*z^4 := by
      calc
        _ = ((Real.sqrt (2*A)*z)^2)^2 := by ring
        _ = (2*A*z^2)^2 := by rw [he2]
        _ = _ := by ring
    rw [he2, he4] at hh
    have hex : Real.exp (k*(2*A*z^2)) ≤ Real.exp (z^2/8) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hkA (sq_nonneg z)]
    have hh' := mul_le_mul_of_nonneg_left hex (show 0 ≤ V*(4*A^2*z^4) by positivity)
    have hq := mul_le_mul_of_nonneg_left (gaussian_quartic_tilt_majorant z)
      (show 0 ≤ 4*V*A^2 by positivity)
    dsimp [M, F, v] at *
    nlinarith
  have hMI : Integrable M (gaussianReal 0 1) :=
    ((integrable_const (1 : ℝ)).add
      ((SparseSGD.Probability.gaussianReal_integrable_pow 0 1 2).const_mul (A*v))).add
      (G.tilted_second.1.const_mul (32*V*A^2))
  have hpair : Integrable F ((gaussianReal 0 1).prod κ) := by
    apply (integrable_prod_iff hmF.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun z => hint (Real.sqrt (2*A)*z)), ?_⟩
    apply hMI.mono' hmF.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards with z
    have he (x : X) : ‖F (z,x)‖ = F (z,x) := by simp only [F, Real.norm_eq_abs, Real.abs_exp]
    simp_rw [he]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => (Real.exp_pos _).le))]
    exact hbound z
  have htarget := hpair.integral_prod_right
  simp_rw [hs] at htarget
  refine ⟨htarget, ?_⟩
  have hswap := integral_integral_swap (f := fun z x => F (z,x)) hpair
  simp_rw [hs] at hswap
  rw [← hswap]
  have hh := integral_mono hpair.integral_prod_left hMI hbound
  dsimp only [M] at hh
  rw [integral_add (f := fun z : ℝ => 1+(A*v)*z^2)
    ((integrable_const (1 : ℝ)).add ((SparseSGD.Probability.gaussianReal_integrable_pow 0 1 2).const_mul (A*v)))
    (G.tilted_second.1.const_mul (32*V*A^2)),
    integral_add (f := fun _ : ℝ => (1 : ℝ)) (integrable_const _)
      ((SparseSGD.Probability.gaussianReal_integrable_pow 0 1 2).const_mul (A*v)),
    integral_const_mul, integral_const_mul, SparseSGD.Probability.gaussianReal_standard_second_moment] at hh
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one] at hh
  have hq := mul_le_mul_of_nonneg_left G.tilted_second.2 (show 0 ≤ 32*V*A^2 by positivity)
  dsimp [v] at hh
  nlinarith

end
end SparseSGD.Logistic
