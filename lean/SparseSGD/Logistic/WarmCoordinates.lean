import SparseSGD.Logistic.FluidDeterministicFree
import SparseSGD.Logistic.FluidDeterministicPhysical

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

def matchedEffectiveSlow (beta : ℝ) (y : Fin 5 → ℝ) : ℝ × ℝ :=
  (y 0-beta*y 1,y 2-2*beta*y 3+beta^2*y 4)

theorem matchedEffectiveSlow_free (beta : ℝ) (y : Fin 5 → ℝ) :
    matchedEffectiveSlow beta (matchedFreeOperator beta y) = matchedEffectiveSlow beta y := by
  ext <;> simp [matchedEffectiveSlow,matchedFreeOperator_apply] <;> ring

theorem matchedEffectiveSlow_bulk_nonneg (beta : ℝ) (y : Fin 5 → ℝ)
    (hy : matchedPhysical y) : 0 ≤ (matchedEffectiveSlow beta y).2 := by
  have h := (matchedPhysical_iff_quadratic y).1 hy 1 (-beta)
  convert h using 1 <;> dsimp [matchedEffectiveSlow] <;> ring

theorem matchedEffectiveSlow_norm_bound (beta : ℝ) (y : Fin 5 → ℝ)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) : ‖matchedEffectiveSlow beta y‖ ≤ 4*‖y‖ := by
  have hc (i : Fin 5) : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i
  have hbn : |beta|=beta := abs_of_nonneg hb0
  apply norm_prod_le_iff.2
  constructor
  · change |y 0-beta*y 1| ≤ _
    apply (abs_sub _ _).trans
    rw [abs_mul,hbn]
    have hh := mul_le_mul hb1 (hc 1) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [hh,hc 0,norm_nonneg y]
  · change |y 2-2*beta*y 3+beta^2*y 4| ≤ _
    apply (abs_add_le _ _).trans
    have h := abs_sub (y 2) (2*beta*y 3)
    rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),hbn] at h
    rw [abs_mul,abs_pow,hbn]
    have hsq : beta^2 ≤ 1 := by nlinarith
    have h3 := mul_le_mul hb1 (hc 3) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have h4 := mul_le_mul hsq (hc 4) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [h,hc 2,h3,h4]

/-- Effective positions carry the finite warm-start momentum displacement.
Their exact update has learning-scale increments even through the fast layer. -/
theorem matchedEffectiveSlow_coefficient_step (r eta beta A b z : ℝ) (y : Fin 5 → ℝ) :
    matchedEffectiveSlow beta (matchedCoefficientStep r eta beta A b z y) =
      ((matchedEffectiveSlow beta y).1-eta*(A*y 0+b*r),
       (matchedEffectiveSlow beta y).2-2*eta*A*(y 2-beta*y 3)+eta^2*(A^2*y 2+z)) := by
  ext <;> simp [matchedEffectiveSlow,matchedCoefficientStep] <;> ring

def matchedColdEffective (beta : ℝ) (y : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![(matchedEffectiveSlow beta y).1,0,(matchedEffectiveSlow beta y).2,0,0]

theorem matchedColdEffective_physical (beta : ℝ) (y : Fin 5 → ℝ) (hy : matchedPhysical y) :
    matchedPhysical (matchedColdEffective beta y) := by
  simpa [matchedPhysical,matchedColdEffective] using matchedEffectiveSlow_bulk_nonneg beta y hy

theorem matchedColdEffective_effective (beta : ℝ) (y : Fin 5 → ℝ) :
    matchedEffectiveSlow beta (matchedColdEffective beta y)=matchedEffectiveSlow beta y := by
  ext <;> simp [matchedEffectiveSlow,matchedColdEffective]

/-- The discrepancy from the effective cold start belongs to the stable
free subspace and decays at the momentum rate, uniformly in retention. -/
theorem matchedColdEffective_free_decay (beta M : ℝ) (y : Fin 5 → ℝ) (n : ℕ)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) (hy : ‖y‖ ≤ M) :
    ‖((matchedFreeOperator beta)^n) (y-matchedColdEffective beta y)‖ ≤ 5*M*beta^n := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hy
  have hpow : 0 ≤ beta^n := pow_nonneg hb0 n
  have hpow1 : beta^n ≤ 1 := pow_le_one₀ hb0 hb1
  have hsq : beta^2 ≤ 1 := by nlinarith
  have hc (i : Fin 5) : |y i| ≤ M := by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y i).trans hy
  let v : Fin 5 → ℝ := ![beta*y 1,y 1,2*beta*y 3+beta^2*(beta^n-2)*y 4,
    y 3-beta*(1-beta^n)*y 4,beta^n*y 4]
  have he : ((matchedFreeOperator beta)^n) (y-matchedColdEffective beta y)=(beta^n) • v := by
    rw [matchedFreeOperator_pow_apply]
    ext i
    fin_cases i <;> simp [v,matchedColdEffective,matchedEffectiveSlow,pow_succ] <;> ring
  have hprod : beta*(1-beta^n) ≤ 1 := by nlinarith [mul_nonneg hb0 hpow]
  have hprod0 : 0 ≤ beta*(1-beta^n) := by positivity
  have hn : ‖v‖ ≤ 5*M := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 5*M)).2
    intro i
    have h1 : |beta*y 1| ≤ M := by
      rw [abs_mul,abs_of_nonneg hb0]
      exact (mul_le_mul hb1 (hc 1) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans (by simp)
    have h3 : |2*beta*y 3+beta^2*(beta^n-2)*y 4| ≤ 4*M := by
      apply (abs_add_le _ _).trans
      simp only [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),abs_of_nonneg hb0,
        abs_of_nonneg (sq_nonneg beta),abs_of_nonpos (by linarith : beta^n-2 ≤ 0)]
      have hleft := mul_le_mul hb1 (hc 3) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have hcoef : beta^2 * -(beta^n-2) ≤ 2 := by nlinarith [mul_nonneg (sq_nonneg beta) hpow]
      have hright := mul_le_mul hcoef (hc 4) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith only [hleft,hright]
    have h4 : |y 3-beta*(1-beta^n)*y 4| ≤ 2*M := by
      apply (abs_sub _ _).trans
      rw [abs_mul,abs_of_nonneg hprod0]
      have h := mul_le_mul hprod (hc 4) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith only [h,hc 3]
    have h5 : |beta^n*y 4| ≤ M := by
      rw [abs_mul,abs_of_nonneg hpow]
      exact (mul_le_mul hpow1 (hc 4) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans (by simp)
    rw [abs_mul] at h1
    rw [abs_mul,abs_pow] at h5
    fin_cases i <;> simp [v,Real.norm_eq_abs] <;> linarith [hc 1]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hpow]
  have h := mul_le_mul_of_nonneg_left hn hpow
  convert h using 1 <;> ring

end
end SparseSGD.Logistic
