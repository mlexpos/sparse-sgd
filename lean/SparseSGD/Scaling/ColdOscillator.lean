import SparseSGD.Scaling.LSRegularCells
import SparseSGD.Comparison.SquareRootLift

open scoped Matrix.Norms.Operator Matrix
namespace SparseSGD.Scaling
noncomputable section

/-- The cold deterministic limiting oscillator in cell 3. -/
def coldOscillatorX (delta R t : ℝ) : ℝ := Real.sqrt R*continuumMeanFlow delta t 0 0
def coldOscillatorY (delta R t : ℝ) : ℝ := Real.sqrt R*continuumMeanFlow delta t 1 0

private theorem coldMean_entry_hasDerivAt (delta t : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => continuumMeanFlow delta t i j)
      ((continuumMeanGenerator delta * continuumMeanFlow delta t) i j) t := by
  let L : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ :=
    (LinearMap.proj j : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).comp
      (LinearMap.proj i : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
  exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' (continuumMeanGenerator delta) t)

theorem coldOscillatorX_derivative (delta R t : ℝ) :
    HasDerivAt (coldOscillatorX delta R) (-delta*coldOscillatorY delta R t) t := by
  convert (coldMean_entry_hasDerivAt delta t 0 0).const_mul (Real.sqrt R) using 1
  · rfl
  · simp [coldOscillatorY,continuumMeanGenerator,Matrix.mul_apply,Fin.sum_univ_two]
    ring

theorem coldOscillatorY_derivative (delta R t : ℝ) :
    HasDerivAt (coldOscillatorY delta R) (coldOscillatorX delta R t-coldOscillatorY delta R t) t := by
  convert (coldMean_entry_hasDerivAt delta t 1 0).const_mul (Real.sqrt R) using 1
  · rfl
  · simp [coldOscillatorX,coldOscillatorY,continuumMeanGenerator,Matrix.mul_apply,Fin.sum_univ_two]
    ring

theorem coldOscillator_equation (delta R t : ℝ) :
    deriv (deriv (coldOscillatorX delta R)) t+deriv (coldOscillatorX delta R) t+
      delta*coldOscillatorX delta R t=0 := by
  have HX : deriv (coldOscillatorX delta R)=fun t => -delta*coldOscillatorY delta R t :=
    funext (fun t => (coldOscillatorX_derivative delta R t).deriv)
  rw [HX,((coldOscillatorY_derivative delta R t).const_mul (-delta)).deriv]
  ring

theorem coldOscillator_initial (delta R : ℝ) :
    coldOscillatorX delta R 0=Real.sqrt R ∧ deriv (coldOscillatorX delta R) 0=0 := by
  rw [(coldOscillatorX_derivative delta R 0).deriv]
  simp [coldOscillatorX,coldOscillatorY,continuumMeanFlow_zero]

/-- The actual continuum risk at zero feedback and temperature is the square of the cold oscillator. -/
theorem continuum_cold_zero_loads_square (delta R t : ℝ) (hR : 0 ≤ R) :
    (continuumFlow delta 0 0 ⟨R,0,0⟩ t).R=(coldOscillatorX delta R t)^2 := by
  rw [continuumFlow_freeRisk]
  simp [continuumFreeRisk,Moments.cov,Matrix.mul_apply,Matrix.transpose_apply,
    Fin.sum_univ_two,coldOscillatorX,mul_pow,Real.sq_sqrt hR]
  ring

end
end SparseSGD.Scaling
