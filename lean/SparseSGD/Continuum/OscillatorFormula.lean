import SparseSGD.Continuum.CovarianceFlow

open scoped Matrix.Norms.Operator
namespace SparseSGD
noncomputable section

def oscillatorFormula (delta : ℝ) (C S : ℝ → ℝ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Real.exp (-t/2) • !![C t + S t / 2, -delta * S t; S t, C t - S t / 2]

theorem oscillatorFormula_hasDerivAt (delta : ℝ) (C S : ℝ → ℝ) (t : ℝ)
    (hC : HasDerivAt C ((1/4-delta)*S t) t) (hS : HasDerivAt S (C t) t) :
    HasDerivAt (oscillatorFormula delta C S)
      (oscillatorFormula delta C S t * continuumMeanGenerator delta) t := by
  have hE : HasDerivAt (fun t : ℝ => Real.exp (-t/2))
      (Real.exp (-t/2) * (-1/2)) t := by
    convert (((hasDerivAt_id t).neg.div_const 2).exp) using 1 <;> simp only [Pi.neg_def, id_eq] <;> ring
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · convert hE.mul (hC.add (hS.div_const 2)) using 1 <;>
      simp [oscillatorFormula, continuumMeanGenerator, Matrix.mul_apply, Fin.sum_univ_two, Pi.mul_def, Pi.add_def, Pi.sub_def, Pi.neg_def] <;> ring
  · convert hE.mul (hS.const_mul (-delta)) using 1 <;>
      simp [oscillatorFormula, continuumMeanGenerator, Matrix.mul_apply, Fin.sum_univ_two, Pi.mul_def, Pi.add_def, Pi.sub_def, Pi.neg_def] <;> ring
  · convert hE.mul hS using 1 <;>
      simp [oscillatorFormula, continuumMeanGenerator, Matrix.mul_apply, Fin.sum_univ_two, Pi.mul_def, Pi.add_def, Pi.sub_def, Pi.neg_def] <;> ring
  · convert hE.mul (hC.sub (hS.div_const 2)) using 1 <;>
      simp [oscillatorFormula, continuumMeanGenerator, Matrix.mul_apply, Fin.sum_univ_two, Pi.mul_def, Pi.add_def, Pi.sub_def, Pi.neg_def] <;> ring

theorem continuumMeanFlow_eq_oscillatorFormula (delta : ℝ) (C S : ℝ → ℝ)
    (hC0 : C 0 = 1) (hS0 : S 0 = 0)
    (hC : ∀ t, HasDerivAt C ((1/4-delta)*S t) t)
    (hS : ∀ t, HasDerivAt S (C t) t) (t : ℝ) (ht : 0 ≤ t) :
    continuumMeanFlow delta t = oscillatorFormula delta C S t := by
  let A := (ContinuousLinearMap.mul ℝ (Matrix (Fin 2) (Fin 2) ℝ)).flip
    (continuumMeanGenerator delta)
  have heq : Set.EqOn (continuumMeanFlow delta) (oscillatorFormula delta C S) (Set.Icc 0 t) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ x => A x) (s := fun _ => Set.univ) (K := ‖A‖₊)
    · intro x _
      exact A.lipschitzWith.lipschitzOnWith
    · exact fun x _ => (continuumMeanFlow_hasDerivAt delta x).continuousAt.continuousWithinAt
    · exact fun x _ => (continuumMeanFlow_hasDerivAt delta x).hasDerivWithinAt
    · simp
    · exact fun x _ => (oscillatorFormula_hasDerivAt delta C S x (hC x) (hS x)).continuousAt.continuousWithinAt
    · exact fun x _ => (oscillatorFormula_hasDerivAt delta C S x (hC x) (hS x)).hasDerivWithinAt
    · simp
    · rw [continuumMeanFlow_zero]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [oscillatorFormula, hC0, hS0]
  exact heq ⟨ht, le_rfl⟩

theorem continuumMeanFlow_critical (t : ℝ) (ht : 0 ≤ t) :
    continuumMeanFlow (1/4) t =
      Real.exp (-t/2) • !![1+t/2, -t/4; t, 1-t/2] := by
  rw [continuumMeanFlow_eq_oscillatorFormula (1/4) (fun _ => 1) id (by simp) (by simp)
    (by intro t; simpa using hasDerivAt_const t (1 : ℝ))
    (by intro t; exact hasDerivAt_id t) t ht]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oscillatorFormula] <;> ring

theorem continuumMeanFlow_critical_impulse_ne_zero (t : ℝ) (ht : 0 < t) :
    continuumMeanFlow (1/4) t 0 1 ≠ 0 := by
  rw [continuumMeanFlow_critical t ht.le]
  simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]
  exact mul_ne_zero (Real.exp_ne_zero _) (div_ne_zero (neg_ne_zero.mpr ht.ne') (by norm_num))

theorem continuumMeanFlow_oscillatory (delta omega t : ℝ) (homega : omega ≠ 0)
    (hsq : omega ^ 2 = delta - 1/4) (ht : 0 ≤ t) :
    continuumMeanFlow delta t = oscillatorFormula delta
      (fun x => Real.cos (x*omega)) (fun x => Real.sin (x*omega) / omega) t := by
  apply continuumMeanFlow_eq_oscillatorFormula
  · simp
  · simp
  · intro x
    convert (((hasDerivAt_id x).mul_const omega).cos) using 1
    · rfl
    · dsimp
      field_simp
      linear_combination 4 * Real.sin (x * omega) * hsq
  · intro x
    convert (((hasDerivAt_id x).mul_const omega).sin.div_const omega) using 1 <;>
      simp [homega]
  · exact ht

theorem continuumMeanFlow_hyperbolic (delta a t : ℝ) (ha : a ≠ 0)
    (hsq : a ^ 2 = 1/4 - delta) (ht : 0 ≤ t) :
    continuumMeanFlow delta t = oscillatorFormula delta
      (fun x => Real.cosh (x*a)) (fun x => Real.sinh (x*a) / a) t := by
  apply continuumMeanFlow_eq_oscillatorFormula
  · simp
  · simp
  · intro x
    convert (((hasDerivAt_id x).mul_const a).cosh) using 1
    · rfl
    · dsimp
      field_simp
      linear_combination -4 * Real.sinh (x * a) * hsq
  · intro x
    convert (((hasDerivAt_id x).mul_const a).sinh.div_const a) using 1 <;>
      simp [ha]
  · exact ht

theorem oscillatorFormula_trace (delta : ℝ) (C S : ℝ → ℝ) (t : ℝ) :
    (oscillatorFormula delta C S t).trace = 2 * Real.exp (-t/2) * C t := by
  simp [oscillatorFormula, Matrix.trace, Fin.sum_univ_two]
  ring

theorem oscillatorFormula_det (delta : ℝ) (C S : ℝ → ℝ) (t : ℝ)
    (hid : C t ^ 2 - (1/4-delta) * S t ^ 2 = 1) :
    (oscillatorFormula delta C S t).det = Real.exp (-t) := by
  have he : Real.exp (-t/2)^2 = Real.exp (-t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [oscillatorFormula, Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  calc
    _ = Real.exp (-t/2)^2 * (C t^2-(1/4-delta)*S t^2) := by ring
    _ = Real.exp (-t) := by rw [hid, mul_one, he]

end
end SparseSGD
