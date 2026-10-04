import SparseSGD.Probability.GaussianCalculus

open MeasureTheory ProbabilityTheory
namespace SparseSGD.Probability
noncomputable section

theorem gaussianAverage_exponential (c q k : ℝ) (hq : 0 ≤ q) :
    gaussianAverage (fun x => Real.exp (k*x)) c q = Real.exp (k*c+k^2*q/2) := by
  rw [gaussianAverage_eq_integral _ (by fun_prop) c q hq]
  have h := congrFun (mgf_fun_id_gaussianReal (μ := c) (v := q.toNNReal)) k
  simpa only [mgf, Real.coe_toNNReal q hq, mul_comm c k, mul_comm q (k^2)] using h

theorem gaussianAverage_exponential_bound (f : ℝ → ℝ) (hf : Continuous f)
    (C k : ℝ) (hb : ∀ x, |f x| ≤ C*Real.exp (k*x)) (c q : ℝ) (hq : 0 ≤ q) :
    Integrable f (gaussianReal c q.toNNReal) ∧
      |gaussianAverage f c q| ≤ C*Real.exp (k*c+k^2*q/2) := by
  have hi : Integrable (fun x : ℝ => C*Real.exp (k*x)) (gaussianReal c q.toNNReal) :=
    (integrable_exp_mul_gaussianReal k).const_mul C
  have hfi : Integrable f (gaussianReal c q.toNNReal) := hi.mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))
  refine ⟨hfi, ?_⟩
  rw [gaussianAverage_eq_integral f hf c q hq]
  calc
    _ ≤ ∫ x, |f x| ∂gaussianReal c q.toNNReal := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f
    _ ≤ ∫ x, C*Real.exp (k*x) ∂gaussianReal c q.toNNReal := integral_mono hfi.abs hi hb
    _ = _ := by
      rw [integral_const_mul, ← gaussianAverage_eq_integral _ (by fun_prop) c q hq,
        gaussianAverage_exponential c q k hq]

theorem gaussianAverage_exponential_error (f : ℝ → ℝ) (hf : Continuous f)
    (C D : ℝ) (hb : ∀ x, |f x| ≤ C*Real.exp x)
    (he : ∀ x, |f x-Real.exp x| ≤ D*Real.exp (2*x)) (c q : ℝ) (hq : 0 ≤ q) :
    |gaussianAverage f c q-Real.exp (c+q/2)| ≤ D*Real.exp (2*c+2*q) := by
  have hi := (gaussianAverage_exponential_bound f hf C 1 (by simpa using hb) c q hq).1
  have H := (gaussianAverage_exponential_bound (fun x => f x-Real.exp x)
    (hf.sub Real.continuous_exp) D 2 he c q hq).2
  rw [gaussianAverage_eq_integral (fun x : ℝ => f x-Real.exp x) (by fun_prop) c q hq,
    integral_sub hi (by simpa using (integrable_exp_mul_gaussianReal (μ := c) (v := q.toNNReal) 1)),
    ← gaussianAverage_eq_integral f hf c q hq,
    ← gaussianAverage_eq_integral Real.exp Real.continuous_exp c q hq] at H
  have hExp : gaussianAverage Real.exp c q = Real.exp (c+q/2) := by
    simpa using gaussianAverage_exponential c q 1 hq
  rw [hExp] at H
  convert H using 1 <;> ring

end
end SparseSGD.Probability
