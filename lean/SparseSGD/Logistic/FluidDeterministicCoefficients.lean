import SparseSGD.Logistic.ScalarCoefficients
import SparseSGD.Logistic.RectangleTaylor
open MeasureTheory SparseSGD.Probability
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

theorem scalarBias_exp_le (p : unitInterval) (r : ℝ) (hp : 0<(p:ℝ))
    (hhalf : (p:ℝ)≤1/2) : Real.exp (scalarBias p r)≤2*(p:ℝ) := by
  have hd : 0<1-(p:ℝ) := by linarith
  have hfrac : (p:ℝ)/(1-(p:ℝ))≤2*(p:ℝ) := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have he : Real.exp (-(r^2/2))≤1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r])
  unfold scalarBias
  rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (div_pos hp hd)]
  exact (mul_le_mul_of_nonneg_left he (div_pos hp hd).le).trans (by simpa using hfrac)

theorem scalarBias_gaussian_exp_le (p : unitInterval) (r q Q : ℝ)
    (hp : 0<(p:ℝ)) (hhalf : (p:ℝ)≤1/2) (hq : q≤Q) :
    Real.exp (scalarBias p r+q/2)≤(2*Real.exp (Q/2))*(p:ℝ) := by
  rw [Real.exp_add]
  calc
    _ ≤ (2*(p:ℝ))*Real.exp (Q/2) :=
      mul_le_mul (scalarBias_exp_le p r hp hhalf) (Real.exp_le_exp.mpr (by linarith))
        (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

theorem scalarBias_gaussian_square_exp_le (p : unitInterval) (r q Q : ℝ)
    (hp : 0<(p:ℝ)) (hhalf : (p:ℝ)≤1/2) (hq : q≤Q) :
    Real.exp (2*scalarBias p r+2*q)≤(4*Real.exp (2*Q))*(p:ℝ) := by
  have hs := scalarBias_exp_le p r hp hhalf
  have hp1 : (p:ℝ)≤1 := p.property.2
  have he : Real.exp (2*scalarBias p r)≤4*(p:ℝ) := by
    rw [show 2*scalarBias p r=scalarBias p r+scalarBias p r by ring,Real.exp_add]
    nlinarith [Real.exp_pos (scalarBias p r),mul_nonneg hp.le (sub_nonneg.mpr hp1)]
  rw [Real.exp_add]
  calc
    _ ≤ (4*(p:ℝ))*Real.exp (2*Q) :=
      mul_le_mul he (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

private theorem bounded_average (f : ℝ→ℝ) (hf : Continuous f) (C : ℝ)
    (hC : ∀ x, |f x|≤C) (c q : ℝ) (hq : 0≤q) : |gaussianAverage f c q|≤C := by
  simpa using (gaussianAverage_exponential_bound f hf C 0 (by simpa using hC) c q hq).2

private theorem scalarGaussianJet_bound_of_averages (f0 f1 : ℕ→ℝ→ℝ)
    (base a b : ℕ) (p : unitInterval) (r t q N P : ℝ)
    (hN : 0≤N) (hP : 0≤P)
    (h0 : |gaussianAverage (f0 (base+a+2*b)) (scalarBias p r) q|≤N*(p:ℝ))
    (h1 : |gaussianAverage (f1 (base+a+2*b)) (r*t+scalarBias p r) q|≤P) :
    |scalarGaussianJet f0 f1 base a b p r t q|≤
      (|r|^a*(1/2:ℝ)^b*(N+P))*(p:ℝ) := by
  have hp0 := p.property.1
  have hp1 := p.property.2
  have hf : 0≤|r|^a*(1/2:ℝ)^b := by positivity
  unfold scalarGaussianJet
  rw [abs_mul,abs_mul,abs_pow,abs_of_nonneg (by positivity : 0≤(1/2:ℝ)^b)]
  rw [mul_assoc (|r|^a*(1/2:ℝ)^b) (N+P) (p:ℝ)]
  apply mul_le_mul_of_nonneg_left _ hf
  by_cases ha : a=0
  · simp only [ha,if_true]
    calc
      _ ≤ |(1-(p:ℝ))*gaussianAverage (f0 (base+0+2*b)) (scalarBias p r) q|+
          |(p:ℝ)*gaussianAverage (f1 (base+0+2*b)) (r*t+scalarBias p r) q| := abs_add_le _ _
      _ ≤ (1-(p:ℝ))*(N*(p:ℝ))+(p:ℝ)*P := by
        rw [abs_mul,abs_of_nonneg (by linarith : 0≤1-(p:ℝ)),abs_mul,abs_of_nonneg hp0]
        exact add_le_add (mul_le_mul_of_nonneg_left (by simpa [ha] using h0) (by linarith))
          (mul_le_mul_of_nonneg_left (by simpa [ha] using h1) hp0)
      _ ≤ (N+P)*(p:ℝ) := by nlinarith [mul_nonneg hp0 (mul_nonneg hN hp0)]
  · simp only [ha,if_false,zero_add,abs_mul,abs_of_nonneg hp0]
    nlinarith [mul_le_mul_of_nonneg_left h1 hp0,mul_nonneg hN hp0]

/-- Every scalar A jet is O(p), uniformly on any bounded nonnegative variance
interval. No actual-vector embedding or path tameness is required. -/
theorem scalarCoefAJet_compact_bound (a b : ℕ) (r Q : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (p : unitInterval) (t q : ℝ),
      0<(p:ℝ) → (p:ℝ)≤1/2 → 0≤q → q≤Q →
      |scalarCoefAJet a b p r t q|≤C*(p:ℝ) := by
  obtain ⟨N,hN,h0⟩ := gaussian_sigmaDerivative_bounds (1+a+2*b)
  obtain ⟨P,h1⟩ := sigma_boundedDerivativeSequence.bounded (1+a+2*b)
  have hP : 0≤P := (abs_nonneg _).trans (h1 0)
  refine ⟨|r|^a*(1/2:ℝ)^b*(N*(2*Real.exp (Q/2))+P),by positivity,?_⟩
  intro p t q hp hh hq hQ
  apply scalarGaussianJet_bound_of_averages _ _ _ _ _ _ _ _ _ _ _ (by positivity) hP
  · exact ((h0 _ _ hq).1).trans (by
      have H := mul_le_mul_of_nonneg_left (scalarBias_gaussian_exp_le p r q Q hp hh hQ) (by linarith : 0≤N)
      convert H using 1 <;> ring)
  · exact bounded_average _ (sigma_boundedDerivativeSequence.continuous _) P h1 _ _ hq
/-- Square coefficient jets share the same O(p) bound on nonnegative bounded
variance, including the zeroth moment. -/
theorem scalarSquareJet_compact_bound (base a b : ℕ) (r Q : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (p : unitInterval) (t q : ℝ),
      0<(p:ℝ) → (p:ℝ)≤1/2 → 0≤q → q≤Q →
      |scalarGaussianJet sigmaSquareDerivative oneMinusSigmaSquareDerivative base a b p r t q|≤C*(p:ℝ) := by
  obtain ⟨N,hN,h0⟩ := gaussian_sigmaSquareDerivative_bound (base+a+2*b)
  obtain ⟨P,h1⟩ := oneMinusSigmaSquare_boundedDerivativeSequence.bounded (base+a+2*b)
  have hP : 0≤P := (abs_nonneg _).trans (h1 0)
  refine ⟨|r|^a*(1/2:ℝ)^b*(N*(4*Real.exp (2*Q))+P),by positivity,?_⟩
  intro p t q hp hh hq hQ
  apply scalarGaussianJet_bound_of_averages _ _ _ _ _ _ _ _ _ _ _ (by positivity) hP
  · exact (h0 _ _ hq).trans (by
      have H := mul_le_mul_of_nonneg_left (scalarBias_gaussian_square_exp_le p r q Q hp hh hQ) hN
      convert H using 1 <;> ring)
  · exact bounded_average _ (oneMinusSigmaSquare_boundedDerivativeSequence.continuous _) P h1 _ _ hq

theorem scalarCoefBJet_compact_bound (a b : ℕ) (r : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (p : unitInterval) (t q : ℝ), 0≤q →
      |scalarCoefBJet a b p r t q|≤C*(p:ℝ) := by
  obtain ⟨P,h1⟩ := sigma_boundedDerivativeSequence.bounded (a+2*b)
  have hP : 0≤P := (abs_nonneg _).trans (h1 0)
  refine ⟨|r|^a*(1/2:ℝ)^b*P+1,by positivity,?_⟩
  intro p t q hq
  have hp := p.property.1
  have hAvg := bounded_average _ (sigma_boundedDerivativeSequence.continuous _) P h1
    (r*t+scalarBias p r) q hq
  have H : |scalarGaussianJet (fun _ _ =>0) sigmaDerivative 0 a b p r t q|≤
      (|r|^a*(1/2:ℝ)^b*P)*(p:ℝ) := by
    unfold scalarGaussianJet
    simp only [scalar_gaussianAverage_zero,mul_zero,ite_self,zero_add,Nat.zero_add,
      abs_mul,abs_pow,abs_of_nonneg (by positivity : 0≤(1/2:ℝ)^b),abs_of_nonneg hp]
    have HH := mul_le_mul_of_nonneg_left hAvg (by positivity : 0≤|r|^a*(1/2:ℝ)^b*(p:ℝ))
    convert HH using 1 <;> ring
  unfold scalarCoefBJet
  apply (abs_sub _ _).trans
  by_cases hz : a+b=0
  · simp only [hz,ite_true,abs_of_nonneg hp]
    nlinarith
  · simp only [hz,ite_false,abs_zero,add_zero]
    nlinarith

end
end SparseSGD.Logistic
