import SparseSGD.Comparison.QuadratureBound
import SparseSGD.Comparison.RiemannBound

namespace SparseSGD
noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def exponentialModeSum (rates coeff : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ i, coeff i*Complex.exp (rates i*(t : ℂ))

theorem exponentialModeSum_continuous (rates coeff : ι → ℂ) :
    Continuous (exponentialModeSum rates coeff) := by
  unfold exponentialModeSum
  fun_prop

theorem sampledModeConvolution_eq_pairs (mu b : ι → ℂ) (lambda c : κ → ℂ)
    (h : ℝ) (k : ℕ) :
    rightEndpointSum (fun x => exponentialModeSum mu b x*
      exponentialModeSum lambda c ((k : ℝ)*h-x)) h k =
      ∑ i, ∑ j, b i*c j*sampledPairSum (mu i) (lambda j) (h : ℂ) k := by
  unfold rightEndpointSum exponentialModeSum sampledPairSum
  simp only [Complex.real_smul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro n hn
  have hnlt : n < k := Finset.mem_range.mp hn
  have hcast : ((k : ℝ)*h-((n+1 : ℕ) : ℝ)*h : ℝ) = ((k-n-1 : ℕ) : ℝ)*h := by
    have H : (k : ℝ) = ((n+1 : ℕ) : ℝ)+((k-n-1 : ℕ) : ℝ) := by
      exact_mod_cast (show k = (n+1)+(k-n-1) by omega)
    rw [H]
    ring
  rw [hcast]
  push_cast
  ring

theorem modeConvolution_eq_pairs (mu b : ι → ℂ) (lambda c : κ → ℂ) (T : ℝ) :
    (∫ x in (0 : ℝ)..T, exponentialModeSum mu b x*
      exponentialModeSum lambda c (T-x)) =
      ∑ i, ∑ j, b i*c j*pairIntegral (mu i) (lambda j) T := by
  unfold exponentialModeSum
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      have heq : (fun x : ℝ => b i*Complex.exp (mu i*(x : ℂ))*
          (c j*Complex.exp (lambda j*((T-x : ℝ) : ℂ)))) =
          (fun x : ℝ => (b i*c j)*(Complex.exp (mu i*(x : ℂ))*
            Complex.exp (lambda j*((T-x : ℝ) : ℂ)))) := by funext x; ring
      rw [heq,intervalIntegral.integral_const_mul]
      rfl
    · intro j _
      exact (by fun_prop : Continuous (fun x : ℝ => b i*Complex.exp (mu i*(x : ℂ))*
        (c j*Complex.exp (lambda j*((T-x : ℝ) : ℂ))))).intervalIntegrable 0 T
  · intro i _
    exact (by fun_prop : Continuous (fun x : ℝ => ∑ j, b i*Complex.exp (mu i*(x : ℂ))*
      (c j*Complex.exp (lambda j*((T-x : ℝ) : ℂ))))).intervalIntegrable 0 T

/-- Finite mode quadrature incurs only the coefficient masses, uniformly in all
frequencies; the hypotheses are the explicit relative-phase strip. -/
theorem modal_convolution_quadrature_bound (margin : ℝ) (hm : 0 < margin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu b : ι → ℂ) (lambda c : κ → ℂ) (h : ℝ) (k : ℕ),
      0 < h → (∀ i, (mu i).re ≤ 0) → (∀ j, (lambda j).re ≤ 0) →
      (∀ i j, |((lambda j-mu i)*(h : ℂ)).re| ≤ 3) →
      (∀ i j, |((lambda j-mu i)*(h : ℂ)).im| ≤ 2*Real.pi-margin) →
      ‖rightEndpointSum (fun x => exponentialModeSum mu b x*
          exponentialModeSum lambda c ((k : ℝ)*h-x)) h k -
        (∫ x in (0 : ℝ)..(k : ℝ)*h, exponentialModeSum mu b x*
          exponentialModeSum lambda c ((k : ℝ)*h-x))‖ ≤
        2*C*h*(∑ i, ‖b i‖)*(∑ j, ‖c j‖) := by
  obtain ⟨C,hC0,hC⟩ := exponential_pair_quadrature_bound_stable margin hm
  refine ⟨C,hC0,?_⟩
  intro mu b lambda c h k hh hmu hlam hre him
  rw [sampledModeConvolution_eq_pairs,modeConvolution_eq_pairs,← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib,← mul_sub]
  calc
    _ ≤ ∑ i, ∑ j, ‖b i*c j*(sampledPairSum (mu i) (lambda j) (h : ℂ) k-
        pairIntegral (mu i) (lambda j) ((k : ℝ)*h))‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, ‖b i‖*‖c j‖*(2*C*h) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _ _ h k (hmu i) (hlam j) hh (hre i j) (him i j))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      simp_rw [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring


theorem real_modal_convolution_error_eq (q f : ℝ → ℝ) (mu b : ι → ℂ) (lambda c : κ → ℂ)
    (hq : ∀ t, 0 ≤ t → (q t : ℂ) = exponentialModeSum mu b t)
    (hf : ∀ t, 0 ≤ t → (f t : ℂ) = exponentialModeSum lambda c t)
    (h : ℝ) (hh : 0 < h) (k : ℕ) :
    |rightEndpointSum (fun x => q x*f ((k : ℝ)*h-x)) h k-
      (∫ x in (0 : ℝ)..(k : ℝ)*h, q x*f ((k : ℝ)*h-x))| =
      ‖rightEndpointSum (fun x => exponentialModeSum mu b x*
          exponentialModeSum lambda c ((k : ℝ)*h-x)) h k-
        (∫ x in (0 : ℝ)..(k : ℝ)*h, exponentialModeSum mu b x*
          exponentialModeSum lambda c ((k : ℝ)*h-x))‖ := by
  have hT : 0 ≤ (k : ℝ)*h := by positivity
  have hsum : rightEndpointSum (fun x => exponentialModeSum mu b x*
      exponentialModeSum lambda c ((k : ℝ)*h-x)) h k =
      ((rightEndpointSum (fun x => q x*f ((k : ℝ)*h-x)) h k : ℝ) : ℂ) := by
    unfold rightEndpointSum
    push_cast
    apply Finset.sum_congr rfl
    intro n hn
    have hnlt := Finset.mem_range.mp hn
    have hnk : ((n+1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show n+1 ≤ k by omega)
    have hx : 0 ≤ ((n+1 : ℕ) : ℝ)*h := by positivity
    have htx : 0 ≤ (k : ℝ)*h-((n+1 : ℕ) : ℝ)*h := by
      nlinarith [mul_le_mul_of_nonneg_right hnk hh.le]
    simp only [Nat.cast_add,Nat.cast_one] at hx htx
    rw [← hq _ hx,← hf _ htx]
    simp [Complex.real_smul]
  have hint : (∫ x in (0 : ℝ)..(k : ℝ)*h, exponentialModeSum mu b x*
      exponentialModeSum lambda c ((k : ℝ)*h-x)) =
      (((∫ x in (0 : ℝ)..(k : ℝ)*h, q x*f ((k : ℝ)*h-x)) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    dsimp only
    rw [← hq _ hx.1,← hf _ (by linarith [hx.2])]
    simp
  rw [hsum,hint]
  simp only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]


theorem complex_modal_convolution_error_eq (q f : ℝ → ℂ) (mu b : ι → ℂ) (lambda c : κ → ℂ)
    (hq : ∀ t, 0 ≤ t → q t = exponentialModeSum mu b t)
    (hf : ∀ t, 0 ≤ t → f t = exponentialModeSum lambda c t)
    (h : ℝ) (hh : 0 < h) (k : ℕ) :
    ‖rightEndpointSum (fun x => q x*f ((k : ℝ)*h-x)) h k-
      (∫ x in (0 : ℝ)..(k : ℝ)*h, q x*f ((k : ℝ)*h-x))‖ =
      ‖rightEndpointSum (fun x => exponentialModeSum mu b x*
          exponentialModeSum lambda c ((k : ℝ)*h-x)) h k-
        (∫ x in (0 : ℝ)..(k : ℝ)*h, exponentialModeSum mu b x*
          exponentialModeSum lambda c ((k : ℝ)*h-x))‖ := by
  have hT : 0 ≤ (k : ℝ)*h := by positivity
  have hsum : rightEndpointSum (fun x => q x*f ((k : ℝ)*h-x)) h k =
      rightEndpointSum (fun x => exponentialModeSum mu b x*
        exponentialModeSum lambda c ((k : ℝ)*h-x)) h k := by
    unfold rightEndpointSum
    apply Finset.sum_congr rfl
    intro n hn
    have hnk : ((n+1 : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (show n+1 ≤ k by have := Finset.mem_range.mp hn; omega)
    dsimp only
    rw [hq _ (by positivity),hf _ (by nlinarith [mul_le_mul_of_nonneg_right hnk hh.le])]
  have hint : (∫ x in (0 : ℝ)..(k : ℝ)*h, q x*f ((k : ℝ)*h-x)) =
      ∫ x in (0 : ℝ)..(k : ℝ)*h, exponentialModeSum mu b x*
        exponentialModeSum lambda c ((k : ℝ)*h-x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    dsimp only
    rw [hq _ hx.1,hf _ (by linarith [hx.2])]
  rw [hsum,hint]

end
end SparseSGD
