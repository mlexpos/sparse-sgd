import SparseSGD.Logistic.GaussianSigmoid
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace SparseSGD.Logistic
noncomputable section
open Polynomial
set_option maxHeartbeats 1000000

/-- Polynomial remainders in `D^n σ = σ + σ² Qₙ(σ)`. -/
def sigmoidRemainderPoly : ℕ → Polynomial ℝ
  | 0 => 0
  | n+1 => -1 + 2*(1-X)*sigmoidRemainderPoly n +
      X*(1-X)*(sigmoidRemainderPoly n).derivative

def sigmaDerivative (n : ℕ) (t : ℝ) : ℝ :=
  sigma t + sigma t^2*(sigmoidRemainderPoly n).eval (sigma t)

/-- Polynomial factors in `D^n(σ²) = σ² Rₙ(σ)`. -/
def sigmoidSquarePoly : ℕ → Polynomial ℝ
  | 0 => 1
  | n+1 => (1-X)*(2*sigmoidSquarePoly n + X*(sigmoidSquarePoly n).derivative)

def sigmaSquareDerivative (n : ℕ) (t : ℝ) : ℝ :=
  sigma t^2*(sigmoidSquarePoly n).eval (sigma t)

def oneMinusSigmaSquareDerivative (n : ℕ) (t : ℝ) : ℝ :=
  (if n=0 then 1 else 0) - 2*sigmaDerivative n t + sigmaSquareDerivative n t

@[simp] theorem sigmaDerivative_zero (t : ℝ) : sigmaDerivative 0 t = sigma t := by
  simp [sigmaDerivative, sigmoidRemainderPoly]
@[simp] theorem sigmaSquareDerivative_zero (t : ℝ) : sigmaSquareDerivative 0 t = sigma t^2 := by
  simp [sigmaSquareDerivative, sigmoidSquarePoly]
@[simp] theorem oneMinusSigmaSquareDerivative_zero (t : ℝ) :
    oneMinusSigmaSquareDerivative 0 t = (1-sigma t)^2 := by
  simp [oneMinusSigmaSquareDerivative]
  ring

@[fun_prop] theorem sigmaDerivative_continuous (n : ℕ) : Continuous (sigmaDerivative n) := by
  unfold sigmaDerivative
  fun_prop
@[fun_prop] theorem sigmaSquareDerivative_continuous (n : ℕ) : Continuous (sigmaSquareDerivative n) := by
  unfold sigmaSquareDerivative
  fun_prop
@[fun_prop] theorem oneMinusSigmaSquareDerivative_continuous (n : ℕ) :
    Continuous (oneMinusSigmaSquareDerivative n) := by
  unfold oneMinusSigmaSquareDerivative
  fun_prop

theorem hasDerivAt_sigmaDerivative (n : ℕ) (t : ℝ) :
    HasDerivAt (sigmaDerivative n) (sigmaDerivative (n+1) t) t := by
  have h := (hasDerivAt_sigma t).add (((hasDerivAt_sigma t).pow 2).mul
    (((sigmoidRemainderPoly n).hasDerivAt (sigma t)).comp t (hasDerivAt_sigma t)))
  convert h using 1
  · rfl
  · simp only [sigmaDerivative, sigmoidRemainderPoly, eval_add, eval_mul, eval_neg,
      eval_one, eval_ofNat, eval_sub, eval_X, sigmaPrime, Pi.pow_apply, Function.comp_apply]
    ring

theorem hasDerivAt_sigmaSquareDerivative (n : ℕ) (t : ℝ) :
    HasDerivAt (sigmaSquareDerivative n) (sigmaSquareDerivative (n+1) t) t := by
  have h := ((hasDerivAt_sigma t).pow 2).mul
    (((sigmoidSquarePoly n).hasDerivAt (sigma t)).comp t (hasDerivAt_sigma t))
  convert h using 1
  · rfl
  · simp only [sigmaSquareDerivative, sigmoidSquarePoly, eval_add, eval_mul,
      eval_one, eval_ofNat, eval_sub, eval_X, sigmaPrime, Pi.pow_apply, Function.comp_apply]
    ring

theorem hasDerivAt_oneMinusSigmaSquareDerivative (n : ℕ) (t : ℝ) :
    HasDerivAt (oneMinusSigmaSquareDerivative n) (oneMinusSigmaSquareDerivative (n+1) t) t := by
  have h := ((hasDerivAt_const t (if n=0 then (1 : ℝ) else 0)).sub
    ((hasDerivAt_sigmaDerivative n t).const_mul 2)).add (hasDerivAt_sigmaSquareDerivative n t)
  convert h using 1
  · rfl
  · simp only [oneMinusSigmaSquareDerivative, Nat.add_one_ne_zero, if_false, zero_sub]

@[simp] theorem sigmaDerivative_one (t : ℝ) : sigmaDerivative 1 t = sigmaPrime t := by
  simp [sigmaDerivative, sigmoidRemainderPoly, sigmaPrime]
  ring
@[simp] theorem sigmaDerivative_two (t : ℝ) : sigmaDerivative 2 t = sigmaSecond t := by
  have h := hasDerivAt_sigmaDerivative 1 t
  rw [show sigmaDerivative 1 = sigmaPrime by funext x; simp] at h
  exact h.unique (hasDerivAt_sigmaPrime t)
@[simp] theorem sigmaSquareDerivative_two (t : ℝ) : sigmaSquareDerivative 2 t = sigmaSqSecond t := by
  simp [sigmaSquareDerivative, sigmoidSquarePoly, sigmaSqSecond, sigmaSecond, sigmaPrime]
  ring
@[simp] theorem oneMinusSigmaSquareDerivative_two (t : ℝ) :
    oneMinusSigmaSquareDerivative 2 t = oneMinusSigmaSqSecond t := by
  simp [oneMinusSigmaSquareDerivative, oneMinusSigmaSqSecond, sigmaSqSecond]
  ring

theorem polynomial_sigma_bounded (P : Polynomial ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |P.eval (sigma t)| ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    P.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  have h : |P.eval (sigma t)| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (sigma t) ⟨(sigma_pos t).le,(sigma_lt_one t).le⟩
  exact h.trans (le_max_left _ _)

theorem sigma_exp_error (t : ℝ) : |sigma t-Real.exp t| ≤ Real.exp (2*t) := by
  have he := sigma_le_exp t
  have h0 := (sigma_pos t).le
  rw [abs_of_nonpos (sub_nonpos.mpr he)]
  have hi : Real.exp t-sigma t = sigma t*Real.exp t := by
    unfold sigma
    field_simp
    ring
  rw [neg_sub, hi, two_mul, Real.exp_add]
  exact mul_le_mul_of_nonneg_right he (Real.exp_pos t).le

/-- Constants depend only on the derivative order, never on the logit. -/
theorem sigmaDerivative_bounds (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ,
      |sigmaDerivative n t| ≤ C ∧
      |sigmaDerivative n t| ≤ C*Real.exp t ∧
      |sigmaDerivative n t-Real.exp t| ≤ C*Real.exp (2*t) := by
  obtain ⟨B,hB,hP⟩ := polynomial_sigma_bounded (sigmoidRemainderPoly n)
  refine ⟨1+B, by linarith, fun t => ?_⟩
  have hs0 := (sigma_pos t).le
  have hs1 := (sigma_lt_one t).le
  have hsq : sigma t^2 ≤ sigma t := by nlinarith
  have hprod : |sigma t^2*(sigmoidRemainderPoly n).eval (sigma t)| ≤ sigma t^2*B := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hP t) (sq_nonneg _)
  have ha : |sigmaDerivative n t| ≤ (1+B)*sigma t := by
    unfold sigmaDerivative
    calc
      _ ≤ |sigma t|+|sigma t^2*(sigmoidRemainderPoly n).eval (sigma t)| := abs_add_le _ _
      _ ≤ sigma t+sigma t^2*B := by simpa only [abs_of_nonneg hs0] using add_le_add_right hprod |sigma t|
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hsq hB]
  refine ⟨ha.trans ?_, ha.trans ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hs1 (show 0≤1+B by linarith)]
  · exact mul_le_mul_of_nonneg_left (sigma_le_exp t) (by linarith)
  · have heq : sigmaDerivative n t-Real.exp t =
        (sigma t-Real.exp t)+sigma t^2*(sigmoidRemainderPoly n).eval (sigma t) := by unfold sigmaDerivative; ring
    rw [heq]
    calc
      _ ≤ |sigma t-Real.exp t|+|sigma t^2*(sigmoidRemainderPoly n).eval (sigma t)| := abs_add_le _ _
      _ ≤ Real.exp (2*t)+sigma t^2*B := add_le_add (sigma_exp_error t) hprod
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (sigma_sq_le_exp t) hB]

theorem sigmaSquareDerivative_bounds (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      |sigmaSquareDerivative n t| ≤ C ∧
      |sigmaSquareDerivative n t| ≤ C*Real.exp (2*t) := by
  obtain ⟨C,hC,hP⟩ := polynomial_sigma_bounded (sigmoidSquarePoly n)
  refine ⟨C,hC, fun t => ?_⟩
  have h : |sigmaSquareDerivative n t| ≤ sigma t^2*C := by
    unfold sigmaSquareDerivative
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hP t) (sq_nonneg _)
  constructor
  · have hs : sigma t^2 ≤ 1 := by nlinarith [sigma_pos t, sigma_lt_one t]
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right hs hC])
  · exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right (sigma_sq_le_exp t) hC])

theorem sigmaSquareDerivative_exp_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |sigmaSquareDerivative n t| ≤ C*Real.exp t := by
  obtain ⟨C,hC,hP⟩ := polynomial_sigma_bounded (sigmoidSquarePoly n)
  refine ⟨C,hC, fun t => ?_⟩
  have hs : sigma t^2 ≤ sigma t := by nlinarith [sigma_pos t, sigma_lt_one t]
  unfold sigmaSquareDerivative
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ sigma t^2*C := mul_le_mul_of_nonneg_left (hP t) (sq_nonneg _)
    _ ≤ sigma t*C := mul_le_mul_of_nonneg_right hs hC
    _ ≤ C*Real.exp t := by nlinarith [mul_le_mul_of_nonneg_right (sigma_le_exp t) hC]

theorem oneMinusSigmaSquareDerivative_bounded (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |oneMinusSigmaSquareDerivative n t| ≤ C := by
  obtain ⟨A,hA,hsa⟩ := sigmaDerivative_bounds n
  obtain ⟨B,hB,hsb⟩ := sigmaSquareDerivative_bounds n
  refine ⟨1+2*A+B, by linarith, fun t => ?_⟩
  have hc : |(if n=0 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
  unfold oneMinusSigmaSquareDerivative
  calc
    _ ≤ |(if n=0 then (1 : ℝ) else 0)-2*sigmaDerivative n t| + |sigmaSquareDerivative n t| := abs_add_le _ _
    _ ≤ |(if n=0 then (1 : ℝ) else 0)|+|2*sigmaDerivative n t|+|sigmaSquareDerivative n t| := by linarith [abs_sub (if n=0 then (1 : ℝ) else 0) (2*sigmaDerivative n t)]
    _ ≤ _ := by rw [abs_mul]; norm_num; linarith [(hsa t).1,(hsb t).1]

theorem oneMinusSigmaSquareDerivative_exp_bound (n : ℕ) (hn : n ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |oneMinusSigmaSquareDerivative n t| ≤ C*Real.exp t := by
  obtain ⟨A,hA,hsa⟩ := sigmaDerivative_bounds n
  obtain ⟨B,hB,hsb⟩ := sigmaSquareDerivative_exp_bound n
  refine ⟨2*A+B, by linarith, fun t => ?_⟩
  simp only [oneMinusSigmaSquareDerivative, hn, if_false, zero_sub]
  calc
    _ ≤ |-(2*sigmaDerivative n t)|+|sigmaSquareDerivative n t| := abs_add_le _ _
    _ ≤ _ := by rw [abs_neg,abs_mul]; norm_num; nlinarith [(hsa t).2.1,hsb t]

end
end SparseSGD.Logistic
