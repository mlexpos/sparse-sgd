import SparseSGD.Logistic.StoppedFluid
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1500000

def matchedFreeLinear (beta : ℝ) : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun y := ![y 0-(1-beta)*beta*y 1,beta*y 1,
    y 2-2*beta*(1-beta)*y 3+beta^2*(1-beta)^2*y 4,
    beta*y 3-beta^2*(1-beta)*y 4,beta^2*y 4]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c y := by ext i; fin_cases i <;> simp <;> ring

def matchedFreeOperator (beta : ℝ) : (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ) :=
  (matchedFreeLinear beta).toContinuousLinearMap

theorem matchedFreeOperator_apply (beta : ℝ) (y : Fin 5 → ℝ) :
    matchedFreeOperator beta y = ![y 0-(1-beta)*beta*y 1,beta*y 1,
      y 2-2*beta*(1-beta)*y 3+beta^2*(1-beta)^2*y 4,
      beta*y 3-beta^2*(1-beta)*y 4,beta^2*y 4] := rfl

/-- Exact powers of the zero-gradient fast block, in the source matched order. -/
theorem matchedFreeOperator_pow_apply (beta : ℝ) (n : ℕ) (y : Fin 5 → ℝ) :
    ((matchedFreeOperator beta)^n) y =
      ![y 0-beta*(1-beta^n)*y 1,beta^n*y 1,
        y 2-2*beta*(1-beta^n)*y 3+beta^2*(1-beta^n)^2*y 4,
        beta^n*y 3-beta^(n+1)*(1-beta^n)*y 4,(beta^n)^2*y 4] := by
  induction n with
  | zero => ext i; fin_cases i <;> simp
  | succ n ih =>
    rw [pow_succ',ContinuousLinearMap.mul_apply,ih,matchedFreeOperator_apply]
    ext i
    fin_cases i <;> simp [pow_succ] <;> ring

/-- All powers have a uniform sup-norm bound, independent of the retention
step. This includes the cold fast layer and needs no moving eigenbasis. -/
theorem matchedFreeOperator_pow_norm_le_four (beta : ℝ) (hb0 : 0≤beta) (hb1 : beta≤1) (n : ℕ) :
    ‖(matchedFreeOperator beta)^n‖≤4 := by
  have hpow : 0≤beta^n := pow_nonneg hb0 n
  have hpow1 : beta^n≤1 := pow_le_one₀ hb0 hb1
  have hg : 0≤beta*(1-beta^n) := mul_nonneg hb0 (by linarith)
  have hg1 : beta*(1-beta^n)≤1 := (mul_le_mul hb1 (show 1-beta^n≤1 by linarith)
    (by linarith) (by norm_num)).trans (by norm_num)
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  have hcoords (i : Fin 5) : |y i|≤‖y‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i
  have hy : 0≤‖y‖ := norm_nonneg y
  rw [matchedFreeOperator_pow_apply]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤4*‖y‖)).mpr
  intro i
  have h1 : |y 0-beta*(1-beta^n)*y 1|≤2*‖y‖ := by
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg hg]
    nlinarith only [hcoords 0,hcoords 1,mul_le_mul hg1 (hcoords 1) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)]
  have h2 : |y 2-2*beta*(1-beta^n)*y 3+beta^2*(1-beta^n)^2*y 4|≤4*‖y‖ := by
    have he : beta^2*(1-beta^n)^2=(beta*(1-beta^n))^2 := by ring
    rw [he]
    have hsq : (beta*(1-beta^n))^2≤1 := by nlinarith
    have hA := abs_add_le (y 2-2*beta*(1-beta^n)*y 3) ((beta*(1-beta^n))^2*y 4)
    have hB := abs_sub (y 2) (2*beta*(1-beta^n)*y 3)
    rw [abs_mul,abs_of_nonneg (by nlinarith [hg] : 0≤2*beta*(1-beta^n))] at hB
    have hterm : |(beta*(1-beta^n))^2*y 4|=(beta*(1-beta^n))^2*|y 4| := by rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    rw [hterm] at hA
    have hc3 := mul_le_mul_of_nonneg_right hg1 (abs_nonneg (y 3))
    have hc4 := mul_le_mul_of_nonneg_right hsq (abs_nonneg (y 4))
    nlinarith only [hA,hB,hc3,hc4,hcoords 2,hcoords 3,hcoords 4]
  have h3 : |beta^n*y 3-beta^(n+1)*(1-beta^n)*y 4|≤2*‖y‖ := by
    have he : beta^(n+1)*(1-beta^n)=beta^n*(beta*(1-beta^n)) := by rw [pow_succ]; ring
    rw [he]
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg hpow,abs_mul,abs_mul,abs_of_nonneg hpow,abs_of_nonneg hg]
    have hleft := mul_le_mul_of_nonneg_right hpow1 (abs_nonneg (y 3))
    have hprod : beta^n*(beta*(1-beta^n))≤1 := (mul_le_mul hpow1 hg1 hg (by norm_num : (0:ℝ)≤1)).trans (by norm_num)
    have hright := mul_le_mul_of_nonneg_right hprod (abs_nonneg (y 4))
    nlinarith only [hleft,hright,hcoords 3,hcoords 4]
  fin_cases i
  · simp [Real.norm_eq_abs]; linarith
  · simp [Real.norm_eq_abs,abs_mul,abs_of_nonneg hb0,abs_of_nonneg hpow]
    have H := mul_le_mul_of_nonneg_right hpow1 (abs_nonneg (y 1))
    nlinarith only [H,hcoords 1,hy]
  · simpa [Real.norm_eq_abs] using h2
  · simp [Real.norm_eq_abs]; linarith
  · simp [Real.norm_eq_abs,abs_mul,abs_of_nonneg hb0,abs_of_nonneg (sq_nonneg (beta^n))]
    have hs : (beta^n)^2≤1 := by nlinarith
    have H := mul_le_mul_of_nonneg_right hs (abs_nonneg (y 4))
    nlinarith only [H,hcoords 4,hy]
end
end SparseSGD.Logistic
