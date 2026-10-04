import SparseSGD.Logistic.FluidClock
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

/-- Polynomially many observations at confidence 1-d^(-10) cost only log d. -/
theorem fluid_polynomial_log_confidence (d N : ℕ) (q : ℝ)
    (hd : 2 ≤ d) (hN : 0 < N) (hpoly : (N : ℝ) ≤ (d : ℝ)^q) :
    Real.log (10*(N : ℝ)/((d : ℝ)^10)⁻¹) ≤ (q+14)*Real.log d := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hnp : (0 : ℝ) < N := by exact_mod_cast hN
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h10 : (10 : ℝ) ≤ (d : ℝ)^4 := by nlinarith [sq_nonneg ((d : ℝ)^2-4)]
  have hl10 := Real.log_le_log (by norm_num : (0 : ℝ)<10) h10
  rw [Real.log_pow] at hl10
  have hlN := Real.log_le_log hnp hpoly
  rw [Real.log_rpow hdp] at hlN
  rw [div_inv_eq_mul,Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (ne_of_gt hnp),Real.log_pow]
  norm_num at hl10 ⊢
  nlinarith

/-- The dimension-dependent failure probability used in the source is valid. -/
theorem fluid_dimension_confidence (d : ℕ) (hd : 2 ≤ d) :
    0 < ((d : ℝ)^10)⁻¹ ∧ ((d : ℝ)^10)⁻¹ < 1 := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hp : (1 : ℝ) < (d : ℝ)^10 := one_lt_pow₀ hdR (by norm_num)
  constructor
  · positivity
  · exact inv_lt_one_of_one_lt₀ hp

/-- Absorption of the linear Bernstein term with an explicit finite step-size
condition. Constants vC,mC are dimension-independent variance/scale factors. -/
theorem fluid_radius_sqrt_dimension_bound (d N : ℕ) (q vC mC eta a Gamma v M : ℝ)
    (hd : 2 ≤ d) (hN : 0 < N) (hpoly : (N : ℝ) ≤ (d : ℝ)^q)
    (hq : 0 ≤ q+14) (hvC : 0 ≤ vC) (hmC : 0 ≤ mC) (heta : 0 ≤ eta)
    (hGamma : 0 ≤ Gamma) (hv : (N : ℝ)*v ≤ vC/(d : ℝ))
    (hM : M ≤ mC*(1+eta)/(d : ℝ))
    (hetaSize : eta*Real.sqrt (Real.log d/(d : ℝ)) ≤ a) :
    2*Gamma*(Real.sqrt (2*N*v*Real.log (10*(N : ℝ)/((d : ℝ)^10)⁻¹))+
      2*M*Real.log (10*(N : ℝ)/((d : ℝ)^10)⁻¹)) ≤
      2*Gamma*(Real.sqrt (2*vC*(q+14))+2*mC*(q+14)*(1+a))*
        Real.sqrt (Real.log d/(d : ℝ)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hld : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have hconf := fluid_dimension_confidence d hd
  have hellpos := (fluid_log_confidence (by norm_num : 0<5) hN hconf.1 hconf.2).1
  have hell : 0 ≤ Real.log (10*(N : ℝ)/((d : ℝ)^10)⁻¹) := by
    simpa only [Nat.cast_ofNat,show (2 : ℝ)*5=10 by norm_num] using hellpos.le
  have hlog := fluid_polynomial_log_confidence d N q hd hN hpoly
  let s := Real.sqrt (Real.log d/(d : ℝ))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2 = Real.log d/(d : ℝ) := Real.sq_sqrt (by positivity)
  have hs1 : s ≤ 1 := by
    have hlogd := Real.log_le_self hdpos.le
    have hr : Real.log d/(d : ℝ) ≤ 1 := (div_le_one hdpos).2 hlogd
    nlinarith
  have hsvar : Real.sqrt (2*N*v*Real.log (10*(N : ℝ)/((d : ℝ)^10)⁻¹)) ≤
      Real.sqrt (2*vC*(q+14))*s := by
    calc
      _ ≤ Real.sqrt ((2*vC*(q+14))*(Real.log d/(d : ℝ))) := by
        apply Real.sqrt_le_sqrt
        have hh := mul_le_mul hv hlog hell (by positivity : 0 ≤ vC/(d : ℝ))
        convert mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ)≤2) using 1 <;> ring
      _ = _ := Real.sqrt_mul (by positivity) _
  have hsm : 2*M*Real.log (10*(N : ℝ)/((d : ℝ)^10)⁻¹) ≤
      2*mC*(q+14)*(1+a)*s := by
    have hh := mul_le_mul hM hlog hell (by positivity : 0 ≤ mC*(1+eta)/(d : ℝ))
    have ha : (1+eta)*s ≤ 1+a := by dsimp [s] at *; nlinarith
    have hb := mul_le_mul_of_nonneg_right ha hs0
    rw [mul_assoc,← pow_two] at hb
    have hc := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*mC*(q+14) by positivity)
    rw [hs2] at hc
    calc
      _ ≤ 2*(mC*(1+eta)/(d : ℝ)*((q+14)*Real.log d)) := by
        convert mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
      _ ≤ _ := by convert hc using 1 <;> ring
  have hh := mul_le_mul_of_nonneg_left (add_le_add hsvar hsm) (show 0 ≤ 2*Gamma by positivity)
  convert hh using 1 <;> ring

end
end SparseSGD.Logistic
