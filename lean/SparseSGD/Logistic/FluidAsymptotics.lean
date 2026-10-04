import SparseSGD.Logistic.FluidDimensionRate
import SparseSGD.Scaling.IntegerFamilies

open Filter Topology
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

/-- The fluctuation rate appearing in the finite-horizon theorem vanishes. -/
theorem fluid_sqrt_log_dimension_tendsto :
    Tendsto (fun d : ℕ => Real.sqrt (Real.log d/(d : ℝ))) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simpa only [Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp (h.comp tendsto_natCast_atTop_atTop)

/-- Once N*Gamma*L2 has a uniform bound, the nonlinear bootstrap conditions
hold eventually for every fixed positive tube radius. -/
theorem fluid_sqrt_rate_eventual_bootstrap (C D radius : ℝ) (hradius : 0 < radius) :
    ∀ᶠ d : ℕ in atTop,
      C*Real.sqrt (Real.log d/(d : ℝ)) ≤ radius ∧
      D*(C*Real.sqrt (Real.log d/(d : ℝ))) ≤ 1 := by
  have h : Tendsto (fun d : ℕ => C*Real.sqrt (Real.log d/(d : ℝ))) atTop (𝓝 0) := by
    simpa using fluid_sqrt_log_dimension_tendsto.const_mul C
  have h' := h.const_mul D
  simp only [mul_zero] at h'
  filter_upwards [h.eventually (gt_mem_nhds hradius),h'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))] with d hd hd'
  exact ⟨hd.le,hd'.le⟩

/-- Power-law learning rates absorb the Bernstein correction if their growth
exponent is strictly below one half. This is the source proof's additional
eta=o(sqrt(d/log d)) condition. -/
theorem fluid_power_learning_absorption (etaStar alpha : ℝ)
    (heta : 0 ≤ etaStar) (halpha : -(1/2 : ℝ) < alpha) :
    Tendsto (fun d : ℕ => (etaStar*(d : ℝ)^(-alpha))*
      Real.sqrt (Real.log d/(d : ℝ))) atTop (𝓝 0) := by
  have hpow : 0 < 2*alpha+1 := by linarith
  have hlog : Tendsto (fun x : ℝ => Real.log x / x^(2*alpha+1)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hpow).tendsto_div_nhds_zero
  have h := (hlog.comp tendsto_natCast_atTop_atTop).const_mul (etaStar^2)
  have hs := (Real.continuous_sqrt.tendsto 0).comp (by simpa using h)
  simp only [Real.sqrt_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with d hd
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hld : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have hid : etaStar^2*(Real.log d/(d : ℝ)^(2*alpha+1)) =
      (etaStar*(d : ℝ)^(-alpha))^2*(Real.log d/(d : ℝ)) := by
    rw [mul_pow,← Real.rpow_mul_natCast hdpos.le]
    rw [show -alpha*(2 : ℕ) = -(2*alpha) by push_cast; ring]
    rw [Real.rpow_neg hdpos.le,Real.rpow_add hdpos,Real.rpow_one]
    field_simp
  dsimp only [Function.comp_def]
  rw [hid,Real.sqrt_mul (by positivity),Real.sqrt_sq (by positivity)]

end
end SparseSGD.Logistic
