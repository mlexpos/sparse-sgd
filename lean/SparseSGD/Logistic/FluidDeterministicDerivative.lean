import SparseSGD.Logistic.FluidDeterministicStateTaylor
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

/-- A local quadratic Taylor bound yields the actual derivative within an
arbitrary physical domain. No ambient extension is required. -/
theorem hasFDerivWithinAt_of_local_quadratic_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E→F) (D : E →L[ℝ] F) (s : Set E) (x : E) (L radius : ℝ)
    (hL : 0≤L) (hradius : 0<radius)
    (hbound : ∀ y∈s, ‖y-x‖≤radius → ‖f y-f x-D (y-x)‖≤L*‖y-x‖^2) :
    HasFDerivWithinAt f D s x := by
  rw [hasFDerivWithinAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro c hc
  have hevent : ∀ᶠ y in nhdsWithin x s, dist y x < min radius (c/(L+1)) :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds x (by positivity : 0 < min radius (c/(L+1))))
  filter_upwards [hevent,self_mem_nhdsWithin] with y hy hys
  rw [dist_eq_norm] at hy
  have hyR : ‖y-x‖≤radius := (hy.trans_le (min_le_left _ _)).le
  have hyc : ‖y-x‖≤c/(L+1) := (hy.trans_le (min_le_right _ _)).le
  have H : L*‖y-x‖≤c := by
    have HH := (le_div_iff₀ (by linarith : 0<L+1)).mp hyc
    nlinarith [norm_nonneg (y-x)]
  apply (hbound y hys hyR).trans
  have HH := mul_le_mul_of_nonneg_right H (norm_nonneg (y-x))
  nlinarith
end
end SparseSGD.Logistic
