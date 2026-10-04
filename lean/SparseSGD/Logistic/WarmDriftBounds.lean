import SparseSGD.Logistic.IncrementFluidMapBounds

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

/-- The nonlinear part of the actual matched map is uniformly Lipschitz of
order eta*p on physical bounded states. The free fast block is kept exact. -/
theorem matchedDriftMap_uniform_free_lipschitz
    (S : SparseSGD.External.GaussianSteinCertificate 1) (teacherNorm R P : ℝ)
    (hR : 0 ≤ R) (hP : 0 ≤ P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d),
      r mu=teacherNorm → 0 ≤ eta → 0 < (p : ℝ) → (p : ℝ) ≤ 1/2 →
      ‖matchedDimensionlessParameters (B := B) eta beta p mu‖ ≤ P →
      ∀ x y : MatchedCoordinate, matchedPhysical x → matchedPhysical y → ‖x‖ ≤ R → ‖y‖ ≤ R →
        ‖matchedDriftMap (B := B) eta beta p mu x-matchedDriftMap (B := B) eta beta p mu y-
          matchedFreeOperator beta (x-y)‖ ≤ C*(eta*(p : ℝ))*‖x-y‖ := by
  obtain ⟨C,hC,hctrl⟩ := matchedPopulationJacobian_uniform_controls S teacherNorm R P hR hP
  refine ⟨C*(1+2*R),by positivity,?_⟩
  intro d B eta beta p mu hr heta hp hpHalf hpar x y hx hy hxn hyn
  have hz : 0 ≤ eta*(p : ℝ) := mul_nonneg heta hp.le
  have hh := hctrl eta beta p mu hr heta hp hpHalf hpar
  have hJ := hh.1 y hy hyn
  have hrem := hh.2 x y hx hy hxn hyn
  have hd : ‖x-y‖ ≤ 2*R := (norm_sub_le x y).trans (by linarith)
  have heq : matchedDriftMap (B := B) eta beta p mu x-matchedDriftMap (B := B) eta beta p mu y-
      matchedFreeOperator beta (x-y) =
      (matchedDriftMap (B := B) eta beta p mu x-matchedDriftMap (B := B) eta beta p mu y-
        matchedPopulationJacobian (B := B) eta beta p mu y (x-y))+
      (matchedPopulationJacobian (B := B) eta beta p mu y-matchedFreeOperator beta) (x-y) := by
    simp only [ContinuousLinearMap.sub_apply]
    module
  rw [heq]
  apply (norm_add_le _ _).trans
  have hjapp := ((matchedPopulationJacobian (B := B) eta beta p mu y-matchedFreeOperator beta).le_opNorm (x-y)).trans
    (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
  have hsq := mul_le_mul_of_nonneg_right hd (norm_nonneg (x-y))
  have hsq' := mul_le_mul_of_nonneg_left hsq (mul_nonneg hC hz)
  nlinarith only [hrem,hjapp,hsq']

end
end SparseSGD.Logistic
