import SparseSGD.Logistic.DynamicClipped
import SparseSGD.Logistic.DynamicEnergy
import SparseSGD.Logistic.DynamicPhysical
import SparseSGD.Logistic.ContinuousBootstrap

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 2400000

/-- Actual dynamic-alpha trajectories exist throughout every finite forward
horizon from every physical initial state. Positivity and a coercive energy
remove the bounded extension; no long-time stability assumption is used. -/
theorem dynamic_solution_exists_on_finite_horizon (r delta Phi T : ℝ) (y0 : DynamicState)
    (hd : 0 < delta) (hPhi : 0 ≤ Phi) (hT : 0 ≤ T) (hy0 : dynamicPhysical y0) :
    ∃ y : ℝ → DynamicState, y 0=y0 ∧
      (∀ t ∈ Set.Icc 0 T, HasDerivAt y (dynamicField r delta Phi (y t)) t) ∧
      (∀ t ∈ Set.Icc 0 T, dynamicPhysical (y t)) := by
  let E := dynamicEnergy r delta y0+Phi*T
  let A := 4*(|E|+2*r^2+1)*(1+1/delta)+1
  let M := max A ‖y0‖+1
  have hM : 0 ≤ M := by dsimp [M]; linarith [le_max_right A ‖y0‖,norm_nonneg y0]
  have h0 : ‖y0‖ < M := by dsimp [M]; linarith [le_max_right A ‖y0‖]
  have hAM : A < M := by dsimp [M]; linarith [le_max_left A ‖y0‖]
  obtain ⟨y,hy0eq,hy⟩ := dynamic_clipped_solution_exists r delta Phi M hM y0
  have hcont : ContinuousOn y (Set.Icc 0 T) := fun t ht => (hy t).continuousAt.continuousWithinAt
  have hlocal (t : ℝ) (ht : t ∈ Set.Icc 0 T) (hprefix : ∀ s ∈ Set.Icc 0 t, ‖y s‖ ≤ M) :
      ‖y t‖ ≤ A := by
    have hactual : ∀ s ∈ Set.Icc 0 t, HasDerivAt y (dynamicField r delta Phi (y s)) s := by
      intro s hs
      simpa only [dynamicBoxClamp_eq M (y s) (hprefix s hs)] using hy s
    have hphys := dynamicPhysical_preserved r delta Phi 0 t y ht.1 hd hPhi hactual (by simpa [hy0eq] using hy0)
    have henergy := dynamicEnergy_finite_horizon_bound r delta Phi t hd y hactual
      (fun s hs => (hphys s hs).2.1) t ⟨ht.1,le_rfl⟩
    have hE : dynamicEnergy r delta (y t) ≤ E := by
      rw [hy0eq] at henergy
      exact henergy.trans (add_le_add (le_refl (dynamicEnergy r delta y0)) (mul_le_mul_of_nonneg_left ht.2 hPhi))
    have hp := hphys t ⟨ht.1,le_rfl⟩
    exact dynamicEnergy_controls_norm r delta E (y t) hd hp.1 hp.2.1 hp.2.2 hE
  have hnorm := continuous_norm_no_escape y T M A hT hcont (by simpa [hy0eq] using h0) hAM hlocal
  have hactual : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (dynamicField r delta Phi (y t)) t := by
    intro t ht
    simpa only [dynamicBoxClamp_eq M (y t) (hnorm t ht)] using hy t
  refine ⟨y,hy0eq,hactual,?_⟩
  exact dynamicPhysical_preserved r delta Phi 0 T y hT hd hPhi hactual (by simpa [hy0eq] using hy0)

end
end SparseSGD.Logistic
