import SparseSGD.Continuum.PositiveFlow
import SparseSGD.Continuum.Energy

namespace SparseSGD

theorem continuumFlow_freeRisk (delta : ℝ) (s : Moments) (t : ℝ) :
    (continuumFlow delta 0 0 s t).R = continuumFreeRisk delta s t := by
  rw [continuumFlow_renewal]
  simp

/-- The actual free covariance flow has nonincreasing energy. -/
theorem continuumFlow_free_energy_antitone (delta : ℝ) (hd : 0 < delta)
    (s : Moments) (hs : s.psd) :
    AntitoneOn (fun t => (continuumFlow delta 0 0 s t).R +
      delta * (continuumFlow delta 0 0 s t).V) (Set.Ici 0) := by
  apply free_moment_energy_antitone delta _ hd.le (continuumFlow_isMomentSolution delta 0 0 s)
  intro t ht
  exact (continuumFlow_psd hd (by norm_num) (by norm_num) s hs ht).diag_nonneg (i := 1)

/-- The paper's free-risk bound, with positivity proved from the initial covariance. -/
theorem continuumFreeRisk_le_initial_energy (delta : ℝ) (hd : 0 < delta)
    (s : Moments) (hs : s.psd) (t : ℝ) (ht : 0 ≤ t) :
    continuumFreeRisk delta s t ≤ s.R + delta * s.V := by
  rw [← continuumFlow_freeRisk]
  have h := free_moment_risk_le_initial_energy delta _ hd.le
    (continuumFlow_isMomentSolution delta 0 0 s)
    (fun t ht => (continuumFlow_psd hd (by norm_num) (by norm_num) s hs ht).diag_nonneg (i := 1))
    t ht
  simpa only [continuumFlow_initial] using h

end SparseSGD
