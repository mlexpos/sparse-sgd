import SparseSGD.Scaling.Exponents

namespace SparseSGD

/-- The critical alpha plane consists of the noise-limited cells 2/4/6,
    the switch cell 8, and the curvature-limited cell 7. -/
theorem critical_plane_cell_classification (sigma kappa gamma : ℝ)
    (hg : 0 < gamma) :
    Cell2 (eDelta gamma kappa (criticalAlpha sigma kappa gamma))
      (eNoise sigma (criticalAlpha sigma kappa gamma))
      (eCurvature gamma kappa (criticalAlpha sigma kappa gamma)) ∨
    Cell4 (eDelta gamma kappa (criticalAlpha sigma kappa gamma))
      (eNoise sigma (criticalAlpha sigma kappa gamma))
      (eCurvature gamma kappa (criticalAlpha sigma kappa gamma)) ∨
    Cell6 (eDelta gamma kappa (criticalAlpha sigma kappa gamma))
      (eNoise sigma (criticalAlpha sigma kappa gamma))
      (eCurvature gamma kappa (criticalAlpha sigma kappa gamma)) ∨
    Cell7 (eDelta gamma kappa (criticalAlpha sigma kappa gamma))
      (eNoise sigma (criticalAlpha sigma kappa gamma))
      (eCurvature gamma kappa (criticalAlpha sigma kappa gamma)) ∨
    Cell8 (eDelta gamma kappa (criticalAlpha sigma kappa gamma))
      (eNoise sigma (criticalAlpha sigma kappa gamma))
      (eCurvature gamma kappa (criticalAlpha sigma kappa gamma)) := by
  let a := criticalAlpha sigma kappa gamma
  have hswitch : gamma < sigma - 1 - kappa ∨ gamma = sigma - 1 - kappa ∨ gamma > sigma - 1 - kappa :=
    lt_trichotomy gamma (sigma - 1 - kappa)
  rcases hswitch with hs | hs | hs
  · have ha := critical_curvature_limited sigma kappa gamma hs
    have hd : eDelta gamma kappa a = 2*gamma := by dsimp [a]; rw [ha]; simp [eDelta]; ring
    have hn : eNoise sigma a < 0 := by change eNoise sigma (criticalAlpha sigma kappa gamma) < 0; rw [ha]; simp [eNoise]; linarith [hs]
    have hc : eCurvature gamma kappa a = 0 := by change eCurvature gamma kappa (criticalAlpha sigma kappa gamma) = 0; rw [ha]; simp [eCurvature]
    right; right; right; left
    exact ⟨by rw [hd]; linarith, hn, hc⟩
  · have ha := critical_switch sigma kappa gamma hs
    rcases ha with ⟨haN, haC⟩
    have hd : eDelta gamma kappa a = 2*gamma := by change eDelta gamma kappa (criticalAlpha sigma kappa gamma) = 2*gamma; rw [haN]; simp [eDelta]; linarith
    have hn : eNoise sigma a = 0 := by change eNoise sigma (criticalAlpha sigma kappa gamma) = 0; rw [haN]; simp [eNoise]
    have hc : eCurvature gamma kappa a = 0 := by change eCurvature gamma kappa (criticalAlpha sigma kappa gamma) = 0; rw [haC]; simp [eCurvature]
    right; right; right; right
    exact ⟨by rw [hd]; linarith, hn, hc⟩
  · have ha := critical_noise_limited sigma kappa gamma hs
    have hd : eDelta gamma kappa a = gamma - (1-sigma) - kappa := by dsimp [a]; rw [ha]; simp [eDelta]; ring
    have hn : eNoise sigma a = 0 := by change eNoise sigma (criticalAlpha sigma kappa gamma) = 0; rw [ha]; simp [eNoise]
    have hc : eCurvature gamma kappa a < 0 := by change eCurvature gamma kappa (criticalAlpha sigma kappa gamma) < 0; rw [ha]; simp [eCurvature]; linarith [hs]
    rcases lt_trichotomy gamma (1-sigma+kappa) with hr | hr | hr
    · left; exact ⟨by rw [hd]; linarith, hn, hc⟩
    · right; left; exact ⟨by rw [hd]; linarith, hn, hc⟩
    · right; right; left; exact ⟨by rw [hd]; linarith, hn, hc⟩

/-- The apparent lines are not additional boundaries, but they can intersect a
    genuine resonance or switch. These identities make the intersections explicit. -/
theorem apparent_line_intersections (sigma kappa gamma : ℝ) :
    (kappa = sigma → gamma = 1-sigma+kappa → gamma = 1) ∧
    (kappa = sigma-1 → gamma = 1-sigma+kappa → gamma = 0) ∧
    (kappa = sigma-1 → gamma = sigma-1-kappa → gamma = 0) ∧
    (gamma = kappa-sigma → gamma = 1-sigma+kappa → False) ∧
    (gamma = kappa-sigma → gamma = sigma-1-kappa → gamma = -(1:ℝ)/2) ∧
    (kappa = sigma → gamma = sigma-1-kappa → gamma = -1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h₁ h₂; linarith
  · intro h₁ h₂; linarith
  · intro h₁ h₂; linarith
  · intro h₁ h₂; linarith
  · intro h₁ h₂; linarith
  · intro h₁ h₂; linarith

end SparseSGD
