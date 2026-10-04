import SparseSGD.Foundations

namespace SparseSGD

def eDelta (gamma kappa alpha : ℝ) : ℝ := gamma - kappa - alpha
def eNoise (sigma alpha : ℝ) : ℝ := 1 - sigma - alpha
def eCurvature (gamma kappa alpha : ℝ) : ℝ := -alpha - kappa - gamma
def criticalAlpha (sigma kappa gamma : ℝ) : ℝ := max (1 - sigma) (-kappa - gamma)

theorem eCurvature_eq_eDelta_sub_two_gamma (gamma kappa alpha : ℝ) :
    eCurvature gamma kappa alpha = eDelta gamma kappa alpha - 2 * gamma := by
  simp [eCurvature, eDelta]; ring

theorem load_exponents_nonpos_iff (sigma kappa gamma alpha : ℝ) :
    eNoise sigma alpha ≤ 0 ∧ eCurvature gamma kappa alpha ≤ 0 ↔
      alpha ≥ criticalAlpha sigma kappa gamma := by
  unfold eNoise eCurvature criticalAlpha
  constructor
  · rintro ⟨hn, hc⟩
    apply (max_le_iff).2
    constructor <;> linarith
  · intro h
    have hh : max (1 - sigma) (-kappa - gamma) ≤ alpha := h
    have hh' := (max_le_iff).1 hh
    constructor <;> linarith

def Cell1 (d n c : ℝ) : Prop := d < 0 ∧ n < 0 ∧ c < 0
def Cell2 (d n c : ℝ) : Prop := d < 0 ∧ n = 0 ∧ c < 0
def Cell3 (d n c : ℝ) : Prop := d = 0 ∧ n < 0 ∧ c < 0
def Cell4 (d n c : ℝ) : Prop := d = 0 ∧ n = 0 ∧ c < 0
def Cell5 (d n c : ℝ) : Prop := d > 0 ∧ n < 0 ∧ c < 0
def Cell6 (d n c : ℝ) : Prop := d > 0 ∧ n = 0 ∧ c < 0
def Cell7 (d n c : ℝ) : Prop := d > 0 ∧ n < 0 ∧ c = 0
def Cell8 (d n c : ℝ) : Prop := d > 0 ∧ n = 0 ∧ c = 0

theorem eight_cells_exhaustive (gamma d n c : ℝ) (hg : gamma > 0)
    (hc : c = d - 2 * gamma) (hn : n ≤ 0) (hload : c ≤ 0) :
    Cell1 d n c ∨ Cell2 d n c ∨ Cell3 d n c ∨ Cell4 d n c ∨
    Cell5 d n c ∨ Cell6 d n c ∨ Cell7 d n c ∨ Cell8 d n c := by
  have hd : d < 0 ∨ d = 0 ∨ d > 0 := lt_trichotomy d 0
  have hn' : n < 0 ∨ n = 0 := lt_or_eq_of_le hn
  have hc' : c < 0 ∨ c = 0 := lt_or_eq_of_le hload
  rcases hd with hd | hd | hd
  · rcases hn' with hn | hn
    · left; exact ⟨hd, hn, by linarith [hc]⟩
    · right; left; exact ⟨hd, hn, by linarith [hc]⟩
  · rcases hn' with hn | hn
    · right; right; left; exact ⟨hd, hn, by linarith [hc, hg]⟩
    · right; right; right; left; exact ⟨hd, hn, by linarith [hc, hg]⟩
  · rcases hn' with hn | hn
    · rcases hc' with hc' | hc'
      · right; right; right; right; left; exact ⟨hd, hn, hc'⟩
      · right; right; right; right; right; right; left; exact ⟨hd, hn, hc'⟩
    · rcases hc' with hc' | hc'
      · right; right; right; right; right; left; exact ⟨hd, hn, hc'⟩
      · right; right; right; right; right; right; right; exact ⟨hd, hn, hc'⟩

theorem critical_noise_limited (sigma kappa gamma : ℝ)
    (h : gamma > sigma - 1 - kappa) :
    criticalAlpha sigma kappa gamma = 1 - sigma := by
  unfold criticalAlpha
  apply max_eq_left
  linarith

theorem critical_curvature_limited (sigma kappa gamma : ℝ)
    (h : gamma < sigma - 1 - kappa) :
    criticalAlpha sigma kappa gamma = -kappa - gamma := by
  unfold criticalAlpha
  apply max_eq_right
  linarith

theorem critical_switch (sigma kappa gamma : ℝ)
    (h : gamma = sigma - 1 - kappa) :
    criticalAlpha sigma kappa gamma = 1 - sigma ∧
      criticalAlpha sigma kappa gamma = -kappa - gamma := by
  have heq : 1 - sigma = -kappa - gamma := by linarith
  rw [criticalAlpha, heq, max_self]
  exact ⟨by simp, by simp [heq]⟩

end SparseSGD
