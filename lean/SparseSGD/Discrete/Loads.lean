import SparseSGD.Foundations

namespace SparseSGD

theorem renormNoise_lt_one_iff (p : Params) (hc : p.curvature < 1) :
    p.renormNoise < 1 ↔ p.totalLoad < 1 := by
  unfold Params.renormNoise Params.totalLoad
  rw [div_lt_one (by linarith : 0 < 1 - p.curvature)]
  constructor <;> intro h <;> linarith

theorem floor_identity (p : Params) (hc : p.curvature ≠ 1)
    (hu : p.totalLoad ≠ 1) :
    p.renormAdditive / (1 - p.renormNoise) = p.additive / (1 - p.totalLoad) := by
  unfold Params.renormAdditive Params.renormNoise Params.totalLoad at *
  have hc' : 1 - p.curvature ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hu' : 1 - (p.noise + p.curvature) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hu'' : 1 - p.noise - p.curvature ≠ 0 := by intro h; apply hu'; linarith
  have hden : 1 - p.noise / (1 - p.curvature) =
      (1 - (p.noise + p.curvature)) / (1 - p.curvature) := by
    field_simp
    <;> ring
  rw [hden, div_div_div_cancel_right₀ hc']

theorem total_minus_renorm (p : Params) (hc : p.curvature ≠ 1) :
    p.totalLoad - p.renormNoise =
      p.curvature * (1-p.totalLoad) / (1-p.curvature) := by
  unfold Params.totalLoad Params.renormNoise
  have : 1 - p.curvature ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  field_simp
  <;> ring

theorem switch_rate_strict (p : Params) (hc0 : 0 < p.curvature)
    (hc1 : p.curvature < 1) (hn : 0 < p.noise) (hu : p.totalLoad < 1) :
    1-p.totalLoad < 1-p.renormNoise ∧ 1-p.renormNoise < 1 := by
  have h := total_minus_renorm p (ne_of_lt hc1)
  have hp : 0 < p.curvature * (1-p.totalLoad) / (1-p.curvature) :=
    div_pos (mul_pos hc0 (by linarith)) (by linarith)
  have hn' : 0 < p.renormNoise := div_pos hn (by linarith)
  constructor <;> linarith

end SparseSGD
