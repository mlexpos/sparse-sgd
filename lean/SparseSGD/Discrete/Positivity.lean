import SparseSGD.Discrete.Algebra

namespace SparseSGD

theorem Moments.rankDefect_eq_cov_det (s : Moments) : s.rankDefect = s.cov.det := by
  simp [Moments.rankDefect, Moments.cov, Matrix.det_fin_two]
  ring

theorem Moments.psd_R_nonneg {s : Moments} (h : s.psd) : 0 ≤ s.R := by
  have h' := h.diag_nonneg (i := 0)
  simpa [Moments.cov] using h'

theorem Moments.psd_V_nonneg {s : Moments} (h : s.psd) : 0 ≤ s.V := by
  have h' := h.diag_nonneg (i := 1)
  simpa [Moments.cov] using h'

theorem Moments.psd_rankDefect_nonneg {s : Moments} (h : s.psd) :
    0 ≤ s.rankDefect := by
  rw [Moments.rankDefect_eq_cov_det]
  exact h.det_nonneg

theorem Params.step_psd (p : Params) (s : Moments) (hs : s.psd)
    (hw : 0 ≤ p.w) (he : 0 ≤ p.eps) (hn : 0 ≤ p.noise) (ha : 0 ≤ p.additive) :
    (p.step s).psd := by
  rw [Moments.psd, Params.step_cov]
  apply Matrix.PosSemidef.add
    (Matrix.PosSemidef.mul_mul_conjTranspose_same hs p.meanMatrix)
  apply Matrix.PosSemidef.smul
    (Matrix.posSemidef_vecMulVec_self_star kick)
  positivity [Moments.psd_R_nonneg hs]

theorem Params.trajectory_psd (p : Params) (s : Moments) (hs : s.psd)
    (hw : 0 ≤ p.w) (he : 0 ≤ p.eps) (hn : 0 ≤ p.noise) (ha : 0 ≤ p.additive)
    (n : ℕ) : (p.trajectory s n).psd := by
  induction n with
  | zero => simpa [Params.trajectory] using hs
  | succ n ih =>
      simpa [Params.trajectory] using Params.step_psd p (p.trajectory s n) ih hw he hn ha

end SparseSGD
