import SparseSGD.Continuum.Algebra

namespace SparseSGD

/-- A coordinatewise classical solution on nonnegative time. -/
def IsMomentSolution (delta u phi : ℝ) (s : ℝ → Moments) : Prop :=
  ∀ t, 0 ≤ t →
    HasDerivAt (fun t => (s t).R) (continuumField delta u phi (s t)).R t ∧
    HasDerivAt (fun t => (s t).V) (continuumField delta u phi (s t)).V t ∧
    HasDerivAt (fun t => (s t).C) (continuumField delta u phi (s t)).C t

theorem slowEnergy_hasDerivAt {delta u phi : ℝ} {s : ℝ → Moments}
    (hs : IsMomentSolution delta u phi s) (hd : delta ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t => slowEnergy delta (s t))
      (-slowEnergy delta (s t) + 2 * (u * (s t).R + phi)) t := by
  obtain ⟨hR, hV, hC⟩ := hs t ht
  have h := (hR.add (hV.const_mul delta)).sub hC
  change HasDerivAt (fun t => slowEnergy delta (s t))
    (slowEnergy delta (continuumField delta u phi (s t))) t at h
  rwa [slowEnergy_field delta u phi (s t) hd] at h

theorem rankDefect_hasDerivAt {delta u phi : ℝ} {s : ℝ → Moments}
    (hs : IsMomentSolution delta u phi s) (hd : delta ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t => (s t).rankDefect)
      (-2 * (s t).rankDefect + 2 / delta * (s t).R * (u * (s t).R + phi)) t := by
  obtain ⟨hR, hV, hC⟩ := hs t ht
  have h := (hR.mul hV).sub (hC.pow 2)
  convert h using 1
  · funext x
    rfl
  · have ha := rankDefect_field delta u phi (s t) hd
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at *
    nlinarith [ha]

end SparseSGD
