import SparseSGD.Continuum.Algebra
import SparseSGD.Continuum.Differential

namespace SparseSGD
noncomputable section

def oscillatoryEnergy (delta : ℝ) (lambda : ℂ) (s : Moments) : ℂ :=
  s.R - lambda * delta / (lambda + 2) * s.V + lambda * s.C

theorem oscillatoryEnergy_field (delta u phi : ℝ) (lambda : ℂ) (s : Moments)
    (hd : delta ≠ 0) (hl : lambda + 2 ≠ 0)
    (hq : lambda ^ 2 + 2 * lambda + 4 * (delta : ℂ) = 0) :
    oscillatoryEnergy delta lambda (continuumField delta u phi s) =
      lambda * oscillatoryEnergy delta lambda s -
        2 * lambda / (lambda + 2) * ((u : ℂ) * s.R + phi) := by
  have hd' : (delta : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  unfold oscillatoryEnergy continuumField
  push_cast
  field_simp
  linear_combination -(s.C : ℂ) * (lambda + 1) * hq

theorem oscillatoryEnergy_hasDerivAt {delta u phi : ℝ} {s : ℝ → Moments}
    (hs : IsMomentSolution delta u phi s) (hd : delta ≠ 0)
    (lambda : ℂ) (hl : lambda + 2 ≠ 0)
    (hq : lambda ^ 2 + 2 * lambda + 4 * (delta : ℂ) = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t => oscillatoryEnergy delta lambda (s t))
      (lambda * oscillatoryEnergy delta lambda (s t) -
        2 * lambda / (lambda + 2) * ((u : ℂ) * (s t).R + phi)) t := by
  obtain ⟨hR, hV, hC⟩ := hs t ht
  have h := (hR.ofReal_comp.sub (hV.ofReal_comp.const_mul
    (lambda * delta / (lambda + 2)))).add (hC.ofReal_comp.const_mul lambda)
  change HasDerivAt (fun t => oscillatoryEnergy delta lambda (s t))
    (oscillatoryEnergy delta lambda (continuumField delta u phi (s t))) t at h
  rwa [oscillatoryEnergy_field delta u phi lambda (s t) hd hl hq] at h

end
end SparseSGD
