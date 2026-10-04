import SparseSGD.Discrete.KernelMass
import SparseSGD.External.Jury

namespace SparseSGD

noncomputable section

def normalizedKernelLag (p : Params) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 - p.curvature) * 2 * p.w * p.eps * (kickResponse p n) ^ 2

theorem stable_kernel_masses (jury : External.JuryStability) (p : Params)
    (hb0 : 1 / 2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta)) :
    HasSum (fun n => 2 * p.w * p.eps * p.noise * (kickResponse p n) ^ 2)
      p.renormNoise ∧
    HasSum (fun n => 2 * p.w * p.eps * p.additive * (kickResponse p n) ^ 2)
      p.renormAdditive := by
  have heps : 1 - p.beta ≠ 0 := by linarith
  have hplus : 1 + p.beta ≠ 0 := by linarith
  have hcurv_pos : 0 < 1 - p.curvature := by
    unfold Params.curvature
    rw [sub_pos]
    apply (div_lt_iff₀ (by linarith : 0 < 2 * (1 + p.beta))).2
    linarith
  have hcurv : 1 - p.curvature ≠ 0 := ne_of_gt hcurv_pos
  have hdecay := External.mean_powers_tendsto_zero jury p hb1 hw0 hw1
  have hmass := p.renewal_kernel_hasSum hw0.ne' heps hplus hcurv hdecay
  constructor
  · have h := hmass.mul_left p.noise
    convert h using 1
    · funext n
      ring
    · simp only [Params.renormNoise, div_eq_mul_inv, one_mul]
  · have h := hmass.mul_left p.additive
    convert h using 1
    · funext n
      ring
    · simp only [Params.renormAdditive, div_eq_mul_inv, one_mul]

theorem normalized_kernel_lag_nonneg (_jury : External.JuryStability) (p : Params)
    (hb0 : 1 / 2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta)) :
    ∀ n, 0 ≤ normalizedKernelLag p n := by
  intro n
  cases n with
  | zero => simp [normalizedKernelLag]
  | succ n =>
      have hcurv : 0 < 1 - p.curvature := by
        unfold Params.curvature
        rw [sub_pos]
        apply (div_lt_iff₀ (by linarith : 0 < 2 * (1 + p.beta))).2
        linarith
      simp [normalizedKernelLag]
      have heps : 0 < p.eps := by
        unfold Params.eps
        linarith
      positivity

theorem normalized_kernel_lag_hasSum (jury : External.JuryStability) (p : Params)
    (hb0 : 1 / 2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1 + p.beta)) :
    HasSum (normalizedKernelLag p) 1 := by
  have hcurv : 1 - p.curvature ≠ 0 := by
    have hc : 0 < 1 - p.curvature := by
      unfold Params.curvature
      rw [sub_pos]
      apply (div_lt_iff₀ (by linarith : 0 < 2 * (1 + p.beta))).2
      linarith
    exact ne_of_gt hc
  have hmass := p.renewal_kernel_hasSum hw0.ne' (by linarith : 1-p.beta ≠ 0)
    (by linarith : 1+p.beta ≠ 0) hcurv
    (External.mean_powers_tendsto_zero jury p hb1 hw0 hw1)
  have hscaled := hmass.mul_left (1 - p.curvature)
  have hshifted : HasSum (fun n => normalizedKernelLag p (n + 1)) 1 := by
    convert hscaled using 1
    · funext n
      simp only [normalizedKernelLag]
      ring
    · simp [hcurv]
  apply (hasSum_nat_add_iff' 1).1
  simpa only [Finset.sum_range_one, normalizedKernelLag, sub_zero] using hshifted

end
end SparseSGD
