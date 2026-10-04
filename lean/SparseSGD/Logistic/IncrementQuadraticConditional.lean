import SparseSGD.Logistic.IncrementFiniteMGF
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

theorem measurable_state_projection_energy {d B m : ℕ} (p : unitInterval) (mu : Vec d)
    (u : Fin m → State d → Vec d) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun z : State d × Batch d B => batchProjectionEnergy p mu z.1.1 (fun i => u i z.1) z.2) := by
  have hg : Measurable (fun z : State d × Batch d B => centeredBatchGradient p mu z.1.1 z.2) :=
    (measurable_centeredBatchGradient (B := B) p mu).comp
      (f := fun z : State d × Batch d B => (z.1.1,z.2))
      ((measurable_fst.fst).prodMk measurable_snd)
  exact Finset.measurable_sum _ (fun i _ => ((hu i).comp measurable_fst |>.inner hg).pow_const 2)

/-- Actual conditional MGF for the finite dependent active bulk energy,
localized to a stopped neighborhood and conditioned on the full past. -/
theorem process_tame_projection_energy_condLExp {d B m : ℕ}
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (ρ : Measure (State d))
    [IsProbabilityMeasure ρ] (k : ℕ) (u : Fin m → State d → Vec d) (hu : ∀ i, Measurable (u i))
    (U : Set (State d)) (Q t : ℝ) (hB : 0 < B) (hp : 0 < (p : ℝ))
    (htame : ∀ s ∈ U, tameError p mu s.1 ≤ 1/2)
    (hθ : ∀ s ∈ U, ‖s.1‖ ≤ Q) (hunit : ∀ i s, s ∈ U → ‖u i s‖ ≤ 1)
    (hmu : ∀ i s, s ∈ U → |inner ℝ (u i s) mu| ≤ 1)
    (ht : |(m : ℝ)*t| ≤ projectionSquareRadius Q B) :
    let Z := fun s : State d => batchProjectionEnergy p mu s.1 (fun i => u i s)
    ∀ᵐ ω ∂worldLaw p ρ, process eta beta p mu ω k ∈ U →
      (worldLaw p ρ)⁻[fun ω : World d B => ENNReal.ofReal (Real.exp
        (t*(Z (process eta beta p mu ω k) (ω.2 k)-
          (∫ a, Z (process eta beta p mu ω k) a ∂batchLaw d B p)))) | pastSigma d B k] ω ≤
      ENNReal.ofReal (Real.exp (Real.exp (8*Real.exp (2*Q^2+4))*
        projectionSquareVariance Q p B*((m : ℝ)*t)^2)) := by
  let Z := fun z : State d × Batch d B => batchProjectionEnergy p mu z.1.1 (fun i => u i z.1) z.2
  have hZm : Measurable Z := measurable_state_projection_energy p mu u hu
  have hmeanm : Measurable (fun s : State d => ∫ a, Z (s,a) ∂batchLaw d B p) :=
    hZm.stronglyMeasurable.integral_prod_right'.measurable
  let F : State d × Batch d B → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp
    (t*(Z z-(∫ a, Z (z.1,a) ∂batchLaw d B p))))
  have hF : Measurable F := ENNReal.measurable_ofReal.comp
    ((hZm.sub (hmeanm.comp measurable_fst)).const_mul t).exp
  have he := process_fresh_condLExp eta beta p mu ρ k F hF
  filter_upwards [he] with ω hω hU
  rw [hω]
  have hh := tame_batch_projection_energy_mgf G p mu (process eta beta p mu ω k).1
    (fun i => u i (process eta beta p mu ω k)) Q t hB hp (htame _ hU) (hθ _ hU)
    (fun i => hunit i _ hU) (fun i => hmu i _ hU) ht
  change (∫⁻ a : Batch d B, ENNReal.ofReal (Real.exp
    (t*(Z (process eta beta p mu ω k,a)-
      (∫ b, Z (process eta beta p mu ω k,b) ∂batchLaw d B p)))) ∂batchLaw d B p) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hh.1
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
  exact ENNReal.ofReal_le_ofReal hh.2
end
end SparseSGD.Logistic
