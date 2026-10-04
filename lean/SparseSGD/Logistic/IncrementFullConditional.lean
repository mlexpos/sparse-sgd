import SparseSGD.Logistic.IncrementFullMGF
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

theorem measurable_matchedSummary {d : ℕ} (eta beta : ℝ) (mu : Vec d) :
    Measurable (matchedSummary eta beta mu) := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> simp only [matchedSummary, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  · exact (measurable_signalCoord mu).comp measurable_fst
  · exact ((measurable_signalCoord mu).comp measurable_snd).const_mul _
  · exact ((measurable_bulkPart mu).comp measurable_fst).norm.pow_const 2
  · exact (((measurable_bulkPart mu).comp measurable_fst).inner
      ((measurable_bulkPart mu).comp measurable_snd)).const_mul _
  · exact (((measurable_bulkPart mu).comp measurable_snd).norm.pow_const 2).const_mul _

theorem measurable_matchedDrift {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) :
    Measurable (matchedDrift (B := B) eta beta p mu) := by
  apply measurable_pi_lambda
  intro i
  have hm := (measurable_pi_apply i).comp
    ((measurable_matchedSummary eta beta mu).comp (measurable_update d B eta beta p mu))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_matchedIncrement {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) :
    Measurable (fun z : State d × Batch d B => matchedIncrement eta beta p mu z.1 z.2) :=
  ((measurable_matchedSummary eta beta mu).comp (measurable_update d B eta beta p mu)).sub
    ((measurable_matchedDrift eta beta p mu).comp measurable_fst)

/-- Full actual LRinc on the entire sample history, localized to the
bounded stopped neighborhood. The nonnegative conditional expectation
needs no exponential integrability hypothesis outside the neighborhood. -/
theorem process_tame_matchedIncrement_dual_condLExp {d B : ℕ}
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (J : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : SparseSGD.External.GaussianSteinCertificate d)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (ρ : Measure (State d))
    [IsProbabilityMeasure ρ] (j : ℕ) (U : Set (State d))
    (ell : (Fin 5 → ℝ) →L[ℝ] ℝ) (Q K L t : ℝ)
    (hB : 0 < B) (hp : 0 < (p : ℝ)) (hr : 0 < r mu)
    (heta : 0 ≤ eta) (hbeta : 0 ≤ beta) (hbeta1 : beta < 1) (hell : ‖ell‖ ≤ 1)
    (htame : ∀ s ∈ U, tameError p mu s.1 ≤ 1/2) (hθ : ∀ s ∈ U, ‖s.1‖ ≤ Q)
    (hm : ∀ s ∈ U, ‖(eta/(1-beta)) • bulkPart mu s.2‖ ≤ K) (hstep : eta*(p : ℝ) ≤ L)
    (ht : |t| * lrIncrementScale eta mu Q K L B < 1) :
    ∀ᵐ ω ∂worldLaw p ρ, process eta beta p mu ω j ∈ U →
      (worldLaw p ρ)⁻[fun ω : World d B => ENNReal.ofReal (Real.exp
        (t*ell (matchedIncrement eta beta p mu (process eta beta p mu ω j) (ω.2 j)))) | pastSigma d B j] ω ≤
      ENNReal.ofReal (Real.exp (t^2*lrIncrementVariance eta p mu Q K L B/
        (2*(1-|t| * lrIncrementScale eta mu Q K L B)))) := by
  let F : State d × Batch d B → ℝ≥0∞ := fun z => ENNReal.ofReal
    (Real.exp (t*ell (matchedIncrement eta beta p mu z.1 z.2)))
  have hF : Measurable F := ENNReal.measurable_ofReal.comp
    (((ell.continuous.measurable).comp (measurable_matchedIncrement eta beta p mu)).const_mul t).exp
  have he := process_fresh_condLExp eta beta p mu ρ j F hF
  filter_upwards [he] with ω hω hU
  rw [hω]
  have hh := tame_matchedIncrement_dual_mgf H J G S eta beta p mu (process eta beta p mu ω j) ell
    Q K L t hB hp hr heta hbeta hbeta1 hell (htame _ hU) (hθ _ hU) (hm _ hU) hstep ht
  change (∫⁻ a : Batch d B, ENNReal.ofReal (Real.exp
    (t*ell (matchedIncrement eta beta p mu (process eta beta p mu ω j) a))) ∂batchLaw d B p) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hh.1
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
  exact ENNReal.ofReal_le_ofReal hh.2
end
end SparseSGD.Logistic
