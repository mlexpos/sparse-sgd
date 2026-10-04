import SparseSGD.Probability.GramStep
import SparseSGD.Probability.Orthogonality

open MeasureTheory

namespace SparseSGD

theorem l2_norm_sq {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure Ω}
    (f : Lp E 2 μ) : ‖f‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- One-step stochastic moment reduction from a conditional second-order oracle.
The L2 norm and inner product are the actual integrated second moments. -/
theorem conditional_moment_step {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (p : Params) (e momentum ξ : Lp E 2 μ) (c vinc vadd : ℝ)
    (he : AEStronglyMeasurable[m] e μ)
    (hmom : AEStronglyMeasurable[m] momentum μ)
    (hzero : μ[ξ | m] =ᵐ[μ] 0)
    (hvar : μ[fun ω => ‖ξ ω‖ ^ 2 | m] =ᵐ[μ]
      fun ω => vinc * ‖e ω‖ ^ 2 + vadd)
    (hscale : c ^ 2 * (vinc * ‖e‖ ^ 2 + vadd) =
      2 * p.w * p.eps * (p.noise * ‖e‖ ^ 2 + p.additive)) :
    gramMoments ((1-p.w) • e - p.beta • momentum - c • ξ)
      (p.w • e + p.beta • momentum + c • ξ) = p.step (gramMoments e momentum) := by
  letI : MeasurableSpace Ω := mΩ
  have hi : Integrable (fun ω => ξ ω) μ := (Lp.memLp ξ).integrable (by norm_num)
  have heξ : inner ℝ e ξ = 0 := by
    rw [L2.inner_def]
    exact integral_inner_noise_eq_zero hm he (L2.integrable_inner e ξ) hi hzero
  have hmξ : inner ℝ momentum ξ = 0 := by
    rw [L2.inner_def]
    exact integral_inner_noise_eq_zero hm hmom (L2.integrable_inner momentum ξ) hi hzero
  have hsq : Integrable (fun ω => ‖e ω‖ ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) e e
  have hnorm : ‖ξ‖ ^ 2 = vinc * ‖e‖ ^ 2 + vadd := by
    rw [l2_norm_sq ξ, l2_norm_sq e, ← integral_condExp hm]
    rw [integral_congr_ae hvar, integral_add (hsq.const_mul vinc) (integrable_const vadd),
      integral_const_mul]
    simp
  exact gramMoments_step p e momentum ξ c heξ hmξ (by rwa [hnorm])

noncomputable def oracleParams (beta eta A vinc vadd : ℝ) : Params :=
  ⟨beta, eta*(1-beta)*A, eta*vinc/(2*A), eta*vadd/(2*A)⟩

theorem oracleParams_scale (beta eta A vinc vadd R : ℝ) (hA : A ≠ 0) :
    (eta*(1-beta)) ^ 2 * (vinc*R+vadd) =
      2*(oracleParams beta eta A vinc vadd).w *
        (oracleParams beta eta A vinc vadd).eps *
        ((oracleParams beta eta A vinc vadd).noise*R+
          (oracleParams beta eta A vinc vadd).additive) := by
  simp only [oracleParams, Params.eps]
  field_simp
  <;> ring

/-- Lemma L1's one-step identity with the paper's actual parameter normalization. -/
theorem oracle_moment_step {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (beta eta A vinc vadd : ℝ) (hA : A ≠ 0) (e momentum ξ : Lp E 2 μ)
    (he : AEStronglyMeasurable[m] e μ)
    (hmom : AEStronglyMeasurable[m] momentum μ)
    (hzero : μ[ξ | m] =ᵐ[μ] 0)
    (hvar : μ[fun ω => ‖ξ ω‖ ^ 2 | m] =ᵐ[μ]
      fun ω => vinc * ‖e ω‖ ^ 2 + vadd) :
    gramMoments ((1-eta*(1-beta)*A) • e - beta • momentum - (eta*(1-beta)) • ξ)
      ((eta*(1-beta)*A) • e + beta • momentum + (eta*(1-beta)) • ξ) =
        (oracleParams beta eta A vinc vadd).step (gramMoments e momentum) := by
  letI : MeasurableSpace Ω := mΩ
  exact conditional_moment_step hm (oracleParams beta eta A vinc vadd) e momentum ξ
    (eta*(1-beta)) vinc vadd he hmom hzero hvar
    (oracleParams_scale beta eta A vinc vadd _ hA)

/-- The entire moment sequence agrees with the deterministic four-parameter chain. -/
theorem oracle_moment_trajectory {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ k, F k ≤ mΩ)
    (beta eta A vinc vadd : ℝ) (hA : A ≠ 0)
    (e momentum ξ : ℕ → Lp E 2 μ)
    (he : ∀ k, AEStronglyMeasurable[F k] (e k) μ)
    (hmom : ∀ k, AEStronglyMeasurable[F k] (momentum k) μ)
    (hzero : ∀ k, μ[ξ k | F k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => ‖ξ k ω‖ ^ 2 | F k] =ᵐ[μ]
      fun ω => vinc * ‖e k ω‖ ^ 2 + vadd)
    (heStep : ∀ k, e (k+1) = (1-eta*(1-beta)*A) • e k -
      beta • momentum k - (eta*(1-beta)) • ξ k)
    (hmStep : ∀ k, momentum (k+1) = (eta*(1-beta)*A) • e k +
      beta • momentum k + (eta*(1-beta)) • ξ k) :
    ∀ k, gramMoments (e k) (momentum k) =
      (oracleParams beta eta A vinc vadd).trajectory (gramMoments (e 0) (momentum 0)) k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [heStep k, hmStep k,
      oracle_moment_step (hF k) beta eta A vinc vadd hA (e k) (momentum k) (ξ k)
        (he k) (hmom k) (hzero k) (hvar k), ih]
    rfl

end SparseSGD
