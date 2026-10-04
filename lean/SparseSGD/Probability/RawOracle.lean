import SparseSGD.Probability.LeastSquares.Trajectory
import SparseSGD.Discrete.Algebra
import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner

open MeasureTheory
open scoped ProbabilityTheory ENNReal

namespace SparseSGD
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A finite conditional second moment implies L2 integrability. Using nonnegative
conditional expectation avoids assuming the integrability being proved. -/
theorem memLp_of_condLExp_sq {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {ξ : Ω → E} {v : Ω → ℝ} (hξ : AEStronglyMeasurable[mΩ] ξ μ)
    (hv : Integrable v μ) (hv0 : ∀ ω, 0 ≤ v ω)
    (hvar : μ⁻[fun ω => ENNReal.ofReal (‖ξ ω‖ ^ 2) | m] =ᵐ[μ]
      fun ω => ENNReal.ofReal (v ω)) : MemLp ξ 2 μ := by
  have hvf : (∫⁻ ω, ENNReal.ofReal (v ω) ∂μ) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hv.aestronglyMeasurable
      (Filter.Eventually.of_forall hv0)).mpr hv
  have hfinite : (∫⁻ ω, ENNReal.ofReal (‖ξ ω‖ ^ 2) ∂μ) ≠ ∞ := by
    rw [← lintegral_condLExp hm, lintegral_congr_ae hvar]
    exact hvf
  apply (memLp_two_iff_integrable_sq_norm hξ).mpr
  exact (lintegral_ofReal_ne_top_iff_integrable (hξ.norm.pow 2)
    (Filter.Eventually.of_forall (fun ω => sq_nonneg ‖ξ ω‖))).mp hfinite

theorem condExp_sq_of_condLExp {m : MeasurableSpace Ω}
    {ξ : Ω → E} {v : Ω → ℝ} (hξ : MemLp ξ 2 μ) (hv0 : ∀ ω, 0 ≤ v ω)
    (hvar : μ⁻[fun ω => ENNReal.ofReal (‖ξ ω‖ ^ 2) | m] =ᵐ[μ]
      fun ω => ENNReal.ofReal (v ω)) :
    μ[fun ω => ‖ξ ω‖ ^ 2 | m] =ᵐ[μ] v := by
  have hi := (memLp_two_iff_integrable_sq_norm hξ.aestronglyMeasurable).mp hξ
  have hf := (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => sq_nonneg ‖ξ ω‖))).mpr hi
  have ht := toReal_condLExp m
    (f := fun ω => ENNReal.ofReal (‖ξ ω‖ ^ 2))
    (hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal) hf
  have ht' : (fun ω => (μ⁻[fun ω => ENNReal.ofReal (‖ξ ω‖ ^ 2) | m] ω).toReal)
      =ᵐ[μ] μ[fun ω => ‖ξ ω‖ ^ 2 | m] := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ht
  apply ht'.symm.trans
  filter_upwards [hvar] with ω hω
  rw [hω, ENNReal.toReal_ofReal (hv0 ω)]

/-- The measurable and conditional-moment content of Assumption G. The second
moment uses the nonnegative conditional expectation, so integrability is a
consequence rather than an extra assumption at every time. -/
structure RawOracleHypotheses (μ : Measure Ω) (F : ℕ → MeasurableSpace Ω)
    (e q ξ : ℕ → Ω → E) (vinc vadd : ℝ) : Prop where
  filtration_le : ∀ k, F k ≤ mΩ
  filtration_mono : Monotone F
  error_adapted : ∀ k, AEStronglyMeasurable[F k] (e k) μ
  momentum_adapted : ∀ k, AEStronglyMeasurable[F k] (q k) μ
  noise_measurable : ∀ k, AEStronglyMeasurable[mΩ] (ξ k) μ
  vinc_nonneg : 0 ≤ vinc
  vadd_nonneg : 0 ≤ vadd
  centered : ∀ k, μ[ξ k | F k] =ᵐ[μ] 0
  variance : ∀ k,
    μ⁻[fun ω => ENNReal.ofReal (‖ξ k ω‖ ^ 2) | F k] =ᵐ[μ]
      fun ω => ENNReal.ofReal (vinc * ‖e k ω‖ ^ 2 + vadd)

variable {F : ℕ → MeasurableSpace Ω} {e q ξ : ℕ → Ω → E} {vinc vadd : ℝ}

private theorem raw_noise_memLp (O : RawOracleHypotheses μ F e q ξ vinc vadd)
    (k : ℕ) (he : MemLp (e k) 2 μ) : MemLp (ξ k) 2 μ := by
  have hi := (memLp_two_iff_integrable_sq_norm he.aestronglyMeasurable).mp he
  exact memLp_of_condLExp_sq (O.filtration_le k) (O.noise_measurable k)
    ((hi.const_mul vinc).add (integrable_const vadd))
    (fun ω => add_nonneg (mul_nonneg O.vinc_nonneg (sq_nonneg _)) O.vadd_nonneg)
    (O.variance k)

theorem raw_oracle_memLp (O : RawOracleHypotheses μ F e q ξ vinc vadd)
    (beta eta A : ℝ) (he0 : MemLp (e 0) 2 μ) (hq0 : MemLp (q 0) 2 μ)
    (heStep : ∀ k, e (k+1) = (1-eta*(1-beta)*A) • e k -
      beta • q k - (eta*(1-beta)) • ξ k)
    (hqStep : ∀ k, q (k+1) = (eta*(1-beta)*A) • e k +
      beta • q k + (eta*(1-beta)) • ξ k) (k : ℕ) :
    MemLp (e k) 2 μ ∧ MemLp (q k) 2 μ ∧ MemLp (ξ k) 2 μ := by
  have hp (k : ℕ) : MemLp (e k) 2 μ ∧ MemLp (q k) 2 μ := by
    induction k with
    | zero => exact ⟨he0, hq0⟩
    | succ k ih =>
      have hx := raw_noise_memLp O k ih.1
      constructor
      · rw [heStep]
        exact ((ih.1.const_smul _).sub (ih.2.const_smul _)).sub (hx.const_smul _)
      · rw [hqStep]
        exact ((ih.1.const_smul _).add (ih.2.const_smul _)).add (hx.const_smul _)
  exact ⟨(hp k).1, (hp k).2, raw_noise_memLp O k (hp k).1⟩

/-- The general source Lemma L1, with raw integrated moments and integrability
derived from the initial state and the second-order oracle. -/
theorem raw_oracle_moment_trajectory (O : RawOracleHypotheses μ F e q ξ vinc vadd)
    (beta eta A : ℝ) (hA : 0 < A) (he0 : MemLp (e 0) 2 μ) (hq0 : MemLp (q 0) 2 μ)
    (heStep : ∀ k, e (k+1) = (1-eta*(1-beta)*A) • e k -
      beta • q k - (eta*(1-beta)) • ξ k)
    (hqStep : ∀ k, q (k+1) = (eta*(1-beta)*A) • e k +
      beta • q k + (eta*(1-beta)) • ξ k) (k : ℕ) :
    Probability.LeastSquares.integratedMoments μ (e k) (q k) =
      (oracleParams beta eta A vinc vadd).trajectory
        (Probability.LeastSquares.integratedMoments μ (e 0) (q 0)) k := by
  have hl := raw_oracle_memLp O beta eta A he0 hq0 heStep hqStep
  let eL (k) := (hl k).1.toLp (e k)
  let qL (k) := (hl k).2.1.toLp (q k)
  let xL (k) := (hl k).2.2.toLp (ξ k)
  have heL (k) : eL k =ᵐ[μ] e k := (hl k).1.coeFn_toLp
  have hqL (k) : qL k =ᵐ[μ] q k := (hl k).2.1.coeFn_toLp
  have hxL (k) : xL k =ᵐ[μ] ξ k := (hl k).2.2.coeFn_toLp
  have heAdapt (k) : AEStronglyMeasurable[F k] (eL k) μ :=
    (O.error_adapted k).congr (heL k).symm
  have hqAdapt (k) : AEStronglyMeasurable[F k] (qL k) μ :=
    (O.momentum_adapted k).congr (hqL k).symm
  have hz (k) : μ[xL k | F k] =ᵐ[μ] 0 :=
    (condExp_congr_ae (hxL k)).trans (O.centered k)
  have hv (k) : μ[fun ω => ‖xL k ω‖ ^ 2 | F k] =ᵐ[μ]
      fun ω => vinc * ‖eL k ω‖ ^ 2 + vadd := by
    apply (condExp_congr_ae ((hxL k).fun_comp (fun v => ‖v‖ ^ 2))).trans
    apply (condExp_sq_of_condLExp (hl k).2.2
      (fun ω => add_nonneg (mul_nonneg O.vinc_nonneg (sq_nonneg _)) O.vadd_nonneg)
      (O.variance k)).trans
    exact ((heL k).fun_comp (fun v => vinc * ‖v‖ ^ 2 + vadd)).symm
  have heS (k) : eL (k+1) = (1-eta*(1-beta)*A) • eL k -
      beta • qL k - (eta*(1-beta)) • xL k := by
    exact MemLp.toLp_congr (hl (k+1)).1
      ((((hl k).1.const_smul _).sub ((hl k).2.1.const_smul _)).sub
        ((hl k).2.2.const_smul _)) (Filter.EventuallyEq.of_eq (heStep k))
  have hqS (k) : qL (k+1) = (eta*(1-beta)*A) • eL k +
      beta • qL k + (eta*(1-beta)) • xL k := by
    exact MemLp.toLp_congr (hl (k+1)).2.1
      ((((hl k).1.const_smul _).add ((hl k).2.1.const_smul _)).add
        ((hl k).2.2.const_smul _)) (Filter.EventuallyEq.of_eq (hqStep k))
  have ht := oracle_moment_trajectory F O.filtration_le beta eta A vinc vadd hA.ne'
    eL qL xL heAdapt hqAdapt hz hv heS hqS k
  simpa only [eL, qL, Probability.LeastSquares.gramMoments_toLp] using ht

theorem raw_oracle_moment_step (O : RawOracleHypotheses μ F e q ξ vinc vadd)
    (beta eta A : ℝ) (hA : 0 < A) (he0 : MemLp (e 0) 2 μ) (hq0 : MemLp (q 0) 2 μ)
    (heStep : ∀ k, e (k+1) = (1-eta*(1-beta)*A) • e k -
      beta • q k - (eta*(1-beta)) • ξ k)
    (hqStep : ∀ k, q (k+1) = (eta*(1-beta)*A) • e k +
      beta • q k + (eta*(1-beta)) • ξ k) (k : ℕ) :
    Probability.LeastSquares.integratedMoments μ (e (k+1)) (q (k+1)) =
      (oracleParams beta eta A vinc vadd).step
        (Probability.LeastSquares.integratedMoments μ (e k) (q k)) := by
  rw [raw_oracle_moment_trajectory O beta eta A hA he0 hq0 heStep hqStep (k+1),
    raw_oracle_moment_trajectory O beta eta A hA he0 hq0 heStep hqStep k]
  rfl

theorem raw_oracle_covariance_step (O : RawOracleHypotheses μ F e q ξ vinc vadd)
    (beta eta A : ℝ) (hA : 0 < A) (he0 : MemLp (e 0) 2 μ) (hq0 : MemLp (q 0) 2 μ)
    (heStep : ∀ k, e (k+1) = (1-eta*(1-beta)*A) • e k -
      beta • q k - (eta*(1-beta)) • ξ k)
    (hqStep : ∀ k, q (k+1) = (eta*(1-beta)*A) • e k +
      beta • q k + (eta*(1-beta)) • ξ k) (k : ℕ) :
    let p := oracleParams beta eta A vinc vadd
    let s := Probability.LeastSquares.integratedMoments μ (e k) (q k)
    (Probability.LeastSquares.integratedMoments μ (e (k+1)) (q (k+1))).cov =
      p.meanMatrix * s.cov * p.meanMatrix.transpose +
        (2 * p.w * p.eps * (p.noise * s.R + p.additive)) • Matrix.vecMulVec kick kick := by
  dsimp only
  rw [raw_oracle_moment_step O beta eta A hA he0 hq0 heStep hqStep k, Params.step_cov]

end
end SparseSGD
