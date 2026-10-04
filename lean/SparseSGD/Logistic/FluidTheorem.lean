import SparseSGD.Logistic.StoppedFluid
import SparseSGD.External.MartingaleBernstein
import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner

open MeasureTheory
open scoped ENNReal
namespace SparseSGD.Logistic
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
set_option maxHeartbeats 1600000

/-- Predictable localization for nonnegative conditional expectation. -/
theorem condLExp_predictable_indicator {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (A : Set Ω) (hA : MeasurableSet[m] A) (f : Ω → ℝ≥0∞) :
    μ⁻[A.indicator f | m] =ᵐ[μ] A.indicator (μ⁻[f | m]) := by
  apply (ae_eq_condLExp hm μ (A.indicator f)
    ((measurable_condLExp m μ f).indicator hA) ?_).symm
  intro s hs
  rw [lintegral_indicator (hm _ hA), lintegral_indicator (hm _ hA),
    Measure.restrict_restrict (hm _ hA)]
  exact setLIntegral_condLExp hm μ f (hA.inter hs)

/-- A localized Bernstein MGF bound is preserved by predictable stopping.
The exponent equals one after stopping, so no integrability outside `A` is needed. -/
theorem stopped_condLExp_exp_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (A : Set Ω) (hA : MeasurableSet[m] A) (Y : Ω → ℝ) (hY : Measurable[mΩ] Y)
    (t c : ℝ) (hc : 0 ≤ c)
    (hmgf : ∀ᵐ ω ∂μ, ω ∈ A →
      μ⁻[fun ω => ENNReal.ofReal (Real.exp (t * Y ω)) | m] ω ≤ ENNReal.ofReal (Real.exp c)) :
    μ⁻[fun ω => ENNReal.ofReal (Real.exp (t * A.indicator Y ω)) | m] ≤ᵐ[μ]
      fun _ => ENNReal.ofReal (Real.exp c) := by
  classical
  letI : MeasurableSpace Ω := mΩ
  let f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (t * Y ω))
  have hf : Measurable f := by fun_prop
  have heq : (fun ω => ENNReal.ofReal (Real.exp (t * A.indicator Y ω))) =
      A.indicator f + Aᶜ.indicator (fun _ => 1) := by
    funext ω
    by_cases h : ω ∈ A <;> simp [f, h]
  rw [heq]
  have hfi : AEMeasurable (A.indicator f) μ := by
    exact (hf.indicator (hm A hA)).aemeasurable
  have ha := condLExp_add_left (mΩ := m) (P := μ) (X := A.indicator f)
    (Aᶜ.indicator (fun _ => (1 : ℝ≥0∞))) hfi
  have hb := condLExp_predictable_indicator μ hm A hA f
  have hcomp : μ⁻[Aᶜ.indicator (fun _ => (1 : ℝ≥0∞)) | m] =
      Aᶜ.indicator (fun _ => 1) := by
    letI : MeasurableSpace Ω := m
    exact condLExp_eq_self hm μ (measurable_const.indicator hA.compl)
  filter_upwards [ha, hb, hmgf] with ω hω hωb hωmgf
  rw [hω, Pi.add_apply, hωb, hcomp]
  by_cases h : ω ∈ A
  · simpa [h, f] using hωmgf h
  · simp only [Set.indicator_of_notMem h, Set.indicator_of_mem (show ω ∈ Aᶜ from h), zero_add]
    rw [← ENNReal.ofReal_one]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr hc)

abbrev FluidState (n : ℕ) := Fin n → ℝ

def fluidNoise {Ω : Type*} (Ψ : E → E)
    (X : ℕ → Ω → E) (j : ℕ) (ω : Ω) : E := X (j+1) ω - Ψ (X j ω)

def fluidError {Ω : Type*} (X : ℕ → Ω → E)
    (x : ℕ → E) (j : ℕ) (ω : Ω) : E := X j ω - x j

/-- Survival through time `j` in the closed balls along the reference path. -/
def fluidAlive {Ω : Type*} (X : ℕ → Ω → E)
    (x : ℕ → E) (ρ : ℝ) (j : ℕ) : Set Ω :=
  {ω | ∀ i ≤ j, ‖fluidError X x i ω‖ ≤ ρ}

theorem measurableSet_fluidAlive {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → E) (x : ℕ → E)
    (hX : StronglyAdapted ℱ X) (ρ : ℝ) (j : ℕ) : MeasurableSet[ℱ j] (fluidAlive X x ρ j) := by
  classical
  have heq : fluidAlive X x ρ j = ⋂ i ≤ j, {ω | ‖X i ω - x i‖ ≤ ρ} := by
    ext ω
    simp [fluidAlive, fluidError]
  rw [heq]
  letI : MeasurableSpace Ω := ℱ j
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro hi
  exact measurableSet_le ((hX.stronglyMeasurable_le hi).sub stronglyMeasurable_const).norm.measurable measurable_const

def fluidStoppedSum {Ω : Type*} (Ψ : E → E)
    (X : ℕ → Ω → E) (x : ℕ → E)
    (J : ℕ → E →L[ℝ] E) (ρ : ℝ) (k : ℕ) (ω : Ω) : E :=
  ∑ j ∈ Finset.range k, jacobianResponse J k j
    ((fluidAlive X x ρ j).indicator (fluidNoise Ψ X j) ω)

/-- A3 uses nonnegative conditional expectation on the closed neighborhood.
The dual ball version is equivalent to the usual unit-dual formulation. -/
def FluidBernstein {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (Ψ : E → E)
    (X : ℕ → Ω → E) (x : ℕ → E) (ρ v M : ℝ) (K : ℕ) : Prop :=
  ∀ j < K, ∀ ell : E →L[ℝ] ℝ, ‖ell‖ ≤ 1 → ∀ t : ℝ, |t| * M < 1 →
    ∀ᵐ ω ∂μ, (∃ i ≤ K, ‖X j ω - x i‖ ≤ ρ) →
      μ⁻[fun ω => ENNReal.ofReal (Real.exp (t * ell (fluidNoise Ψ X j ω))) | ℱ j] ω ≤
        ENNReal.ofReal (Real.exp (t^2 * v / (2 * (1 - |t| * M))))

/-- The source A3, using unit dual functionals and nonnegative MGF arguments.
`t * M < 1` is the division-free domain, meaningful also when `M = 0`. -/
def FluidUnitBernstein {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (Ψ : E → E)
    (X : ℕ → Ω → E) (x : ℕ → E) (ρ v M : ℝ) (K : ℕ) : Prop :=
  ∀ j < K, ∀ ell : E →L[ℝ] ℝ, ‖ell‖ = 1 → ∀ t : ℝ, 0 ≤ t → t * M < 1 →
    ∀ᵐ ω ∂μ, (∃ i ≤ K, ‖X j ω - x i‖ ≤ ρ) →
      μ⁻[fun ω => ENNReal.ofReal (Real.exp (t * ell (fluidNoise Ψ X j ω))) | ℱ j] ω ≤
        ENNReal.ofReal (Real.exp (t^2 * v / (2 * (1 - t * M))))

/-- Unit-dual A3 implies the two-sided dual-ball condition needed for the
deterministic Jacobian weights. Both the zero functional and either sign of
the MGF argument are handled explicitly. -/
theorem fluidBernstein_of_unit {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (Ψ : E → E) (X : ℕ → Ω → E)
    (x : ℕ → E) (ρ v M : ℝ) (K : ℕ) (hv : 0 ≤ v) (hM : 0 ≤ M)
    (h : FluidUnitBernstein μ ℱ Ψ X x ρ v M K) : FluidBernstein μ ℱ Ψ X x ρ v M K := by
  intro j hj ell hell t ht
  have hc : 0 ≤ t^2 * v / (2 * (1 - |t| * M)) := by positivity
  by_cases hz : ell = 0
  · subst ell
    simp only [ContinuousLinearMap.zero_apply, mul_zero, Real.exp_zero, ENNReal.ofReal_one,
      condLExp_const (ℱ.le j) μ 1]
    filter_upwards with ω hω
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr hc)
  · have hg : 0 < ‖ell‖ := norm_pos_iff.mpr hz
    let f : E →L[ℝ] ℝ :=
      if 0 ≤ t then ‖ell‖⁻¹ • ell else -(‖ell‖⁻¹ • ell)
    have hf : ‖f‖ = 1 := by
      have hnorm : ‖‖ell‖⁻¹ • ell‖ = 1 := by
        simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hg]
        exact inv_mul_cancel₀ hg.ne'
      dsimp [f]
      split_ifs <;> simp [hnorm]
    have hd : |t| * ‖ell‖ * M < 1 := by
      calc
        |t| * ‖ell‖ * M ≤ |t| * 1 * M := by gcongr
        _ = |t| * M := by ring
        _ < 1 := ht
    have hraw := h j hj f hf (|t| * ‖ell‖) (by positivity) hd
    have harg (y : E) : (|t| * ‖ell‖) * f y = t * ell y := by
      dsimp [f]
      split_ifs with htt
      · simp only [abs_of_nonneg htt, ContinuousLinearMap.smul_apply, smul_eq_mul]
        field_simp
      · simp only [abs_of_neg (lt_of_not_ge htt), ContinuousLinearMap.neg_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        field_simp
    have hden : 0 < 2 * (1 - |t| * M) := by linarith
    have hden' : 2 * (1 - |t| * M) ≤ 2 * (1 - (|t| * ‖ell‖) * M) := by
      have hmul : |t| * ‖ell‖ * M ≤ |t| * M := by nlinarith [mul_le_mul_of_nonneg_left hell (mul_nonneg (abs_nonneg t) hM)]
      linarith
    have hnum : (|t| * ‖ell‖)^2 * v ≤ t^2 * v := by
      have hg2 : ‖ell‖^2 ≤ 1 := by nlinarith [norm_nonneg ell]
      rw [mul_pow, sq_abs]
      nlinarith [mul_le_mul_of_nonneg_left hg2 (mul_nonneg (sq_nonneg t) hv)]
    have hce : (|t| * ‖ell‖)^2 * v / (2 * (1 - (|t| * ‖ell‖) * M)) ≤
        t^2 * v / (2 * (1 - |t| * M)) := by
      apply div_le_div₀ (by positivity) hnum hden hden'
    filter_upwards [hraw] with ω hω hU
    have hb : μ⁻[fun ω => ENNReal.ofReal (Real.exp (t * ell (fluidNoise Ψ X j ω))) | ℱ j] ω ≤
        ENNReal.ofReal (Real.exp ((|t| * ‖ell‖)^2 * v / (2 * (1 - (|t| * ‖ell‖) * M)))) := by
      simpa only [harg] using hω hU
    exact hb.trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hce))

def fluidRemainder {Ω : Type*} (Ψ : E → E)
    (X : ℕ → Ω → E) (x : ℕ → E)
    (J : ℕ → E →L[ℝ] E) (j : ℕ) (ω : Ω) : E :=
  Ψ (X j ω) - Ψ (x j) - J j (fluidError X x j ω)

theorem fluid_error_unroll {Ω : Type*} (Ψ : E → E)
    (X : ℕ → Ω → E) (x : ℕ → E)
    (J : ℕ → E →L[ℝ] E)
    (hx : ∀ k, x (k+1) = Ψ (x k)) (ω : Ω) (h0 : X 0 ω = x 0) (k : ℕ) :
    fluidError X x k ω =
      (∑ j ∈ Finset.range k, jacobianResponse J k j (fluidNoise Ψ X j ω)) +
      ∑ j ∈ Finset.range k, jacobianResponse J k j (fluidRemainder Ψ X x J j ω) := by
  have h := vector_recurrence_unroll J
    (fun j => fluidNoise Ψ X j ω + fluidRemainder Ψ X x J j ω)
    (fun j => fluidError X x j ω) (by simp [fluidError, h0])
    (fun j => by simp only [fluidError, fluidNoise, fluidRemainder, hx]; abel) k
  simpa only [map_add, Finset.sum_add_distrib] using h

/-- The nonlinear step: a uniformly small stopped linear-noise convolution
keeps the actual process inside the closed Taylor neighborhoods. -/
theorem fluid_pathwise_bootstrap {Ω : Type*} (Ψ : E → E)
    (X : ℕ → Ω → E) (x : ℕ → E)
    (J : ℕ → E →L[ℝ] E) (K : ℕ) (ρ Γ L2 lambda : ℝ)
    (hΓ : 0 ≤ Γ) (hL2 : 0 ≤ L2) (hlambda : 0 ≤ lambda)
    (hradius : 2 * lambda ≤ ρ) (hsmall : 2 * K * Γ * L2 * lambda ≤ 1)
    (hx : ∀ k, x (k+1) = Ψ (x k))
    (hJ : ∀ k ≤ K, ∀ j < k, ‖jacobianResponse J k j‖ ≤ Γ)
    (hTaylor : ∀ j < K, ∀ y, ‖y - x j‖ ≤ ρ →
      ‖Ψ y - Ψ (x j) - J j (y - x j)‖ ≤ L2 / 2 * ‖y - x j‖^2)
    (ω : Ω) (h0 : X 0 ω = x 0)
    (hnoise : ∀ k ≤ K, ‖fluidStoppedSum Ψ X x J ρ k ω‖ ≤ lambda) :
    ∀ k ≤ K, ‖fluidError X x k ω‖ ≤ 2 * lambda := by
  classical
  apply fluidBootstrap_of_parameters (fun k => norm_nonneg _) hlambda hΓ hL2
    (by simp [fluidError, h0]) _ hsmall
  intro k hk hprev
  have halive (j : ℕ) (hj : j < k) : ω ∈ fluidAlive X x ρ j := by
    intro i hi
    exact (hprev i (hi.trans_lt hj)).trans hradius
  have hnoise' : ‖∑ j ∈ Finset.range k, jacobianResponse J k j (fluidNoise Ψ X j ω)‖ ≤ lambda := by
    convert hnoise k hk using 1
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Set.indicator_of_mem (halive j (Finset.mem_range.mp hj))]
  have hrem : ‖∑ j ∈ Finset.range k, jacobianResponse J k j (fluidRemainder Ψ X x J j ω)‖ ≤
      (Γ * L2 / 2) * ∑ j ∈ Finset.range k, ‖fluidError X x j ω‖^2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range k, ‖jacobianResponse J k j (fluidRemainder Ψ X x J j ω)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range k, (Γ * L2 / 2) * ‖fluidError X x j ω‖^2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk := Finset.mem_range.mp hj
        have hjK : j < K := hjk.trans_le hk
        have ht := hTaylor j hjK (X j ω) ((hprev j hjk).trans hradius)
        calc
          _ ≤ ‖jacobianResponse J k j‖ * ‖fluidRemainder Ψ X x J j ω‖ :=
            (jacobianResponse J k j).le_opNorm _
          _ ≤ Γ * (L2 / 2 * ‖fluidError X x j ω‖^2) :=
            mul_le_mul (hJ k hk j hjk) ht (norm_nonneg _) hΓ
          _ = _ := by ring
      _ = _ := by rw [Finset.mul_sum]
  rw [fluid_error_unroll Ψ X x J hx ω h0 k]
  exact (norm_add_le _ _).trans (add_le_add hnoise' hrem)

/-- A stopped convolution at a fixed terminal time satisfies the scalar
conditional Bernstein hypotheses, with variance `Γ² v` and scale `Γ M`. -/
theorem fluidStoppedSum_dual_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (H : SparseSGD.External.MartingaleBernsteinCertificate Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (Ψ : E → E) (hΨ : Measurable Ψ)
    (X : ℕ → Ω → E) (x : ℕ → E) (hX : StronglyAdapted ℱ X)
    (J : ℕ → E →L[ℝ] E) (K : ℕ) (ρ Γ v M L : ℝ)
    (hΓ : 0 < Γ) (hv : 0 ≤ v) (hM : 0 ≤ M) (hL : 0 < L)
    (hJ : ∀ k ≤ K, ∀ j < k, ‖jacobianResponse J k j‖ ≤ Γ)
    (hA3 : FluidBernstein μ ℱ Ψ X x ρ v M K) (k : ℕ) (hk : k ≤ K) (ell0 : E →L[ℝ] ℝ) (hell0 : ‖ell0‖ ≤ 1) :
    μ {ω | Γ * (Real.sqrt (2 * k * v * L) + 2 * M * L) <
      |ell0 (fluidStoppedSum Ψ X x J ρ k ω)|} ≤ ENNReal.ofReal (2 * Real.exp (-L)) := by
  classical
  let F (j : ℕ) : E →L[ℝ] ℝ :=
    ell0.comp (jacobianResponse J k j)
  let Y (j : ℕ) : Ω → ℝ := (fluidAlive X x ρ j).indicator
    (fun ω => F j (fluidNoise Ψ X j ω))
  have hnoise (j : ℕ) : StronglyMeasurable[ℱ (j+1)] (fluidNoise Ψ X j) := by
    exact (hX (j+1)).sub
      (hΨ.stronglyMeasurable.comp_measurable ((hX.stronglyMeasurable_le (Nat.le_succ j)).measurable))
  have hYa (j : ℕ) : StronglyMeasurable[ℱ (j+1)] (Y j) :=
    ((F j).continuous.comp_stronglyMeasurable (hnoise j)).indicator
      ((ℱ.mono (Nat.le_succ j)) _ (measurableSet_fluidAlive ℱ X x hX ρ j))
  have hmgf (j : ℕ) (hj : j < k) (t : ℝ) (ht : |t| * (Γ * M) < 1) :
      μ⁻[fun ω => ENNReal.ofReal (Real.exp (t * Y j ω)) | ℱ j] ≤ᵐ[μ]
        fun _ => ENNReal.ofReal (Real.exp (t^2 * (Γ^2 * v) / (2 * (1 - |t| * (Γ * M))))) := by
    let ell : E →L[ℝ] ℝ := Γ⁻¹ • F j
    have hF : ‖F j‖ ≤ Γ := by
      apply (F j).opNorm_le_bound hΓ.le
      intro y
      calc
        ‖F j y‖ ≤ ‖jacobianResponse J k j y‖ := by
          exact (ell0.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right hell0 (norm_nonneg (jacobianResponse J k j y)))
        _ ≤ ‖jacobianResponse J k j‖ * ‖y‖ := (jacobianResponse J k j).le_opNorm y
        _ ≤ Γ * ‖y‖ := mul_le_mul_of_nonneg_right (hJ k hk j hj) (norm_nonneg y)
    have hell : ‖ell‖ ≤ 1 := by
      simp only [ell, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hΓ]
      calc
        Γ⁻¹ * ‖F j‖ ≤ Γ⁻¹ * Γ := mul_le_mul_of_nonneg_left hF (inv_nonneg.mpr hΓ.le)
        _ = 1 := inv_mul_cancel₀ hΓ.ne'
    have ht' : |t * Γ| * M < 1 := by
      simpa only [abs_mul, abs_of_pos hΓ, mul_assoc] using ht
    have hraw := hA3 j (hj.trans_le hk) ell hell (t * Γ) ht'
    have hscale (ω : Ω) : (t * Γ) * ell (fluidNoise Ψ X j ω) =
        t * F j (fluidNoise Ψ X j ω) := by
      simp only [ell, ContinuousLinearMap.smul_apply, smul_eq_mul]
      field_simp
    have hexponent : (t * Γ)^2 * v / (2 * (1 - |t * Γ| * M)) =
        t^2 * (Γ^2 * v) / (2 * (1 - |t| * (Γ * M))) := by
      rw [abs_mul, abs_of_pos hΓ]
      ring
    apply stopped_condLExp_exp_le μ (ℱ.le j) (fluidAlive X x ρ j)
      (measurableSet_fluidAlive ℱ X x hX ρ j) (fun ω => F j (fluidNoise Ψ X j ω))
      (((F j).continuous.comp_stronglyMeasurable (hnoise j)).measurable.mono (ℱ.le _) le_rfl)
      t _ (by positivity)
    filter_upwards [hraw] with ω hω hAlive
    have hu : ∃ q ≤ K, ‖X j ω - x q‖ ≤ ρ := ⟨j, Nat.le_of_lt (hj.trans_le hk), hAlive j le_rfl⟩
    simpa only [hscale, hexponent] using hω hu
  have ht := H.tail μ ℱ Y k (Γ^2 * v) (Γ * M) L (by positivity) (by positivity) hL
    (fun j _ => hYa j) hmgf
  have hsqrt : Real.sqrt (2 * k * (Γ^2 * v) * L) = Γ * Real.sqrt (2 * k * v * L) := by
    rw [show 2 * k * (Γ^2 * v) * L = Γ^2 * (2 * k * v * L) by ring,
      Real.sqrt_mul (sq_nonneg Γ), Real.sqrt_sq_eq_abs, abs_of_pos hΓ]
  have hsum (ω : Ω) : (∑ j ∈ Finset.range k, Y j ω) = ell0 (fluidStoppedSum Ψ X x J ρ k ω) := by
    simp only [fluidStoppedSum, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases ha : ω ∈ fluidAlive X x ρ j <;> simp [Y, F, ha]
  rw [hsqrt, show 2 * (Γ * M) * L = Γ * (2 * M * L) by ring, ← mul_add] at ht
  simpa only [hsum] using ht

theorem fluidStoppedSum_coordinate_tail {n : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (H : SparseSGD.External.MartingaleBernsteinCertificate Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (Ψ : FluidState n → FluidState n) (hΨ : Measurable Ψ)
    (X : ℕ → Ω → FluidState n) (x : ℕ → FluidState n) (hX : StronglyAdapted ℱ X)
    (J : ℕ → FluidState n →L[ℝ] FluidState n) (K : ℕ) (ρ Γ v M L : ℝ)
    (hΓ : 0 < Γ) (hv : 0 ≤ v) (hM : 0 ≤ M) (hL : 0 < L)
    (hJ : ∀ k ≤ K, ∀ j < k, ‖jacobianResponse J k j‖ ≤ Γ)
    (hA3 : FluidBernstein μ ℱ Ψ X x ρ v M K) (k : ℕ) (hk : k ≤ K) (i : Fin n) :
    μ {ω | Γ * (Real.sqrt (2 * k * v * L) + 2 * M * L) <
      |fluidStoppedSum Ψ X x J ρ k ω i|} ≤ ENNReal.ofReal (2 * Real.exp (-L)) := by
  have hp : ‖(ContinuousLinearMap.proj i : FluidState n →L[ℝ] ℝ)‖ ≤ 1 := by
    apply (ContinuousLinearMap.proj i : FluidState n →L[ℝ] ℝ).opNorm_le_bound (by norm_num)
    intro y
    simpa using norm_le_pi_norm y i
  simpa only [ContinuousLinearMap.proj_apply] using
    fluidStoppedSum_dual_tail H μ ℱ Ψ hΨ X x hX J K ρ Γ v M L hΓ hv hM hL hJ hA3 k hk
      (ContinuousLinearMap.proj i) hp

def fluidThreshold (Γ v M : ℝ) (K : ℕ) (L : ℝ) : ℝ :=
  Γ * (Real.sqrt (2 * K * v * L) + 2 * M * L)

theorem measurable_fluidStoppedSum {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℕ mΩ) (Ψ : E → E) (hΨ : Measurable Ψ)
    (X : ℕ → Ω → E) (x : ℕ → E) (hX : StronglyAdapted ℱ X)
    (J : ℕ → E →L[ℝ] E) (ρ : ℝ) (k : ℕ) :
    Measurable (fluidStoppedSum Ψ X x J ρ k) := by
  classical
  apply Finset.measurable_sum
  intro j hj
  apply (jacobianResponse J k j).continuous.measurable.comp
  apply Measurable.indicator
  · exact ((hX (j+1)).measurable.mono (ℱ.le _) le_rfl).sub
      (hΨ.comp ((hX j).measurable.mono (ℱ.le _) le_rfl))
  · exact (ℱ.le j) _ (measurableSet_fluidAlive ℱ X x hX ρ j)

/-- The coordinate/time union bound for the actual stopped convolutions. -/
theorem fluidStoppedSum_union_bound {n : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (H : SparseSGD.External.MartingaleBernsteinCertificate Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (Ψ : FluidState n → FluidState n) (hΨ : Measurable Ψ)
    (X : ℕ → Ω → FluidState n) (x : ℕ → FluidState n) (hX : StronglyAdapted ℱ X)
    (J : ℕ → FluidState n →L[ℝ] FluidState n) (K : ℕ) (ρ Γ v M L : ℝ)
    (hΓ : 0 < Γ) (hv : 0 ≤ v) (hM : 0 ≤ M) (hL : 0 < L)
    (hJ : ∀ k ≤ K, ∀ j < k, ‖jacobianResponse J k j‖ ≤ Γ)
    (hA3 : FluidBernstein μ ℱ Ψ X x ρ v M K) :
    μ (⋃ q : Fin K × Fin n, {ω | fluidThreshold Γ v M K L <
      |fluidStoppedSum Ψ X x J ρ (q.1.val+1) ω q.2|}) ≤
        ENNReal.ofReal (2 * n * K * Real.exp (-L)) := by
  classical
  have ht (q : Fin K × Fin n) :
      μ {ω | fluidThreshold Γ v M K L < |fluidStoppedSum Ψ X x J ρ (q.1.val+1) ω q.2|} ≤
        ENNReal.ofReal (2 * Real.exp (-L)) := by
    have hk : q.1.val+1 ≤ K := q.1.isLt
    have hl : fluidThreshold Γ v M (q.1.val+1) L ≤ fluidThreshold Γ v M K L := by
      unfold fluidThreshold
      gcongr
    exact (measure_mono (fun ω hω => lt_of_le_of_lt hl hω)).trans
      (fluidStoppedSum_coordinate_tail H μ ℱ Ψ hΨ X x hX J K ρ Γ v M L hΓ hv hM hL hJ hA3 _ hk q.2)
  calc
    _ ≤ ∑ q : Fin K × Fin n, μ {ω | fluidThreshold Γ v M K L <
      |fluidStoppedSum Ψ X x J ρ (q.1.val+1) ω q.2|} := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _q : Fin K × Fin n, ENNReal.ofReal (2 * Real.exp (-L)) := Finset.sum_le_sum (fun q _ => ht q)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      ring

/-- Finite-horizon fluid theorem in the sup norm, with an arbitrary logarithmic
confidence parameter. A1 and A2 are concrete Taylor and Jacobian-product bounds;
A3 is the local nonnegative conditional Bernstein condition. -/
theorem fluid_probability_bound {n : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (H : SparseSGD.External.MartingaleBernsteinCertificate Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (Ψ : FluidState n → FluidState n) (hΨ : Measurable Ψ)
    (X : ℕ → Ω → FluidState n) (x : ℕ → FluidState n) (hX : StronglyAdapted ℱ X)
    (J : ℕ → FluidState n →L[ℝ] FluidState n) (K : ℕ) (ρ Γ L2 v M L δ : ℝ)
    (hΓ : 0 < Γ) (hL2 : 0 ≤ L2) (hv : 0 ≤ v) (hM : 0 ≤ M) (hL : 0 < L)
    (hδ : 0 ≤ δ) (hconfidence : 2 * n * K * Real.exp (-L) ≤ δ)
    (hx : ∀ k, x (k+1) = Ψ (x k)) (h0 : ∀ᵐ ω ∂μ, X 0 ω = x 0)
    (hJ : ∀ k ≤ K, ∀ j < k, ‖jacobianResponse J k j‖ ≤ Γ)
    (hTaylor : ∀ j < K, ∀ y, ‖y - x j‖ ≤ ρ →
      ‖Ψ y - Ψ (x j) - J j (y - x j)‖ ≤ L2 / 2 * ‖y - x j‖^2)
    (hA3 : FluidBernstein μ ℱ Ψ X x ρ v M K)
    (hradius : 2 * fluidThreshold Γ v M K L ≤ ρ)
    (hsmall : 2 * K * Γ * L2 * fluidThreshold Γ v M K L ≤ 1) :
    ENNReal.ofReal (1-δ) ≤ μ {ω | ∀ k ≤ K,
      ‖X k ω - x k‖ ≤ 2 * fluidThreshold Γ v M K L} := by
  classical
  let lambda := fluidThreshold Γ v M K L
  let Bad : Set Ω := ⋃ q : Fin K × Fin n,
    {ω | lambda < |fluidStoppedSum Ψ X x J ρ (q.1.val+1) ω q.2|}
  have hBad : MeasurableSet Bad := by
    apply MeasurableSet.iUnion
    intro q
    exact measurableSet_lt measurable_const
      (((measurable_pi_apply q.2).comp (measurable_fluidStoppedSum ℱ Ψ hΨ X x hX J ρ _)).abs)
  have hbad : μ Bad ≤ ENNReal.ofReal δ :=
    (fluidStoppedSum_union_bound H μ ℱ Ψ hΨ X x hX J K ρ Γ v M L hΓ hv hM hL hJ hA3).trans
      (ENNReal.ofReal_le_ofReal hconfidence)
  have hlambda : 0 ≤ lambda := by dsimp [lambda, fluidThreshold]; positivity
  have hsub : Badᶜ ≤ᵐ[μ] {ω | ∀ k ≤ K, ‖X k ω - x k‖ ≤ 2 * lambda} := by
    filter_upwards [h0] with ω hω hgood
    apply fluid_pathwise_bootstrap Ψ X x J K ρ Γ L2 lambda hΓ.le hL2 hlambda
      hradius hsmall hx hJ hTaylor ω hω
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0, fluidStoppedSum, hlambda]
    · apply (pi_norm_le_iff_of_nonneg hlambda).mpr
      intro i
      have hki : k-1 < K := by omega
      have hq : ω ∉ {ω | lambda < |fluidStoppedSum Ψ X x J ρ ((⟨k-1,hki⟩ : Fin K).val+1) ω i|} :=
        fun hm => hgood (Set.mem_iUnion.mpr ⟨(⟨k-1,hki⟩,i), hm⟩)
      simp only [Set.mem_setOf_eq, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)] at hq
      simpa only [Real.norm_eq_abs] using le_of_not_gt hq
  calc
    ENNReal.ofReal (1-δ) = 1 - ENNReal.ofReal δ := by
      rw [ENNReal.ofReal_sub 1 hδ, ENNReal.ofReal_one]
    _ ≤ 1 - μ Bad := tsub_le_tsub_left hbad 1
    _ = μ Badᶜ := by rw [measure_compl hBad (measure_ne_top μ Bad), measure_univ]
    _ ≤ _ := measure_mono_ae hsub

theorem fluid_log_confidence {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < Real.log (2 * n * K / δ) ∧
      2 * n * K * Real.exp (-Real.log (2 * n * K / δ)) = δ := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hnum : 0 < (2 * n * K : ℝ) := by positivity
  have htwo : (2 : ℝ) ≤ 2 * n * K := by nlinarith [mul_le_mul hnR hKR (by positivity) (by positivity)]
  have hq : 0 < (2 * n * K : ℝ) / δ := div_pos hnum hδ0
  constructor
  · apply Real.log_pos
    exact (one_lt_div hδ0).mpr (hδ1.trans_le (by linarith))
  · rw [Real.exp_neg, Real.exp_log hq]
    field_simp

/-- Source Theorem A for a finite-dimensional sup-norm process.

The reference path, its initial state and Jacobian products are deterministic;
the random initial state equals the reference initial state almost surely.
Taylor and Bernstein bounds hold on closed balls, so `2 lambda ≤ ρ` also works
at equality. The only external input is the scalar conditional Bernstein
certificate; adaptation, MGF scaling, stopping, union bound and nonlinear
absorption are proved here. The theorem does not require a Markov assumption,
since its conditional increment hypothesis already contains the needed information. -/
theorem fluid_limit_supNorm {n : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (H : SparseSGD.External.MartingaleBernsteinCertificate Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (Ψ : FluidState n → FluidState n) (hΨ : Measurable Ψ)
    (X : ℕ → Ω → FluidState n) (x : ℕ → FluidState n) (hX : StronglyAdapted ℱ X)
    (J : ℕ → FluidState n →L[ℝ] FluidState n) (K : ℕ) (ρ Γ L2 v M δ : ℝ)
    (hn : 0 < n) (hK : 0 < K) (hΓ : 0 < Γ) (hL2 : 0 ≤ L2) (hv : 0 ≤ v) (hM : 0 ≤ M)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hx : ∀ k, x (k+1) = Ψ (x k)) (h0 : ∀ᵐ ω ∂μ, X 0 ω = x 0)
    (hJ : ∀ k ≤ K, ∀ j < k, ‖jacobianResponse J k j‖ ≤ Γ)
    (hTaylor : ∀ j < K, ∀ y, ‖y - x j‖ ≤ ρ →
      ‖Ψ y - Ψ (x j) - J j (y - x j)‖ ≤ L2 / 2 * ‖y - x j‖^2)
    (hA3 : FluidUnitBernstein μ ℱ Ψ X x ρ v M K)
    (hradius : 2 * fluidThreshold Γ v M K (Real.log (2 * n * K / δ)) ≤ ρ)
    (hsmall : 2 * K * Γ * L2 * fluidThreshold Γ v M K (Real.log (2 * n * K / δ)) ≤ 1) :
    ENNReal.ofReal (1-δ) ≤ μ {ω | ∀ k ≤ K,
      ‖X k ω - x k‖ ≤ 2 * Γ * (Real.sqrt (2 * K * v * Real.log (2 * n * K / δ)) +
        2 * M * Real.log (2 * n * K / δ))} := by
  have hlog := fluid_log_confidence hn hK hδ0 hδ1
  have h := fluid_probability_bound H μ ℱ Ψ hΨ X x hX J K ρ Γ L2 v M
    (Real.log (2 * n * K / δ)) δ hΓ hL2 hv hM hlog.1 hδ0.le hlog.2.le
    hx h0 hJ hTaylor (fluidBernstein_of_unit μ ℱ Ψ X x ρ v M K hv hM hA3) hradius hsmall
  simpa only [fluidThreshold, mul_assoc] using h

/-- The finite-time union bound for an arbitrary finite family of dual functionals. -/
theorem fluidStoppedSum_family_union_bound {m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (H : SparseSGD.External.MartingaleBernsteinCertificate Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (Ψ : E → E) (hΨ : Measurable Ψ)
    (X : ℕ → Ω → E) (x : ℕ → E) (hX : StronglyAdapted ℱ X)
    (ell : Fin m → E →L[ℝ] ℝ) (hell : ∀ i, ‖ell i‖ ≤ 1)
    (J : ℕ → E →L[ℝ] E) (K : ℕ) (ρ Γ v M L : ℝ)
    (hΓ : 0 < Γ) (hv : 0 ≤ v) (hM : 0 ≤ M) (hL : 0 < L)
    (hJ : ∀ k ≤ K, ∀ j < k, ‖jacobianResponse J k j‖ ≤ Γ)
    (hA3 : FluidBernstein μ ℱ Ψ X x ρ v M K) :
    μ (⋃ q : Fin K × Fin m, {ω | fluidThreshold Γ v M K L <
      |ell q.2 (fluidStoppedSum Ψ X x J ρ (q.1.val+1) ω)|}) ≤
        ENNReal.ofReal (2 * m * K * Real.exp (-L)) := by
  classical
  have ht (q : Fin K × Fin m) :
      μ {ω | fluidThreshold Γ v M K L < |ell q.2 (fluidStoppedSum Ψ X x J ρ (q.1.val+1) ω)|} ≤
        ENNReal.ofReal (2 * Real.exp (-L)) := by
    have hk : q.1.val+1 ≤ K := q.1.isLt
    have hl : fluidThreshold Γ v M (q.1.val+1) L ≤ fluidThreshold Γ v M K L := by
      unfold fluidThreshold
      gcongr
    exact (measure_mono (fun ω hω => lt_of_le_of_lt hl hω)).trans
      (fluidStoppedSum_dual_tail H μ ℱ Ψ hΨ X x hX J K ρ Γ v M L hΓ hv hM hL hJ hA3 _ hk (ell q.2) (hell q.2))
  calc
    _ ≤ ∑ q : Fin K × Fin m, μ {ω | fluidThreshold Γ v M K L <
      |ell q.2 (fluidStoppedSum Ψ X x J ρ (q.1.val+1) ω)|} := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _q : Fin K × Fin m, ENNReal.ofReal (2 * Real.exp (-L)) := Finset.sum_le_sum (fun q _ => ht q)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      ring


theorem fluid_probability_norming_bound {m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (H : SparseSGD.External.MartingaleBernsteinCertificate Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (Ψ : E → E) (hΨ : Measurable Ψ)
    (X : ℕ → Ω → E) (x : ℕ → E) (hX : StronglyAdapted ℱ X)
    (ell : Fin m → E →L[ℝ] ℝ) (hell : ∀ i, ‖ell i‖ ≤ 1)
    (hnorming : ∀ y : E, ‖y‖ ≤ ‖fun i => ell i y‖)
    (J : ℕ → E →L[ℝ] E) (K : ℕ) (ρ Γ L2 v M L δ : ℝ)
    (hΓ : 0 < Γ) (hL2 : 0 ≤ L2) (hv : 0 ≤ v) (hM : 0 ≤ M) (hL : 0 < L)
    (hδ : 0 ≤ δ) (hconfidence : 2 * m * K * Real.exp (-L) ≤ δ)
    (hx : ∀ k, x (k+1) = Ψ (x k)) (h0 : ∀ᵐ ω ∂μ, X 0 ω = x 0)
    (hJ : ∀ k ≤ K, ∀ j < k, ‖jacobianResponse J k j‖ ≤ Γ)
    (hTaylor : ∀ j < K, ∀ y, ‖y - x j‖ ≤ ρ →
      ‖Ψ y - Ψ (x j) - J j (y - x j)‖ ≤ L2 / 2 * ‖y - x j‖^2)
    (hA3 : FluidBernstein μ ℱ Ψ X x ρ v M K)
    (hradius : 2 * fluidThreshold Γ v M K L ≤ ρ)
    (hsmall : 2 * K * Γ * L2 * fluidThreshold Γ v M K L ≤ 1) :
    ENNReal.ofReal (1-δ) ≤ μ {ω | ∀ k ≤ K,
      ‖X k ω - x k‖ ≤ 2 * fluidThreshold Γ v M K L} := by
  classical
  let lambda := fluidThreshold Γ v M K L
  let Bad : Set Ω := ⋃ q : Fin K × Fin m,
    {ω | lambda < |ell q.2 (fluidStoppedSum Ψ X x J ρ (q.1.val+1) ω)|}
  have hBad : MeasurableSet Bad := by
    apply MeasurableSet.iUnion
    intro q
    exact measurableSet_lt measurable_const
      (((ell q.2).continuous.measurable.comp (measurable_fluidStoppedSum ℱ Ψ hΨ X x hX J ρ _)).abs)
  have hbad : μ Bad ≤ ENNReal.ofReal δ :=
    (fluidStoppedSum_family_union_bound H μ ℱ Ψ hΨ X x hX ell hell J K ρ Γ v M L hΓ hv hM hL hJ hA3).trans
      (ENNReal.ofReal_le_ofReal hconfidence)
  have hlambda : 0 ≤ lambda := by dsimp [lambda, fluidThreshold]; positivity
  have hsub : Badᶜ ≤ᵐ[μ] {ω | ∀ k ≤ K, ‖X k ω - x k‖ ≤ 2 * lambda} := by
    filter_upwards [h0] with ω hω hgood
    apply fluid_pathwise_bootstrap Ψ X x J K ρ Γ L2 lambda hΓ.le hL2 hlambda
      hradius hsmall hx hJ hTaylor ω hω
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0, fluidStoppedSum, hlambda]
    · apply (hnorming (fluidStoppedSum Ψ X x J ρ k ω)).trans
      apply (pi_norm_le_iff_of_nonneg hlambda).mpr
      intro i
      have hki : k-1 < K := by omega
      have hq : ω ∉ {ω | lambda < |ell i (fluidStoppedSum Ψ X x J ρ ((⟨k-1,hki⟩ : Fin K).val+1) ω)|} :=
        fun hm => hgood (Set.mem_iUnion.mpr ⟨(⟨k-1,hki⟩,i), hm⟩)
      simp only [Set.mem_setOf_eq, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)] at hq
      simpa only [Real.norm_eq_abs] using le_of_not_gt hq
  calc
    ENNReal.ofReal (1-δ) = 1 - ENNReal.ofReal δ := by
      rw [ENNReal.ofReal_sub 1 hδ, ENNReal.ofReal_one]
    _ ≤ 1 - μ Bad := tsub_le_tsub_left hbad 1
    _ = μ Badᶜ := by rw [measure_compl hBad (measure_ne_top μ Bad), measure_univ]
    _ ≤ _ := measure_mono_ae hsub


/-- Arbitrary-norm source Theorem A. The finite norming dual family is given
by unit continuous linear functionals; its image has the sup norm, so the
`hnorming` hypothesis is exactly the source's maximum-of-duals bound.
This applies in particular to every finite-dimensional normed space satisfying
that hypothesis, and requires no coordinate choice in the original space. -/
theorem fluid_limit_normingFamily {m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (H : SparseSGD.External.MartingaleBernsteinCertificate Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (Ψ : E → E) (hΨ : Measurable Ψ)
    (X : ℕ → Ω → E) (x : ℕ → E) (hX : StronglyAdapted ℱ X)
    (ell : Fin m → E →L[ℝ] ℝ) (hell : ∀ i, ‖ell i‖ = 1)
    (hnorming : ∀ y : E, ‖y‖ ≤ ‖fun i => ell i y‖)
    (J : ℕ → E →L[ℝ] E) (K : ℕ) (ρ Γ L2 v M δ : ℝ)
    (hn : 0 < m) (hK : 0 < K) (hΓ : 0 < Γ) (hL2 : 0 ≤ L2) (hv : 0 ≤ v) (hM : 0 ≤ M)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hx : ∀ k, x (k+1) = Ψ (x k)) (h0 : ∀ᵐ ω ∂μ, X 0 ω = x 0)
    (hJ : ∀ k ≤ K, ∀ j < k, ‖jacobianResponse J k j‖ ≤ Γ)
    (hTaylor : ∀ j < K, ∀ y, ‖y - x j‖ ≤ ρ →
      ‖Ψ y - Ψ (x j) - J j (y - x j)‖ ≤ L2 / 2 * ‖y - x j‖^2)
    (hA3 : FluidUnitBernstein μ ℱ Ψ X x ρ v M K)
    (hradius : 2 * fluidThreshold Γ v M K (Real.log (2 * m * K / δ)) ≤ ρ)
    (hsmall : 2 * K * Γ * L2 * fluidThreshold Γ v M K (Real.log (2 * m * K / δ)) ≤ 1) :
    ENNReal.ofReal (1-δ) ≤ μ {ω | ∀ k ≤ K,
      ‖X k ω - x k‖ ≤ 2 * Γ * (Real.sqrt (2 * K * v * Real.log (2 * m * K / δ)) +
        2 * M * Real.log (2 * m * K / δ))} := by
  have hlog := fluid_log_confidence hn hK hδ0 hδ1
  have h := fluid_probability_norming_bound H μ ℱ Ψ hΨ X x hX ell (fun i => (hell i).le) hnorming J K ρ Γ L2 v M
    (Real.log (2 * m * K / δ)) δ hΓ hL2 hv hM hlog.1 hδ0.le hlog.2.le
    hx h0 hJ hTaylor (fluidBernstein_of_unit μ ℱ Ψ X x ρ v M K hv hM hA3) hradius hsmall
  simpa only [fluidThreshold, mul_assoc] using h

end
end SparseSGD.Logistic
