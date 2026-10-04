import SparseSGD.Logistic.FluidTheorem

open MeasureTheory
open scoped ENNReal
namespace SparseSGD.Logistic
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
set_option maxHeartbeats 1600000

/-! Fluid bounds with a Taylor estimate only on states visited by the actual
process. This permits a physical Gram-state domain and one-sided variance
calculus at zero, without asserting smoothness at negative variances. -/

theorem fluid_pathwise_bootstrap_on_process {Ω : Type*} (Ψ : E → E)
    (X : ℕ → Ω → E) (x : ℕ → E)
    (J : ℕ → E →L[ℝ] E) (K : ℕ) (ρ Γ L2 lambda : ℝ)
    (hΓ : 0 ≤ Γ) (hL2 : 0 ≤ L2) (hlambda : 0 ≤ lambda)
    (hradius : 2 * lambda ≤ ρ) (hsmall : 2 * K * Γ * L2 * lambda ≤ 1)
    (hx : ∀ k, x (k+1) = Ψ (x k))
    (hJ : ∀ k ≤ K, ∀ j < k, ‖jacobianResponse J k j‖ ≤ Γ)
    (hTaylor : ∀ j < K, ∀ ω, ‖X j ω - x j‖ ≤ ρ →
      ‖Ψ (X j ω) - Ψ (x j) - J j (X j ω - x j)‖ ≤ L2 / 2 * ‖X j ω - x j‖^2)
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
        have ht := hTaylor j hjK ω ((hprev j hjk).trans hradius)
        calc
          _ ≤ ‖jacobianResponse J k j‖ * ‖fluidRemainder Ψ X x J j ω‖ :=
            (jacobianResponse J k j).le_opNorm _
          _ ≤ Γ * (L2 / 2 * ‖fluidError X x j ω‖^2) :=
            mul_le_mul (hJ k hk j hjk) ht (norm_nonneg _) hΓ
          _ = _ := by ring
      _ = _ := by rw [Finset.mul_sum]
  rw [fluid_error_unroll Ψ X x J hx ω h0 k]
  exact (norm_add_le _ _).trans (add_le_add hnoise' hrem)


theorem fluid_probability_norming_bound_on_process {m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
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
    (hTaylor : ∀ j < K, ∀ ω, ‖X j ω - x j‖ ≤ ρ →
      ‖Ψ (X j ω) - Ψ (x j) - J j (X j ω - x j)‖ ≤ L2 / 2 * ‖X j ω - x j‖^2)
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
    apply fluid_pathwise_bootstrap_on_process Ψ X x J K ρ Γ L2 lambda hΓ.le hL2 hlambda
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



theorem fluid_limit_normingFamily_on_process {m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
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
    (hTaylor : ∀ j < K, ∀ ω, ‖X j ω - x j‖ ≤ ρ →
      ‖Ψ (X j ω) - Ψ (x j) - J j (X j ω - x j)‖ ≤ L2 / 2 * ‖X j ω - x j‖^2)
    (hA3 : FluidUnitBernstein μ ℱ Ψ X x ρ v M K)
    (hradius : 2 * fluidThreshold Γ v M K (Real.log (2 * m * K / δ)) ≤ ρ)
    (hsmall : 2 * K * Γ * L2 * fluidThreshold Γ v M K (Real.log (2 * m * K / δ)) ≤ 1) :
    ENNReal.ofReal (1-δ) ≤ μ {ω | ∀ k ≤ K,
      ‖X k ω - x k‖ ≤ 2 * Γ * (Real.sqrt (2 * K * v * Real.log (2 * m * K / δ)) +
        2 * M * Real.log (2 * m * K / δ))} := by
  have hlog := fluid_log_confidence hn hK hδ0 hδ1
  have h := fluid_probability_norming_bound_on_process H μ ℱ Ψ hΨ X x hX ell (fun i => (hell i).le) hnorming J K ρ Γ L2 v M
    (Real.log (2 * m * K / δ)) δ hΓ hL2 hv hM hlog.1 hδ0.le hlog.2.le
    hx h0 hJ hTaylor (fluidBernstein_of_unit μ ℱ Ψ X x ρ v M K hv hM hA3) hradius hsmall
  simpa only [fluidThreshold, mul_assoc] using h

end
end SparseSGD.Logistic
