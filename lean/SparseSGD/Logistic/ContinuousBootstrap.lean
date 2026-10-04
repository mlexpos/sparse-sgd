import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
namespace SparseSGD.Logistic
noncomputable section
open Set

/-- A continuous path cannot first leave a closed norm ball when staying in
that ball up to a time yields a strict interior estimate at that time. -/
theorem continuous_norm_no_escape {E : Type*} [NormedAddCommGroup E]
    (y : ℝ → E) (T M A : ℝ) (hT : 0 ≤ T)
    (hy : ContinuousOn y (Icc 0 T)) (h0 : ‖y 0‖ < M) (hAM : A < M)
    (hbootstrap : ∀ t ∈ Icc 0 T,
      (∀ s ∈ Icc 0 t, ‖y s‖ ≤ M) → ‖y t‖ ≤ A) :
    ∀ t ∈ Icc 0 T, ‖y t‖ ≤ M := by
  classical
  have hf : ContinuousOn (fun t => ‖y t‖) (Icc 0 T) := hy.norm
  by_contra hn
  push Not at hn
  obtain ⟨b,hb,hbM⟩ := hn
  have hfsub (s : ℝ) (hs : s ∈ Icc 0 T) :
      ContinuousOn (fun t => ‖y t‖) (Icc 0 s) :=
    hf.mono (Icc_subset_Icc_right hs.2)
  obtain ⟨a,ha,haM⟩ := intermediate_value_Icc hb.1 (hfsub b hb) ⟨h0.le,hbM.le⟩
  obtain ⟨u,hu,heq⟩ := (continuousOn_iff_isClosed.mp hf) {M} isClosed_singleton
  have hcompact : IsCompact (((fun t => ‖y t‖) ⁻¹' {M}) ∩ Icc 0 T) := by
    rw [heq]
    exact isCompact_Icc.inter_left hu
  have haT : a ∈ Icc 0 T := ⟨ha.1,ha.2.trans hb.2⟩
  obtain ⟨t,ht⟩ := hcompact.exists_isLeast ⟨a,⟨haM,haT⟩⟩
  have htT : t ∈ Icc 0 T := ht.1.2
  have htM : ‖y t‖=M := ht.1.1
  have hprefix : ∀ s ∈ Icc 0 t, ‖y s‖ ≤ M := by
    intro s hs
    by_contra hsM
    have hsM' : M < ‖y s‖ := lt_of_not_ge hsM
    have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.trans htT.2⟩
    obtain ⟨a,ha,haM⟩ := intermediate_value_Icc hs.1 (hfsub s hsT) ⟨h0.le,hsM'.le⟩
    have haT : a ∈ Icc 0 T := ⟨ha.1,ha.2.trans hsT.2⟩
    have hta : t ≤ a := ht.2 ⟨haM,haT⟩
    have has : a=s := le_antisymm ha.2 (hs.2.trans hta)
    have hsEq : ‖y s‖=M := has ▸ haM
    linarith
  have H := hbootstrap t htT hprefix
  rw [htM] at H
  linarith

/-- The interior estimate holds for the entire interval once no-escape is
established. -/
theorem continuous_norm_bootstrap_bound {E : Type*} [NormedAddCommGroup E]
    (y : ℝ → E) (T M A : ℝ) (hT : 0 ≤ T)
    (hy : ContinuousOn y (Icc 0 T)) (h0 : ‖y 0‖ < M) (hAM : A < M)
    (hbootstrap : ∀ t ∈ Icc 0 T,
      (∀ s ∈ Icc 0 t, ‖y s‖ ≤ M) → ‖y t‖ ≤ A) :
    ∀ t ∈ Icc 0 T, ‖y t‖ ≤ A := by
  have H := continuous_norm_no_escape y T M A hT hy h0 hAM hbootstrap
  intro t ht
  exact hbootstrap t ht (fun s hs => H s ⟨hs.1,hs.2.trans ht.2⟩)

/-- The common margin-one version of continuous no-escape. -/
theorem continuous_norm_no_escape_margin_one {E : Type*} [NormedAddCommGroup E]
    (y : ℝ → E) (T M : ℝ) (hT : 0 ≤ T)
    (hy : ContinuousOn y (Icc 0 T)) (h0 : ‖y 0‖ < M)
    (hbootstrap : ∀ t ∈ Icc 0 T,
      (∀ s ∈ Icc 0 t, ‖y s‖ ≤ M) → ‖y t‖ ≤ M-1) :
    ∀ t ∈ Icc 0 T, ‖y t‖ ≤ M :=
  continuous_norm_no_escape y T M (M-1) hT hy h0 (by linarith) hbootstrap
end
end SparseSGD.Logistic
