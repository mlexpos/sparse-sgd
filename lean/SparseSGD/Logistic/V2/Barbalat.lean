import Mathlib

/-!
# Integral-free Barbalat lemmas and cluster-point convergence (v2)

Abstract real-analysis lemmas used in place of LaSalle's invariance principle
in the v2 proof of `prop:S` (global convergence of the LR5 system).
-/

open Filter Topology Set Metric

namespace SparseSGD.Logistic.V2

/-- v2 prop:S (iii), Barbalat's lemma without integrals: if `F' = f` on `[0,∞)`,
`F` converges at infinity and `f` is uniformly continuous on `[0,∞)`, then `f → 0`. -/
theorem tendsto_zero_of_hasDerivAt_of_tendsto {F f : ℝ → ℝ} {l : ℝ}
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (f t) t)
    (hlim : Tendsto F atTop (𝓝 l))
    (hf : UniformContinuousOn f (Ici 0)) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.mp hf (ε / 2) (by linarith)
  set h : ℝ := δ / 2 with hh
  have hhpos : 0 < h := by positivity
  have hhδ : h < δ := by rw [hh]; linarith
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.mp hlim (h * ε / 4) (by positivity)
  refine ⟨max T 0, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have hlt : t < t + h := by linarith
  obtain ⟨ξ, hξ, hfξ⟩ := exists_hasDerivAt_eq_slope F f hlt
    (fun x hx => (hF x (by linarith [hx.1])).continuousAt.continuousWithinAt)
    (fun x hx => hF x (by linarith [hx.1]))
  have h1 := hT t htT
  have h2 := hT (t + h) (by linarith)
  rw [Real.dist_eq] at h1 h2
  have hdiff : |F (t + h) - F t| < h * ε / 2 := by
    have : F (t + h) - F t = (F (t + h) - l) - (F t - l) := by ring
    rw [this]
    calc |(F (t + h) - l) - (F t - l)| ≤ |F (t + h) - l| + |F t - l| := abs_sub _ _
      _ < h * ε / 4 + h * ε / 4 := add_lt_add h2 h1
      _ = h * ε / 2 := by ring
  have hfξabs : |f ξ| < ε / 2 := by
    rw [hfξ, show t + h - t = h by ring, abs_div, abs_of_pos hhpos, div_lt_iff₀ hhpos]
    linarith
  have hξ0 : 0 ≤ ξ := by linarith [hξ.1]
  have hd : dist t ξ < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hξ.1, hξ.2]
  have := hδf t (mem_Ici.mpr ht0) ξ (mem_Ici.mpr hξ0) hd
  rw [Real.dist_eq] at this ⊢
  rw [sub_zero]
  calc |f t| = |(f t - f ξ) + f ξ| := by ring_nf
    _ ≤ |f t - f ξ| + |f ξ| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add this hfξabs
    _ = ε := by ring

/-- v2 prop:S (iii), monotone convergence: a function antitone on `[t0,∞)` and bounded
below there has a limit at infinity. -/
theorem antitone_bddBelow_tendsto {F : ℝ → ℝ} {t0 : ℝ}
    (hanti : AntitoneOn F (Ici t0)) (hbdd : BddBelow (F '' Ici t0)) :
    ∃ l, Tendsto F atTop (𝓝 l) := by
  set G : ℝ → ℝ := fun t => F (max t t0) with hG
  have hGanti : Antitone G := fun a b hab =>
    hanti (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _))
      (max_le_max hab le_rfl)
  have hGbdd : BddBelow (range G) := by
    obtain ⟨m, hm⟩ := hbdd
    exact ⟨m, by rintro _ ⟨t, rfl⟩; exact hm ⟨max t t0, mem_Ici.mpr (le_max_right _ _), rfl⟩⟩
  refine ⟨⨅ t, G t, (tendsto_atTop_ciInf hGanti hGbdd).congr' ?_⟩
  filter_upwards [eventually_ge_atTop t0] with t ht
  simp [hG, max_eq_left ht]

/-- v2 prop:S (iii): a path with derivative bounded by `M` on `[0,∞)` is
`M`-Lipschitz there. -/
theorem lipschitz_of_norm_deriv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y y' : ℝ → E} {M : ℝ}
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (y' t) t)
    (hM : ∀ t, 0 ≤ t → ‖y' t‖ ≤ M) :
    ∀ s ∈ Ici (0:ℝ), ∀ t ∈ Ici (0:ℝ), ‖y s - y t‖ ≤ M * |s - t| := by
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → ‖y b - y a‖ ≤ M * (b - a) := by
    intro a b ha hab
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := y) (f' := y') (a := a) (b := b)
      (fun x hx => (hy x (le_trans ha hx.1)).hasDerivWithinAt)
      (fun x hx => hM x (le_trans ha hx.1)) b ⟨hab, le_rfl⟩
    exact this
  intro s hs t ht
  have hs' : 0 ≤ s := hs
  have ht' : 0 ≤ t := ht
  rcases le_total s t with h | h
  · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact key s t hs' h
  · rw [abs_of_nonneg (by linarith)]
    exact key t s ht' h

/-- v2 prop:S (iii): a continuous function on a compact set `K` composed with a
Lipschitz path valued in `K` is uniformly continuous on `[0,∞)`. -/
theorem uniformContinuousOn_comp_path {E G : Type*} [PseudoMetricSpace E]
    [PseudoMetricSpace G] {y : ℝ → E} {g : E → G} {K : Set E} {M : ℝ}
    (hlip : ∀ s ∈ Ici (0:ℝ), ∀ t ∈ Ici (0:ℝ), dist (y s) (y t) ≤ M * dist s t)
    (hK : IsCompact K) (hyK : ∀ t, 0 ≤ t → y t ∈ K) (hg : ContinuousOn g K) :
    UniformContinuousOn (g ∘ y) (Ici 0) := by
  have hgu : UniformContinuousOn g K := hK.uniformContinuousOn_of_continuous hg
  have hyu : UniformContinuousOn y (Ici 0) := by
    have hL : LipschitzOnWith (Real.toNNReal M) y (Ici 0) := by
      refine LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_
      refine (hlip s hs t ht).trans ?_
      by_cases hM : 0 ≤ M
      · simp [Real.coe_toNNReal _ hM]
      · replace hM := not_le.mp hM
        have : 0 ≤ M * dist s t := le_trans dist_nonneg (hlip s hs t ht)
        have h0 : dist s t = 0 := by
          by_contra hne
          have := mul_neg_of_neg_of_pos hM (lt_of_le_of_ne dist_nonneg (Ne.symm hne))
          linarith
        simp [h0]
    exact hL.uniformContinuousOn
  exact hgu.comp hyu (fun t ht => hyK t ht)

/-- v2 prop:S (iii): if a trajectory stays in a compact set and its only cluster point
at infinity is `zstar`, it converges to `zstar` (replaces LaSalle's invariance principle
once the cluster set is identified). -/
theorem tendsto_of_compact_unique_cluster {E : Type*} [TopologicalSpace E]
    {z : ℝ → E} {zstar : E} {K : Set E} (hK : IsCompact K)
    (hzK : ∀ t, 0 ≤ t → z t ∈ K)
    (hcl : ∀ w, MapClusterPt w atTop z → w = zstar) :
    Tendsto z atTop (𝓝 zstar) := by
  refine hK.tendsto_nhds_of_unique_mapClusterPt ?_ (fun w _ hw => hcl w hw)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht using hzK t ht

end SparseSGD.Logistic.V2
