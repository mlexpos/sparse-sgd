import SparseSGD.Logistic.V2.RecursionContraction
import SparseSGD.Logistic.V2.LyapunovCertificate
import SparseSGD.Logistic.ContinuousBootstrap
import SparseSGD.Logistic.V2.GlobalConvergence
import SparseSGD.Logistic.V2.Hurwitz
import SparseSGD.Logistic.DynamicParameters

/-! # v2 prop:S (iii): uniform exponential rate on compacts and uniform entry

New (v2) results; nothing here replaces a v1 declaration.  `SourceAssumptionS` (v1) quantifies
over all physical initial states with constants independent of the initial state; the results
below give uniform constants only for initial states in a compact set `K` and parameters in a
compact `Pset`, so they do not imply `SourceAssumptionS`.

* `local_exponential_stability` (T1, generic): local exponential decay for any field with a
  Lyapunov-certified linearization, via the quadratic form `W = (y - y*)ᵀ P (y - y*)`.
* `local_exponential_stability_uniform` / `_uniform_o` (T1, parametric): uniform `ρ, κ, C` over
  a compact parameter set, using `certificate_robust` and a finite subcover.
* `positiveRoot_continuousOn`, `canonicalEquilibrium_continuousOn` (T2).
* `prop_S_iii_proportional` (T4) and `prop_S_iii` (T3): `‖y t - y*(q)‖ ≤ C e^{-c t} ‖y 0 - y*(q)‖`
  and `≤ C e^{-c t}` for `y 0 ∈ K`, `q ∈ Pset`.  Proof: solutions from the data enter the
  uniform local-stability ball at some time (`prop_S_i`); Grönwall on a compact box where the
  field is Lipschitz keeps nearby data and parameters in the ball at the same time; finite
  subcover.
* `dynamicField_uniformEntry` (T5): `UniformEntry` of `RecursionContraction`, for fixed
  parameters and compact `K`.

Differences from the tex: the generic local statement assumes `HasFDerivAt` (implied by
`HasStrictFDerivAt`); the proof of the uniform local step uses robustness of Lyapunov
certificates (not continuity of eigenvalues), joint `C^1` regularity of the field for
`delta > 0`, and continuity of `y*` in the parameters. -/

namespace SparseSGD.Logistic.V2
noncomputable section

open Matrix Filter Topology Set
open SparseSGD.Logistic.V2.RecursionContraction

section Generic

variable {n : ℕ}

/-- Derivative of the quadratic form `z ⬝ P z` along a path, for symmetric `P`. -/
lemma hasDerivAt_quadForm (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P)
    (z : ℝ → Fin n → ℝ) (z' : Fin n → ℝ) (t : ℝ) (hz : HasDerivAt z z' t) :
    HasDerivAt (fun s => z s ⬝ᵥ (P *ᵥ z s)) (2 * (z t ⬝ᵥ (P *ᵥ z'))) t := by
  have hc := hasDerivAt_pi.1 hz
  have h : HasDerivAt (fun s => ∑ i, ∑ j, z s i * (P i j * z s j))
      (∑ i, ∑ j, (z' i * (P i j * z t j) + z t i * (P i j * z' j))) t := by
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
    exact (hc i).mul (((hc j).const_mul (P i j)))
  convert h using 1
  · funext s
    simp [dotProduct, mulVec, Finset.mul_sum]
  · have hsw : z' ⬝ᵥ (P *ᵥ z t) = z t ⬝ᵥ (P *ᵥ z') := qf_sym P hP z' (z t)
    have e1 : z' ⬝ᵥ (P *ᵥ z t) = ∑ i, ∑ j, z' i * (P i j * z t j) := by
      simp [dotProduct, mulVec, Finset.mul_sum]
    have e2 : z t ⬝ᵥ (P *ᵥ z') = ∑ i, ∑ j, z t i * (P i j * z' j) := by
      simp [dotProduct, mulVec, Finset.mul_sum]
    simp only [Finset.sum_add_distrib]
    rw [← e1, ← e2, hsw]; ring


/-- The Lyapunov rate `W' ≤ -(c/(2S)) W` for the quadratic form of a certificate, under a
linear-plus-small remainder bound. -/
lemma quadForm_dissipation (A P : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 < c)
    (hPs : Pᵀ = P)
    (hdec : ∀ x : Fin n → ℝ, x ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x) ≤ -c * (x ⬝ᵥ x))
    (z v : Fin n → ℝ)
    (hv : ‖v - A *ᵥ z‖ ≤ (c / (4 * (absSum P + 1))) * ‖z‖) :
    2 * (z ⬝ᵥ (P *ᵥ v)) ≤ -(c / (2 * (absSum P + 1))) * (z ⬝ᵥ (P *ᵥ z)) := by
  set S := absSum P + 1 with hS
  have hS1 : 1 ≤ S := by have := absSum_nonneg P; linarith
  have hSpos : 0 < S := by linarith
  set e := v - A *ᵥ z with he
  have hve : v = A *ᵥ z + e := by rw [he]; abel
  have hsw : (A *ᵥ z) ⬝ᵥ (P *ᵥ z) = z ⬝ᵥ (P *ᵥ (A *ᵥ z)) := qf_sym P hPs _ z |>.symm ▸ (qf_sym P hPs (A *ᵥ z) z)
  have hM : z ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ z) = 2 * (z ⬝ᵥ (P *ᵥ (A *ᵥ z))) := by
    rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
      vecMul_transpose, hsw]
    ring
  have h1 : 2 * (z ⬝ᵥ (P *ᵥ v)) = z ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ z) + 2 * (z ⬝ᵥ (P *ᵥ e)) := by
    rw [hve, hM, mulVec_add, dotProduct_add]; ring
  have h2 : z ⬝ᵥ (P *ᵥ e) ≤ absSum P * ‖z‖ * ‖e‖ := (le_abs_self _).trans (abs_bil_le P z e)
  have hz2 : ‖z‖ ^ 2 ≤ z ⬝ᵥ z := norm_sq_le_dot z
  have hW : z ⬝ᵥ (P *ᵥ z) ≤ S * ‖z‖ ^ 2 := by
    have := abs_bil_le P z z
    have h3 := (le_abs_self _).trans this
    nlinarith [sq_nonneg ‖z‖]
  have hzn : 0 ≤ ‖z‖ := norm_nonneg z
  have hP0 := absSum_nonneg P
  have h4 : absSum P * ‖z‖ * ‖e‖ ≤ absSum P * ‖z‖ * ((c / (4 * S)) * ‖z‖) :=
    mul_le_mul_of_nonneg_left hv (by positivity)
  have h5 : absSum P * (c / (4 * S)) ≤ c / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h6 : 2 * (z ⬝ᵥ (P *ᵥ e)) ≤ (c / 2) * ‖z‖ ^ 2 := by
    have : absSum P * ‖z‖ * ((c / (4 * S)) * ‖z‖) =
        (absSum P * (c / (4 * S))) * ‖z‖ ^ 2 := by ring
    nlinarith [sq_nonneg ‖z‖]
  have h7 := hdec z
  have h8 : z ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ z) + 2 * (z ⬝ᵥ (P *ᵥ e)) ≤ -(c / 2) * (z ⬝ᵥ z) := by
    nlinarith
  rw [h1]
  refine h8.trans ?_
  have hxx : z ⬝ᵥ (P *ᵥ z) ≤ S * (z ⬝ᵥ z) := by nlinarith
  have : -(c / (2 * S)) * (z ⬝ᵥ (P *ᵥ z)) ≥ -(c / (2 * S)) * (S * (z ⬝ᵥ z)) := by
    apply mul_le_mul_of_nonpos_left hxx
    have : 0 < c / (2 * S) := by positivity
    linarith
  have e3 : -(c / (2 * S)) * (S * (z ⬝ᵥ z)) = -(c / 2) * (z ⬝ᵥ z) := by
    field_simp
  linarith

/-- Core local exponential decay (v2 prop:S (iii), proof of the local step).  If `(P, c)` is a
Lyapunov certificate of `A` and `f y = A (y - ystar) + e` with `‖e‖ ≤ (c/(4S)) ‖y - ystar‖` on
`‖y - ystar‖ ≤ r0` (`S = absSum P + 1`), then every solution starting in the ball of radius
`r0/(2S)` decays like `S exp(-(c/(4S)) t)`. -/
theorem local_decay_core (A P : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 < c)
    (hPs : Pᵀ = P) (hge : ∀ x : Fin n → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ (P *ᵥ x))
    (hdec : ∀ x : Fin n → ℝ, x ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x) ≤ -c * (x ⬝ᵥ x))
    (f : (Fin n → ℝ) → (Fin n → ℝ)) (ystar : Fin n → ℝ) (r0 : ℝ) (hr0 : 0 < r0)
    (hrem : ∀ y, ‖y - ystar‖ ≤ r0 →
      ‖f y - A *ᵥ (y - ystar)‖ ≤ (c / (4 * (absSum P + 1))) * ‖y - ystar‖)
    (y : ℝ → Fin n → ℝ) (hy : ∀ t, 0 ≤ t → HasDerivAt y (f (y t)) t)
    (h0 : ‖y 0 - ystar‖ ≤ r0 / (2 * (absSum P + 1))) :
    ∀ t, 0 ≤ t → ‖y t - ystar‖ ≤
      (absSum P + 1) * Real.exp (-(c / (4 * (absSum P + 1))) * t) * ‖y 0 - ystar‖ := by
  set S := absSum P + 1 with hS
  have hP0 := absSum_nonneg P
  have hS1 : 1 ≤ S := by linarith
  have hSpos : 0 < S := by linarith
  set z : ℝ → Fin n → ℝ := fun t => y t - ystar with hz
  set W : ℝ → ℝ := fun t => z t ⬝ᵥ (P *ᵥ z t) with hW
  have hzd : ∀ t, 0 ≤ t → HasDerivAt z (f (y t)) t := fun t ht => (hy t ht).sub_const ystar
  have hWd : ∀ t, 0 ≤ t → HasDerivAt W (2 * (z t ⬝ᵥ (P *ᵥ f (y t)))) t :=
    fun t ht => hasDerivAt_quadForm P hPs z _ t (hzd t ht)
  have hWlow : ∀ t, ‖z t‖ ^ 2 ≤ W t := fun t => (norm_sq_le_dot (z t)).trans (hge _)
  have hWup : ∀ t, W t ≤ S * ‖z t‖ ^ 2 := by
    intro t
    have h3 := (le_abs_self _).trans (abs_bil_le P (z t) (z t))
    show z t ⬝ᵥ (P *ᵥ z t) ≤ _
    nlinarith [sq_nonneg ‖z t‖]
  have hWnn : ∀ t, 0 ≤ W t := fun t => (sq_nonneg _).trans (hWlow t)
  have hdiss : ∀ t, 0 ≤ t → ‖z t‖ ≤ r0 →
      2 * (z t ⬝ᵥ (P *ᵥ f (y t))) ≤ -(c / (2 * S)) * W t := by
    intro t ht hzt
    refine quadForm_dissipation A P c hc hPs hdec (z t) (f (y t)) ?_
    exact hrem (y t) hzt
  have hW0 : W 0 ≤ r0 ^ 2 / 4 := by
    have h1 := hWup 0
    have h2 : ‖z 0‖ ≤ r0 / (2 * S) := h0
    have h3 : ‖z 0‖ ^ 2 ≤ (r0 / (2 * S)) ^ 2 := by gcongr
    have h4 : S * (r0 / (2 * S)) ^ 2 = r0 ^ 2 / (4 * S) := by field_simp; ring
    have h5 : r0 ^ 2 / (4 * S) ≤ r0 ^ 2 / 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    nlinarith
  -- phase 1: no escape
  have hcontW : ∀ T, ContinuousOn W (Icc 0 T) := fun T t ht =>
    (hWd t ht.1).continuousAt.continuousWithinAt
  have hbound : ∀ t, 0 ≤ t → W t ≤ r0 ^ 2 := by
    intro T hT
    have := continuous_norm_no_escape (E := ℝ) W T (r0 ^ 2) (W 0) hT (hcontW T)
      (by rw [Real.norm_eq_abs, abs_of_nonneg (hWnn 0)]; nlinarith [sq_pos_of_pos hr0])
      (by nlinarith [sq_pos_of_pos hr0]) (by
        intro t ht hpre
        have hz' : ∀ s ∈ Icc 0 t, ‖z s‖ ≤ r0 := by
          intro s hs
          have := hpre s hs
          rw [Real.norm_eq_abs, abs_of_nonneg (hWnn s)] at this
          have h' : ‖z s‖ ^ 2 ≤ r0 ^ 2 := (hWlow s).trans this
          exact le_of_sq_le_sq h' hr0.le |>.trans le_rfl
        have hanti : AntitoneOn W (Icc 0 t) := by
          refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t)
            (hcontW t) (f' := fun s => 2 * (z s ⬝ᵥ (P *ᵥ f (y s)))) ?_ ?_
          · intro s hs
            have hs' := interior_subset hs
            exact (hWd s hs'.1).hasDerivWithinAt
          · intro s hs
            have hs' := interior_subset hs
            have := hdiss s hs'.1 (hz' s hs')
            have : 0 ≤ (c / (2 * S)) * W s := by have := hWnn s; positivity
            nlinarith [hdiss s hs'.1 (hz' s hs')]
        have := hanti ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
        rw [Real.norm_eq_abs, abs_of_nonneg (hWnn t)]
        exact this)
    have h := this T ⟨hT, le_rfl⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hWnn T)] at h
    exact h
  have hzr : ∀ t, 0 ≤ t → ‖z t‖ ≤ r0 := fun t ht =>
    le_of_sq_le_sq ((hWlow t).trans (hbound t ht)) hr0.le
  -- phase 2: exponential decay of W
  set k : ℝ := c / (2 * S) with hk
  have hkpos : 0 < k := by positivity
  set φ : ℝ → ℝ := fun t => Real.exp (k * t) * W t with hφ
  have hφd : ∀ t, 0 ≤ t → HasDerivAt φ (Real.exp (k * t) * (k * W t +
      2 * (z t ⬝ᵥ (P *ᵥ f (y t))))) t := by
    intro t ht
    have he : HasDerivAt (fun t : ℝ => Real.exp (k * t)) (Real.exp (k * t) * k) t := by
      simpa using ((hasDerivAt_id t).const_mul k).exp
    convert he.mul (hWd t ht) using 1
    ring
  have hφanti : AntitoneOn φ (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (f' := fun t =>
      Real.exp (k * t) * (k * W t + 2 * (z t ⬝ᵥ (P *ᵥ f (y t))))) ?_ ?_ ?_
    · intro t ht; exact (hφd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hφd t (le_of_lt ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have := hdiss t (le_of_lt ht) (hzr t (le_of_lt ht))
      have h2 : k * W t + 2 * (z t ⬝ᵥ (P *ᵥ f (y t))) ≤ 0 := by
        have : -(c / (2 * S)) * W t = -(k * W t) := by rw [hk]; ring
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h2
  intro t ht
  have hφt : φ t ≤ φ 0 := hφanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  have hφ0 : φ 0 = W 0 := by simp [hφ]
  have hWt : W t ≤ Real.exp (-(k * t)) * W 0 := by
    have : Real.exp (k * t) * W t ≤ W 0 := by rw [← hφ0]; exact hφt
    have h2 : W t = Real.exp (-(k * t)) * (Real.exp (k * t) * W t) := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
  have hfin : ‖z t‖ ^ 2 ≤ (S * Real.exp (-(c / (4 * S)) * t) * ‖z 0‖) ^ 2 := by
    have h1 : ‖z t‖ ^ 2 ≤ Real.exp (-(k * t)) * (S * ‖z 0‖ ^ 2) :=
      (hWlow t).trans (hWt.trans (mul_le_mul_of_nonneg_left (hWup 0) (Real.exp_pos _).le))
    have h2 : (S * Real.exp (-(c / (4 * S)) * t) * ‖z 0‖) ^ 2 =
        S ^ 2 * Real.exp (-(k * t)) * ‖z 0‖ ^ 2 := by
      have : Real.exp (-(c / (4 * S)) * t) ^ 2 = Real.exp (-(k * t)) := by
        rw [← Real.exp_nat_mul]
        congr 1; rw [hk]; push_cast; field_simp; ring
      calc _ = S ^ 2 * Real.exp (-(c / (4 * S)) * t) ^ 2 * ‖z 0‖ ^ 2 := by ring
        _ = _ := by rw [this]
    rw [h2]
    have h3 : S * ‖z 0‖ ^ 2 ≤ S ^ 2 * ‖z 0‖ ^ 2 := by
      have := mul_nonneg (mul_nonneg hSpos.le (sub_nonneg.2 hS1)) (sq_nonneg ‖z 0‖)
      nlinarith
    calc ‖z t‖ ^ 2 ≤ Real.exp (-(k * t)) * (S * ‖z 0‖ ^ 2) := h1
      _ ≤ Real.exp (-(k * t)) * (S ^ 2 * ‖z 0‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      _ = _ := by ring
  exact le_of_sq_le_sq hfin (by positivity)

/-- Local exponential decay with a fixed rate, constant and radius, for a field `f` with
equilibrium `ystar` and a family of states and parameters. -/
def LocalDecay {Θ : Type*} (f : Θ → (Fin n → ℝ) → (Fin n → ℝ)) (ystar : Θ → Fin n → ℝ)
    (S : Set Θ) (ρ κ C : ℝ) : Prop :=
  ∀ q ∈ S, ∀ y : ℝ → Fin n → ℝ, (∀ t, 0 ≤ t → HasDerivAt y (f q (y t)) t) →
    ‖y 0 - ystar q‖ ≤ ρ → ∀ t, 0 ≤ t →
      ‖y t - ystar q‖ ≤ C * Real.exp (-κ * t) * ‖y 0 - ystar q‖

/-- `LocalDecay` is monotone in the set, radius, rate and constant. -/
lemma LocalDecay.mono {Θ : Type*} {f : Θ → (Fin n → ℝ) → (Fin n → ℝ)}
    {ystar : Θ → Fin n → ℝ} {S S' : Set Θ} {ρ κ C ρ' κ' C' : ℝ}
    (h : LocalDecay f ystar S ρ κ C) (hS : S' ⊆ S) (hρ : ρ' ≤ ρ) (hκκ : κ' ≤ κ)
    (hC : C ≤ C') (hC0 : 0 ≤ C) : LocalDecay f ystar S' ρ' κ' C' := by
  intro q hq y hy h0 t ht
  refine (h q (hS hq) y hy (h0.trans hρ) t ht).trans ?_
  have h1 : Real.exp (-κ * t) ≤ Real.exp (-κ' * t) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h2 : C * Real.exp (-κ * t) ≤ C' * Real.exp (-κ' * t) :=
    mul_le_mul hC h1 (Real.exp_pos _).le (hC0.trans hC)
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- v2 prop:S (iii), local step (generic).  If `f ystar = 0`, `f` is differentiable at
`ystar` with derivative `toLin' A`, and `(P, c)` is a Lyapunov certificate of `A`
(`P` symmetric, `x ⬝ x ≤ x ⬝ P x`, `x ⬝ (Aᵀ P + P A) x ≤ -c x ⬝ x`), then there are `ρ, κ, C > 0`
such that every solution on `[0,∞)` with `‖y 0 - ystar‖ ≤ ρ` satisfies
`‖y t - ystar‖ ≤ C exp(-κ t) ‖y 0 - ystar‖`. -/
theorem local_exponential_stability (f : (Fin n → ℝ) → (Fin n → ℝ)) (ystar : Fin n → ℝ)
    (A P : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 < c)
    (hPs : Pᵀ = P) (hge : ∀ x : Fin n → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ (P *ᵥ x))
    (hdec : ∀ x : Fin n → ℝ, x ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x) ≤ -c * (x ⬝ᵥ x))
    (hf0 : f ystar = 0)
    (hd : HasFDerivAt f (LinearMap.toContinuousLinearMap (Matrix.toLin' A)) ystar) :
    ∃ ρ κ C : ℝ, 0 < ρ ∧ 0 < κ ∧ 0 < C ∧
      ∀ y : ℝ → Fin n → ℝ, (∀ t, 0 ≤ t → HasDerivAt y (f (y t)) t) →
        ‖y 0 - ystar‖ ≤ ρ → ∀ t, 0 ≤ t →
          ‖y t - ystar‖ ≤ C * Real.exp (-κ * t) * ‖y 0 - ystar‖ := by
  have hP0 := absSum_nonneg P
  set S := absSum P + 1 with hS
  have hSpos : 0 < S := by linarith
  have hε : 0 < c / (4 * S) := by positivity
  have hlo := hd.isLittleO.def hε
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hlo
  have hrem : ∀ y, ‖y - ystar‖ ≤ r / 2 →
      ‖f y - A *ᵥ (y - ystar)‖ ≤ (c / (4 * S)) * ‖y - ystar‖ := by
    intro y hy
    have := hball y (by rw [Metric.mem_ball, dist_eq_norm]; linarith)
    simpa [hf0, Matrix.toLin'_apply, Matrix.mulVecLin_apply] using this
  refine ⟨(r / 2) / (2 * S), c / (4 * S), S, by positivity, hε, hSpos, ?_⟩
  intro y hy h0 t ht
  exact local_decay_core A P c hc hPs hge hdec f ystar (r / 2) (by positivity) hrem y hy h0 t ht


/-- Compactness step: a locally uniform decay estimate over a compact parameter set is
uniform over the set (finite subcover, with `min`/`max` of the finitely many constants). -/
theorem localDecay_of_compact {Θ : Type*} [TopologicalSpace Θ] (Pset : Set Θ)
    (hK : IsCompact Pset) (f : Θ → (Fin n → ℝ) → (Fin n → ℝ)) (ystar : Θ → Fin n → ℝ)
    (hloc : ∀ q ∈ Pset, ∃ U ∈ 𝓝[Pset] q, ∃ ρ κ C : ℝ, 0 < ρ ∧ 0 < κ ∧ 0 < C ∧
      LocalDecay f ystar (U ∩ Pset) ρ κ C) :
    ∃ ρ κ C : ℝ, 0 < ρ ∧ 0 < κ ∧ 0 < C ∧ LocalDecay f ystar Pset ρ κ C := by
  let p : Set Θ → Prop := fun S => ∃ ρ κ C : ℝ, 0 < ρ ∧ 0 < κ ∧ 0 < C ∧
    LocalDecay f ystar (S ∩ Pset) ρ κ C
  have hp : p Pset := by
    refine hK.induction_on (p := p) ?_ ?_ ?_ hloc
    · exact ⟨1, 1, 1, one_pos, one_pos, one_pos, fun q hq => absurd hq.1 (by simp)⟩
    · rintro S T hST ⟨ρ, κ, C, hρ, hκ, hC, h⟩
      exact ⟨ρ, κ, C, hρ, hκ, hC, h.mono (inter_subset_inter_left _ hST) le_rfl le_rfl le_rfl hC.le⟩
    · rintro S T ⟨ρ, κ, C, hρ, hκ, hC, h⟩ ⟨ρ', κ', C', hρ', hκ', hC', h'⟩
      refine ⟨min ρ ρ', min κ κ', max C C', lt_min hρ hρ', lt_min hκ hκ',
        lt_max_of_lt_left hC, ?_⟩
      intro q hq y hy h0 t ht
      rcases hq.1 with hqS | hqT
      · exact (h.mono (S := S ∩ Pset) (S' := S ∩ Pset) le_rfl (min_le_left _ _)
          (min_le_left _ _) (le_max_left _ _) hC.le) q ⟨hqS, hq.2⟩ y hy h0 t ht
      · exact (h'.mono (S := T ∩ Pset) (S' := T ∩ Pset) le_rfl (min_le_right _ _)
          (min_le_right _ _) (le_max_right _ _) hC'.le) q ⟨hqT, hq.2⟩ y hy h0 t ht
  obtain ⟨ρ, κ, C, hρ, hκ, hC, h⟩ := hp
  exact ⟨ρ, κ, C, hρ, hκ, hC, h.mono (by intro q hq; exact ⟨hq, hq⟩) le_rfl le_rfl le_rfl hC.le⟩

/-- Uniformity over a compact parameter set (v2 prop:S (iii), parametric local step), with a
locally uniform little-o remainder.  `A q` is continuous on the compact set `Pset` and Hurwitz
at each parameter, and for every `q0 ∈ Pset` and `ε > 0` there is a radius `r > 0` such that
`‖f q y - A q (y - ystar q)‖ ≤ ε ‖y - ystar q‖` for `‖y - ystar q‖ ≤ r` and all `q ∈ Pset`
near `q0`.  Then `ρ, κ, C` can be chosen uniformly over `Pset`.  The certificate of `A q0` is
robust (`certificate_robust`), so it certifies `A q` for `q` near `q0`; compactness of `Pset`
picks finitely many such neighbourhoods. -/
theorem local_exponential_stability_uniform_o {Θ : Type*} [TopologicalSpace Θ] (Pset : Set Θ)
    (hK : IsCompact Pset) (f : Θ → (Fin n → ℝ) → (Fin n → ℝ)) (ystar : Θ → Fin n → ℝ)
    (A : Θ → Matrix (Fin n) (Fin n) ℝ) (hA : ContinuousOn A Pset)
    (hH : ∀ q ∈ Pset, IsHurwitz (A q))
    (hrem : ∀ q0 ∈ Pset, ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ᶠ q in 𝓝[Pset] q0, ∀ y,
      ‖y - ystar q‖ ≤ r → ‖f q y - A q *ᵥ (y - ystar q)‖ ≤ ε * ‖y - ystar q‖) :
    ∃ ρ κ C : ℝ, 0 < ρ ∧ 0 < κ ∧ 0 < C ∧ LocalDecay f ystar Pset ρ κ C := by
  refine localDecay_of_compact Pset hK f ystar fun q0 hq0 => ?_
  obtain ⟨P, c, hc, hPs, hge, hdec⟩ := exists_lyapunov_certificate (A q0) (hH q0 hq0)
  obtain ⟨η, hη, hrob⟩ := certificate_robust (A q0) P c hc hdec
  have hev : ∀ᶠ q in 𝓝[Pset] q0, ∀ i j, |A q i j - A q0 i j| ≤ η := by
    have ht : Tendsto A (𝓝[Pset] q0) (𝓝 (A q0)) := hA q0 hq0
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    have h1 : Tendsto (fun q => A q i j) (𝓝[Pset] q0) (𝓝 (A q0 i j)) :=
      ((continuous_apply j).tendsto _).comp (((continuous_apply i).tendsto _).comp ht)
    filter_upwards [Metric.tendsto_nhds.1 h1 η hη] with q hq
    rw [Real.dist_eq] at hq
    exact hq.le
  have hP0 := absSum_nonneg P
  set S := absSum P + 1 with hS
  have hSpos : 0 < S := by linarith
  set ε := (c / 2) / (4 * S) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨r1, hr1pos, hevr⟩ := hrem q0 hq0 ε hεpos
  refine ⟨{q | (∀ i j, |A q i j - A q0 i j| ≤ η) ∧ ∀ y, ‖y - ystar q‖ ≤ r1 →
    ‖f q y - A q *ᵥ (y - ystar q)‖ ≤ ε * ‖y - ystar q‖}, hev.and hevr, ?_⟩
  refine ⟨r1 / (2 * S), ε, S, by positivity, hεpos, hSpos, ?_⟩
  intro q hq y hy h0 t ht
  have hdec' := hrob (A q) hq.1.1
  exact local_decay_core (A q) P (c / 2) (by positivity) hPs hge hdec' (f q) (ystar q) r1 hr1pos
    hq.1.2 y hy h0 t ht

/-- v2 prop:S (iii), parametric local step with the quadratic remainder of the statement:
`‖f q y - A q (y - ystar q)‖ ≤ L ‖y - ystar q‖²` for `‖y - ystar q‖ ≤ r0` and all `q ∈ Pset`.
The certificate of `A q0` is robust, so the constants are uniform over the compact `Pset`. -/
theorem local_exponential_stability_uniform {Θ : Type*} [TopologicalSpace Θ] (Pset : Set Θ)
    (hK : IsCompact Pset) (f : Θ → (Fin n → ℝ) → (Fin n → ℝ)) (ystar : Θ → Fin n → ℝ)
    (A : Θ → Matrix (Fin n) (Fin n) ℝ) (hA : ContinuousOn A Pset)
    (hH : ∀ q ∈ Pset, IsHurwitz (A q))
    (r0 L : ℝ) (hr0 : 0 < r0)
    (hrem : ∀ q ∈ Pset, ∀ y, ‖y - ystar q‖ ≤ r0 →
      ‖f q y - A q *ᵥ (y - ystar q)‖ ≤ L * ‖y - ystar q‖ ^ 2) :
    ∃ ρ κ C : ℝ, 0 < ρ ∧ 0 < κ ∧ 0 < C ∧ LocalDecay f ystar Pset ρ κ C := by
  refine local_exponential_stability_uniform_o Pset hK f ystar A hA hH
    (fun q0 hq0 ε hε => ?_)
  set L' := max L 0 with hL'
  have hL'0 : 0 ≤ L' := le_max_right _ _
  set r1 := min r0 (ε / (L' + 1)) with hr1
  have hr1pos : 0 < r1 := lt_min hr0 (by positivity)
  refine ⟨r1, hr1pos, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with q hqP y hy'
  have hz : ‖y - ystar q‖ ≤ r0 := hy'.trans (min_le_left _ _)
  have hz2 : ‖y - ystar q‖ ≤ ε / (L' + 1) := hy'.trans (min_le_right _ _)
  have h1 := hrem q hqP y hz
  have hzn := norm_nonneg (y - ystar q)
  have h2 : L * ‖y - ystar q‖ ^ 2 ≤ L' * ‖y - ystar q‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  have h3 : L' * ‖y - ystar q‖ ≤ ε := by
    have : ‖y - ystar q‖ * (L' + 1) ≤ ε := by rwa [le_div_iff₀ (by positivity)] at hz2
    nlinarith
  calc _ ≤ L * ‖y - ystar q‖ ^ 2 := h1
    _ ≤ L' * ‖y - ystar q‖ ^ 2 := h2
    _ = (L' * ‖y - ystar q‖) * ‖y - ystar q‖ := by ring
    _ ≤ ε * ‖y - ystar q‖ := mul_le_mul_of_nonneg_right h3 hzn

end Generic

/-! ### Continuity of the equilibrium in the parameters -/

section Equilibrium

open SparseSGD.Logistic

/-- Continuity of `g r Phi θ` in `(r, Phi)` at `r ≠ 0`, for fixed `θ`. -/
lemma g_continuousAt_pair (θ : ℝ) (p0 : ℝ × ℝ) (hr : p0.1 ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ => g p.1 p.2 θ) p0 := by
  unfold g
  have : ContinuousAt (fun p : ℝ × ℝ => p.2 * θ / p.1) p0 :=
    (continuous_snd.continuousAt.mul continuousAt_const).div continuous_fst.continuousAt hr
  have h2 : ContinuousAt (fun p : ℝ × ℝ => (θ ^ 2 - p.1 ^ 2 + p.2 * θ / p.1) / 2) p0 := by
    have h1 : ContinuousAt (fun p : ℝ × ℝ => θ ^ 2 - p.1 ^ 2) p0 :=
      continuousAt_const.sub (continuous_fst.pow 2).continuousAt
    exact (h1.add this).div_const 2
  exact continuousAt_const.mul (Real.continuous_exp.continuousAt.comp h2)

/-- v2 prop:S (iii) (T2), continuity of the positive root: `(r, Phi) ↦ positiveRoot r Phi`
is continuous on `{r > 0, Phi ≥ 0}`.  By strict monotonicity of `g r Phi` and continuity
of `g` in `(r, Phi)` at the fixed points `θ0 ± ε` the root of nearby parameters is
trapped in `(θ0 - ε, θ0 + ε)`. -/
theorem positiveRoot_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => positiveRoot p.1 p.2) {p : ℝ × ℝ | 0 < p.1 ∧ 0 ≤ p.2} := by
  intro p0 hp0
  obtain ⟨hr0, hPhi0⟩ := hp0
  obtain ⟨hθ0, hg0⟩ := positiveRoot_spec p0.1 p0.2 hr0 hPhi0
  set θ0 := positiveRoot p0.1 p0.2 with hθ0def
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  set e := min ε (θ0 / 2) with he
  have hepos : 0 < e := lt_min hε (by positivity)
  have he1 : e ≤ ε := min_le_left _ _
  have he2 : e ≤ θ0 / 2 := min_le_right _ _
  have hmono := g_strictMonoOn_pos p0.1 p0.2 hr0 hPhi0
  have hlo : g p0.1 p0.2 (θ0 - e) < p0.1 := by
    have := hmono (Set.mem_Ioi.2 (by linarith : 0 < θ0 - e)) (Set.mem_Ioi.2 hθ0)
      (by linarith : θ0 - e < θ0)
    linarith
  have hhi : p0.1 < g p0.1 p0.2 (θ0 + e) := by
    have := hmono (Set.mem_Ioi.2 hθ0) (Set.mem_Ioi.2 (by linarith : 0 < θ0 + e))
      (by linarith : θ0 < θ0 + e)
    linarith
  have c1 := (g_continuousAt_pair (θ0 - e) p0 hr0.ne').eventually_lt
    (continuous_fst.continuousAt (x := p0)) hlo
  have c2 := (continuous_fst.continuousAt (x := p0)).eventually_lt
    (g_continuousAt_pair (θ0 + e) p0 hr0.ne') hhi
  have hD : ∀ᶠ p in 𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 ≤ p.2}] p0, 0 < p.1 ∧ 0 ≤ p.2 :=
    self_mem_nhdsWithin
  filter_upwards [nhdsWithin_le_nhds c1, nhdsWithin_le_nhds c2, hD] with p h1 h2 hpD
  obtain ⟨hθp, hgp⟩ := positiveRoot_spec p.1 p.2 hpD.1 hpD.2
  have hmp := g_strictMonoOn_pos p.1 p.2 hpD.1 hpD.2
  rw [Real.dist_eq, abs_lt]
  constructor
  · by_contra hcon
    push Not at hcon
    have : positiveRoot p.1 p.2 ≤ θ0 - e := by linarith
    have := hmp.monotoneOn (Set.mem_Ioi.2 hθp) (Set.mem_Ioi.2 (by linarith : 0 < θ0 - e)) this
    linarith
  · by_contra hcon
    push Not at hcon
    have : θ0 + e ≤ positiveRoot p.1 p.2 := by linarith
    have := hmp.monotoneOn (Set.mem_Ioi.2 (by linarith : 0 < θ0 + e)) (Set.mem_Ioi.2 hθp) this
    linarith


/-- The parameter domain `{delta > 0, Phi ≥ 0, r > 0}`, with parameters ordered `(delta, Phi, r)`
as in `SourceAssumptionS`. -/
def paramDomain : Set (ℝ × ℝ × ℝ) := {q | 0 < q.1 ∧ 0 ≤ q.2.1 ∧ 0 < q.2.2}

/-- v2 prop:S (iii) (T2): the canonical equilibrium `y*(q)` is continuous in the parameters
`q = (delta, Phi, r)` on `{delta > 0, Phi ≥ 0, r > 0}`. -/
theorem canonicalEquilibrium_continuousOn :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1)
      paramDomain := by
  have hroot : ContinuousOn (fun q : ℝ × ℝ × ℝ => positiveRoot q.2.2 q.2.1) paramDomain := by
    have h1 : ContinuousOn (fun q : ℝ × ℝ × ℝ => (q.2.2, q.2.1)) paramDomain := by fun_prop
    exact positiveRoot_continuousOn.comp h1 (fun q hq => ⟨hq.2.2, hq.2.1⟩)
  apply continuousOn_pi.2
  intro i
  fin_cases i
  · simpa [dynamicCanonicalEquilibrium] using hroot
  · simp [dynamicCanonicalEquilibrium]; exact continuousOn_const
  · simp only [dynamicCanonicalEquilibrium, equilibriumBulk]
    have : ContinuousOn (fun q : ℝ × ℝ × ℝ => q.2.1 * positiveRoot q.2.2 q.2.1) paramDomain :=
      (by fun_prop : ContinuousOn (fun q : ℝ × ℝ × ℝ => q.2.1) paramDomain).mul hroot
    exact this.div (by fun_prop) (fun q hq => hq.2.2.ne') |>.congr (fun q _ => by simp)
  · simp only [dynamicCanonicalEquilibrium]
    exact (by fun_prop : ContinuousOn (fun q : ℝ × ℝ × ℝ => q.2.1) paramDomain).div
      (by fun_prop) (fun q hq => hq.1.ne') |>.congr (fun q _ => by simp)
  · simp [dynamicCanonicalEquilibrium]; exact continuousOn_const

end Equilibrium


/-! ### The field as a function of state and parameters -/

section Joint

open SparseSGD.Logistic
open scoped NNReal

/-- The LR5 field as a function of the pair `(q, y)` with `q = (delta, Phi, r)`. -/
def jointField (x : (ℝ × ℝ × ℝ) × DynamicState) : DynamicState :=
  dynamicField x.1.2.2 x.1.1 x.1.2.1 x.2

/-- Unfolding of `jointField`. -/
lemma jointField_apply (q : ℝ × ℝ × ℝ) (y : DynamicState) :
    jointField (q, y) = dynamicField q.2.2 q.1 q.2.1 y := rfl

/-- The joint field is smooth on `{delta > 0}`. -/
theorem contDiffOn_jointField :
    ContDiffOn ℝ ⊤ jointField {x | 0 < x.1.1} := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i <;> simp [jointField, dynamicField, dynamicAlpha]
  · fun_prop
  · fun_prop
  · fun_prop
  · have h : ContDiffOn ℝ ⊤ (fun x : (ℝ × ℝ × ℝ) × DynamicState => 2 * x.1.2.1 / x.1.1)
        {x | 0 < x.1.1} :=
      ContDiffOn.div (by fun_prop) (by fun_prop) (fun x hx => (ne_of_gt hx))
    have h2 : ContDiffOn ℝ ⊤ (fun x : (ℝ × ℝ × ℝ) × DynamicState =>
        -(2 * x.2 3) + 2 * Real.exp ((x.2 0 ^ 2 + x.2 2 - x.1.2.2 ^ 2) / 2) * x.2 4)
        {x | 0 < x.1.1} := by fun_prop
    exact h2.add h
  · fun_prop

/-- The joint field is Lipschitz on a compact box of parameters (`delta ≥ δ1 > 0`) and states. -/
theorem jointField_lipschitz (δ1 δ2 Φ1 Φ2 r1 r2 M : ℝ) (hδ1 : 0 < δ1) :
    ∃ L : ℝ≥0, LipschitzOnWith L jointField
      ((Set.Icc δ1 δ2 ×ˢ (Set.Icc Φ1 Φ2 ×ˢ Set.Icc r1 r2)) ×ˢ Metric.closedBall (0 : DynamicState) M) := by
  have hc : IsCompact ((Set.Icc δ1 δ2 ×ˢ (Set.Icc Φ1 Φ2 ×ˢ Set.Icc r1 r2)) ×ˢ
      Metric.closedBall (0 : DynamicState) M) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod (isCompact_closedBall 0 M)
  have hv : Convex ℝ ((Set.Icc δ1 δ2 ×ˢ (Set.Icc Φ1 Φ2 ×ˢ Set.Icc r1 r2)) ×ˢ
      Metric.closedBall (0 : DynamicState) M) :=
    ((convex_Icc δ1 δ2).prod ((convex_Icc Φ1 Φ2).prod (convex_Icc r1 r2))).prod
      (convex_closedBall 0 M)
  have hsub : ((Set.Icc δ1 δ2 ×ˢ (Set.Icc Φ1 Φ2 ×ˢ Set.Icc r1 r2)) ×ˢ
      Metric.closedBall (0 : DynamicState) M) ⊆ {x : (ℝ × ℝ × ℝ) × DynamicState | 0 < x.1.1} := by
    intro x hx
    exact lt_of_lt_of_le hδ1 hx.1.1.1
  exact (contDiffOn_jointField.mono hsub).exists_lipschitzOnWith (by simp) hv hc

/-- `gronwallBound` is at most `(δ + ε x) exp (K x)` for `K, ε ≥ 0`. -/
lemma gronwallBound_le_aux (δ K ε x : ℝ) (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound δ K ε x ≤ (δ + ε * x) * Real.exp (K * x) := by
  rcases hK.eq_or_lt with h0 | hpos
  · subst h0
    rw [gronwallBound_K0]
    simp
  · rw [gronwallBound_of_K_ne_0 hpos.ne']
    have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
      have := Real.add_one_le_exp (-(K * x))
      have h2 : Real.exp (K * x) * Real.exp (-(K * x)) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (K * x)]
    have h3 : ε / K * (Real.exp (K * x) - 1) ≤ ε / K * (K * x * Real.exp (K * x)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : ε / K * (K * x * Real.exp (K * x)) = ε * x * Real.exp (K * x) := by
      field_simp
    nlinarith

/-- Continuous dependence on data and parameters, by Grönwall: two solutions of the field, with
parameters `q` and `q'`, that stay in a set `B` on which `jointField` is `L`-Lipschitz,
satisfy `‖y' t - y t‖ ≤ (‖y' 0 - y 0‖ + L ‖q' - q‖ t) exp (L t)`. -/
theorem compare_solutions (L : ℝ) (hL : 0 ≤ L)
    (B : Set ((ℝ × ℝ × ℝ) × DynamicState))
    (hLip : ∀ x ∈ B, ∀ x' ∈ B, ‖jointField x - jointField x'‖ ≤ L * ‖x - x'‖)
    (q q' : ℝ × ℝ × ℝ) (y y' : ℝ → DynamicState) (T : ℝ)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (dynamicField q.2.2 q.1 q.2.1 (y t)) t)
    (hy' : ∀ t ∈ Set.Icc 0 T, HasDerivAt y' (dynamicField q'.2.2 q'.1 q'.2.1 (y' t)) t)
    (hB : ∀ t ∈ Set.Icc 0 T, (q, y t) ∈ B ∧ (q', y' t) ∈ B) :
    ∀ t ∈ Set.Icc 0 T, ‖y' t - y t‖ ≤ (‖y' 0 - y 0‖ + L * ‖q' - q‖ * t) * Real.exp (L * t) := by
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun t => y' t - y t)
    (f' := fun t => dynamicField q'.2.2 q'.1 q'.2.1 (y' t) - dynamicField q.2.2 q.1 q.2.1 (y t))
    (a := 0) (b := T) (δ := ‖y' 0 - y 0‖) (K := L) (ε := L * ‖q' - q‖)
    (fun t ht => ((hy' t ht).sub (hy t ht)).continuousAt.continuousWithinAt)
    (fun t ht => (((hy' t (Set.Ico_subset_Icc_self ht)).sub
      (hy t (Set.Ico_subset_Icc_self ht))).hasDerivWithinAt))
    le_rfl (by
      intro t ht
      have ht' : t ∈ Set.Icc 0 T := Set.Ico_subset_Icc_self ht
      have h1 := hLip _ (hB t ht').2 _ (hB t ht').1
      have h2 : ‖((q', y' t) : (ℝ × ℝ × ℝ) × DynamicState) - (q, y t)‖ ≤
          ‖q' - q‖ + ‖y' t - y t‖ := by
        rw [Prod.norm_def]
        simp only [Prod.fst_sub, Prod.snd_sub]
        exact max_le (by linarith [norm_nonneg (y' t - y t)])
          (by linarith [norm_nonneg (q' - q)])
      have h3 := mul_le_mul_of_nonneg_left h2 hL
      simp only [jointField_apply] at h1
      linarith)
  intro t ht
  have := hg t ht
  refine this.trans ?_
  have h := gronwallBound_le_aux ‖y' 0 - y 0‖ L (L * ‖q' - q‖) (t - 0) hL (by positivity)
  simpa using h


/-- The Jacobian of the field at the equilibrium `y*(q)`, as a function of `q`. -/
def eqJacobian (q : ℝ × ℝ × ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  jacobianMatrix (dynamicAlpha q.2.2 (dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1))
    (positiveRoot q.2.2 q.2.1) (equilibriumBulk q.2.2 q.2.1) q.1

/-- Continuity of the equilibrium Jacobian in the parameters (v2 prop:S (iii)). -/
theorem eqJacobian_continuousOn : ContinuousOn eqJacobian paramDomain := by
  have hy := canonicalEquilibrium_continuousOn
  have hroot : ContinuousOn (fun q : ℝ × ℝ × ℝ => positiveRoot q.2.2 q.2.1) paramDomain := by
    have h1 : ContinuousOn (fun q : ℝ × ℝ × ℝ => (q.2.2, q.2.1)) paramDomain := by fun_prop
    exact positiveRoot_continuousOn.comp h1 (fun q hq => ⟨hq.2.2, hq.2.1⟩)
  have hR : ContinuousOn (fun q : ℝ × ℝ × ℝ => equilibriumBulk q.2.2 q.2.1) paramDomain := by
    unfold equilibriumBulk
    exact ((by fun_prop : ContinuousOn (fun q : ℝ × ℝ × ℝ => q.2.1) paramDomain).mul hroot).div
      (by fun_prop) (fun q hq => hq.2.2.ne')
  have hy0 : ContinuousOn (fun q : ℝ × ℝ × ℝ => (dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1) 0)
      paramDomain := (continuous_apply 0).comp_continuousOn hy
  have hy2 : ContinuousOn (fun q : ℝ × ℝ × ℝ => (dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1) 2)
      paramDomain := (continuous_apply 2).comp_continuousOn hy
  have ha : ContinuousOn (fun q : ℝ × ℝ × ℝ =>
      dynamicAlpha q.2.2 (dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1)) paramDomain := by
    unfold dynamicAlpha
    have : ContinuousOn (fun q : ℝ × ℝ × ℝ =>
        ((dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1) 0 ^ 2 +
          (dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1) 2 - q.2.2 ^ 2) / 2) paramDomain := by
      fun_prop
    exact Real.continuous_exp.comp_continuousOn this
  apply continuousOn_pi.2
  intro i
  apply continuousOn_pi.2
  intro j
  fin_cases i <;> fin_cases j <;> simp [eqJacobian, jacobianMatrix] <;> first
    | exact continuousOn_const
    | fun_prop


/-- The domain `delta > 0` of smoothness of the joint field is open. -/
lemma isOpen_delta_pos : IsOpen {x : (ℝ × ℝ × ℝ) × DynamicState | 0 < x.1.1} :=
  isOpen_lt continuous_const (by fun_prop)

/-- The partial derivative of the joint field in the state variable. -/
theorem hasFDerivAt_jointField_state (q : ℝ × ℝ × ℝ) (hq : 0 < q.1) (y : DynamicState) :
    HasFDerivAt (dynamicField q.2.2 q.1 q.2.1)
      ((fderiv ℝ jointField (q, y)).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) DynamicState)) y := by
  have hd : DifferentiableAt ℝ jointField (q, y) :=
    (contDiffOn_jointField.differentiableOn (by simp)).differentiableAt
      (isOpen_delta_pos.mem_nhds hq)
  exact hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right q y)

/-- v2 prop:S (iii), locally uniform little-o remainder at the equilibrium: for every
`q0 ∈ {delta > 0, Phi ≥ 0, r > 0}` and `ε > 0` there is a radius `r > 0` such that, for all
parameters `q` of the domain near `q0`, `‖f_q(y) - J(q)(y - y*(q))‖ ≤ ε ‖y - y*(q)‖` whenever
`‖y - y*(q)‖ ≤ r`.  Joint continuity of the derivative of the field (smooth for `delta > 0`)
and of `y*(q)` replace a uniform second-derivative bound. -/
theorem dynamicField_remainder_uniform (q0 : ℝ × ℝ × ℝ) (hq0 : q0 ∈ paramDomain)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ q in 𝓝[paramDomain] q0, ∀ y : DynamicState,
      ‖y - dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1‖ ≤ r →
        ‖dynamicField q.2.2 q.1 q.2.1 y -
            eqJacobian q *ᵥ (y - dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1)‖ ≤
          ε * ‖y - dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1‖ := by
  set ys : (ℝ × ℝ × ℝ) → DynamicState := fun q => dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1
    with hys
  have hysc : ContinuousOn ys paramDomain := canonicalEquilibrium_continuousOn
  have hDc : ContinuousOn (fun x => fderiv ℝ jointField x) {x | 0 < x.1.1} :=
    contDiffOn_jointField.continuousOn_fderiv_of_isOpen isOpen_delta_pos (by simp)
  set x0 : (ℝ × ℝ × ℝ) × DynamicState := (q0, ys q0) with hx0
  have hDx0 : ContinuousAt (fun x => fderiv ℝ jointField x) x0 :=
    hDc.continuousAt (isOpen_delta_pos.mem_nhds hq0.1)
  obtain ⟨η, hη, hDη⟩ := Metric.continuousAt_iff.1 hDx0 (ε / 2) (by positivity)
  refine ⟨η / 4, by positivity, ?_⟩
  have h1 : ∀ᶠ q in 𝓝[paramDomain] q0, dist q q0 < η := by
    have : ∀ᶠ q in 𝓝 q0, dist q q0 < η := Metric.ball_mem_nhds q0 hη
    exact nhdsWithin_le_nhds this
  have h2 : ∀ᶠ q in 𝓝[paramDomain] q0, dist (ys q) (ys q0) < η / 2 :=
    Metric.tendsto_nhds.1 (hysc q0 hq0) (η / 2) (by positivity)
  filter_upwards [h1, h2, self_mem_nhdsWithin] with q hq1 hq2 hqD y hy
  have hbound : ∀ z : DynamicState, ‖z - ys q‖ ≤ η / 4 →
      ‖(fderiv ℝ jointField (q, z)).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) DynamicState) -
        (fderiv ℝ jointField (q, ys q)).comp
          (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) DynamicState)‖ ≤ ε := by
    intro z hz
    have hd1 : dist (q, z) x0 < η := by
      rw [Prod.dist_eq, max_lt_iff]
      refine ⟨by simpa [hx0] using hq1, ?_⟩
      show dist z (ys q0) < η
      rw [dist_eq_norm] at hq2 ⊢
      calc ‖z - ys q0‖ = ‖(z - ys q) + (ys q - ys q0)‖ := by congr 1; abel
        _ ≤ ‖z - ys q‖ + ‖ys q - ys q0‖ := norm_add_le _ _
        _ < η := by linarith
    have hd2 : dist (q, ys q) x0 < η := by
      rw [Prod.dist_eq, max_lt_iff]
      refine ⟨by simpa [hx0] using hq1, ?_⟩
      show dist (ys q) (ys q0) < η
      linarith
    have e1 := hDη hd1
    have e2 := hDη hd2
    rw [dist_eq_norm] at e1 e2
    rw [← ContinuousLinearMap.sub_comp]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hin : ‖ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) DynamicState‖ ≤ 1 :=
      ContinuousLinearMap.norm_inr_le_one ℝ _ _
    have hsub : ‖fderiv ℝ jointField (q, z) - fderiv ℝ jointField (q, ys q)‖ ≤ ε := by
      calc _ = ‖(fderiv ℝ jointField (q, z) - fderiv ℝ jointField x0) -
            (fderiv ℝ jointField (q, ys q) - fderiv ℝ jointField x0)‖ := by congr 1; abel
        _ ≤ ‖fderiv ℝ jointField (q, z) - fderiv ℝ jointField x0‖ +
            ‖fderiv ℝ jointField (q, ys q) - fderiv ℝ jointField x0‖ := norm_sub_le _ _
        _ ≤ ε := by linarith
    calc _ ≤ ‖fderiv ℝ jointField (q, z) - fderiv ℝ jointField (q, ys q)‖ * 1 :=
          mul_le_mul_of_nonneg_left hin (norm_nonneg _)
      _ ≤ ε := by linarith
  -- equality of the derivative at the equilibrium with the explicit Jacobian
  set M : DynamicState →L[ℝ] DynamicState :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' (eqJacobian q)) with hM
  have hMeq : (fderiv ℝ jointField (q, ys q)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) DynamicState) = M := by
    have h1 := hasFDerivAt_jointField_state q hqD.1 (ys q)
    have h2 := hasFDerivAt_dynamicField_equilibrium q.2.2 q.1 q.2.1
    exact h1.unique h2
  -- mean value inequality for `g z = f z - M z` on the closed ball
  have hg : ∀ z ∈ Metric.closedBall (ys q) (η / 4),
      HasFDerivWithinAt (fun z => dynamicField q.2.2 q.1 q.2.1 z - M z)
        (((fderiv ℝ jointField (q, z)).comp
          (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) DynamicState)) - M) (Metric.closedBall (ys q) (η / 4)) z := by
    intro z _
    exact ((hasFDerivAt_jointField_state q hqD.1 z).sub M.hasFDerivAt).hasFDerivWithinAt
  have hbd : ∀ z ∈ Metric.closedBall (ys q) (η / 4),
      ‖((fderiv ℝ jointField (q, z)).comp
          (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) DynamicState)) - M‖ ≤ ε := by
    intro z hz
    rw [← hMeq]
    exact hbound z (by simpa [dist_eq_norm] using hz)
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hg hbd
    (convex_closedBall (ys q) (η / 4)) (Metric.mem_closedBall_self (by positivity))
    (show y ∈ Metric.closedBall (ys q) (η / 4) by simpa [dist_eq_norm] using hy)
  have hstat : dynamicField q.2.2 q.1 q.2.1 (ys q) = 0 :=
    dynamicCanonicalEquilibrium_is_stationary q.2.2 q.1 q.2.1 hqD.2.2 hqD.1 hqD.2.1
  have hMv : M (y - ys q) = eqJacobian q *ᵥ (y - ys q) := by
    simp [hM, Matrix.toLin'_apply]
  simp only [hstat, zero_sub] at hmv
  rw [← hMv]
  have : dynamicField q.2.2 q.1 q.2.1 y - M y - (-M (ys q)) =
      dynamicField q.2.2 q.1 q.2.1 y - M (y - ys q) := by
    rw [map_sub]; abel
  rw [this] at hmv
  simpa [dist_eq_norm] using hmv


/-- v2 prop:S (iii), local step for the LR5 field, uniform over compact parameter sets: there are
`ρ, κ, C > 0` such that every solution of `dynamicField q.2.2 q.1 q.2.1` with
`‖y 0 - y*(q)‖ ≤ ρ` satisfies `‖y t - y*(q)‖ ≤ C exp(-κ t) ‖y 0 - y*(q)‖`, for all `q ∈ Pset`.
Uses `prop_S_ii` (Hurwitz Jacobian), `exists_lyapunov_certificate`, `certificate_robust`,
`dynamicField_remainder_uniform` and `local_exponential_stability_uniform_o`. -/
theorem dynamicField_localDecay_uniform (Pset : Set (ℝ × ℝ × ℝ)) (hK : IsCompact Pset)
    (hP : Pset ⊆ paramDomain) :
    ∃ ρ κ C : ℝ, 0 < ρ ∧ 0 < κ ∧ 0 < C ∧
      LocalDecay (fun q : ℝ × ℝ × ℝ => dynamicField q.2.2 q.1 q.2.1)
        (fun q : ℝ × ℝ × ℝ => dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1) Pset ρ κ C := by
  refine local_exponential_stability_uniform_o Pset hK _ _ eqJacobian
    (eqJacobian_continuousOn.mono hP) (fun q hq => ?_) (fun q0 hq0 ε hε => ?_)
  · exact (prop_S_ii q.2.2 q.1 q.2.1 (hP hq).2.2 (hP hq).1 (hP hq).2.1).2
  · obtain ⟨r, hr, hev⟩ := dynamicField_remainder_uniform q0 (hP hq0) ε hε
    exact ⟨r, hr, hev.filter_mono (nhdsWithin_mono q0 hP)⟩


/-! ### Uniform entry by continuous dependence and compactness -/

/-- The canonical equilibrium as a function of the parameter triple `q = (delta, Phi, r)`. -/
abbrev eqPt (q : ℝ × ℝ × ℝ) : DynamicState := dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1

/-- `y` is a solution on `[0, ∞)` of the LR5 field with parameters `q`, started at `z`. -/
def IsSolFrom (q : ℝ × ℝ × ℝ) (z : DynamicState) (y : ℝ → DynamicState) : Prop :=
  y 0 = z ∧ ∀ t, 0 ≤ t → HasDerivAt y (dynamicField q.2.2 q.1 q.2.1 (y t)) t

/-- The a priori norm bound of `norm_bound_on_interval`, as a function of the data. -/
def normBnd (T : ℝ) (q : ℝ × ℝ × ℝ) (z : DynamicState) : ℝ :=
  4 * (|dynamicEnergy q.2.2 q.1 z + q.2.1 * T| + 2 * q.2.2 ^ 2 + 1) * (1 + 1 / q.1) + 1

lemma normBnd_spec (T : ℝ) (hT : 0 ≤ T) (q : ℝ × ℝ × ℝ) (hq : q ∈ paramDomain)
    (z : DynamicState) (hz : dynamicPhysical z) (y : ℝ → DynamicState)
    (hy : IsSolFrom q z y) : ∀ t ∈ Set.Icc 0 T, ‖y t‖ ≤ normBnd T q z := by
  have := norm_bound_on_interval q.2.2 q.1 q.2.1 T y hq.1 hq.2.1 hT
    (fun t ht => hy.2 t ht.1) (by rw [hy.1]; exact hz)
  intro t ht
  have h := this t ht
  rw [hy.1] at h
  exact h

lemma normBnd_continuousAt (T : ℝ) (p0 : DynamicState × (ℝ × ℝ × ℝ)) (hδ : p0.2.1 ≠ 0) :
    ContinuousAt (fun p : DynamicState × (ℝ × ℝ × ℝ) => normBnd T p.2 p.1) p0 := by
  unfold normBnd
  have h1 : ContinuousAt (fun p : DynamicState × (ℝ × ℝ × ℝ) => 1 / p.2.1) p0 :=
    continuousAt_const.div (by fun_prop) hδ
  have h2 : ContinuousAt (fun p : DynamicState × (ℝ × ℝ × ℝ) =>
      |dynamicEnergy p.2.2.2 p.2.1 p.1 + p.2.2.1 * T| + 2 * p.2.2.2 ^ 2 + 1) p0 := by
    unfold dynamicEnergy dynamicAlpha
    fun_prop
  exact ((continuousAt_const.mul h2).mul (continuousAt_const.add h1)).add continuousAt_const


/-- Local entry: around every data/parameter pair `p0 ∈ K × Pset` there is a neighbourhood
(relative to `K × Pset`) and a time `T` such that every solution started in the neighbourhood is
within `ρ0` of its equilibrium at time `T`, and stays within `B ‖y 0 - y*‖` of it on `[0, T]`.
Proof: a solution from `p0` converges (`prop_S_i`), hence is `ρ0/4`-close at some time `T`;
Grönwall (`compare_solutions`) on a compact box on which the field is Lipschitz carries
this to nearby data; `canonicalEquilibrium_continuousOn` handles the moving target. -/
theorem entry_local (Pset : Set (ℝ × ℝ × ℝ)) (K : Set DynamicState) (hP : Pset ⊆ paramDomain)
    (hKphys : ∀ z ∈ K, dynamicPhysical z) (ρ0 : ℝ) (hρ0 : 0 < ρ0)
    (p0 : DynamicState × (ℝ × ℝ × ℝ)) (hp0 : p0 ∈ K ×ˢ Pset) :
    ∃ T B : ℝ, 0 ≤ T ∧ 0 ≤ B ∧ ∀ᶠ p in 𝓝[K ×ˢ Pset] p0, ∀ y : ℝ → DynamicState,
      IsSolFrom p.2 p.1 y → ‖y T - eqPt p.2‖ ≤ ρ0 ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ‖y t - eqPt p.2‖ ≤ B * ‖p.1 - eqPt p.2‖ := by
  obtain ⟨hz0K, hq0P⟩ := hp0
  obtain ⟨z0, q0⟩ := p0
  simp only at hz0K hq0P
  have hq0 : q0 ∈ paramDomain := hP hq0P
  obtain ⟨hδ0, hΦ0, hr0⟩ := hq0
  -- a solution from `z0` and its time of entry
  obtain ⟨y0, hy00, hy0, -⟩ := global_solution_exists q0.2.2 q0.1 q0.2.1 z0 hδ0 hΦ0 (hKphys z0 hz0K)
  have hy0S : IsSolFrom q0 z0 y0 := ⟨hy00, hy0⟩
  have hconv := solution_tendsto_equilibrium q0.2.2 q0.1 q0.2.1 y0 hr0 hδ0 hΦ0 hy0
    (by rw [hy00]; exact hKphys z0 hz0K)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hconv (ρ0 / 4) (by positivity))
  set T : ℝ := max N 0 with hTdef
  have hT0 : 0 ≤ T := le_max_right _ _
  have hyT : ‖y0 T - eqPt q0‖ < ρ0 / 4 := by
    have := hN T (le_max_left _ _)
    rwa [dist_eq_norm] at this
  -- the box
  set M : ℝ := max (normBnd T q0 z0 + 1) (‖eqPt q0‖ + 1) with hMdef
  set Qb : Set (ℝ × ℝ × ℝ) := Set.Icc (q0.1 / 2) (2 * q0.1) ×ˢ
    (Set.Icc (q0.2.1 - 1) (q0.2.1 + 1) ×ˢ Set.Icc (q0.2.2 / 2) (2 * q0.2.2)) with hQb
  obtain ⟨L, hL⟩ := jointField_lipschitz (q0.1 / 2) (2 * q0.1) (q0.2.1 - 1) (q0.2.1 + 1)
    (q0.2.2 / 2) (2 * q0.2.2) M (by positivity)
  set Bx : Set ((ℝ × ℝ × ℝ) × DynamicState) := Qb ×ˢ Metric.closedBall (0 : DynamicState) M
    with hBx
  have hLip : ∀ x ∈ Bx, ∀ x' ∈ Bx, ‖jointField x - jointField x'‖ ≤ (L : ℝ) * ‖x - x'‖ :=
    fun x hx x' hx' => hL.norm_sub_le hx hx'
  have hQ0 : q0 ∈ Qb := by
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hQnhds : Qb ∈ 𝓝 q0 := by
    refine prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
      (prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
        (Icc_mem_nhds (by linarith) (by linarith)))
  refine ⟨T, Real.exp ((L : ℝ) * T), hT0, (Real.exp_pos _).le, ?_⟩
  -- the eventual properties
  have e1 : ∀ᶠ p in 𝓝[K ×ˢ Pset] (z0, q0), p.2 ∈ Qb :=
    nhdsWithin_le_nhds ((continuous_snd.tendsto (z0, q0)) hQnhds)
  have e2 : ∀ᶠ p in 𝓝[K ×ˢ Pset] (z0, q0), normBnd T p.2 p.1 < normBnd T q0 z0 + 1 :=
    nhdsWithin_le_nhds ((normBnd_continuousAt T (z0, q0) hδ0.ne').eventually_lt
      continuousAt_const (by linarith))
  have hsnd : Tendsto (fun p : DynamicState × (ℝ × ℝ × ℝ) => p.2) (𝓝[K ×ˢ Pset] (z0, q0))
      (𝓝[paramDomain] q0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(continuous_snd.tendsto (z0, q0)).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with p hp using hP hp.2
  have hys : Tendsto (fun p : DynamicState × (ℝ × ℝ × ℝ) => eqPt p.2) (𝓝[K ×ˢ Pset] (z0, q0))
      (𝓝 (eqPt q0)) :=
    ((canonicalEquilibrium_continuousOn q0 ⟨hδ0, hΦ0, hr0⟩).tendsto).comp hsnd
  have e3 : ∀ᶠ p in 𝓝[K ×ˢ Pset] (z0, q0), dist (eqPt p.2) (eqPt q0) < min (ρ0 / 4) 1 :=
    Metric.tendsto_nhds.1 hys _ (lt_min (by positivity) one_pos)
  have hg : ContinuousAt (fun p : DynamicState × (ℝ × ℝ × ℝ) =>
      ‖p.1 - z0‖ + (L : ℝ) * ‖p.2 - q0‖ * T) (z0, q0) := by fun_prop
  have e4 : ∀ᶠ p in 𝓝[K ×ˢ Pset] (z0, q0),
      ‖p.1 - z0‖ + (L : ℝ) * ‖p.2 - q0‖ * T < ρ0 / 4 * Real.exp (-((L : ℝ) * T)) :=
    nhdsWithin_le_nhds (hg.eventually_lt continuousAt_const (by simp; positivity))
  filter_upwards [e1, e2, e3, e4, self_mem_nhdsWithin] with p hp1 hp2 hp3 hp4 hpS y hy
  obtain ⟨hzK, hqP⟩ := hpS
  have hqD : p.2 ∈ paramDomain := hP hqP
  have hzphys := hKphys _ hzK
  -- bounds on both solutions
  have hbd : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖y t‖ ≤ M := by
    intro t ht
    have := normBnd_spec T hT0 p.2 hqD p.1 hzphys y hy t ht
    exact (this.trans hp2.le).trans (le_max_left _ _)
  have hbd0 : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖y0 t‖ ≤ M := by
    intro t ht
    have := normBnd_spec T hT0 q0 ⟨hδ0, hΦ0, hr0⟩ z0 (hKphys z0 hz0K) y0 hy0S t ht
    exact (this.trans (by linarith)).trans (le_max_left _ _)
  have hdist : dist (eqPt p.2) (eqPt q0) < ρ0 / 4 := hp3.trans_le (min_le_left _ _)
  have hdist1 : dist (eqPt p.2) (eqPt q0) < 1 := hp3.trans_le (min_le_right _ _)
  have hysM : ‖eqPt p.2‖ ≤ M := by
    have : ‖eqPt p.2‖ ≤ ‖eqPt q0‖ + dist (eqPt p.2) (eqPt q0) := by
      calc ‖eqPt p.2‖ = ‖(eqPt p.2 - eqPt q0) + eqPt q0‖ := by congr 1; abel
        _ ≤ ‖eqPt p.2 - eqPt q0‖ + ‖eqPt q0‖ := norm_add_le _ _
        _ = ‖eqPt q0‖ + dist (eqPt p.2) (eqPt q0) := by rw [dist_eq_norm]; ring
    exact (by linarith : ‖eqPt p.2‖ ≤ ‖eqPt q0‖ + 1).trans (le_max_right _ _)
  have hstat : dynamicField p.2.2.2 p.2.1 p.2.2.1 (eqPt p.2) = 0 :=
    dynamicCanonicalEquilibrium_is_stationary _ _ _ hqD.2.2 hqD.1 hqD.2.1
  -- comparison with the solution from `p0`
  have hcmp := compare_solutions (L : ℝ) L.coe_nonneg Bx hLip q0 p.2 y0 y T
    (fun t ht => hy0 t ht.1) (fun t ht => hy.2 t ht.1)
    (fun t ht => ⟨⟨hQ0, by simpa using hbd0 t ht⟩, ⟨hp1, by simpa using hbd t ht⟩⟩)
    T ⟨hT0, le_rfl⟩
  rw [hy.1, hy00] at hcmp
  refine ⟨?_, ?_⟩
  · have hexp : (‖p.1 - z0‖ + (L : ℝ) * ‖p.2 - q0‖ * T) * Real.exp ((L : ℝ) * T) ≤ ρ0 / 4 := by
      calc _ ≤ ρ0 / 4 * Real.exp (-((L : ℝ) * T)) * Real.exp ((L : ℝ) * T) :=
            mul_le_mul_of_nonneg_right hp4.le (Real.exp_pos _).le
        _ = ρ0 / 4 := by rw [mul_assoc, ← Real.exp_add]; simp
    have h1 := hcmp.trans hexp
    calc ‖y T - eqPt p.2‖ = ‖(y T - y0 T) + (y0 T - eqPt q0) + (eqPt q0 - eqPt p.2)‖ := by
          congr 1; abel
      _ ≤ ‖y T - y0 T‖ + ‖y0 T - eqPt q0‖ + ‖eqPt q0 - eqPt p.2‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ ρ0 := by
          have : ‖eqPt q0 - eqPt p.2‖ < ρ0 / 4 := by
            rw [← norm_neg, neg_sub, ← dist_eq_norm]; exact hdist
          linarith
  · intro t ht
    have hcmp2 := compare_solutions (L : ℝ) L.coe_nonneg Bx hLip p.2 p.2 (fun _ => eqPt p.2) y T
      (fun t _ => (hasDerivAt_const t (eqPt p.2)).congr_deriv hstat.symm)
      (fun t ht => hy.2 t ht.1)
      (fun t ht => ⟨⟨hp1, by simpa using hysM⟩, ⟨hp1, by simpa using hbd t ht⟩⟩)
      t ht
    rw [hy.1] at hcmp2
    simp only [sub_self, norm_zero, mul_zero, zero_mul, add_zero] at hcmp2
    calc ‖y t - eqPt p.2‖ ≤ ‖p.1 - eqPt p.2‖ * Real.exp ((L : ℝ) * t) := hcmp2
      _ ≤ ‖p.1 - eqPt p.2‖ * Real.exp ((L : ℝ) * T) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left ht.2 L.coe_nonneg)) (norm_nonneg _)
      _ = Real.exp ((L : ℝ) * T) * ‖p.1 - eqPt p.2‖ := by ring


/-- v2 prop:S (iii), proportional form on compact sets of initial data and parameters.
For `K` a compact set of physical states and `Pset` a compact subset of
`{delta > 0, Phi ≥ 0, r > 0}` (ordered `(delta, Phi, r)`), there are `C, c > 0` such that every
solution `y` of `dynamicField q.2.2 q.1 q.2.1` on `[0, ∞)` with `y 0 ∈ K` and `q ∈ Pset`
satisfies `‖y t - y*(q)‖ ≤ C exp(-c t) ‖y 0 - y*(q)‖`.

This is the compact-initial-data form of the v1 `SourceAssumptionS`.  It does NOT give
`SourceAssumptionS`, which quantifies over all physical initial states with constants uniform
in the initial state; here `C` depends on `K`. -/
theorem prop_S_iii_proportional (K : Set DynamicState) (hK : IsCompact K)
    (hKphys : ∀ z ∈ K, dynamicPhysical z) (Pset : Set (ℝ × ℝ × ℝ)) (hPc : IsCompact Pset)
    (hP : ∀ q ∈ Pset, 0 < q.1 ∧ 0 ≤ q.2.1 ∧ 0 < q.2.2) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ q ∈ Pset, ∀ y0 ∈ K, ∀ y : ℝ → DynamicState,
      y 0 = y0 → (∀ t, 0 ≤ t → HasDerivAt y (dynamicField q.2.2 q.1 q.2.1 (y t)) t) →
        ∀ t, 0 ≤ t → ‖y t - dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1‖ ≤
          C * Real.exp (-c * t) * ‖y0 - dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1‖ := by
  have hPsub : Pset ⊆ paramDomain := fun q hq => hP q hq
  obtain ⟨ρ0, κ, C0, hρ0, hκ, hC0, hloc⟩ := dynamicField_localDecay_uniform Pset hPc hPsub
  set S : Set (DynamicState × (ℝ × ℝ × ℝ)) := K ×ˢ Pset with hS
  have hSc : IsCompact S := hK.prod hPc
  let Pr : Set (DynamicState × (ℝ × ℝ × ℝ)) → Prop := fun X => ∃ Tm Bm : ℝ, 0 ≤ Tm ∧ 0 ≤ Bm ∧
    ∀ p ∈ X ∩ S, ∀ y : ℝ → DynamicState, IsSolFrom p.2 p.1 y →
      ∃ T ∈ Set.Icc (0 : ℝ) Tm, ‖y T - eqPt p.2‖ ≤ ρ0 ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ‖y t - eqPt p.2‖ ≤ Bm * ‖p.1 - eqPt p.2‖
  have hPr : Pr S := by
    refine hSc.induction_on (p := Pr) ?_ ?_ ?_ ?_
    · exact ⟨0, 0, le_rfl, le_rfl, fun p hp => absurd hp.1 (by simp)⟩
    · rintro X Y hXY ⟨Tm, Bm, hT, hB, h⟩
      exact ⟨Tm, Bm, hT, hB, fun p hp => h p ⟨hXY hp.1, hp.2⟩⟩
    · rintro X Y ⟨Tm, Bm, hT, hB, h⟩ ⟨Tm', Bm', hT', hB', h'⟩
      refine ⟨max Tm Tm', max Bm Bm', hT.trans (le_max_left _ _), hB.trans (le_max_left _ _), ?_⟩
      intro p hp y hy
      rcases hp.1 with hpX | hpY
      · obtain ⟨T, hTm, h1, h2⟩ := h p ⟨hpX, hp.2⟩ y hy
        refine ⟨T, ⟨hTm.1, hTm.2.trans (le_max_left _ _)⟩, h1, fun t ht => (h2 t ht).trans ?_⟩
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      · obtain ⟨T, hTm, h1, h2⟩ := h' p ⟨hpY, hp.2⟩ y hy
        refine ⟨T, ⟨hTm.1, hTm.2.trans (le_max_right _ _)⟩, h1, fun t ht => (h2 t ht).trans ?_⟩
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    · intro p0 hp0
      obtain ⟨T, B, hT, hB, hev⟩ := entry_local Pset K hPsub hKphys ρ0 hρ0 p0 hp0
      refine ⟨_, hev, T, B, hT, hB, ?_⟩
      intro p hp y hy
      exact ⟨T, ⟨hT, le_rfl⟩, hp.1 y hy⟩
  obtain ⟨Tm, Bm, hTm, hBm, hcov⟩ := hPr
  set C1 := max C0 1 with hC1
  have hC1pos : 0 < C1 := lt_max_of_lt_right one_pos
  refine ⟨C1 * (Bm + 1) * Real.exp (κ * Tm), κ, by positivity, hκ, ?_⟩
  intro q hq y0 hy0K y hy0 hy t ht
  obtain ⟨T, hTm', hT1, hT2⟩ := hcov (y0, q) ⟨⟨hy0K, hq⟩, hy0K, hq⟩ y ⟨hy0, hy⟩
  simp only at hT1 hT2
  set d := ‖y0 - eqPt q‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hexpTm : 0 ≤ Real.exp (κ * Tm) := (Real.exp_pos _).le
  have hC1ge : 1 ≤ C1 := le_max_right _ _
  by_cases htT : t ≤ T
  · have h1 := hT2 t ⟨ht, htT⟩
    have hexp : 1 ≤ Real.exp (κ * Tm) * Real.exp (-κ * t) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [hTm'.2])
    calc ‖y t - eqPt q‖ ≤ Bm * d := h1
      _ ≤ (C1 * (Bm + 1)) * (Real.exp (κ * Tm) * Real.exp (-κ * t)) * d := by
          have h3 : Bm ≤ C1 * (Bm + 1) := by nlinarith
          have h4 : C1 * (Bm + 1) ≤ C1 * (Bm + 1) * (Real.exp (κ * Tm) * Real.exp (-κ * t)) := by
            have : 0 ≤ C1 * (Bm + 1) := by positivity
            nlinarith
          exact mul_le_mul_of_nonneg_right (h3.trans h4) hd0
      _ = _ := by ring
  · push Not at htT
    -- shifted solution
    have hsh : ∀ s, 0 ≤ s → HasDerivAt (fun s => y (T + s)) (dynamicField q.2.2 q.1 q.2.1 (y (T + s))) s :=
      fun s hs => (hy (T + s) (by linarith [hTm'.1])).comp_const_add T s
    have hdec := hloc q hq (fun s => y (T + s)) hsh (by simpa using hT1) (t - T) (by linarith)
    simp only [add_zero] at hdec
    have hTt : T + (t - T) = t := by ring
    rw [hTt] at hdec
    have hB1 : ‖y T - eqPt q‖ ≤ Bm * d := hT2 T ⟨hTm'.1, le_rfl⟩
    have hexp : Real.exp (-κ * (t - T)) ≤ Real.exp (κ * Tm) * Real.exp (-κ * t) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [hTm'.2])
    calc ‖y t - eqPt q‖ ≤ C0 * Real.exp (-κ * (t - T)) * ‖y T - eqPt q‖ := hdec
      _ ≤ C1 * (Real.exp (κ * Tm) * Real.exp (-κ * t)) * (Bm * d) := by
          have h5 : C0 ≤ C1 := le_max_left _ _
          have : 0 ≤ ‖y T - eqPt q‖ := norm_nonneg _
          calc C0 * Real.exp (-κ * (t - T)) * ‖y T - eqPt q‖
              ≤ C1 * Real.exp (-κ * (t - T)) * ‖y T - eqPt q‖ := by
                gcongr
            _ ≤ C1 * (Real.exp (κ * Tm) * Real.exp (-κ * t)) * ‖y T - eqPt q‖ := by gcongr
            _ ≤ _ := by gcongr
      _ ≤ C1 * (Bm + 1) * Real.exp (κ * Tm) * Real.exp (-κ * t) * d := by
          have : 0 ≤ Real.exp (κ * Tm) * Real.exp (-κ * t) := by positivity
          have h6 : C1 * (Real.exp (κ * Tm) * Real.exp (-κ * t)) * (Bm * d) ≤
              C1 * (Real.exp (κ * Tm) * Real.exp (-κ * t)) * ((Bm + 1) * d) :=
            mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
          calc _ ≤ _ := h6
            _ = _ := by ring

/-- v2 prop:S (iii) (T3): uniform exponential convergence on compact sets of initial data and
parameters.  For `K` a compact set of physical states and `Pset` a compact subset of
`{delta > 0, Phi ≥ 0, r > 0}` there are `C, c > 0` such that for all `q ∈ Pset`, `y0 ∈ K`, every
solution of the LR5 field on `[0, ∞)` started at `y0` satisfies `‖y t - y*(q)‖ ≤ C exp(-c t)`. -/
theorem prop_S_iii (K : Set DynamicState) (hK : IsCompact K)
    (hKphys : ∀ z ∈ K, dynamicPhysical z) (Pset : Set (ℝ × ℝ × ℝ)) (hPc : IsCompact Pset)
    (hP : ∀ q ∈ Pset, 0 < q.1 ∧ 0 ≤ q.2.1 ∧ 0 < q.2.2) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ q ∈ Pset, ∀ y0 ∈ K, ∀ y : ℝ → DynamicState,
      y 0 = y0 → (∀ t, 0 ≤ t → HasDerivAt y (dynamicField q.2.2 q.1 q.2.1 (y t)) t) →
        ∀ t, 0 ≤ t → ‖y t - dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1‖ ≤ C * Real.exp (-c * t) := by
  obtain ⟨C, c, hC, hc, h⟩ := prop_S_iii_proportional K hK hKphys Pset hPc hP
  have hcont : ContinuousOn (fun p : DynamicState × (ℝ × ℝ × ℝ) => ‖p.1 - eqPt p.2‖)
      (K ×ˢ Pset) := by
    have h1 : ContinuousOn (fun p : DynamicState × (ℝ × ℝ × ℝ) => eqPt p.2) (K ×ˢ Pset) :=
      canonicalEquilibrium_continuousOn.comp (by fun_prop)
        (fun p hp => hP p.2 hp.2)
    exact (continuousOn_fst.sub h1).norm
  obtain ⟨D, hD⟩ := (hK.prod hPc).exists_bound_of_continuousOn hcont
  refine ⟨C * (max D 0 + 1), c, by positivity, hc, ?_⟩
  intro q hq y0 hy0 y hy0' hy t ht
  have h1 := h q hq y0 hy0 y hy0' hy t ht
  have h2 : ‖y0 - eqPt q‖ ≤ max D 0 + 1 := by
    have := hD (y0, q) ⟨hy0, hq⟩
    simp only [norm_norm] at this
    exact this.trans (by linarith [le_max_left D 0])
  calc _ ≤ _ := h1
    _ ≤ C * Real.exp (-c * t) * (max D 0 + 1) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- v2 prop:S (iii) (T5), uniform entry for a fixed parameter triple: for `r > 0`, `delta > 0`,
`Phi ≥ 0` and `K` a compact set of physical states, every solution started in `K` is within any
prescribed `ρ` of the equilibrium after a time `T0` depending only on `ρ` and `K`.  Consumed by
the recursion hypotheses of `cor:recursion`. -/
theorem dynamicField_uniformEntry (r delta Phi : ℝ) (hr : 0 < r) (hdelta : 0 < delta)
    (hPhi : 0 ≤ Phi) (K : Set DynamicState) (hK : IsCompact K)
    (hKphys : ∀ z ∈ K, dynamicPhysical z) :
    UniformEntry (dynamicField r delta Phi) (dynamicCanonicalEquilibrium r delta Phi) K := by
  obtain ⟨C, c, hC, hc, h⟩ := prop_S_iii K hK hKphys {(delta, Phi, r)} isCompact_singleton
    (by intro q hq; rw [Set.mem_singleton_iff] at hq; subst hq; exact ⟨hdelta, hPhi, hr⟩)
  intro ρ hρ
  refine ⟨max 0 (Real.log (C / ρ) / c), le_max_left _ _, ?_⟩
  intro y0 hy0 y hy t ht
  have h1 := h (delta, Phi, r) rfl y0 hy0 y hy.1 hy.2 t
    (le_trans (le_max_left _ _) ht)
  refine h1.trans ?_
  have hCρ : 0 < C / ρ := by positivity
  have h2 : Real.log (C / ρ) ≤ c * t := by
    have := (le_max_right _ _).trans ht
    rwa [div_le_iff₀ hc, mul_comm] at this
  have h3 : Real.exp (-c * t) ≤ ρ / C := by
    have : Real.exp (-c * t) ≤ Real.exp (-Real.log (C / ρ)) :=
      Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_neg, Real.exp_log hCρ, inv_div] at this
    exact this
  calc C * Real.exp (-c * t) ≤ C * (ρ / C) := mul_le_mul_of_nonneg_left h3 hC.le
    _ = ρ := by field_simp


end Joint


end
end SparseSGD.Logistic.V2
