import SparseSGD.Logistic.V2.Lyapunov
import SparseSGD.Logistic.V2.PositiveDeterminant
import SparseSGD.Logistic.V2.Barbalat
import SparseSGD.Logistic.DynamicGlobal
import SparseSGD.Logistic.SourceAssumptions

/-! # v2 prop:S (i): global existence, boundedness and convergence

Every physical solution of the LR5 field `dynamicField r delta Phi` exists for all
time, stays physical and bounded, and converges to the canonical equilibrium
`dynamicCanonicalEquilibrium r delta Phi`.  LaSalle's principle is replaced by
the free-energy Lyapunov function `lyapunov`, the integral-free Barbalat lemma and
the cluster-point criterion of `V2/Barbalat.lean`. -/
namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic Filter Topology
noncomputable section
set_option maxHeartbeats 2400000

/-- "Regular" states: physical, and (when `Phi > 0`) with strictly positive Gram
determinant, so that the free energy `lyapunov` is defined and differentiable. -/
def Reg (Phi : ℝ) (z : DynamicState) : Prop :=
  dynamicPhysical z ∧ (0 < Phi → 0 < dynamicDeterminant z)

theorem Reg.physical {Phi : ℝ} {z : DynamicState} (h : Reg Phi z) : dynamicPhysical z := h.1

theorem lyapunovBound_pos (r delta Phi E : ℝ) (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) :
    0 < lyapunovBound r delta Phi E := by
  unfold lyapunovBound
  have hb : 0 ≤ Phi / delta := div_nonneg hPhi hdelta.le
  have : 0 ≤ 4 * (delta + 1) * (|E| +
      (Phi / delta) / 2 * |Real.log (2 * Phi) + Real.log (2 * (Phi / delta)) - 2| +
      3 * r ^ 2 / (2 * delta)) := by positivity
  linarith

/-- v2 prop:S (i), proof step 1: along a solution through a regular state the free
energy is differentiable with derivative `-dissipation`. -/
theorem hasDerivAt_lyapunov_reg (r delta Phi : ℝ) (y : ℝ → DynamicState) (t : ℝ)
    (hdelta : 0 < delta) (hPhi : 0 ≤ Phi)
    (hy : HasDerivAt y (dynamicField r delta Phi (y t)) t) (hreg : Reg Phi (y t)) :
    HasDerivAt (fun s => lyapunov r delta Phi (y s)) (-dissipation delta Phi (y t)) t := by
  rcases hPhi.eq_or_lt with h | h
  · subst h
    rw [dissipation_zero_load]
    exact hasDerivAt_lyapunov_zero_load r delta y t hdelta hy
  · have hQ := hreg.2 h
    exact hasDerivAt_lyapunov r delta Phi y t hdelta hy hQ
      (pos_of_physical_det_pos (y t) hreg.1 hQ).2

/-- v2 prop:S (i): the dissipation is nonnegative on regular states. -/
theorem dissipation_nonneg_reg (delta Phi : ℝ) (z : DynamicState) (hPhi : 0 ≤ Phi)
    (hreg : Reg Phi z) : 0 ≤ dissipation delta Phi z := by
  rcases hPhi.eq_or_lt with h | h
  · subst h
    rw [dissipation_zero_load]
    have := hreg.1.2.1
    positivity
  · have hQ := hreg.2 h
    exact dissipation_nonneg delta Phi z (pos_of_physical_det_pos z hreg.1 hQ).2 hQ

/-- v2 prop:S (i), step 1: the free energy is nonincreasing on any interval along
which the solution is regular. -/
theorem lyapunov_antitoneOn (r delta Phi a b : ℝ) (y : ℝ → DynamicState)
    (hdelta : 0 < delta) (hPhi : 0 ≤ Phi)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hreg : ∀ t ∈ Set.Icc a b, Reg Phi (y t)) :
    AntitoneOn (fun t => lyapunov r delta Phi (y t)) (Set.Icc a b) := by
  have hd := fun t (ht : t ∈ Set.Icc a b) =>
    hasDerivAt_lyapunov_reg r delta Phi y t hdelta hPhi (hy t ht) (hreg t ht)
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · exact fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    exact neg_nonpos.2 (dissipation_nonneg_reg delta Phi _ hPhi (hreg t (interior_subset ht)))

/-- v2 prop:S (i), regularity is preserved on `[0,T]`: physical states stay physical and,
for `Phi > 0`, `Q > 0` persists (`v2-posdet`). -/
theorem reg_preserved (r delta Phi T : ℝ) (y : ℝ → DynamicState)
    (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) (hT : 0 ≤ T)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (h0 : Reg Phi (y 0)) : ∀ t ∈ Set.Icc 0 T, Reg Phi (y t) := by
  intro t ht
  refine ⟨dynamicPhysical_preserved r delta Phi 0 T y hT hdelta hPhi hy h0.1 t ht, fun hP => ?_⟩
  exact determinant_pos_of_pos_initial r delta Phi T y hdelta hP hy h0.1 (h0.2 hP) t ht

/-- v2 prop:S (i), `Q > 0` for positive times: a physical start becomes regular at every
positive time. -/
theorem reg_of_pos_time (r delta Phi T : ℝ) (y : ℝ → DynamicState)
    (hdelta : 0 < delta) (hPhi : 0 ≤ Phi)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (h0 : dynamicPhysical (y 0)) : ∀ t ∈ Set.Ioc 0 T, Reg Phi (y t) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.le.trans ht.2
  refine ⟨dynamicPhysical_preserved r delta Phi 0 T y hT hdelta hPhi hy h0 t ⟨ht.1.le, ht.2⟩,
    fun hP => ?_⟩
  exact determinant_pos_of_pos_time r delta Phi T y hdelta hP hy h0 t ht

/-- v2 prop:S (i), sublevel sets of the free energy on regular states: the norm is
bounded and, for `Phi > 0`, `Q` and `V` are bounded below by positive constants. -/
theorem sublevel_bounds (r delta Phi E : ℝ) (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) :
    ∃ A q v : ℝ, 0 < q ∧ 0 < v ∧ ∀ z : DynamicState, Reg Phi z → lyapunov r delta Phi z ≤ E →
      ‖z‖ ≤ A ∧ (0 < Phi → q ≤ dynamicDeterminant z ∧ v ≤ z 3) := by
  rcases hPhi.eq_or_lt with h | h
  · subst h
    refine ⟨4 * (|delta * E| + 2 * r ^ 2 + 1) * (1 + 1 / delta) + 1, 1, 1, one_pos, one_pos,
      fun z hz hE => ⟨?_, fun hp => absurd hp (lt_irrefl _)⟩⟩
    have hE' : dynamicEnergy r delta z ≤ delta * E := by
      have : dynamicEnergy r delta z / delta ≤ E := by
        simpa [lyapunov] using hE
      rwa [div_le_iff₀ hdelta, mul_comm] at this
    exact dynamicEnergy_controls_norm r delta (delta * E) z hdelta hz.1.1 hz.1.2.1 hz.1.2.2 hE'
  · set q := Real.exp (-2 * delta * (E + 3 * r ^ 2 / (2 * delta)) / Phi) with hq
    have hB := lyapunovBound_pos r delta Phi E hdelta h.le
    refine ⟨lyapunovBound r delta Phi E, q, q / lyapunovBound r delta Phi E,
      Real.exp_pos _, div_pos (Real.exp_pos _) hB, fun z hz hE => ?_⟩
    obtain ⟨h1, h2⟩ := lyapunov_sublevel_bounds r delta Phi E z hz.1 (hz.2 h) hdelta h.le hE
    exact ⟨h1, fun hp => h2 hp⟩

/-- v2 prop:S (i), a priori bound on `[0,T]`: constants depending only on the free-energy
level `E` of a regular initial state bound every solution on every finite interval. -/
theorem interval_bounds (r delta Phi E : ℝ) (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) :
    ∃ A q v : ℝ, 0 < q ∧ 0 < v ∧ ∀ (T : ℝ) (y : ℝ → DynamicState), 0 ≤ T →
      (∀ t ∈ Set.Icc 0 T, HasDerivAt y (dynamicField r delta Phi (y t)) t) →
      Reg Phi (y 0) → lyapunov r delta Phi (y 0) ≤ E →
      ∀ t ∈ Set.Icc 0 T, Reg Phi (y t) ∧ lyapunov r delta Phi (y t) ≤ E ∧ ‖y t‖ ≤ A ∧
        (0 < Phi → q ≤ dynamicDeterminant (y t) ∧ v ≤ y t 3) := by
  obtain ⟨A, q, v, hq, hv, hb⟩ := sublevel_bounds r delta Phi E hdelta hPhi
  refine ⟨A, q, v, hq, hv, fun T y hT hy h0 hE t ht => ?_⟩
  have hreg := reg_preserved r delta Phi T y hdelta hPhi hT hy h0
  have hanti := lyapunov_antitoneOn r delta Phi 0 T y hdelta hPhi hy hreg
  have hLt : lyapunov r delta Phi (y t) ≤ lyapunov r delta Phi (y 0) :=
    hanti ⟨le_rfl, hT⟩ ht ht.1
  have hEt := hLt.trans hE
  exact ⟨hreg t ht, hEt, hb _ (hreg t ht) hEt⟩

/-- v2 prop:S (i), existence from a regular initial state: the clipped-field solution
of `DynamicGlobal.lean` never reaches the clip, by the free-energy bound of
`interval_bounds`. -/
theorem global_solution_exists_of_reg (r delta Phi : ℝ) (z0 : DynamicState)
    (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) (hz0 : Reg Phi z0) :
    ∃ y : ℝ → DynamicState, y 0 = z0 ∧
      (∀ t, 0 ≤ t → HasDerivAt y (dynamicField r delta Phi (y t)) t) ∧
      ∀ t, 0 ≤ t → dynamicPhysical (y t) := by
  obtain ⟨A, q, v, hq, hv, hb⟩ :=
    interval_bounds r delta Phi (lyapunov r delta Phi z0) hdelta hPhi
  set M := max A ‖z0‖ + 1 with hMdef
  have hM : 0 ≤ M := by
    have := le_max_right A ‖z0‖
    have := norm_nonneg z0
    linarith
  have hAM : A < M := by linarith [le_max_left A ‖z0‖]
  have h0M : ‖z0‖ < M := by linarith [le_max_right A ‖z0‖]
  obtain ⟨y, hy0, hy⟩ := dynamic_clipped_solution_exists r delta Phi M hM z0
  have key : ∀ T, 0 ≤ T → ∀ t ∈ Set.Icc 0 T, ‖y t‖ ≤ M := by
    intro T hT
    have hcont : ContinuousOn y (Set.Icc 0 T) := fun t _ => (hy t).continuousAt.continuousWithinAt
    refine continuous_norm_no_escape y T M A hT hcont (by rw [hy0]; exact h0M) hAM ?_
    intro t ht hprefix
    have hactual : ∀ s ∈ Set.Icc 0 t, HasDerivAt y (dynamicField r delta Phi (y s)) s := by
      intro s hs
      simpa only [dynamicBoxClamp_eq M (y s) (hprefix s hs)] using hy s
    have := hb t y ht.1 hactual (by rw [hy0]; exact hz0) (by rw [hy0])
    exact (this t ⟨ht.1, le_rfl⟩).2.2.1
  have hactual : ∀ t, 0 ≤ t → ∀ s ∈ Set.Icc 0 t, HasDerivAt y (dynamicField r delta Phi (y s)) s := by
    intro t ht s hs
    simpa only [dynamicBoxClamp_eq M (y s) (key t ht s hs)] using hy s
  refine ⟨y, hy0, fun t ht => hactual t ht t ⟨ht, le_rfl⟩, fun t ht => ?_⟩
  exact (reg_preserved r delta Phi t y hdelta hPhi ht (hactual t ht) (by rw [hy0]; exact hz0)
    t ⟨ht, le_rfl⟩).1

/-- v2 prop:S (i), existence (T2): from every physical initial state there is a global
forward solution of the LR5 field, and it stays physical.  The solution is built on
`[0,1]` by `dynamic_solution_exists_on_finite_horizon`, which makes the state regular at
time `1` (`Q > 0` when `Phi > 0`), and continued by `global_solution_exists_of_reg`. -/
theorem global_solution_exists (r delta Phi : ℝ) (y0 : DynamicState)
    (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) (hy0 : dynamicPhysical y0) :
    ∃ y : ℝ → DynamicState, y 0 = y0 ∧
      (∀ t, 0 ≤ t → HasDerivAt y (dynamicField r delta Phi (y t)) t) ∧
      ∀ t, 0 ≤ t → dynamicPhysical (y t) := by
  obtain ⟨y1, hy10, hy1, hphys1⟩ :=
    dynamic_solution_exists_on_finite_horizon r delta Phi 1 y0 hdelta hPhi zero_le_one hy0
  have hreg1 : Reg Phi (y1 1) :=
    reg_of_pos_time r delta Phi 1 y1 hdelta hPhi hy1 (by rw [hy10]; exact hy0) 1
      ⟨zero_lt_one, le_rfl⟩
  obtain ⟨z, hz0, hz, hzphys⟩ := global_solution_exists_of_reg r delta Phi (y1 1) hdelta hPhi hreg1
  let y : ℝ → DynamicState := fun t => if t ≤ 1 then y1 t else z (t - 1)
  have hyle : ∀ t, t ≤ 1 → y t = y1 t := fun t ht => by simp [y, ht]
  have hygt : ∀ t, 1 < t → y t = z (t - 1) := fun t ht => by simp [y, not_le.2 ht]
  refine ⟨y, by rw [hyle 0 (by norm_num), hy10], ?_, ?_⟩
  · intro t ht
    rcases lt_trichotomy t 1 with h | h | h
    · have hev : y =ᶠ[𝓝 t] y1 := by
        filter_upwards [Iio_mem_nhds h] with s hs using hyle s (le_of_lt hs)
      have := (hy1 t ⟨ht, h.le⟩).congr_of_eventuallyEq hev
      rwa [hyle t h.le]
    · subst h
      have hL : HasDerivWithinAt y (dynamicField r delta Phi (y 1)) (Set.Iic 1) 1 := by
        have := (hy1 1 ⟨zero_le_one, le_rfl⟩).hasDerivWithinAt (s := Set.Iic 1)
        refine (this.congr (fun s hs => hyle s hs) (hyle 1 le_rfl)).congr_deriv ?_
        rw [hyle 1 le_rfl]
      have hR : HasDerivWithinAt y (dynamicField r delta Phi (y 1)) (Set.Ici 1) 1 := by
        have h0 : HasDerivAt z (dynamicField r delta Phi (z (1 - 1))) (1 - 1) := by
          rw [sub_self]; exact hz 0 le_rfl
        have h1 : HasDerivAt (fun s => z (s - 1)) (dynamicField r delta Phi (z 0)) 1 := by
          have := h0.comp_sub_const (1 : ℝ) 1
          simpa using this
        have h2 := h1.hasDerivWithinAt (s := Set.Ici 1)
        refine (h2.congr (fun s hs => ?_) ?_).congr_deriv ?_
        · rcases (Set.mem_Ici.1 hs).eq_or_lt with e | e
          · rw [← e, hyle 1 le_rfl, sub_self, hz0]
          · exact hygt s e
        · rw [hyle 1 le_rfl, sub_self, hz0]
        · rw [hyle 1 le_rfl, hz0]
      have := hL.union hR
      rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
      exact this
    · have hev : y =ᶠ[𝓝 t] fun s => z (s - 1) := by
        filter_upwards [Ioi_mem_nhds h] with s hs using hygt s hs
      have h0 := hz (t - 1) (by linarith)
      have h1 : HasDerivAt (fun s => z (s - 1)) (dynamicField r delta Phi (z (t - 1))) t := by
        have := h0.comp_sub_const t 1
        simpa using this
      have := h1.congr_of_eventuallyEq hev
      rwa [hygt t h]
  · intro t ht
    by_cases h : t ≤ 1
    · rw [hyle t h]; exact hphys1 t ⟨ht, h⟩
    · rw [hygt t (not_le.1 h)]; exact hzphys _ (by linarith [not_le.1 h])

/-- Energy bound on a finite interval `[0,T]` from a physical start (the
`DynamicGlobal.lean` estimate, stated for an arbitrary solution). -/
theorem norm_bound_on_interval (r delta Phi T : ℝ) (y : ℝ → DynamicState)
    (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) (hT : 0 ≤ T)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hy0 : dynamicPhysical (y 0)) :
    ∀ t ∈ Set.Icc 0 T, ‖y t‖ ≤
      4 * (|dynamicEnergy r delta (y 0) + Phi * T| + 2 * r ^ 2 + 1) * (1 + 1 / delta) + 1 := by
  intro t ht
  have hactual : ∀ s ∈ Set.Icc 0 t, HasDerivAt y (dynamicField r delta Phi (y s)) s :=
    fun s hs => hy s ⟨hs.1, hs.2.trans ht.2⟩
  have hphys := dynamicPhysical_preserved r delta Phi 0 T y hT hdelta hPhi hy hy0
  have henergy := dynamicEnergy_finite_horizon_bound r delta Phi T hdelta y hy
    (fun s hs => (hphys s hs).2.1) t ht
  have hE : dynamicEnergy r delta (y t) ≤ dynamicEnergy r delta (y 0) + Phi * T :=
    henergy.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left ht.2 hPhi))
  have hp := hphys t ht
  exact dynamicEnergy_controls_norm r delta _ (y t) hdelta hp.1 hp.2.1 hp.2.2 hE

/-- v2 prop:S (i), a priori bounds along a solution on `[0,oo)` (T1, detailed form): the
solution is regular from time `1` on, the free energy is bounded there by its value at `1`,
and norm, `Q` (when `Phi > 0`) and `V` (when `Phi > 0`) are controlled uniformly. -/
theorem solution_bounds (r delta Phi : ℝ) (y : ℝ → DynamicState)
    (hdelta : 0 < delta) (hPhi : 0 ≤ Phi)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hy0 : dynamicPhysical (y 0)) :
    ∃ M q v : ℝ, 0 < q ∧ 0 < v ∧ (∀ t, 0 ≤ t → ‖y t‖ ≤ M) ∧
      ∀ t, 1 ≤ t → Reg Phi (y t) ∧ lyapunov r delta Phi (y t) ≤ lyapunov r delta Phi (y 1) ∧
        (0 < Phi → q ≤ dynamicDeterminant (y t) ∧ v ≤ y t 3) := by
  have hy01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt y (dynamicField r delta Phi (y t)) t :=
    fun t ht => hy t ht.1
  have hreg1 : Reg Phi (y 1) :=
    reg_of_pos_time r delta Phi 1 y hdelta hPhi hy01 hy0 1 ⟨zero_lt_one, le_rfl⟩
  obtain ⟨A, q, v, hq, hv, hb⟩ :=
    interval_bounds r delta Phi (lyapunov r delta Phi (y 1)) hdelta hPhi
  set A1 := 4 * (|dynamicEnergy r delta (y 0) + Phi * 1| + 2 * r ^ 2 + 1) * (1 + 1 / delta) + 1
    with hA1
  have h1 := norm_bound_on_interval r delta Phi 1 y hdelta hPhi zero_le_one hy01 hy0
  have hlate : ∀ t, 1 ≤ t → Reg Phi (y t) ∧ lyapunov r delta Phi (y t) ≤ lyapunov r delta Phi (y 1) ∧
      ‖y t‖ ≤ A ∧ (0 < Phi → q ≤ dynamicDeterminant (y t) ∧ v ≤ y t 3) := by
    intro t ht
    have hw : ∀ s ∈ Set.Icc 0 (t - 1),
        HasDerivAt (fun x => y (x + 1)) (dynamicField r delta Phi (y (s + 1))) s :=
      fun s hs => (hy (s + 1) (by linarith [hs.1])).comp_add_const s 1
    have := hb (t - 1) (fun x => y (x + 1)) (by linarith) hw (by simpa using hreg1)
      (by simp) (t - 1) ⟨by linarith, le_rfl⟩
    simpa using this
  refine ⟨max A1 A, q, v, hq, hv, fun t ht => ?_, fun t ht => ?_⟩
  · by_cases h : t ≤ 1
    · exact (h1 t ⟨ht, h⟩).trans (le_max_left _ _)
    · exact (hlate t (not_le.1 h).le).2.2.1.trans (le_max_right _ _)
  · obtain ⟨a, b, _, c⟩ := hlate t ht
    exact ⟨a, b, c⟩

/-- v2 prop:S (i), boundedness (T1): every physical solution on `[0,oo)` is bounded, and
for `Phi > 0` its Gram determinant is bounded below by a positive constant for `t >= 1`. -/
theorem solution_bounded (r delta Phi : ℝ) (y : ℝ → DynamicState)
    (hdelta : 0 < delta) (hPhi : 0 ≤ Phi)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hy0 : dynamicPhysical (y 0)) :
    ∃ M q : ℝ, (∀ t, 0 ≤ t → ‖y t‖ ≤ M) ∧
      (0 < Phi → 0 < q ∧ ∀ t, 1 ≤ t → q ≤ dynamicDeterminant (y t)) := by
  obtain ⟨M, q, v, hq, hv, hM, hb⟩ := solution_bounds r delta Phi y hdelta hPhi hy hy0
  exact ⟨M, q, hM, fun hP => ⟨hq, fun t ht => ((hb t ht).2.2 hP).1⟩⟩

/-! ### Barbalat step -/

/-- v2 prop:S (i), proof step 4: if `F' = g (y t)` along a bounded solution on `[0,oo)`,
`F` converges and `g` is continuous on a compact set containing the path, then
`g (y t) -> 0`.  This is `tendsto_zero_of_hasDerivAt_of_tendsto` with uniform continuity
obtained from the Lipschitz bound on the path. -/
theorem tendsto_zero_of_solution_deriv (r delta Phi M : ℝ) {y : ℝ → DynamicState}
    {Fy : ℝ → ℝ} {g : DynamicState → ℝ} {K : Set DynamicState} {l : ℝ}
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hM : ∀ t, 0 ≤ t → ‖y t‖ ≤ M)
    (hF : ∀ t, 0 ≤ t → HasDerivAt Fy (g (y t)) t) (hlim : Tendsto Fy atTop (𝓝 l))
    (hK : IsCompact K) (hyK : ∀ t, 0 ≤ t → y t ∈ K) (hg : ContinuousOn g K) :
    Tendsto (fun t => g (y t)) atTop (𝓝 0) := by
  obtain ⟨L, F, hF0, _, hFb⟩ := dynamicField_compact_bounds r delta Phi M
  have hlip := lipschitz_of_norm_deriv_le (y := y)
    (y' := fun t => dynamicField r delta Phi (y t)) (M := F) hy (fun t ht => hFb _ (hM t ht))
  have huc := uniformContinuousOn_comp_path (g := g) (K := K) (M := F)
    (fun s hs t ht => by rw [dist_eq_norm, Real.dist_eq]; exact hlip s hs t ht) hK hyK hg
  exact tendsto_zero_of_hasDerivAt_of_tendsto (F := Fy) (f := fun t => g (y t)) hF hlim huc

/-- Shifting time by one does not change a limit at infinity. -/
theorem tendsto_of_shift {g : ℝ → ℝ} {l : ℝ} (h : Tendsto (fun t => g (t + 1)) atTop (𝓝 l)) :
    Tendsto g atTop (𝓝 l) := by
  have := h.comp (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
  exact this.congr (fun t => by simp)

/-- The free energy is bounded below on regular states. -/
theorem lyapunov_bddBelow (r delta Phi : ℝ) (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) :
    ∃ m : ℝ, ∀ z : DynamicState, Reg Phi z → m ≤ lyapunov r delta Phi z := by
  rcases hPhi.eq_or_lt with h | h
  · subst h
    refine ⟨-(3 * r ^ 2 / 2) / delta, fun z hz => ?_⟩
    have hco := dynamicEnergy_coercive r delta z
    have hR := hz.1.1
    have hV := hz.1.2.1
    have h1 : -(3 * r ^ 2 / 2) ≤ dynamicEnergy r delta z := by
      have : 0 ≤ delta / 2 * ((z 1) ^ 2 + z 3) := by positivity
      nlinarith [sq_nonneg (z 0)]
    simp only [lyapunov, zero_div, zero_mul, sub_zero]
    exact div_le_div_of_nonneg_right h1 hdelta.le
  · set c := (Phi / delta) / 2 * (Real.log (2 * Phi) + Real.log (2 * (Phi / delta)) - 2) with hc
    refine ⟨-(3 * r ^ 2 / 2) / delta - c, fun z hz => ?_⟩
    have hlow := lyapunov_lower_bound r delta Phi z hz.1 (hz.2 h) hdelta h.le
    have hR := hz.1.1
    have hV := hz.1.2.1
    have e : (1 + (z 0) ^ 2 / 4 + z 2 / 4 - 3 * r ^ 2 / 2) / delta =
        (1 + (z 0) ^ 2 / 4 + z 2 / 4) / delta - (3 * r ^ 2 / 2) / delta := by rw [sub_div]
    have hp : 0 ≤ (1 + (z 0) ^ 2 / 4 + z 2 / 4) / delta := by positivity
    have : -(3 * r ^ 2 / 2) / delta = -((3 * r ^ 2 / 2) / delta) := by rw [neg_div]
    have hy2 := sq_nonneg (z 1)
    linarith

/-- Compact set carrying the dissipation: on it `V` and `Q` are bounded away from zero
(`Phi > 0`), so the dissipation is continuous there. -/
theorem exists_compact_dissipation (delta Phi M q v : ℝ) (hPhi : 0 ≤ Phi) (hq : 0 < q) (hv : 0 < v) :
    ∃ K : Set DynamicState, IsCompact K ∧ ContinuousOn (dissipation delta Phi) K ∧
      ∀ z : DynamicState, ‖z‖ ≤ M → (0 < Phi → q ≤ dynamicDeterminant z ∧ v ≤ z 3) → z ∈ K := by
  rcases hPhi.eq_or_lt with h | h
  · subst h
    refine ⟨Metric.closedBall 0 M, isCompact_closedBall 0 M, ?_, fun z hz _ => by simpa using hz⟩
    have : dissipation delta 0 = fun z : DynamicState => (z 1) ^ 2 + z 3 := by
      funext z; exact dissipation_zero_load delta z
    rw [this]
    fun_prop
  · set K : Set DynamicState := Metric.closedBall 0 M ∩
      ({z | q ≤ dynamicDeterminant z} ∩ {z | v ≤ z 3}) with hK
    have hQc : Continuous (fun z : DynamicState => dynamicDeterminant z) := by
      unfold dynamicDeterminant; fun_prop
    have hKc : IsCompact K := by
      apply (isCompact_closedBall 0 M).inter_right
      exact (isClosed_le continuous_const hQc).inter
        (isClosed_le continuous_const (continuous_apply 3))
    refine ⟨K, hKc, ?_, fun z hz hp => ⟨by simpa using hz, hp h⟩⟩
    have hV : ∀ z ∈ K, z 3 ≠ 0 := fun z hz => (lt_of_lt_of_le hv hz.2.2).ne'
    have hD : ∀ z ∈ K, dynamicDeterminant z * z 3 ≠ 0 := fun z hz =>
      (mul_pos (lt_of_lt_of_le hq hz.2.1) (lt_of_lt_of_le hv hz.2.2)).ne'
    unfold dissipation
    refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
    · fun_prop
    · exact ContinuousOn.div (by fun_prop) (by fun_prop) hV
    · exact ContinuousOn.div (by fun_prop) (hQc.continuousOn.mul (continuous_apply 3).continuousOn) hD

/-- v2 prop:S (i), T3: the dissipation tends to zero along every physical solution on
`[0,oo)`.  The free energy is nonincreasing and bounded below from time `1` on, hence
convergent, and Barbalat's lemma applies to its derivative `-dissipation`. -/
theorem dissipation_tendsto_zero (r delta Phi : ℝ) (y : ℝ → DynamicState)
    (hdelta : 0 < delta) (hPhi : 0 ≤ Phi)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hy0 : dynamicPhysical (y 0)) :
    Tendsto (fun t => dissipation delta Phi (y t)) atTop (𝓝 0) := by
  obtain ⟨M, q, v, hq, hv, hM, hb⟩ := solution_bounds r delta Phi y hdelta hPhi hy hy0
  obtain ⟨K, hKc, hKg, hKmem⟩ := exists_compact_dissipation delta Phi M q v hPhi hq hv
  obtain ⟨m, hm⟩ := lyapunov_bddBelow r delta Phi hdelta hPhi
  set w : ℝ → DynamicState := fun t => y (t + 1) with hw
  have hwd : ∀ t, 0 ≤ t → HasDerivAt w (dynamicField r delta Phi (w t)) t :=
    fun t ht => (hy (t + 1) (by linarith)).comp_add_const t 1
  have hwM : ∀ t, 0 ≤ t → ‖w t‖ ≤ M := fun t ht => hM (t + 1) (by linarith)
  have hwreg : ∀ t, 0 ≤ t → Reg Phi (w t) := fun t ht => (hb (t + 1) (by linarith)).1
  have hF : ∀ t, 0 ≤ t → HasDerivAt (fun s => lyapunov r delta Phi (w s))
      ((fun z => -dissipation delta Phi z) (w t)) t :=
    fun t ht => hasDerivAt_lyapunov_reg r delta Phi w t hdelta hPhi (hwd t ht) (hwreg t ht)
  have hanti : AntitoneOn (fun s => lyapunov r delta Phi (w s)) (Set.Ici 0) := by
    intro a ha b hb' hab
    have := lyapunov_antitoneOn r delta Phi 0 b w hdelta hPhi
      (fun t ht => hwd t ht.1) (fun t ht => hwreg t ht.1)
    exact this ⟨ha, hab⟩ ⟨hb', le_rfl⟩ hab
  have hbdd : BddBelow ((fun s => lyapunov r delta Phi (w s)) '' Set.Ici 0) := by
    refine ⟨m, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hm _ (hwreg t ht)
  obtain ⟨l, hl⟩ := antitone_bddBelow_tendsto hanti hbdd
  have hwK : ∀ t, 0 ≤ t → w t ∈ K := fun t ht =>
    hKmem _ (hwM t ht) (fun hP => ((hb (t + 1) (by linarith)).2.2 hP))
  have hlim := tendsto_zero_of_solution_deriv r delta Phi M (y := w)
    (Fy := fun s => lyapunov r delta Phi (w s)) (g := fun z => -dissipation delta Phi z) (K := K)
    hwd hwM hF hl hKc hwK hKg.neg
  apply tendsto_of_shift
  simpa using hlim.neg

/-- If `g t ^ 2 <= d t` eventually and `d -> 0` then `g -> 0`. -/
theorem tendsto_zero_of_sq_le {g d : ℝ → ℝ} (hd : Tendsto d atTop (𝓝 0))
    (h : ∀ᶠ t in atTop, g t ^ 2 ≤ d t) : Tendsto g atTop (𝓝 0) := by
  have hs : Tendsto (fun t => Real.sqrt (d t)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hd
    rwa [Real.sqrt_zero] at this
  refine squeeze_zero_norm' ?_ hs
  filter_upwards [h] with t ht
  simpa [Real.norm_eq_abs] using Real.abs_le_sqrt ht

/-- v2 prop:S (i), proof step 4: on a regular state of norm at most `M` the dissipation
controls `Y^2`, `(V - b)^2` and `C^2`. -/
theorem dissipation_controls (delta Phi M : ℝ) (hdelta : 0 < delta) (hPhi : 0 ≤ Phi)
    (hM : 0 ≤ M) (z : DynamicState) (hz : Reg Phi z) (hzM : ‖z‖ ≤ M) :
    (z 1) ^ 2 ≤ dissipation delta Phi z ∧
    (z 3 - Phi / delta) ^ 2 ≤ (M + M ^ 3 / (Phi / delta) ^ 2) * dissipation delta Phi z ∧
    (z 4) ^ 2 ≤ (M + M ^ 3 / (Phi / delta) ^ 2) * dissipation delta Phi z := by
  obtain ⟨hR, hV, hC⟩ := hz.1
  have hRM : z 2 ≤ M := (le_abs_self _).trans ((norm_le_pi_norm z 2).trans hzM)
  have hVM : z 3 ≤ M := (le_abs_self _).trans ((norm_le_pi_norm z 3).trans hzM)
  have hd0 := dissipation_nonneg_reg delta Phi z hPhi hz
  rcases hPhi.eq_or_lt with h | h
  · subst h
    simp only [zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
      add_zero, sub_zero]
    rw [dissipation_zero_load]
    refine ⟨by nlinarith [sq_nonneg (z 1)], ?_, ?_⟩
    · nlinarith [sq_nonneg (z 1)]
    · nlinarith [sq_nonneg (z 1), mul_le_mul hRM hVM hV hM]
  · have hQ := hz.2 h
    have hVp := (pos_of_physical_det_pos z hz.1 hQ).2
    have hb : 0 < Phi / delta := div_pos h hdelta
    set b := Phi / delta with hbdef
    set d := dissipation delta Phi z with hd
    have hd' : d = (z 1) ^ 2 + (z 3 - b) ^ 2 / z 3 + b ^ 2 * (z 4) ^ 2 / (dynamicDeterminant z * z 3) := rfl
    have t1 : 0 ≤ (z 1) ^ 2 := sq_nonneg _
    have t2 : 0 ≤ (z 3 - b) ^ 2 / z 3 := div_nonneg (sq_nonneg _) hVp.le
    have t3 : 0 ≤ b ^ 2 * (z 4) ^ 2 / (dynamicDeterminant z * z 3) :=
      div_nonneg (by positivity) (mul_pos hQ hVp).le
    have hc1 : M ≤ M + M ^ 3 / b ^ 2 := by have : 0 ≤ M ^ 3 / b ^ 2 := by positivity
                                           linarith
    have hc2 : 0 ≤ M ^ 3 / b ^ 2 := by positivity
    refine ⟨by linarith, ?_, ?_⟩
    · have h2 : (z 3 - b) ^ 2 / z 3 ≤ d := by linarith
      have h2' : (z 3 - b) ^ 2 ≤ d * z 3 := (div_le_iff₀ hVp).1 h2
      calc (z 3 - b) ^ 2 ≤ d * z 3 := h2'
        _ ≤ d * M := mul_le_mul_of_nonneg_left hVM hd0
        _ ≤ d * (M + M ^ 3 / b ^ 2) := mul_le_mul_of_nonneg_left hc1 hd0
        _ = _ := mul_comm _ _
    · have h3 : b ^ 2 * (z 4) ^ 2 / (dynamicDeterminant z * z 3) ≤ d := by linarith
      have h3' : b ^ 2 * (z 4) ^ 2 ≤ d * (dynamicDeterminant z * z 3) :=
        (div_le_iff₀ (mul_pos hQ hVp)).1 h3
      have hQle : dynamicDeterminant z ≤ M * M := by
        unfold dynamicDeterminant
        nlinarith [sq_nonneg (z 4), mul_le_mul hRM hVM hV hM]
      have hQV : dynamicDeterminant z * z 3 ≤ M ^ 3 := by
        have := mul_le_mul hQle hVM hV (mul_nonneg hM hM)
        nlinarith
      have h4 : b ^ 2 * (z 4) ^ 2 ≤ d * M ^ 3 :=
        h3'.trans (mul_le_mul_of_nonneg_left hQV hd0)
      have h5 : (z 4) ^ 2 ≤ d * M ^ 3 / b ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      calc (z 4) ^ 2 ≤ d * M ^ 3 / b ^ 2 := h5
        _ = d * (M ^ 3 / b ^ 2) := by ring
        _ ≤ d * (M + M ^ 3 / b ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hd0
        _ = _ := mul_comm _ _

/-- v2 prop:S (i), T3 (consequence): `Y -> 0`, `V -> Phi/delta` and `C -> 0`. -/
theorem YVC_tendsto (r delta Phi : ℝ) (y : ℝ → DynamicState)
    (hdelta : 0 < delta) (hPhi : 0 ≤ Phi)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hy0 : dynamicPhysical (y 0)) :
    Tendsto (fun t => y t 1) atTop (𝓝 0) ∧ Tendsto (fun t => y t 3) atTop (𝓝 (Phi / delta)) ∧
      Tendsto (fun t => y t 4) atTop (𝓝 0) := by
  obtain ⟨M, q, v, hq, hv, hM, hb⟩ := solution_bounds r delta Phi y hdelta hPhi hy hy0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 le_rfl)
  have hd := dissipation_tendsto_zero r delta Phi y hdelta hPhi hy hy0
  set c := M + M ^ 3 / (Phi / delta) ^ 2 with hc
  have hcd : Tendsto (fun t => c * dissipation delta Phi (y t)) atTop (𝓝 0) := by
    simpa using hd.const_mul c
  have hev : ∀ᶠ t in atTop, _ := (eventually_ge_atTop (1 : ℝ)).mono fun t ht =>
    dissipation_controls delta Phi M hdelta hPhi hM0 (y t) (hb t ht).1 (hM t (by linarith))
  refine ⟨tendsto_zero_of_sq_le hd (hev.mono fun t ht => ht.1), ?_, ?_⟩
  · have := tendsto_zero_of_sq_le (g := fun t => y t 3 - Phi / delta) hcd
      (hev.mono fun t ht => ht.2.1)
    simpa using this.add_const (Phi / delta)
  · exact tendsto_zero_of_sq_le hcd (hev.mono fun t ht => ht.2.2)

/-- v2 prop:S (i), T4: the slow residuals `alpha theta - r` and `alpha R - Phi` tend to zero.
Barbalat is applied to `F = Y` (derivative `-Y + alpha theta - r`) and to `F = C`
(derivative `-C + alpha R - delta V`). -/
theorem slow_residuals_tendsto_zero (r delta Phi : ℝ) (y : ℝ → DynamicState)
    (hdelta : 0 < delta) (hPhi : 0 ≤ Phi)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hy0 : dynamicPhysical (y 0)) :
    Tendsto (fun t => dynamicAlpha r (y t) * y t 0 - r) atTop (𝓝 0) ∧
      Tendsto (fun t => dynamicAlpha r (y t) * y t 2 - Phi) atTop (𝓝 0) := by
  obtain ⟨M, q, v, hq, hv, hM, hb⟩ := solution_bounds r delta Phi y hdelta hPhi hy hy0
  obtain ⟨hYl, hVl, hCl⟩ := YVC_tendsto r delta Phi y hdelta hPhi hy hy0
  have hcont : Continuous (dynamicField r delta Phi) := (contDiff_dynamicField r delta Phi).continuous
  have hcomp : ∀ i : Fin 5, Tendsto (fun t => y t i) atTop (𝓝 0) →
      Tendsto (fun t => dynamicField r delta Phi (y t) i) atTop (𝓝 0) := by
    intro i hi
    have hF : ∀ t, 0 ≤ t → HasDerivAt (fun s => y s i)
        ((fun z => dynamicField r delta Phi z i) (y t)) t :=
      fun t ht => (hasDerivAt_pi.mp (hy t ht)) i
    exact tendsto_zero_of_solution_deriv r delta Phi M (y := y) (Fy := fun s => y s i)
      (g := fun z => dynamicField r delta Phi z i) (K := Metric.closedBall 0 M) hy
      (fun t ht => hM t ht) hF hi (isCompact_closedBall 0 M)
      (fun t ht => by simpa using hM t ht) ((continuous_apply i).comp hcont).continuousOn
  have h1 := hcomp 1 hYl
  have h4 := hcomp 4 hCl
  have e1 : ∀ z : DynamicState, dynamicField r delta Phi z 1 =
      -z 1 + dynamicAlpha r z * z 0 - r := fun z => by simp [dynamicField]
  have e4 : ∀ z : DynamicState, dynamicField r delta Phi z 4 =
      -z 4 + dynamicAlpha r z * z 2 - delta * z 3 := fun z => by simp [dynamicField]
  refine ⟨?_, ?_⟩
  · have := h1.add hYl
    rw [add_zero] at this
    refine this.congr (fun t => ?_)
    rw [e1]; ring
  · have hVl' : Tendsto (fun t => delta * (y t 3 - Phi / delta)) atTop (𝓝 0) := by
      have := (hVl.sub_const (Phi / delta)).const_mul delta
      simpa using this
    have := (h4.add hCl).add hVl'
    rw [add_zero, add_zero] at this
    refine this.congr (fun t => ?_)
    rw [e4]
    field_simp
    ring

/-- v2 prop:S (i), T5: a pair `(theta, R)` solving the slow stationarity equations
`alpha theta = r`, `alpha R = Phi` is the canonical equilibrium. -/
theorem equilibrium_of_limits (r Phi theta R : ℝ) (hr : 0 < r) (hPhi : 0 ≤ Phi)
    (h1 : alpha theta R r * theta = r) (h2 : alpha theta R r * R = Phi) :
    theta = positiveRoot r Phi ∧ R = equilibriumBulk r Phi := by
  have hα : 0 < alpha theta R r := Real.exp_pos _
  have hθ : 0 < theta := by
    by_contra hneg
    have : alpha theta R r * theta ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα.le (not_lt.1 hneg)
    linarith
  have hf : slowField r Phi theta R = (0, 0) := by
    apply Prod.ext
    · simp only [slowField]; linarith
    · simp only [slowField]; linarith
  obtain ⟨hg, hR⟩ := (slowField_zero_iff r Phi theta R hr hθ).1 hf
  have hspec := positiveRoot_spec r Phi hr hPhi
  have hth : theta = positiveRoot r Phi :=
    (exists_unique_positive_root r Phi hr hPhi).unique ⟨hθ, hg⟩ hspec
  refine ⟨hth, ?_⟩
  rw [hR, hth]
  rfl

/-- A cluster point of a convergent path is its limit. -/
theorem mapClusterPt_eq_of_tendsto {X : Type*} [TopologicalSpace X] [T2Space X] {u : ℝ → X}
    {a c : X} (hu : Tendsto u atTop (𝓝 a)) (hc : MapClusterPt c atTop u) : c = a := by
  by_contra hne
  obtain ⟨U, V, hU, hV, hcU, haV, hUV⟩ := t2_separation hne
  have h1 := hc.frequently (hU.mem_nhds hcU)
  have h2 := hu.eventually (hV.mem_nhds haV)
  obtain ⟨t, ht1, ht2⟩ := (h1.and_eventually h2).exists
  exact (Set.disjoint_left.1 hUV ht1) ht2

/-- v2 prop:S (i), T6 (convergence): every physical solution on `[0,oo)` converges to the
canonical equilibrium.  The slow pair `(theta, R)` stays in a compact set and its cluster
points solve the stationarity equations (T4), hence equal `(theta*, R*)` (T5);
`Y, V, C` converge by T3. -/
theorem solution_tendsto_equilibrium (r delta Phi : ℝ) (y : ℝ → DynamicState)
    (hr : 0 < r) (hdelta : 0 < delta) (hPhi : 0 ≤ Phi)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hy0 : dynamicPhysical (y 0)) :
    Tendsto y atTop (𝓝 (dynamicCanonicalEquilibrium r delta Phi)) := by
  obtain ⟨M, q, hM, -⟩ := solution_bounded r delta Phi y hdelta hPhi hy hy0
  obtain ⟨hYl, hVl, hCl⟩ := YVC_tendsto r delta Phi y hdelta hPhi hy hy0
  obtain ⟨hs1, hs2⟩ := slow_residuals_tendsto_zero r delta Phi y hdelta hPhi hy hy0
  set z : ℝ → ℝ × ℝ := fun t => (y t 0, y t 2) with hz
  have hcoord : ∀ (i : Fin 5) t, 0 ≤ t → |y t i| ≤ M := fun i t ht =>
    (norm_le_pi_norm (y t) i).trans (hM t ht)
  have hK : IsCompact (Set.Icc (-M) M ×ˢ Set.Icc (-M) M : Set (ℝ × ℝ)) :=
    isCompact_Icc.prod isCompact_Icc
  have hzK : ∀ t, 0 ≤ t → z t ∈ (Set.Icc (-M) M ×ˢ Set.Icc (-M) M : Set (ℝ × ℝ)) := fun t ht =>
    ⟨abs_le.1 (hcoord 0 t ht) |> fun h => ⟨h.1, h.2⟩, abs_le.1 (hcoord 2 t ht) |> fun h => ⟨h.1, h.2⟩⟩
  have hf1 : Continuous (fun p : ℝ × ℝ => alpha p.1 p.2 r * p.1 - r) := by
    unfold alpha; fun_prop
  have hf2 : Continuous (fun p : ℝ × ℝ => alpha p.1 p.2 r * p.2 - Phi) := by
    unfold alpha; fun_prop
  have hcl : ∀ p, MapClusterPt p atTop z → p = (positiveRoot r Phi, equilibriumBulk r Phi) := by
    intro p hp
    have c1 := mapClusterPt_eq_of_tendsto (u := fun t => alpha (z t).1 (z t).2 r * (z t).1 - r)
      (a := 0) hs1 (hp.continuousAt_comp hf1.continuousAt)
    have c2 := mapClusterPt_eq_of_tendsto (u := fun t => alpha (z t).1 (z t).2 r * (z t).2 - Phi)
      (a := 0) hs2 (hp.continuousAt_comp hf2.continuousAt)
    have := equilibrium_of_limits r Phi p.1 p.2 hr hPhi (by linarith) (by linarith)
    exact Prod.ext this.1 this.2
  have hzl := tendsto_of_compact_unique_cluster hK hzK hcl
  have hθ : Tendsto (fun t => y t 0) atTop (𝓝 (positiveRoot r Phi)) :=
    (continuous_fst.tendsto _).comp hzl
  have hR : Tendsto (fun t => y t 2) atTop (𝓝 (equilibriumBulk r Phi)) :=
    (continuous_snd.tendsto _).comp hzl
  refine tendsto_pi_nhds.2 fun i => ?_
  fin_cases i
  · simpa [dynamicCanonicalEquilibrium] using hθ
  · simpa [dynamicCanonicalEquilibrium] using hYl
  · simpa [dynamicCanonicalEquilibrium] using hR
  · simpa [dynamicCanonicalEquilibrium] using hVl
  · simpa [dynamicCanonicalEquilibrium] using hCl

/-- v2 prop:S (i): global existence, positivity-cone invariance and convergence.  Every
physical initial state has a global forward solution; every forward solution from a physical
state stays physical, is bounded, and converges to `dynamicCanonicalEquilibrium r delta Phi`. -/
theorem prop_S_i (r delta Phi : ℝ) (hr : 0 < r) (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) :
    (∀ y0 : DynamicState, dynamicPhysical y0 →
      ∃ y : ℝ → DynamicState, y 0 = y0 ∧
        (∀ t, 0 ≤ t → HasDerivAt y (dynamicField r delta Phi (y t)) t) ∧
        (∀ t, 0 ≤ t → dynamicPhysical (y t)) ∧
        Tendsto y atTop (𝓝 (dynamicCanonicalEquilibrium r delta Phi))) ∧
    (∀ y : ℝ → DynamicState,
      (∀ t, 0 ≤ t → HasDerivAt y (dynamicField r delta Phi (y t)) t) → dynamicPhysical (y 0) →
        (∀ t, 0 ≤ t → dynamicPhysical (y t)) ∧ (∃ M : ℝ, ∀ t, 0 ≤ t → ‖y t‖ ≤ M) ∧
        Tendsto y atTop (𝓝 (dynamicCanonicalEquilibrium r delta Phi))) := by
  have hstay : ∀ y : ℝ → DynamicState,
      (∀ t, 0 ≤ t → HasDerivAt y (dynamicField r delta Phi (y t)) t) → dynamicPhysical (y 0) →
        ∀ t, 0 ≤ t → dynamicPhysical (y t) := fun y hy hy0 t ht =>
    dynamicPhysical_preserved r delta Phi 0 t y ht hdelta hPhi
      (fun s hs => hy s hs.1) hy0 t ⟨ht, le_rfl⟩
  refine ⟨fun y0 hy0 => ?_, fun y hy hy0 => ?_⟩
  · obtain ⟨y, h0, hy, hphys⟩ := global_solution_exists r delta Phi y0 hdelta hPhi hy0
    exact ⟨y, h0, hy, hphys, solution_tendsto_equilibrium r delta Phi y hr hdelta hPhi hy
      (by rw [h0]; exact hy0)⟩
  · obtain ⟨M, q, hM, -⟩ := solution_bounded r delta Phi y hdelta hPhi hy hy0
    exact ⟨hstay y hy hy0, ⟨M, hM⟩, solution_tendsto_equilibrium r delta Phi y hr hdelta hPhi hy hy0⟩

end
end SparseSGD.Logistic.V2
