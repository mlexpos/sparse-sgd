import SparseSGD.Continuum.KernelEstimates
import SparseSGD.Continuum.Uniqueness

open scoped Matrix.Norms.Operator Topology
open Set

namespace SparseSGD

noncomputable section

/-- A free covariance transport preserves positive semidefiniteness. -/
theorem continuumFreeCovariance_psd (delta : ℝ) (s : Moments) (hs : s.psd) (t : ℝ) :
    (continuumMeanFlow delta t * s.cov * (continuumMeanFlow delta t).transpose).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hs.mul_mul_conjTranspose_same (continuumMeanFlow delta t)

theorem continuumFreeRisk_nonneg (delta : ℝ) (s : Moments) (hs : s.psd) (t : ℝ) :
    0 ≤ continuumFreeRisk delta s t :=
  (continuumFreeCovariance_psd delta s hs t).diag_nonneg

/-- A scalar renewal equation with a nonnegative kernel preserves nonnegativity. -/
private theorem nonneg_of_renewal {r a k : ℝ → ℝ} {u phi T : ℝ}
    (hr : Continuous r) (hk : Continuous k) (hu : 0 ≤ u) (hp : 0 ≤ phi)
    (hT : 0 ≤ T) (ha : ∀ t, 0 ≤ a t) (hk0 : ∀ t, 0 ≤ k t)
    (heq : ∀ t, r t = a t + ∫ x in (0 : ℝ)..t, k (t - x) * (u * r x + phi)) :
    0 ≤ r T := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).bddAbove_image hk.continuousOn
  let K := max B 0 * u
  have hK : 0 ≤ K := mul_nonneg (le_max_right _ _) hu
  let n := fun t => max (-r t) 0
  have hn : Continuous n := hr.neg.max continuous_const
  let H := fun t => ∫ x in (0 : ℝ)..t, n x
  have hH (t : ℝ) : HasDerivAt H (n t) t :=
    intervalIntegral.integral_hasDerivAt_right (hn.intervalIntegrable 0 t)
      hn.stronglyMeasurable.stronglyMeasurableAtFilter hn.continuousAt
  have hH0 : H 0 = 0 := by simp [H]
  have hHpos {t : ℝ} (ht : 0 ≤ t) : 0 ≤ H t :=
    intervalIntegral.integral_nonneg ht (fun _ _ => le_max_right _ _)
  have hb (t : ℝ) (ht : t ∈ Icc 0 T) : n t ≤ K * H t := by
    have hcont : Continuous (fun x => k (t - x) * (u * r x + phi)) :=
      (hk.comp (continuous_const.sub continuous_id)).mul
        ((continuous_const.mul hr).add continuous_const)
    have hlow : -(K * H t) ≤ ∫ x in (0 : ℝ)..t, k (t - x) * (u * r x + phi) := by
      have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht.1
        ((hn.const_mul (-K)).intervalIntegrable 0 t) (hcont.intervalIntegrable 0 t)
        (fun x hx => ?_)
      · change (∫ x in (0 : ℝ)..t, (-K) * n x) ≤
          (∫ x in (0 : ℝ)..t, k (t - x) * (u * r x + phi)) at hmono
        rw [intervalIntegral.integral_const_mul] at hmono
        simpa only [neg_mul, H] using hmono
      · have htx : t - x ∈ Icc 0 T := ⟨by linarith [hx.2], by linarith [hx.1, ht.2]⟩
        have hkb : k (t - x) ≤ max B 0 := (hB (Set.mem_image_of_mem k htx)).trans (le_max_left _ _)
        have hkn := hk0 (t - x)
        have hn0 : 0 ≤ n x := le_max_right _ _
        have hrn : -n x ≤ r x := by dsimp [n]; linarith [le_max_left (-r x) 0]
        have h1 := mul_le_mul_of_nonneg_left hrn hu
        have h2 := mul_le_mul_of_nonneg_left (show -u * n x ≤ u * r x + phi by nlinarith) hkn
        have h3 := mul_le_mul_of_nonneg_right hkb hu
        have h4 := mul_le_mul_of_nonneg_right h3 hn0
        dsimp [K]
        nlinarith
    have hrt : -(K * H t) ≤ r t := by rw [heq t]; linarith [ha t]
    dsimp [n]
    exact max_le (by linarith) (mul_nonneg hK (hHpos ht.1))
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (a := (0 : ℝ)) (b := T) (K := K) (f := H) (f' := n)
    (fun t _ => (hH t).continuousAt.continuousWithinAt)
    (fun t _ => (hH t).hasDerivWithinAt) hH0
    (fun t ht => ?_)
  · have hzero : H T = 0 := hz T ⟨hT, le_rfl⟩
    have hbT := hb T ⟨hT, le_rfl⟩
    dsimp [n] at hbT
    rw [hzero, mul_zero] at hbT
    linarith [le_max_left (-r T) 0]
  · rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ n t from le_max_right _ _), abs_of_nonneg (hHpos ht.1)]
    exact hb t ⟨ht.1, ht.2.le⟩

/-- The risk of the concrete continuum flow remains nonnegative. -/
theorem continuumFlow_R_nonneg {delta u phi : ℝ} (hd : 0 < delta)
    (hu : 0 ≤ u) (hp : 0 ≤ phi) (s : Moments) (hs : s.psd)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ (continuumFlow delta u phi s t).R := by
  apply nonneg_of_renewal (r := fun t => (continuumFlow delta u phi s t).R)
    (a := continuumFreeRisk delta s) (k := continuumRenewalKernel delta)
    (continuumFlow_R_continuous delta u phi s) (continuumRenewalKernel_continuous delta)
    hu hp ht (continuumFreeRisk_nonneg delta s hs) (continuumRenewalKernel_nonneg hd)
    (continuumFlow_renewal delta u phi s)

private theorem intervalIntegral_matrix_linear (L : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ)
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hF : Continuous F) (a b : ℝ) :
    L (∫ x in a..b, F x) = ∫ x in a..b, L (F x) := by
  convert (L.toContinuousLinearMap.intervalIntegral_comp_comm (μ := MeasureTheory.volume)
    (hF.intervalIntegrable a b)).symm using 1 <;> rfl

private theorem intervalIntegral_matrix_entry
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hF : Continuous F) (a b : ℝ) (i j : Fin 2) :
    (∫ x in a..b, F x) i j = ∫ x in a..b, F x i j := by
  let L : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ :=
    (LinearMap.proj j : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).comp
      (LinearMap.proj i : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
  exact intervalIntegral_matrix_linear L F hF a b

/-- A continuous integral of positive semidefinite covariance matrices is positive semidefinite. -/
private theorem intervalIntegral_matrix_psd {F : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hF : Continuous F) {t : ℝ} (ht : 0 ≤ t)
    (hP : ∀ x ∈ Icc 0 t, (F x).PosSemidef) :
    (∫ x in (0 : ℝ)..t, F x).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    rw [intervalIntegral_matrix_entry F hF 0 t j i,
      intervalIntegral_matrix_entry F hF 0 t i j]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ht] at hx
    simpa only [star_trivial] using (hP x hx).isHermitian.apply i j
  · intro v
    let L : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ :=
      (dotProductBilin ℝ ℝ v).comp ((Matrix.mulVecBilin ℝ ℝ).flip v)
    have hcomm := intervalIntegral_matrix_linear L F hF 0 t
    simp only [star_trivial]
    change 0 ≤ L (∫ x in (0 : ℝ)..t, F x)
    rw [hcomm]
    apply intervalIntegral.integral_nonneg ht
    intro x hx
    convert (hP x hx).dotProduct_mulVec_nonneg v using 1 <;> rfl

/-- Positive semidefiniteness is preserved by the actual continuum covariance flow. -/
theorem continuumFlow_psd {delta u phi : ℝ} (hd : 0 < delta)
    (hu : 0 ≤ u) (hp : 0 ≤ phi) (s : Moments) (hs : s.psd)
    {t : ℝ} (ht : 0 ≤ t) : (continuumFlow delta u phi s t).psd := by
  have hE : continuumKickCovariance.PosSemidef := by
    have heq : continuumKickCovariance = Matrix.diagonal ![(0 : ℝ), 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [continuumKickCovariance, Matrix.diagonal]
    rw [heq]
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  have hcont : Continuous (fun x => continuumMeanFlow delta (t - x) *
      continuumCovarianceSource delta u phi (continuumFlow delta u phi s x) *
      (continuumMeanFlow delta (t - x)).transpose) := by
    have hP : Continuous (fun x : ℝ => continuumMeanFlow delta (t - x)) :=
      (continuumMeanFlow_continuous delta).comp (continuous_const.sub continuous_id)
    have hQ : Continuous (fun x => continuumCovarianceSource delta u phi
        (continuumFlow delta u phi s x)) := by
      exact (continuous_const.mul
        ((continuous_const.mul (continuumFlow_R_continuous delta u phi s)).add continuous_const)).smul
          continuous_const
    exact (hP.mul hQ).mul hP.matrix_transpose
  change (continuumCovarianceFlow delta u phi s t).PosSemidef
  rw [continuumCovarianceFlow_variation_of_constants]
  apply (continuumFreeCovariance_psd delta s hs t).add
  apply intervalIntegral_matrix_psd hcont ht
  intro x hx
  have hR := continuumFlow_R_nonneg hd hu hp s hs hx.1
  have hq : 0 ≤ 2 / delta * (u * (continuumFlow delta u phi s x).R + phi) := by positivity
  have hsource := hE.smul hq
  change (continuumCovarianceSource delta u phi (continuumFlow delta u phi s x)).PosSemidef
    at hsource
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hsource.mul_mul_conjTranspose_same (continuumMeanFlow delta (t - x))

/-- The rank defect remains nonnegative along the actual continuum flow. -/
theorem continuumFlow_rankDefect_nonneg {delta u phi : ℝ} (hd : 0 < delta)
    (hu : 0 ≤ u) (hp : 0 ≤ phi) (s : Moments) (hs : s.psd)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ (continuumFlow delta u phi s t).rankDefect := by
  have h := (continuumFlow_psd hd hu hp s hs ht).det_nonneg
  simpa [Matrix.det_fin_two, Moments.cov, Moments.rankDefect, Moments.psd, pow_two] using h

/-- Variation of constants for the determinant of the actual continuum covariance. -/
theorem continuumFlow_rankDefect_variation_of_constants {delta : ℝ} (hd : delta ≠ 0)
    (u phi : ℝ) (s : Moments) {t : ℝ} (ht : 0 ≤ t) :
    (continuumFlow delta u phi s t).rankDefect = Real.exp (-2 * t) * s.rankDefect +
      ∫ x in (0 : ℝ)..t, Real.exp (-2 * (t - x)) *
        (2 / delta * (continuumFlow delta u phi s x).R *
          (u * (continuumFlow delta u phi s x).R + phi)) := by
  have hder (x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt (fun x => Real.exp (-2 * (t - x)) * (continuumFlow delta u phi s x).rankDefect)
        (Real.exp (-2 * (t - x)) * (2 / delta * (continuumFlow delta u phi s x).R *
          (u * (continuumFlow delta u phi s x).R + phi))) x := by
    have hq := rankDefect_hasDerivAt (continuumFlow_isMomentSolution delta u phi s) hd hx
    have he := (((hasDerivAt_const x t).sub (hasDerivAt_id x)).const_mul (-2)).exp
    convert! he.mul hq using 1 <;> first | rfl | (try simp only [Pi.sub_apply, id_eq]; ring)
  have hcont : Continuous (fun x => Real.exp (-2 * (t - x)) *
      (2 / delta * (continuumFlow delta u phi s x).R *
        (u * (continuumFlow delta u phi s x).R + phi))) := by
    have hR := continuumFlow_R_continuous delta u phi s
    exact (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
      ((continuous_const.mul hR).mul ((continuous_const.mul hR).add continuous_const))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t)
    (fun x hx => hder x (by rw [uIcc_of_le ht] at hx; exact hx.1))
    (hcont.intervalIntegrable 0 t)
  simp only [sub_self, mul_zero, Real.exp_zero, one_mul, sub_zero, continuumFlow_initial] at h
  linarith

/-- Any positive risk inside the time interval forces strictly positive determinant after noise. -/
theorem continuumFlow_rankDefect_pos_of_positive_risk {delta u phi : ℝ}
    (hd : 0 < delta) (hu : 0 ≤ u) (hp : 0 ≤ phi) (hnoise : 0 < u + phi)
    (s : Moments) (hs : s.psd) {t : ℝ} (ht : 0 < t)
    (hR : ∃ x ∈ Ioo 0 t, 0 < (continuumFlow delta u phi s x).R) :
    0 < (continuumFlow delta u phi s t).rankDefect := by
  rw [continuumFlow_rankDefect_variation_of_constants hd.ne' u phi s ht.le]
  have hQ : 0 ≤ s.rankDefect := by
    have h := hs.det_nonneg
    simpa [Matrix.det_fin_two, Moments.cov, Moments.rankDefect, Moments.psd, pow_two] using h
  have hfirst : 0 ≤ Real.exp (-2 * t) * s.rankDefect := mul_nonneg (Real.exp_pos _).le hQ
  have hint : 0 < ∫ x in (0 : ℝ)..t, Real.exp (-2 * (t - x)) *
      (2 / delta * (continuumFlow delta u phi s x).R *
        (u * (continuumFlow delta u phi s x).R + phi)) := by
    apply intervalIntegral.integral_pos ht
    · have hRc := continuumFlow_R_continuous delta u phi s
      exact ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
        ((continuous_const.mul hRc).mul ((continuous_const.mul hRc).add continuous_const))).continuousOn
    · intro x hx
      have hr := continuumFlow_R_nonneg hd hu hp s hs hx.1.le
      positivity
    · obtain ⟨x, hx, hr⟩ := hR
      refine ⟨x, ⟨hx.1.le, hx.2.le⟩, ?_⟩
      have hload : 0 < u * (continuumFlow delta u phi s x).R + phi := by
        rcases lt_or_eq_of_le hu with hu | hu
        · exact add_pos_of_pos_of_nonneg (mul_pos hu hr) hp
        · have hphi : 0 < phi := by rw [← hu] at hnoise; simpa using hnoise
          rw [← hu]
          simpa using hphi
      positivity
  linarith

/-- Nonzero continuum risk is positive somewhere in every initial open time interval. -/
theorem continuumFlow_exists_positive_risk {delta u phi : ℝ} (hd : 0 < delta)
    (hu : 0 ≤ u) (hp : 0 ≤ phi) (s : Moments) (hs : s.psd)
    (hnonzero : ∃ y, 0 ≤ y ∧ (continuumFlow delta u phi s y).R ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    ∃ x ∈ Ioo 0 t, 0 < (continuumFlow delta u phi s x).R := by
  by_contra hn
  have hRzero : Set.EqOn (fun x => (continuumFlow delta u phi s x).R)
      (fun _ => (0 : ℝ)) (Ioo 0 t) := by
    intro x hx
    have hr := continuumFlow_R_nonneg hd hu hp s hs hx.1.le
    have hnot : ¬0 < (continuumFlow delta u phi s x).R := fun hr => hn ⟨x, hx, hr⟩
    exact le_antisymm (le_of_not_gt hnot) hr
  have hCzero : Set.EqOn (fun x => (continuumFlow delta u phi s x).C)
      (fun _ => (0 : ℝ)) (Ioo 0 t) := by
    intro x hx
    have hz : HasDerivAt (fun x => (continuumFlow delta u phi s x).R) 0 x :=
      (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
        (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) (fun y hy => hRzero hy))
    have heq := (continuumFlow_hasDerivAt delta u phi s x).1.unique hz
    change -2 * delta * (continuumFlow delta u phi s x).C = 0 at heq
    nlinarith
  have hVzero : Set.EqOn (fun x => (continuumFlow delta u phi s x).V)
      (fun _ => (0 : ℝ)) (Ioo 0 t) := by
    intro x hx
    have hz : HasDerivAt (fun x => (continuumFlow delta u phi s x).C) 0 x :=
      (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
        (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) (fun y hy => hCzero hy))
    have heq := (continuumFlow_hasDerivAt delta u phi s x).2.2.unique hz
    change (continuumFlow delta u phi s x).R - (continuumFlow delta u phi s x).C -
      delta * (continuumFlow delta u phi s x).V = 0 at heq
    have hr : (continuumFlow delta u phi s x).R = 0 := hRzero hx
    have hc : (continuumFlow delta u phi s x).C = 0 := hCzero hx
    rw [hr, hc] at heq
    nlinarith
  have hmid : t / 2 ∈ Ioo 0 t := by constructor <;> linarith
  have hphi : phi = 0 := by
    have hz : HasDerivAt (fun x => (continuumFlow delta u phi s x).V) 0 (t / 2) :=
      (hasDerivAt_const (t / 2) (0 : ℝ)).congr_of_eventuallyEq
        (Filter.eventually_of_mem (Ioo_mem_nhds hmid.1 hmid.2) (fun y hy => hVzero hy))
    have heq := (continuumFlow_hasDerivAt delta u phi s (t / 2)).2.1.unique hz
    change 2 * (continuumFlow delta u phi s (t / 2)).C -
      2 * (continuumFlow delta u phi s (t / 2)).V +
      2 / delta * (u * (continuumFlow delta u phi s (t / 2)).R + phi) = 0 at heq
    have hr : (continuumFlow delta u phi s (t / 2)).R = 0 := hRzero hmid
    have hc : (continuumFlow delta u phi s (t / 2)).C = 0 := hCzero hmid
    have hv : (continuumFlow delta u phi s (t / 2)).V = 0 := hVzero hmid
    rw [hr, hc, hv] at heq
    field_simp [hd.ne'] at heq
    nlinarith
  have hmidzero : continuumFlow delta u phi s (t / 2) = 0 :=
    Moments.ext (hRzero hmid) (hVzero hmid) (hCzero hmid)
  have hclosed := hRzero.closure (continuumFlow_R_continuous delta u phi s) continuous_const
  rw [closure_Ioo ht.ne] at hclosed
  subst phi
  have hshift : IsMomentSolution delta u 0
      (fun y => continuumFlow delta u 0 s (y + t / 2)) := by
    intro y _
    obtain ⟨hR, hV, hC⟩ := continuumFlow_hasDerivAt delta u 0 s (y + t / 2)
    have hi := (hasDerivAt_id y).add_const (t / 2)
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Function.comp_def, id_eq, mul_one] using hR.comp y hi
    · simpa only [Function.comp_def, id_eq, mul_one] using hV.comp y hi
    · simpa only [Function.comp_def, id_eq, mul_one] using hC.comp y hi
  have hz : IsMomentSolution delta u 0 (fun _ => (0 : Moments)) := by
    intro y _
    simpa [continuumField, show (0 : Moments) = ⟨0, 0, 0⟩ from rfl] using
      And.intro (hasDerivAt_const y (0 : ℝ))
        (And.intro (hasDerivAt_const y (0 : ℝ)) (hasDerivAt_const y (0 : ℝ)))
  obtain ⟨y, hy, hny⟩ := hnonzero
  apply hny
  by_cases hyt : y ≤ t
  · exact hclosed ⟨hy, hyt⟩
  · have hforward := momentSolution_unique hshift hz
      (by simpa only [zero_add] using hmidzero) (t := y - t / 2) (by linarith)
    have hR := congrArg Moments.R hforward
    change (continuumFlow delta u 0 s (y - t / 2 + t / 2)).R = 0 at hR
    simpa only [sub_add_cancel, add_sub_cancel_right] using hR

/-- Noise gives strict rank growth at every positive time whenever risk is not identically zero. -/
theorem continuumFlow_rankDefect_pos {delta u phi : ℝ} (hd : 0 < delta)
    (hu : 0 ≤ u) (hp : 0 ≤ phi) (hnoise : 0 < u + phi)
    (s : Moments) (hs : s.psd)
    (hnonzero : ∃ y, 0 ≤ y ∧ (continuumFlow delta u phi s y).R ≠ 0)
    {t : ℝ} (ht : 0 < t) : 0 < (continuumFlow delta u phi s t).rankDefect :=
  continuumFlow_rankDefect_pos_of_positive_risk hd hu hp hnoise s hs ht
    (continuumFlow_exists_positive_risk hd hu hp s hs hnonzero ht)

/-- The covariance becomes positive definite at every positive time under nontrivial noise. -/
theorem continuumFlow_cov_posDef {delta u phi : ℝ} (hd : 0 < delta)
    (hu : 0 ≤ u) (hp : 0 ≤ phi) (hnoise : 0 < u + phi)
    (s : Moments) (hs : s.psd)
    (hnonzero : ∃ y, 0 ≤ y ∧ (continuumFlow delta u phi s y).R ≠ 0)
    {t : ℝ} (ht : 0 < t) : (continuumFlow delta u phi s t).cov.PosDef := by
  apply (continuumFlow_psd hd hu hp s hs ht.le).posDef_iff_det_ne_zero.mpr
  have hQ := continuumFlow_rankDefect_pos hd hu hp hnoise s hs hnonzero ht
  have heq : (continuumFlow delta u phi s t).cov.det =
      (continuumFlow delta u phi s t).rankDefect := by
    simp [Moments.cov, Matrix.det_fin_two, Moments.rankDefect, pow_two]
  rw [heq]
  exact hQ.ne'

end
end SparseSGD
