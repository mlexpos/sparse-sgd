import SparseSGD.Discrete.FreeRisk
import SparseSGD.Discrete.GeometricDecay
import SparseSGD.Discrete.Loads

open Filter
open scoped Topology Matrix.Norms.Operator

namespace SparseSGD

noncomputable section

/-- A positive free input makes a nonnegative renewal sequence nonsummable
when the feedback mass is at least one. The Cauchy product is Tonelli's
reindexing of all past injections. -/
theorem scalar_renewal_not_summable
    (h a R : ℕ → ℝ) (u : ℝ)
    (hh : ∀ n, 0 ≤ h n) (hzero : h 0 = 0) (hmass : HasSum h 1)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 0 ≤ R n)
    (hu : 1 ≤ u) (hapos : ∃ n, 0 < a n)
    (hrec : ∀ k, R k = a k + ∑ j ∈ Finset.range k, h (k-j) * (u * R j)) :
    ¬ Summable R := by
  intro hsumR
  have haR : ∀ k, a k ≤ R k := by
    intro k
    rw [hrec k]
    have hc : 0 ≤ ∑ j ∈ Finset.range k, h (k-j) * (u * R j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hh _) (mul_nonneg (by linarith) (hR _))
    linarith
  have hsumA : Summable a := hsumR.of_nonneg_of_le ha haR
  have hnormR : Summable (fun n => ‖R n‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hR _)] using hsumR
  have hnormH : Summable (fun n => ‖h n‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hh _)] using hmass.summable
  have hconv := hasSum_sum_range_mul_of_summable_norm hnormR hnormH
  have hconv' : HasSum (fun k => ∑ j ∈ Finset.range k, h (k-j) * (u * R j))
      (u * ∑' n, R n) := by
    have hm := hconv.mul_left u
    rw [hmass.tsum_eq, mul_one] at hm
    convert hm using 1
    funext k
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, hzero, mul_zero, add_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have heq : (∑' n, R n) = (∑' n, a n) + u * ∑' n, R n := by
    have ht := hsumA.hasSum.add hconv'
    have ht' : HasSum R ((∑' n, a n) + u * ∑' n, R n) := by
      convert ht using 1
      funext k
      exact hrec k
    exact hsumR.hasSum.unique ht'
  obtain ⟨n, hn⟩ := hapos
  have hp : 0 < ∑' k, a k := hsumA.tsum_pos ha n hn
  have hS : 0 ≤ ∑' k, R k := tsum_nonneg hR
  have hgain : (∑' k, R k) ≤ u * ∑' k, R k := by nlinarith
  linarith

/-- Every nonzero positive semidefinite start is visible in the free risk at
time zero or one, since the momentum coefficient is nonzero. -/
theorem freeRisk_pos_zero_or_one (p : Params) (s : Moments)
    (hs : s.psd) (hs0 : s ≠ 0) (hb : p.beta ≠ 0) :
    0 < freeRisk p s 0 ∨ 0 < freeRisk p s 1 := by
  have hR := Moments.psd_R_nonneg hs
  have hV := Moments.psd_V_nonneg hs
  have hQ := Moments.psd_rankDefect_nonneg hs
  have hzero : freeRisk p s 0 = s.R := by simp [freeRisk, Moments.cov]
  by_cases hp : 0 < s.R
  · exact Or.inl (hzero ▸ hp)
  have hR0 : s.R = 0 := by linarith
  have hC0 : s.C = 0 := by
    unfold Moments.rankDefect at hQ
    rw [hR0] at hQ
    nlinarith [sq_nonneg s.C]
  have hVpos : 0 < s.V := by
    by_contra hn
    have hV0 : s.V = 0 := by linarith
    apply hs0
    exact Moments.ext hR0 hV0 hC0
  right
  have hfirst : freeRisk p s 1 = p.beta ^ 2 * s.V := by
    simp [freeRisk, Params.meanMatrix, Moments.cov, Matrix.mul_apply,
      Fin.sum_univ_two, hR0, hC0]
    ring
  rw [hfirst]
  exact mul_pos (sq_pos_of_ne_zero hb) hVpos

/-- Above the exact renewal threshold, a nonzero PSD start has infinite total
risk when the additive noise vanishes (source Corollary stab(iii)). -/
theorem trajectory_risk_not_summable (jury : External.JuryStability)
    (p : Params) (s : Moments) (hs : s.psd) (hs0 : s ≠ 0)
    (hb0 : 1 / 2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2 * (1+p.beta))
    (hnoise : 0 ≤ p.noise) (hadd : p.additive = 0)
    (hload : 1 ≤ p.renormNoise) :
    ¬ Summable (fun k => (p.trajectory s k).R) := by
  apply scalar_renewal_not_summable (normalizedKernelLag p) (freeRisk p s)
    (fun k => (p.trajectory s k).R) p.renormNoise
  · exact normalized_kernel_lag_nonneg jury p hb0 hb1 hw0 hw1
  · simp [normalizedKernelLag]
  · exact normalized_kernel_lag_hasSum jury p hb0 hb1 hw0 hw1
  · exact freeRisk_nonneg p s hs
  · intro k
    apply Moments.psd_R_nonneg
    apply p.trajectory_psd s hs hw0.le _ hnoise _ k
    · unfold Params.eps; linarith
    · rw [hadd]
  · exact hload
  · rcases freeRisk_pos_zero_or_one p s hs hs0 (by linarith) with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · intro k
    simpa [Params.renormAdditive, hadd] using
      normalized_trajectory_recurrence jury p s hb0 hb1 hw0 hw1 k

/-- Exponential weighting converts a strict renewal gain into a geometric
error estimate. This is the finite-horizon maximum argument in stab(ii). -/
theorem weighted_renewal_geometric_bound
    (h D : ℕ → ℝ) (u t E gamma : ℝ)
    (hh : ∀ n, 0 ≤ h n) (hu : 0 ≤ u) (ht : 0 < t)
    (hE : 0 ≤ E) (hg0 : 0 ≤ gamma) (hg1 : gamma < 1)
    (hmass : ∀ k, u * (∑ j ∈ Finset.range k, h (k-j) * t ^ (k-j)) ≤ gamma)
    (hrec : ∀ k, t ^ k * |D k| ≤ E +
      u * ∑ j ∈ Finset.range k, (h (k-j) * t ^ (k-j)) * (t ^ j * |D j|)) :
    ∀ k, |D k| ≤ (E / (1-gamma)) * (t⁻¹) ^ k := by
  let M := E / (1-gamma)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hfix : E + gamma * M = M := by
    dsimp [M]
    field_simp [ne_of_gt (by linarith : 0 < 1-gamma)]
    <;> ring
  have hb : ∀ k, t ^ k * |D k| ≤ M := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      calc
        t ^ k * |D k| ≤ E + u * ∑ j ∈ Finset.range k,
            (h (k-j) * t ^ (k-j)) * (t ^ j * |D j|) := hrec k
        _ ≤ E + u * ∑ j ∈ Finset.range k, (h (k-j) * t ^ (k-j)) * M := by
          gcongr with j hj
          · exact mul_nonneg (hh _) (pow_nonneg ht.le _)
          · exact ih j (Finset.mem_range.mp hj)
        _ = E + (u * ∑ j ∈ Finset.range k, h (k-j) * t ^ (k-j)) * M := by
          rw [← Finset.sum_mul]
          ring
        _ ≤ E + gamma * M := by gcongr; exact hmass k
        _ = M := hfix
  intro k
  have h := hb k
  have hp : 0 < t ^ k := pow_pos ht _
  have h' : |D k| ≤ M / t ^ k := (le_div_iff₀ hp).2 (by simpa [mul_comm] using h)
  simpa [M, div_eq_mul_inv, inv_pow] using h'

/-- Rescaling the impulse recurrence gives the response of a nearby mean
dynamics. Thus exponential moments of the actual kernel can be evaluated
using the same two-dimensional Jury assumption and Lyapunov identity. -/
def scaledMeanParams (p : Params) (t : ℝ) : Params :=
  ⟨t^2 * p.beta, 1 + t^2 * p.beta - t * (1+p.beta-p.w), p.noise, p.additive⟩

theorem kickResponse_scaledMeanParams (p : Params) (t : ℝ) (n : ℕ) :
    kickResponse (scaledMeanParams p t) n = t ^ n * kickResponse p n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [kickResponse_one, kickResponse_one]
    simp [scaledMeanParams]
    ring
  | more n h0 h1 =>
    rw [kickResponse_recurrence, h0, h1, kickResponse_recurrence]
    simp only [scaledMeanParams]
    rw [pow_add, pow_succ]
    ring

theorem weighted_normalized_kernel_hasSum (jury : External.JuryStability)
    (p : Params) (t : ℝ)
    (hb : (scaledMeanParams p t).beta < 1)
    (hw0 : 0 < (scaledMeanParams p t).w)
    (hw1 : (scaledMeanParams p t).w < 2 * (1+(scaledMeanParams p t).beta))
    (hplus : 1 + (scaledMeanParams p t).beta ≠ 0) :
    HasSum (fun n => normalizedKernelLag p n * (t^2)^n)
      (((1-p.curvature) * 2*p.w*p.eps * t^2) /
        (2*(scaledMeanParams p t).w * (1-(scaledMeanParams p t).beta) *
          (1-(scaledMeanParams p t).curvature))) := by
  let q := scaledMeanParams p t
  have hc : 0 < 1-q.curvature := by
    unfold Params.curvature
    rw [sub_pos]
    apply (div_lt_iff₀ (by linarith : 0 < 2*(1+q.beta))).2
    simpa only [one_mul] using hw1
  have hs := kickResponse_sq_hasSum q hw0.ne' (by linarith) hplus hc.ne'
    (External.mean_powers_tendsto_zero jury q hb hw0 hw1)
  have h := hs.mul_left ((1-p.curvature)*2*p.w*p.eps*t^2)
  have hshift : HasSum (fun n => normalizedKernelLag p (n+1) * (t^2)^(n+1))
      (((1-p.curvature)*2*p.w*p.eps*t^2) /
        (2*q.w*(1-q.beta)*(1-q.curvature))) := by
    convert h using 1
    · funext n
      simp only [q, kickResponse_scaledMeanParams, normalizedKernelLag]
      rw [pow_succ (t^2) n]
      rw [show (t^2)^n = (t^n)^2 by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      ring
    · ring
  apply (hasSum_nat_add_iff' 1).1
  simpa [normalizedKernelLag, q] using hshift

def weightedKernelMass (p : Params) (t : ℝ) : ℝ :=
  ((1-p.curvature)*2*p.w*p.eps*t^2) /
    (2*(scaledMeanParams p t).w * (1-(scaledMeanParams p t).beta) *
      (1-(scaledMeanParams p t).curvature))

/-- Strict gain at weight one persists for some exponential weight greater
than one. Both the weighted mass and stability are proved for the actual
impulse kernel, rather than postulated. -/
theorem exists_weighted_kernel_gain (jury : External.JuryStability)
    (p : Params) (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))
    (hload : p.renormNoise < 1) :
    ∃ t : ℝ, 1 < t ∧
      (scaledMeanParams p t).beta < 1 ∧
      0 < (scaledMeanParams p t).w ∧
      (scaledMeanParams p t).w < 2*(1+(scaledMeanParams p t).beta) ∧
      HasSum (fun n => normalizedKernelLag p n * (t^2)^n) (weightedKernelMass p t) ∧
      p.renormNoise * weightedKernelMass p t < 1 := by
  have hc : 0 < 1-p.curvature := by
    unfold Params.curvature
    rw [sub_pos]
    apply (div_lt_iff₀ (by linarith : 0 < 2*(1+p.beta))).2
    simpa using hw1
  have hq1 : scaledMeanParams p 1 = p := by
    cases p
    simp [scaledMeanParams]
  have hm1 : weightedKernelMass p 1 = 1 := by
    unfold weightedKernelMass
    rw [hq1]
    unfold Params.eps
    field_simp [hw0.ne', hc.ne', ne_of_gt (by linarith : 0 < 1-p.beta)]
  have hbcont : ContinuousAt (fun t : ℝ => (scaledMeanParams p t).beta) 1 := by
    unfold scaledMeanParams
    fun_prop
  have hwcont : ContinuousAt (fun t : ℝ => (scaledMeanParams p t).w) 1 := by
    unfold scaledMeanParams
    fun_prop
  have hccont : ContinuousAt (fun t : ℝ => (scaledMeanParams p t).curvature) 1 := by
    unfold Params.curvature
    apply hwcont.div
      (continuousAt_const.mul (continuousAt_const.add hbcont))
    simp [hq1]
    linarith
  have hmcont : ContinuousAt (weightedKernelMass p) 1 := by
    unfold weightedKernelMass
    apply ContinuousAt.div
    · fun_prop
    · exact ((continuousAt_const.mul hwcont).mul
        (continuousAt_const.sub hbcont)).mul (continuousAt_const.sub hccont)
    · simp only [hq1]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hw0.ne')
        (by linarith)) hc.ne'
  have hbNear : ∀ᶠ t : ℝ in 𝓝 1, (scaledMeanParams p t).beta < 1 :=
    hbcont.eventually_lt_const (by simpa [hq1] using hb1)
  have hbPos : ∀ᶠ t : ℝ in 𝓝 1, 0 < (scaledMeanParams p t).beta :=
    hbcont.eventually_const_lt (by simp [hq1]; linarith)
  have hwNear : ∀ᶠ t : ℝ in 𝓝 1, 0 < (scaledMeanParams p t).w :=
    hwcont.eventually_const_lt (by simpa [hq1] using hw0)
  have hwUpper : ∀ᶠ t : ℝ in 𝓝 1,
      (scaledMeanParams p t).w < 2*(1+(scaledMeanParams p t).beta) :=
    hwcont.eventually_lt (continuousAt_const.mul (continuousAt_const.add hbcont))
      (by simpa [hq1] using hw1)
  have hgain : ∀ᶠ t : ℝ in 𝓝 1, p.renormNoise * weightedKernelMass p t < 1 :=
    (continuousAt_const.mul hmcont).eventually_lt_const (by simpa [hm1] using hload)
  have hall := hbNear.and (hbPos.and (hwNear.and (hwUpper.and hgain)))
  obtain ⟨t, ht, hb, hbpos, hw, hwupper, hgain⟩ := hall.exists_gt
  refine ⟨t, ht, hb, hw, hwupper, ?_, hgain⟩
  exact weighted_normalized_kernel_hasSum jury p t hb hw hwupper (by linarith)

/-- Weighted free risk is bounded whenever the nearby scaled mean dynamics
satisfies Jury. -/
theorem weighted_freeRisk_bounded (jury : External.JuryStability)
    (p : Params) (s : Moments) (t : ℝ) (ht : 0 < t)
    (hb : (scaledMeanParams p t).beta < 1)
    (hw0 : 0 < (scaledMeanParams p t).w)
    (hw1 : (scaledMeanParams p t).w < 2*(1+(scaledMeanParams p t).beta)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k, (t^2)^k * |freeRisk p s k| ≤ A := by
  have hdecay : Tendsto (fun n : ℕ => (t • p.meanMatrix)^n) atTop (𝓝 0) := by
    apply jury
    · simpa [Matrix.det_smul, p.det_meanMatrix, scaledMeanParams] using hb
    · rw [Matrix.det_smul, p.det_meanMatrix, Matrix.trace_smul]
      norm_num only [Fintype.card_fin, smul_eq_mul]
      simp only [Params.meanMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      change 0 < 1+t^2*p.beta-t*(1+p.beta-p.w) at hw0
      nlinarith
    · have h : 0 < 1 + (t*p.meanMatrix.trace) + t^2*p.beta := by
        simp [scaledMeanParams] at hw1
        simp [Params.meanMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
        linarith
      simpa [Matrix.det_smul, p.det_meanMatrix, Matrix.trace_smul] using h
  have hcont : Continuous (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
      |(M * s.cov * M.transpose) 0 0|) := by fun_prop
  have hlim := (hcont.tendsto 0).comp hdecay
  have hid : ∀ k, |(((t • p.meanMatrix)^k) * s.cov *
      ((t • p.meanMatrix)^k).transpose) 0 0| = (t^2)^k * |freeRisk p s k| := by
    intro k
    rw [smul_pow, Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm,
      smul_mul_assoc, smul_smul]
    simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, freeRisk]
    simp only [abs_of_nonneg (pow_nonneg ht.le k)]
    rw [show (t^2)^k = t^k*t^k by
      rw [← pow_two, ← pow_mul, ← pow_mul, Nat.mul_comm]]
  have hlim' : Tendsto (fun k => (t^2)^k * |freeRisk p s k|) atTop (𝓝 0) := by
    change Tendsto (fun k => |(((t • p.meanMatrix)^k) * s.cov *
      ((t • p.meanMatrix)^k).transpose) 0 0|) atTop
        (𝓝 |((0 : Matrix (Fin 2) (Fin 2) ℝ) * s.cov *
          (0 : Matrix (Fin 2) (Fin 2) ℝ).transpose) 0 0|) at hlim
    simpa only [hid, zero_mul, Matrix.zero_apply, abs_zero] using hlim
  obtain ⟨A, hA⟩ := hlim'.bddAbove_range
  refine ⟨max A 0, le_max_right _ _, ?_⟩
  intro k
  exact (hA (Set.mem_range_self k)).trans (le_max_left _ _)

theorem renewal_partial_mass_eq (h : ℕ → ℝ) (hzero : h 0 = 0) (k : ℕ) :
    (∑ j ∈ Finset.range k, h (k-j)) = ∑ n ∈ Finset.range (k+1), h n := by
  have hreflect : (∑ j ∈ Finset.range k, h (k-j)) =
      ∑ j ∈ Finset.range k, h (j+1) := by
    calc
      _ = ∑ j ∈ Finset.range k, h ((k-1-j)+1) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        have := Finset.mem_range.mp hj
        omega
      _ = _ := Finset.sum_range_reflect (fun n => h (n+1)) k
  rw [hreflect, Finset.sum_range_succ']
  simp [hzero]

/-- An exponential moment bounds the mass remaining after every horizon. -/
theorem weighted_renewal_tail_bound (h : ℕ → ℝ) (t B : ℝ)
    (hh : ∀ n, 0 ≤ h n) (hzero : h 0 = 0)
    (hmass : HasSum h 1) (ht : 1 ≤ t)
    (hweight : HasSum (fun n => h n * t^n) B) (k : ℕ) :
    0 ≤ 1-(∑ j ∈ Finset.range k, h (k-j)) ∧
    t^k * (1-(∑ j ∈ Finset.range k, h (k-j))) ≤ B := by
  rw [renewal_partial_mass_eq h hzero]
  have htail := hmass.summable.sum_add_tsum_nat_add (k+1)
  rw [hmass.tsum_eq] at htail
  have htailEq : 1-(∑ n ∈ Finset.range (k+1), h n) = ∑' n, h (n+(k+1)) := by
    linarith
  rw [htailEq]
  constructor
  · exact tsum_nonneg fun n => hh _
  · have hs : Summable (fun n => h (n+(k+1))) :=
      hmass.summable.comp_injective (add_left_injective (k+1))
    have hsw : Summable (fun n => h (n+(k+1))*t^(n+(k+1))) :=
      hweight.summable.comp_injective (add_left_injective (k+1))
    rw [← hs.tsum_mul_left]
    calc
      (∑' n, t^k*h (n+(k+1))) ≤ ∑' n, h (n+(k+1))*t^(n+(k+1)) := by
        apply Summable.tsum_le_tsum _ (hs.mul_left _) hsw
        intro n
        have hp : t^k ≤ t^(n+(k+1)) := pow_le_pow_right₀ ht (by omega)
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (hh (n+(k+1)))
      _ ≤ B := by
        have hwTail := hweight.summable.sum_add_tsum_nat_add (k+1)
        rw [hweight.tsum_eq] at hwTail
        have hp : 0 ≤ ∑ n ∈ Finset.range (k+1), h n*t^n :=
          Finset.sum_nonneg fun n _ => mul_nonneg (hh _) (pow_nonneg (by linarith) _)
        linarith

/-- The full weighted-renewal floor estimate, including the exponentially
small missing kernel tail. -/
theorem scalar_renewal_floor_geometric
    (h a R : ℕ → ℝ) (u phi t A B : ℝ)
    (hh : ∀ n, 0 ≤ h n) (hzero : h 0 = 0) (hmass : HasSum h 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hphi : 0 ≤ phi) (ht : 1 < t)
    (hA : 0 ≤ A) (hfree : ∀ k, t^k * |a k| ≤ A)
    (hweight : HasSum (fun n => h n*t^n) B) (hgain : u*B < 1)
    (hrec : ∀ k, R k = a k + ∑ j ∈ Finset.range k, h (k-j)*(u*R j+phi)) :
    ∀ k, |R k-phi/(1-u)| ≤
      ((A+(phi/(1-u))*B)/(1-u*B))*(t⁻¹)^k := by
  let L := phi/(1-u)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLfix : u*L+phi = L := by
    dsimp [L]
    field_simp [ne_of_gt (by linarith : 0 < 1-u)]
    ring
  have hB : 0 ≤ B := by rw [← hweight.tsum_eq]; exact tsum_nonneg fun n => by positivity [hh n]
  apply weighted_renewal_geometric_bound h (fun k => R k-L) u t (A+L*B) (u*B)
    hh hu0 (by linarith) (by positivity) (by positivity) hgain
  · intro k
    have hz : h 0*t^0 = 0 := by simp [hzero]
    rw [renewal_partial_mass_eq (fun n => h n*t^n) hz]
    apply mul_le_mul_of_nonneg_left _ hu0
    exact sum_le_hasSum _ (fun n _ => by positivity [hh n]) hweight
  · intro k
    let P := ∑ j ∈ Finset.range k, h (k-j)
    have htail := weighted_renewal_tail_bound h t B hh hzero hmass ht.le hweight k
    have hD : R k-L = a k-L*(1-P)+
        ∑ j ∈ Finset.range k, h (k-j)*(u*(R j-L)) := by
      rw [hrec k]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, mul_add,
        Finset.sum_add_distrib]
      dsimp [P]
      nlinarith [hLfix]
    have hc : |∑ j ∈ Finset.range k, h (k-j)*(u*(R j-L))| ≤
        u*∑ j ∈ Finset.range k, h (k-j)*|R j-L| := by
      calc
        _ ≤ ∑ j ∈ Finset.range k, |h (k-j)*(u*(R j-L))| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_mul, abs_mul, abs_of_nonneg (hh _), abs_of_nonneg hu0]
          ring
    have hab : |R k-L| ≤ |a k|+L*(1-P)+
        u*∑ j ∈ Finset.range k, h (k-j)*|R j-L| := by
      rw [hD]
      calc
        _ ≤ |a k-L*(1-P)|+|∑ j ∈ Finset.range k, h (k-j)*(u*(R j-L))| := abs_add_le _ _
        _ ≤ (|a k|+|L*(1-P)|)+u*∑ j ∈ Finset.range k, h (k-j)*|R j-L| :=
          add_le_add (abs_sub _ _) hc
        _ = _ := by rw [abs_of_nonneg (mul_nonneg hL htail.1)]
    have hmul := mul_le_mul_of_nonneg_left hab (pow_nonneg (by linarith : 0 ≤ t) k)
    have hconv : t^k*(u*∑ j ∈ Finset.range k, h (k-j)*|R j-L|) =
        u*∑ j ∈ Finset.range k, (h (k-j)*t^(k-j))*(t^j*|R j-L|) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk := Finset.mem_range.mp hj
      have hp : t^k = t^(k-j)*t^j := by rw [← pow_add]; congr 1; omega
      rw [hp]
      ring
    rw [mul_add, mul_add, hconv] at hmul
    have htail' : t^k*(L*(1-P)) ≤ L*B := by
      have H := mul_le_mul_of_nonneg_left htail.2 hL
      simpa [P, mul_comm, mul_left_comm, mul_assoc] using H
    linarith [hfree k]

/-- Below the renewal threshold the actual risk approaches the exact floor
at a geometric rate, obtained from an exponential moment of its kernel. -/
theorem trajectory_risk_geometric_convergence (jury : External.JuryStability)
    (p : Params) (s : Moments)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))
    (hnoise : 0 ≤ p.noise) (hadd : 0 ≤ p.additive)
    (hload : p.totalLoad < 1) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r < 1 ∧
      ∀ k, |(p.trajectory s k).R-p.additive/(1-p.totalLoad)| ≤ C*r^k := by
  have hc : 0 < 1-p.curvature := by
    unfold Params.curvature
    rw [sub_pos]
    apply (div_lt_iff₀ (by linarith : 0 < 2*(1+p.beta))).2
    simpa using hw1
  have hu1 : p.renormNoise < 1 := (renormNoise_lt_one_iff p (by linarith)).2 hload
  have hu0 : 0 ≤ p.renormNoise := div_nonneg hnoise hc.le
  have hphi : 0 ≤ p.renormAdditive := div_nonneg hadd hc.le
  obtain ⟨t, ht, hb, hw, hwupper, hweight, hgain⟩ :=
    exists_weighted_kernel_gain jury p hb0 hb1 hw0 hw1 hu1
  obtain ⟨A, hA, hfree⟩ := weighted_freeRisk_bounded jury p s t (by linarith) hb hw hwupper
  let B := weightedKernelMass p t
  have hnonneg := normalized_kernel_lag_nonneg jury p hb0 hb1 hw0 hw1
  have hB : 0 ≤ B := by
    dsimp [B]
    rw [← hweight.tsum_eq]
    exact tsum_nonneg fun n => mul_nonneg (hnonneg _) (pow_nonneg (sq_nonneg _) _)
  have ht2 : 1 < t^2 := by nlinarith
  have hbound := scalar_renewal_floor_geometric (normalizedKernelLag p) (freeRisk p s)
    (fun k => (p.trajectory s k).R) p.renormNoise p.renormAdditive (t^2) A B
    hnonneg (by simp [normalizedKernelLag])
    (normalized_kernel_lag_hasSum jury p hb0 hb1 hw0 hw1)
    hu0 hu1 hphi ht2 hA hfree hweight hgain
    (normalized_trajectory_recurrence jury p s hb0 hb1 hw0 hw1)
  have hfloor := floor_identity p (by linarith) (ne_of_lt hload)
  rw [hfloor] at hbound
  refine ⟨(A+(p.additive/(1-p.totalLoad))*B)/(1-p.renormNoise*B),
    (t^2)⁻¹, ?_, inv_pos.2 (sq_pos_of_pos (by linarith)), ?_, hbound⟩
  · have hden : 0 < 1-p.renormNoise*B := by dsimp [B]; linarith
    exact div_nonneg (add_nonneg hA (mul_nonneg (div_nonneg hadd (by linarith)) hB)) hden.le
  · exact (inv_lt_one₀ (sq_pos_of_pos (by linarith))).2 ht2

theorem trajectory_risk_tendsto_floor (jury : External.JuryStability)
    (p : Params) (s : Moments)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))
    (hnoise : 0 ≤ p.noise) (hadd : 0 ≤ p.additive)
    (hload : p.totalLoad < 1) :
    Tendsto (fun k => (p.trajectory s k).R) atTop
      (𝓝 (p.additive/(1-p.totalLoad))) := by
  obtain ⟨C, r, hC, hr, hr1, hb⟩ :=
    trajectory_risk_geometric_convergence jury p s hb0 hb1 hw0 hw1 hnoise hadd hload
  have hlim : Tendsto (fun k : ℕ => C*r^k) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1)
  apply Metric.tendsto_atTop.2
  intro e he
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim e he
  refine ⟨N, fun k hk => ?_⟩
  have h := hN k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hC (pow_nonneg hr.le _))] at h
  rw [Real.dist_eq]
  exact (hb k).trans_lt h

/-- The actual normalized lag kernel itself has a geometric envelope below
the threshold. -/
theorem normalized_kernel_geometric_bound (jury : External.JuryStability)
    (p : Params) (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))
    (hload : p.renormNoise < 1) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r < 1 ∧
      ∀ n, normalizedKernelLag p n ≤ C*r^n := by
  obtain ⟨t, ht, _, _, _, hsum, _⟩ :=
    exists_weighted_kernel_gain jury p hb0 hb1 hw0 hw1 hload
  have hh := normalized_kernel_lag_nonneg jury p hb0 hb1 hw0 hw1
  have hC : 0 ≤ weightedKernelMass p t := by
    rw [← hsum.tsum_eq]
    exact tsum_nonneg fun n => mul_nonneg (hh _) (pow_nonneg (sq_nonneg _) _)
  have ht2 : 1 < t^2 := by nlinarith
  refine ⟨weightedKernelMass p t, (t^2)⁻¹, hC,
    inv_pos.2 (by positivity), (inv_lt_one₀ (by positivity)).2 ht2, ?_⟩
  intro n
  have hterm : normalizedKernelLag p n*(t^2)^n ≤ weightedKernelMass p t :=
    by
      have H := sum_le_hasSum {n}
        (fun m _ => mul_nonneg (hh m) (pow_nonneg (sq_nonneg t) m)) hsum
      simpa using H
  have hn : 0 < (t^2)^n := pow_pos (by positivity) _
  have H := (le_div_iff₀ hn).2 hterm
  simpa [div_eq_mul_inv, inv_pow] using H

/-- Nonsummability rules out exponential decay of the noise-free affine
recursion's linear part on any nonzero PSD initial condition. -/
theorem trajectory_risk_not_geometrically_decaying (jury : External.JuryStability)
    (p : Params) (s : Moments) (hs : s.psd) (hs0 : s ≠ 0)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))
    (hnoise : 0 ≤ p.noise) (hadd : p.additive = 0)
    (hload : 1 ≤ p.renormNoise) :
    ¬ ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧
      ∀ k, (p.trajectory s k).R ≤ C*r^k := by
  rintro ⟨C, r, _, hr, hr1, hbound⟩
  apply trajectory_risk_not_summable jury p s hs hs0 hb0 hb1 hw0 hw1 hnoise hadd hload
  have hsum := (summable_geometric_of_lt_one hr hr1).mul_left C
  apply hsum.of_nonneg_of_le _ hbound
  intro k
  apply Moments.psd_R_nonneg
  apply p.trajectory_psd s hs hw0.le _ hnoise _ k
  · unfold Params.eps; linarith
  · rw [hadd]

end
end SparseSGD
