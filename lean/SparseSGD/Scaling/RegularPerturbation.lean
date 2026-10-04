import SparseSGD.Continuum.ExponentialStability
import SparseSGD.Comparison.UniformBounds

open scoped Topology Matrix.Norms.Operator
open Filter Set NormedSpace

namespace SparseSGD
noncomputable section

/-- Three-vector form of the moment coordinates. -/
def regularMomentVector (s : Moments) : Fin 3 → ℝ := ![s.R, s.V, s.C]

def regularVectorMoments (v : Fin 3 → ℝ) : Moments := ⟨v 0, v 1, v 2⟩

def regularSemigroup (delta u t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  NormedSpace.exp (t • continuumGenerator delta u)

private theorem regular_mulVec_hasDerivAt
    {M : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {M' : Matrix (Fin 3) (Fin 3) ℝ}
    {v : ℝ → (Fin 3 → ℝ)} {v' : Fin 3 → ℝ} {x : ℝ}
    (hM : HasDerivAt M M' x) (hv : HasDerivAt v v' x) :
    HasDerivAt (fun t => (M t).mulVec (v t))
      (M'.mulVec (v x) + (M x).mulVec v') x := by
  apply hasDerivAt_pi.2
  intro i
  have h (j : Fin 3) := (hasDerivAt_pi.1 (hasDerivAt_pi.1 hM i) j).mul (hasDerivAt_pi.1 hv j)
  convert ((h 0).add (h 1)).add (h 2) using 1
  · funext t
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.mul_apply]
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.add_apply]
    ring

/-- The three-dimensional semigroup is the actual zero-additive-load flow. -/
theorem regularSemigroup_flow (delta u : ℝ) (s : Moments) {t : ℝ} (ht : 0 ≤ t) :
    regularMomentVector (continuumFlow delta u 0 s t) =
      (regularSemigroup delta u t).mulVec (regularMomentVector s) := by
  let f := fun t => regularVectorMoments ((regularSemigroup delta u t).mulVec (regularMomentVector s))
  have hder (x : ℝ) : HasDerivAt
      (fun x => (regularSemigroup delta u x).mulVec (regularMomentVector s))
      ((continuumGenerator delta u).mulVec
        ((regularSemigroup delta u x).mulVec (regularMomentVector s))) x := by
    let L : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] (Fin 3 → ℝ) :=
      (Matrix.mulVecBilin ℝ ℝ).flip (regularMomentVector s)
    have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_exp_smul_const' (continuumGenerator delta u) x)
    change HasDerivAt (fun t => (exp (t • continuumGenerator delta u)).mulVec (regularMomentVector s))
      ((continuumGenerator delta u * exp (x • continuumGenerator delta u)).mulVec
        (regularMomentVector s)) x at h
    simpa only [regularSemigroup, ← Matrix.mulVec_mulVec] using h
  have hsol : IsMomentSolution delta u 0 f := by
    intro x _
    have h := hder x
    refine ⟨?_, ?_, ?_⟩
    · simpa [f, regularVectorMoments, continuumField, continuumGenerator, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three] using hasDerivAt_pi.1 h 0
    · convert hasDerivAt_pi.1 h 1 using 1
      · rfl
      · simp [f, regularVectorMoments, continuumField, continuumGenerator, Matrix.mulVec,
          dotProduct, Fin.sum_univ_three]
        ring
    · convert hasDerivAt_pi.1 h 2 using 1
      · rfl
      · simp [f, regularVectorMoments, continuumField, continuumGenerator, Matrix.mulVec,
          dotProduct, Fin.sum_univ_three]
        ring
  have hf0 : f 0 = s := by simp [f, regularVectorMoments, regularSemigroup,
    regularMomentVector, NormedSpace.exp_zero]
  have heq := continuum_solution_unique delta u 0 s f hf0 hsol t ht
  have hvec := congrArg regularMomentVector heq
  convert hvec.symm using 1
  ext i
  fin_cases i <;> rfl

/-- Variation of constants with respect to a fixed stable reference generator. -/
theorem regular_vector_duhamel (delta u : ℝ) (v F : ℝ → (Fin 3 → ℝ))
    (hv : ∀ x, HasDerivAt v ((continuumGenerator delta u).mulVec (v x) + F x) x)
    (hF : Continuous F) (T : ℝ) :
    v T = (regularSemigroup delta u T).mulVec (v 0) +
      ∫ x in (0 : ℝ)..T, (regularSemigroup delta u (T-x)).mulVec (F x) := by
  have htransport (x : ℝ) : HasDerivAt
      (fun x => (regularSemigroup delta u (T-x)).mulVec (v x))
      ((regularSemigroup delta u (T-x)).mulVec (F x)) x := by
    have hE := (hasDerivAt_exp_smul_const (continuumGenerator delta u) (T-x)).scomp x
      ((hasDerivAt_const x T).sub (hasDerivAt_id x))
    have h := regular_mulVec_hasDerivAt hE (hv x)
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, regularSemigroup, zero_sub, neg_smul, one_smul,
        Matrix.neg_mulVec, Matrix.mulVec_add, ← Matrix.mulVec_mulVec]
      abel
  have hcE : Continuous (fun x => regularSemigroup delta u (T-x)) := by
    unfold regularSemigroup
    exact NormedSpace.exp_continuous.comp ((continuous_const.sub continuous_id).smul continuous_const)
  have hc : Continuous (fun x => (regularSemigroup delta u (T-x)).mulVec (F x)) := by
    apply continuous_pi
    intro i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have he (j : Fin 3) := (continuous_apply j).comp ((continuous_apply i).comp hcE)
    have hf (j : Fin 3) := (continuous_apply j).comp hF
    exact ((he 0).mul (hf 0) |>.add ((he 1).mul (hf 1))).add ((he 2).mul (hf 2))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => htransport x) (hc.intervalIntegrable 0 T)
  simpa only [sub_self, regularSemigroup, zero_smul, NormedSpace.exp_zero,
    Matrix.one_mulVec, sub_zero, add_comm] using (eq_add_of_sub_eq h.symm)

def regularVectorSize (v : Fin 3 → ℝ) : ℝ := |v 0| + |v 1| + |v 2|

@[simp] theorem regularVectorMoments_roundtrip (v : Fin 3 → ℝ) :
    regularMomentVector (regularVectorMoments v) = v := by
  ext i
  fin_cases i <;> rfl

theorem regularVector_norm_le_size (v : Fin 3 → ℝ) : ‖v‖ ≤ regularVectorSize v := by
  apply (pi_norm_le_iff_of_nonneg (show 0 ≤ regularVectorSize v by unfold regularVectorSize; positivity)).2
  intro i
  fin_cases i <;> norm_num [Real.norm_eq_abs, regularVectorSize] <;>
    linarith [abs_nonneg (v 0), abs_nonneg (v 1), abs_nonneg (v 2)]

theorem regularSemigroup_norm_decay {delta u : ℝ} (hd : 0 < delta) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ A lambda : ℝ, 0 < A ∧ 0 < lambda ∧ ∀ v : Fin 3 → ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖(regularSemigroup delta u t).mulVec v‖ ≤ A * regularVectorSize v * Real.exp (-lambda * t) := by
  obtain ⟨A,lambda,hA,hl,hbound⟩ := continuumFlow_exponentially_stable hd hu0 hu1
  refine ⟨A,lambda,hA,hl,?_⟩
  intro v t ht
  have hs := hbound (regularVectorMoments v) t ht
  have hvec := regularSemigroup_flow delta u (regularVectorMoments v) ht
  simp only [regularVectorMoments_roundtrip] at hvec
  rw [← hvec]
  apply (regularVector_norm_le_size _).trans
  exact hs

theorem regular_exp_integral_bound (lambda : ℝ) (hl : 0 < lambda) (T : ℝ) :
    (∫ x in (0 : ℝ)..T, Real.exp (-lambda * (T-x))) ≤ 1 / lambda := by
  have hder (x : ℝ) : HasDerivAt (fun x => Real.exp (-lambda * (T-x)) / lambda)
      (Real.exp (-lambda * (T-x))) x := by
    convert (((((hasDerivAt_const x T).sub (hasDerivAt_id x)).const_mul (-lambda)).exp).div_const lambda) using 1
    · rfl
    · simp only [Pi.sub_apply, id_eq, zero_sub, mul_neg, neg_neg, mul_one]
      field_simp
  have hc : Continuous (fun x => Real.exp (-lambda * (T-x))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x) (hc.intervalIntegrable 0 T)]
  simp only [sub_self, mul_zero, Real.exp_zero, sub_zero]
  have hn : 0 ≤ Real.exp (-lambda * T) / lambda := by positivity
  linarith

theorem regular_duhamel_uniform_bound (delta u A lambda : ℝ) (hA : 0 < A) (hl : 0 < lambda)
    (hsemigroup : ∀ v : Fin 3 → ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖(regularSemigroup delta u t).mulVec v‖ ≤ A * regularVectorSize v * Real.exp (-lambda * t))
    (v F : ℝ → (Fin 3 → ℝ))
    (hv : ∀ x, HasDerivAt v ((continuumGenerator delta u).mulVec (v x) + F x) x)
    (hF : Continuous F) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, 0 ≤ x → regularVectorSize (F x) ≤ B)
    (T : ℝ) (hT : 0 ≤ T) : ‖v T‖ ≤ A * regularVectorSize (v 0) + A * B / lambda := by
  rw [regular_vector_duhamel delta u v F hv hF T]
  have hinit := hsemigroup (v 0) T hT
  have he : Real.exp (-lambda * T) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hinit' : ‖(regularSemigroup delta u T).mulVec (v 0)‖ ≤ A * regularVectorSize (v 0) := by
    apply hinit.trans
    have hz : 0 ≤ A * regularVectorSize (v 0) := by unfold regularVectorSize; positivity
    simpa using mul_le_mul_of_nonneg_left he hz
  have hint := intervalIntegral.norm_integral_le_of_norm_le hT
    (Filter.Eventually.of_forall (fun x (hx : x ∈ Ioc 0 T) => by
      apply (hsemigroup (F x) (T-x) (by linarith [hx.2])).trans
      have hb := mul_le_mul_of_nonneg_left (hbound x hx.1.le) hA.le
      exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le))
    (show IntervalIntegrable (fun x => A * B * Real.exp (-lambda * (T-x))) MeasureTheory.volume 0 T from
      (by fun_prop : Continuous (fun x => A * B * Real.exp (-lambda * (T-x)))).intervalIntegrable 0 T)
  rw [intervalIntegral.integral_const_mul] at hint
  have hexp := mul_le_mul_of_nonneg_left (regular_exp_integral_bound lambda hl T)
    (show 0 ≤ A * B by positivity)
  have hfinal : ‖∫ x in (0 : ℝ)..T, (regularSemigroup delta u (T-x)).mulVec (F x)‖ ≤ A * B / lambda :=
    hint.trans (by simpa [div_eq_mul_inv] using hexp)
  exact (norm_add_le _ _).trans (add_le_add hinit' hfinal)

/-- Parameter perturbations enter as an explicit forcing of the reference generator. -/
def regularParameterForcing (delta u phi delta₀ u₀ phi₀ : ℝ) (s : Moments)
    (t : ℝ) : Fin 3 → ℝ :=
  let x := continuumFlow delta u phi s t
  ![-2 * (delta-delta₀) * x.C,
    2 * (u/delta-u₀/delta₀) * x.R + 2 * (phi/delta-phi₀/delta₀),
    -(delta-delta₀) * x.V]

theorem regularFlowDifference_hasDerivAt (delta u phi delta₀ u₀ phi₀ : ℝ)
    (s s₀ : Moments) (x : ℝ) :
    HasDerivAt
      (fun t => regularMomentVector (continuumFlow delta u phi s t) -
        regularMomentVector (continuumFlow delta₀ u₀ phi₀ s₀ t))
      ((continuumGenerator delta₀ u₀).mulVec
        (regularMomentVector (continuumFlow delta u phi s x) -
          regularMomentVector (continuumFlow delta₀ u₀ phi₀ s₀ x)) +
        regularParameterForcing delta u phi delta₀ u₀ phi₀ s x) x := by
  obtain ⟨hR,hV,hC⟩ := continuumFlow_hasDerivAt delta u phi s x
  obtain ⟨hR₀,hV₀,hC₀⟩ := continuumFlow_hasDerivAt delta₀ u₀ phi₀ s₀ x
  apply hasDerivAt_pi.2
  intro i
  fin_cases i
  · convert hR.sub hR₀ using 1
    · rfl
    · simp [regularMomentVector, regularParameterForcing, continuumGenerator, continuumField,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring
  · convert hV.sub hV₀ using 1
    · rfl
    · simp [regularMomentVector, regularParameterForcing, continuumGenerator, continuumField,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring
  · convert hC.sub hC₀ using 1
    · rfl
    · simp [regularMomentVector, regularParameterForcing, continuumGenerator, continuumField,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring

theorem regularParameterForcing_continuous (delta u phi delta₀ u₀ phi₀ : ℝ) (s : Moments) :
    Continuous (regularParameterForcing delta u phi delta₀ u₀ phi₀ s) := by
  have hR : Continuous (fun t => (continuumFlow delta u phi s t).R) :=
    continuous_iff_continuousAt.2 (fun t => (continuumFlow_hasDerivAt delta u phi s t).1.continuousAt)
  have hV : Continuous (fun t => (continuumFlow delta u phi s t).V) :=
    continuous_iff_continuousAt.2 (fun t => (continuumFlow_hasDerivAt delta u phi s t).2.1.continuousAt)
  have hC : Continuous (fun t => (continuumFlow delta u phi s t).C) :=
    continuous_iff_continuousAt.2 (fun t => (continuumFlow_hasDerivAt delta u phi s t).2.2.continuousAt)
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [regularParameterForcing, Matrix.cons_val] <;> fun_prop

/-- A uniform bound for each coordinate of a positive-semidefinite trajectory. -/
theorem regularFlow_coordinate_bound {delta u phi : ℝ} (hd : 0 < delta)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hp : 0 ≤ phi) (s : Moments) (hs : s.psd)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ i : Fin 3, |regularMomentVector (continuumFlow delta u phi s t) i| ≤
      (1+1/delta) * continuumEnergyBound delta u phi s := by
  let x := continuumFlow delta u phi s t
  let E := continuumEnergyBound delta u phi s
  have hpsd : x.psd := continuumFlow_psd hd hu0 hp s hs ht
  have hR : 0 ≤ x.R := Moments.psd_R_nonneg hpsd
  have hV : 0 ≤ x.V := Moments.psd_V_nonneg hpsd
  have hE : x.R + delta * x.V ≤ E := continuumFlow_energy_uniform_bound hd hu0 hu1 hp s hs ht
  have hEn : 0 ≤ E := le_trans (by positivity) hE
  have hr : x.R ≤ E := by nlinarith
  have hv : x.V ≤ E / delta := (le_div_iff₀ hd).2 (by nlinarith)
  have hc : |x.C| ≤ x.R + x.V := by
    have h := Moments.psd_cross_energy_bound 1 (by norm_num) x hpsd
    norm_num at h
    linarith [abs_nonneg x.C]
  have hb : x.R + x.V ≤ (1+1/delta)*E := by
    convert add_le_add hr hv using 1 <;> ring
  intro i
  fin_cases i
  · change |x.R| ≤ _
    rw [abs_of_nonneg hR]
    exact (show x.R ≤ x.R+x.V by linarith).trans hb
  · change |x.V| ≤ _
    rw [abs_of_nonneg hV]
    exact (show x.V ≤ x.R+x.V by linarith).trans hb
  · change |x.C| ≤ _
    exact hc.trans hb

/-- A concrete bound for the reference-generator forcing, uniform in time. -/
theorem regularParameterForcing_bound {delta u phi : ℝ} (hd : 0 < delta)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hp : 0 ≤ phi) (s : Moments) (hs : s.psd)
    (delta₀ u₀ phi₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    regularVectorSize (regularParameterForcing delta u phi delta₀ u₀ phi₀ s t) ≤
      (3 * |delta-delta₀| + 2 * |u/delta-u₀/delta₀|) *
        ((1+1/delta) * continuumEnergyBound delta u phi s) +
          2 * |phi/delta-phi₀/delta₀| := by
  have hcoords := regularFlow_coordinate_bound hd hu0 hu1 hp s hs ht
  have hR := mul_le_mul_of_nonneg_left (hcoords 0) (show 0 ≤ 2 * |u/delta-u₀/delta₀| by positivity)
  have hV := mul_le_mul_of_nonneg_left (hcoords 1) (abs_nonneg (delta-delta₀))
  have hC := mul_le_mul_of_nonneg_left (hcoords 2) (show 0 ≤ 2 * |delta-delta₀| by positivity)
  simp [regularMomentVector] at hR hV hC
  have ha := abs_add_le (2 * (u/delta-u₀/delta₀) * (continuumFlow delta u phi s t).R)
    (2 * (phi/delta-phi₀/delta₀))
  norm_num [abs_mul] at ha
  norm_num [regularVectorSize, regularParameterForcing, abs_mul, abs_neg]
  rw [abs_sub_comm delta₀ delta]
  nlinarith


/-- Quantitative parameter dependence uniform over every nonnegative time.
The constants depend only on the fixed subcritical reference generator. -/
theorem continuumFlow_uniform_perturbation_bound (delta₀ u₀ : ℝ)
    (hd0 : 0 < delta₀) (hu00 : 0 ≤ u₀) (hu01 : u₀ < 1) :
    ∃ A lambda : ℝ, 0 < A ∧ 0 < lambda ∧
      ∀ (delta u phi phi₀ : ℝ) (s s₀ : Moments),
      0 < delta → 0 ≤ u → u < 1 → 0 ≤ phi → s.psd → ∀ t : ℝ, 0 ≤ t →
      ‖regularMomentVector (continuumFlow delta u phi s t) -
        regularMomentVector (continuumFlow delta₀ u₀ phi₀ s₀ t)‖ ≤
      A * regularVectorSize (regularMomentVector s - regularMomentVector s₀) +
      A * ((3 * |delta-delta₀| + 2 * |u/delta-u₀/delta₀|) *
        ((1+1/delta) * continuumEnergyBound delta u phi s) +
        2 * |phi/delta-phi₀/delta₀|) / lambda := by
  obtain ⟨A,lambda,hA,hl,hsemigroup⟩ := regularSemigroup_norm_decay hd0 hu00 hu01
  refine ⟨A,lambda,hA,hl,?_⟩
  intro delta u phi phi₀ s s₀ hd hu0 hu1 hp hs t ht
  let B := (3 * |delta-delta₀| + 2 * |u/delta-u₀/delta₀|) *
    ((1+1/delta) * continuumEnergyBound delta u phi s) + 2 * |phi/delta-phi₀/delta₀|
  have hS : 0 ≤ (1+1/delta) * continuumEnergyBound delta u phi s :=
    le_trans (abs_nonneg _) (regularFlow_coordinate_bound hd hu0 hu1 hp s hs (t := 0) le_rfl 0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have h := regular_duhamel_uniform_bound delta₀ u₀ A lambda hA hl hsemigroup
    (fun t => regularMomentVector (continuumFlow delta u phi s t) -
      regularMomentVector (continuumFlow delta₀ u₀ phi₀ s₀ t))
    (regularParameterForcing delta u phi delta₀ u₀ phi₀ s)
    (regularFlowDifference_hasDerivAt delta u phi delta₀ u₀ phi₀ s s₀)
    (regularParameterForcing_continuous delta u phi delta₀ u₀ phi₀ s) B hB
    (fun x hx => regularParameterForcing_bound hd hu0 hu1 hp s hs delta₀ u₀ phi₀ hx) t ht
  simpa only [continuumFlow_initial] using h


end
end SparseSGD
