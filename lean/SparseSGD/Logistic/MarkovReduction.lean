import SparseSGD.Logistic.ConditionalDrift
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

abbrev Summary := ℝ × ℝ × ℝ × ℝ × ℝ

def rotateNoise {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (z : Fin d → ℝ) : Fin d → ℝ :=
  WithLp.ofLp (O (WithLp.toLp 2 z))

def rotateSample {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (a : Sample d) : Sample d :=
  (a.1, rotateNoise O a.2)

def rotateBatch {d B : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (a : Batch d B) : Batch d B :=
  fun i => rotateSample O (a i)

def rotateState {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (s : State d) : State d := (O s.1, O s.2)

theorem measurable_rotateNoise {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) : Measurable (rotateNoise O) :=
  (WithLp.measurable_ofLp 2 (Fin d → ℝ)).comp
    (O.continuous.measurable.comp (WithLp.measurable_toLp 2 (Fin d → ℝ)))

theorem measurable_rotateSample {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) : Measurable (rotateSample O) :=
  measurable_fst.prodMk ((measurable_rotateNoise O).comp measurable_snd)

theorem measurable_rotateBatch {d B : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) : Measurable (rotateBatch (B := B) O) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_rotateSample O).comp (measurable_pi_apply i)

theorem feature_rotation {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (mu : Vec d) (hmu : O mu = mu)
    (a : Sample d) : feature mu (rotateSample O a) = O (feature mu a) := by
  rcases a with ⟨y, z⟩
  cases y <;> simp [feature, rotateSample, rotateNoise, map_add, hmu]

theorem gradient_rotation {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (p : unitInterval)
    (mu theta : Vec d) (hmu : O mu = mu) (a : Sample d) :
    gradient p mu (O theta) (rotateSample O a) = O (gradient p mu theta a) := by
  simp only [gradient, feature_rotation O mu hmu, O.inner_map_map, map_smul]
  rfl

theorem batchGradient_rotation {d B : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (p : unitInterval)
    (mu theta : Vec d) (hmu : O mu = mu) (a : Batch d B) :
    batchGradient p mu (O theta) (rotateBatch O a) = O (batchGradient p mu theta a) := by
  simp only [batchGradient, rotateBatch, gradient_rotation O p mu theta hmu, map_smul, map_sum]

theorem update_rotation {d B : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (hmu : O mu = mu) (s : State d) (a : Batch d B) :
    update eta beta p mu (rotateState O s) (rotateBatch O a) =
      rotateState O (update eta beta p mu s a) := by
  simp only [update, rotateState, batchGradient_rotation O p mu s.1 hmu,
    map_sub, map_add, map_smul]

theorem signalCoord_rotation {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (mu theta : Vec d) (hmu : O mu = mu) :
    signalCoord mu (O theta) = signalCoord mu theta := by
  unfold signalCoord
  congr 1
  calc
    inner ℝ (O theta) mu = inner ℝ (O theta) (O mu) := by rw [hmu]
    _ = inner ℝ theta mu := O.inner_map_map theta mu

theorem bulkPart_rotation {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (mu theta : Vec d) (hmu : O mu = mu) :
    bulkPart mu (O theta) = O (bulkPart mu theta) := by
  simp only [bulkPart, signalCoord_rotation O mu theta hmu, map_sub, map_smul, hmu]

theorem summary_rotation {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (mu : Vec d) (hmu : O mu = mu)
    (s : State d) : summary mu (rotateState O s) = summary mu s := by
  simp only [summary, rotateState, signalCoord_rotation O mu _ hmu, bulkPart_rotation O mu _ hmu,
    O.norm_map, O.inner_map_map]

theorem measurable_summary {d : ℕ} (mu : Vec d) : Measurable (summary mu) := by
  unfold summary
  have hθ := (measurable_bulkPart mu).comp (measurable_fst : Measurable (Prod.fst : State d → Vec d))
  have hm := (measurable_bulkPart mu).comp (measurable_snd : Measurable (Prod.snd : State d → Vec d))
  exact ((measurable_signalCoord mu).comp measurable_fst).prodMk
    (((measurable_signalCoord mu).comp measurable_snd).prodMk
      ((hθ.norm.pow_const 2).prodMk ((hm.norm.pow_const 2).prodMk (hθ.inner hm))))

/-- The actual product Gaussian is invariant under every orthogonal rotation. -/
theorem gaussian_rotation_invariant {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) :
    (SparseSGD.Probability.standardGaussianProduct d).map (rotateNoise O) =
      SparseSGD.Probability.standardGaussianProduct d := by
  apply (MeasurableEquiv.toLp 2 (Fin d → ℝ)).map_measurableEquiv_injective
  have he : (fun z : Fin d → ℝ => WithLp.toLp 2 (rotateNoise O z)) =
      fun z => O (WithLp.toLp 2 z) := by funext z; rfl
  rw [MeasurableEquiv.coe_toLp, Measure.map_map (WithLp.measurable_toLp 2 (Fin d → ℝ))
    (measurable_rotateNoise O)]
  change (SparseSGD.Probability.standardGaussianProduct d).map
    (fun z => WithLp.toLp 2 (rotateNoise O z)) = _
  rw [he]
  change (SparseSGD.Probability.standardGaussianProduct d).map (O ∘ WithLp.toLp 2) = _
  rw [← Measure.map_map O.continuous.measurable (WithLp.measurable_toLp 2 (Fin d → ℝ))]
  simp only [SparseSGD.Probability.standardGaussianProduct, map_pi_eq_stdGaussian, stdGaussian_map]

theorem sample_rotation_invariant {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (p : unitInterval) :
    (sampleLaw d p).map (rotateSample O) = sampleLaw d p := by
  change ((bernoulliMeasure true false p).prod (SparseSGD.Probability.standardGaussianProduct d)).map
    (Prod.map id (rotateNoise O)) = _
  rw [← Measure.map_prod_map _ _ measurable_id (measurable_rotateNoise O), Measure.map_id,
    gaussian_rotation_invariant]
  rfl

theorem batch_rotation_invariant {d B : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (p : unitInterval) :
    (batchLaw d B p).map (rotateBatch O) = batchLaw d B p := by
  change (Measure.pi fun _ : Fin B => sampleLaw d p).map
    (fun a i => rotateSample O (a i)) = _
  rw [Measure.pi_map_pi (fun _ => (measurable_rotateSample O).aemeasurable)]
  simp only [sample_rotation_invariant, batchLaw]

private def markov_familyCombination {d n : ℕ} (v : Fin n → Vec d) : (Fin n → ℝ) →ₗ[ℝ] Vec d where
  toFun c := ∑ i, c i • v i
  map_add' c e := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Pi.smul_apply, Finset.smul_sum, smul_smul]

private theorem markov_familyCombination_norm {d n : ℕ} (v w : Fin n → Vec d)
    (hG : ∀ i j, inner ℝ (v i) (v j) = inner ℝ (w i) (w j)) (c : Fin n → ℝ) :
    ‖markov_familyCombination v c‖ = ‖markov_familyCombination w c‖ := by
  have hs : ‖markov_familyCombination v c‖ ^ 2 = ‖markov_familyCombination w c‖ ^ 2 := by
    simp only [← real_inner_self_eq_norm_sq, markov_familyCombination, LinearMap.coe_mk,
      AddHom.coe_mk, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hG]
  nlinarith [norm_nonneg (markov_familyCombination v c), norm_nonneg (markov_familyCombination w c)]

/-- Equal finite Gram matrices determine an ambient orthogonal map, including
linearly dependent families. This supplies the orbit-classification step. -/
theorem exists_rotation_of_gram_eq {d n : ℕ} (v w : Fin n → Vec d)
    (hG : ∀ i j, inner ℝ (v i) (v j) = inner ℝ (w i) (w j)) :
    ∃ O : Vec d ≃ₗᵢ[ℝ] Vec d, ∀ i, O (v i) = w i := by
  classical
  let L := markov_familyCombination v
  let W := markov_familyCombination w
  have hn (c : Fin n → ℝ) : ‖L c‖ = ‖W c‖ := markov_familyCombination_norm v w hG c
  have hk : LinearMap.ker L ≤ LinearMap.ker W := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    apply norm_eq_zero.mp
    rw [← hn, hc, norm_zero]
  let T : LinearMap.range L →ₗ[ℝ] Vec d :=
    ((LinearMap.ker L).liftQ W hk).comp L.quotKerEquivRange.symm.toLinearMap
  have hT (c : Fin n → ℝ) : T ⟨L c, LinearMap.mem_range_self L c⟩ = W c := by
    simp only [T, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.liftQ_apply]
    rfl
  let I : LinearMap.range L →ₗᵢ[ℝ] Vec d :=
    { toLinearMap := T
      norm_map' := by
        intro x
        obtain ⟨c, hc⟩ := x.property
        have he : x = ⟨L c, LinearMap.mem_range_self L c⟩ := Subtype.ext hc.symm
        rw [he, hT]
        exact (hn c).symm }
  let O := I.extend.toLinearIsometryEquiv rfl
  refine ⟨O, ?_⟩
  intro i
  have hv : L (Pi.single i 1) = v i := by simp [L, markov_familyCombination, Pi.single_apply]
  have hw : W (Pi.single i 1) = w i := by simp [W, markov_familyCombination, Pi.single_apply]
  rw [← hv]
  change I.extend.toLinearIsometryEquiv rfl (L (Pi.single i 1)) = _
  rw [LinearIsometry.toLinearIsometryEquiv_apply]
  have he := I.extend_apply ⟨L (Pi.single i 1), LinearMap.mem_range_self L _⟩
  rw [he]
  exact (hT (Pi.single i 1)).trans hw

private theorem markov_bulk_inner {d : ℕ} (mu x y : Vec d) (hr : 0 < r mu) :
    inner ℝ (bulkPart mu x) (bulkPart mu y) =
      inner ℝ x y - inner ℝ x mu * inner ℝ y mu / r mu ^ 2 := by
  simp only [bulkPart, signalCoord, smul_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm mu y]
  simp only [r] at hr ⊢
  field_simp
  <;> ring

/-- The five source coordinates classify the complete state modulo rotations
fixing the signal, even when the two bulk vectors are dependent or zero. -/
theorem summary_eq_iff_rotation {d : ℕ} (mu : Vec d) (hr : 0 < r mu) (s t : State d) :
    summary mu s = summary mu t ↔
      ∃ O : Vec d ≃ₗᵢ[ℝ] Vec d, O mu = mu ∧ rotateState O s = t := by
  constructor
  · intro hs
    have hθ := congrArg (fun x : Summary => x.1) hs
    have hm := congrArg (fun x : Summary => x.2.1) hs
    have hR := congrArg (fun x : Summary => x.2.2.1) hs
    have hV := congrArg (fun x : Summary => x.2.2.2.1) hs
    have hC := congrArg (fun x : Summary => x.2.2.2.2) hs
    change inner ℝ s.1 mu / r mu = inner ℝ t.1 mu / r mu at hθ
    change inner ℝ s.2 mu / r mu = inner ℝ t.2 mu / r mu at hm
    field_simp [ne_of_gt hr] at hθ hm
    change ‖bulkPart mu s.1‖ ^ 2 = ‖bulkPart mu t.1‖ ^ 2 at hR
    change ‖bulkPart mu s.2‖ ^ 2 = ‖bulkPart mu t.2‖ ^ 2 at hV
    change inner ℝ (bulkPart mu s.1) (bulkPart mu s.2) =
      inner ℝ (bulkPart mu t.1) (bulkPart mu t.2) at hC
    rw [bulkPart_norm_sq mu s.1 hr, bulkPart_norm_sq mu t.1 hr, hθ] at hR
    rw [bulkPart_norm_sq mu s.2 hr, bulkPart_norm_sq mu t.2 hr, hm] at hV
    rw [markov_bulk_inner mu s.1 s.2 hr, markov_bulk_inner mu t.1 t.2 hr, hθ, hm] at hC
    have hnθ : ‖s.1‖ ^ 2 = ‖t.1‖ ^ 2 := by linarith
    have hnm : ‖s.2‖ ^ 2 = ‖t.2‖ ^ 2 := by linarith
    have hinner : inner ℝ s.1 s.2 = inner ℝ t.1 t.2 := by linarith
    have hθrev : inner ℝ mu s.1 = inner ℝ mu t.1 := by
      rw [real_inner_comm s.1 mu, real_inner_comm t.1 mu]; exact hθ
    have hmrev : inner ℝ mu s.2 = inner ℝ mu t.2 := by
      rw [real_inner_comm s.2 mu, real_inner_comm t.2 mu]; exact hm
    have hinnerrev : inner ℝ s.2 s.1 = inner ℝ t.2 t.1 := by
      rw [real_inner_comm s.1 s.2, real_inner_comm t.1 t.2]; exact hinner
    have hG : ∀ i j : Fin 3, inner ℝ (![mu, s.1, s.2] i) (![mu, s.1, s.2] j) =
        inner ℝ (![mu, t.1, t.2] i) (![mu, t.1, t.2] j) := by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [real_inner_self_eq_norm_sq, hnθ, hnm, hinner, hθ, hm, hθrev, hmrev, hinnerrev]
    obtain ⟨O, hO⟩ := exists_rotation_of_gram_eq ![mu, s.1, s.2] ![mu, t.1, t.2] hG
    refine ⟨O, ?_, ?_⟩
    · simpa using hO 0
    · apply Prod.ext
      · simpa [rotateState] using hO 1
      · simpa [rotateState] using hO 2
  · rintro ⟨O, hmu, rfl⟩
    exact (summary_rotation O mu hmu s).symm

/-- Equality of five-variable summaries gives identical transition laws of the
five-variable summary, for the actual sample law. -/
theorem summary_transition_eq {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (hr : 0 < r mu) (s t : State d) (hs : summary mu s = summary mu t) :
    (batchLaw d B p).map (fun a => summary mu (update eta beta p mu s a)) =
      (batchLaw d B p).map (fun a => summary mu (update eta beta p mu t a)) := by
  obtain ⟨O, hmu, rfl⟩ := (summary_eq_iff_rotation mu hr s t).mp hs
  have ht : Measurable (fun a : Batch d B => summary mu (update eta beta p mu (rotateState O s) a)) :=
    (measurable_summary mu).comp
      ((measurable_update d B eta beta p mu).comp (measurable_const.prodMk measurable_id))
  symm
  calc
    _ = ((batchLaw d B p).map (rotateBatch O)).map
        (fun a => summary mu (update eta beta p mu (rotateState O s) a)) := by
      rw [batch_rotation_invariant]
    _ = (batchLaw d B p).map
        (fun a => summary mu (update eta beta p mu (rotateState O s) (rotateBatch O a))) := by
      simpa only [Function.comp_def] using Measure.map_map ht (measurable_rotateBatch O)
    _ = _ := by
      congr 1
      funext a
      rw [update_rotation O eta beta p mu hmu s a, summary_rotation O mu hmu]

/-- The feasible five-coordinate states, with their inherited measurable structure. -/
abbrev ReducedState {d : ℕ} (mu : Vec d) := Set.range (summary mu)

def reduceState {d : ℕ} (mu : Vec d) (s : State d) : ReducedState mu :=
  ⟨summary mu s, ⟨s, rfl⟩⟩

theorem measurable_reduceState {d : ℕ} (mu : Vec d) : Measurable (reduceState mu) :=
  (measurable_summary mu).subtype_mk

theorem reduceState_surjective {d : ℕ} (mu : Vec d) : Function.Surjective (reduceState mu) := by
  rintro ⟨x, s, rfl⟩
  exact ⟨s, rfl⟩

theorem reduceState_rotation {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (mu : Vec d)
    (hmu : O mu = mu) (s : State d) : reduceState mu (rotateState O s) = reduceState mu s :=
  Subtype.ext (summary_rotation O mu hmu s)

def fullSummaryKernel {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) :
    Kernel (State d) (ReducedState mu) :=
  ((Kernel.id : Kernel (State d) (State d)).prod
    (Kernel.const (State d) (batchLaw d B p))).map
    (fun z : State d × Batch d B => reduceState mu (update eta beta p mu z.1 z.2))

theorem fullSummaryKernel_apply {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) : fullSummaryKernel (B := B) eta beta p mu s =
    (batchLaw d B p).map (fun a => reduceState mu (update eta beta p mu s a)) := by
  have hF : Measurable (fun z : State d × Batch d B => reduceState mu (update eta beta p mu z.1 z.2)) :=
    (measurable_reduceState mu).comp (measurable_update d B eta beta p mu)
  rw [fullSummaryKernel, Kernel.map_apply _ hF, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hF measurable_prodMk_left]
  rfl

instance fullSummaryKernel_markov {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) :
    IsMarkovKernel (fullSummaryKernel (B := B) eta beta p mu) :=
  Kernel.IsMarkovKernel.map _ ((measurable_reduceState mu).comp (measurable_update d B eta beta p mu))

theorem fullSummaryKernel_fiber {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (hr : 0 < r mu) (s t : State d) (hs : reduceState mu s = reduceState mu t) :
    fullSummaryKernel (B := B) eta beta p mu s = fullSummaryKernel (B := B) eta beta p mu t := by
  obtain ⟨O, hmu, rfl⟩ := (summary_eq_iff_rotation mu hr s t).mp (congrArg Subtype.val hs)
  rw [fullSummaryKernel_apply, fullSummaryKernel_apply]
  have ht : Measurable (fun a : Batch d B => reduceState mu
      (update eta beta p mu (rotateState O s) a)) :=
    (measurable_reduceState mu).comp
      ((measurable_update d B eta beta p mu).comp (measurable_const.prodMk measurable_id))
  symm
  calc
    _ = ((batchLaw d B p).map (rotateBatch O)).map
        (fun a => reduceState mu (update eta beta p mu (rotateState O s) a)) := by
      rw [batch_rotation_invariant]
    _ = (batchLaw d B p).map
        (fun a => reduceState mu (update eta beta p mu (rotateState O s) (rotateBatch O a))) := by
      simpa only [Function.comp_def] using Measure.map_map ht (measurable_rotateBatch O)
    _ = _ := by
      congr 1
      funext a
      rw [update_rotation O eta beta p mu hmu s a, reduceState_rotation O mu hmu]

def summaryRepresentative {d : ℕ} (mu : Vec d) (x : ReducedState mu) : State d :=
  Classical.choose x.property

theorem reduceState_representative {d : ℕ} (mu : Vec d) (x : ReducedState mu) :
    reduceState mu (summaryRepresentative mu x) = x :=
  Subtype.ext (Classical.choose_spec x.property)

/-- The actual five-variable transition kernel. Measurability descends through
the surjective Borel summary map; the chosen representative need not be measurable. -/
def reducedKernel {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (hr : 0 < r mu) : Kernel (ReducedState mu) (ReducedState mu) where
  toFun x := fullSummaryKernel (B := B) eta beta p mu (summaryRepresentative mu x)
  measurable' := by
    apply ((measurable_reduceState mu).measurable_comp_iff_of_surjective
      (reduceState_surjective mu)).mp
    convert (fullSummaryKernel (B := B) eta beta p mu).measurable using 1
    funext s
    exact fullSummaryKernel_fiber eta beta p mu hr _ _ (reduceState_representative mu _)

theorem reducedKernel_apply_reduceState {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (hr : 0 < r mu) (s : State d) :
    reducedKernel (B := B) eta beta p mu hr (reduceState mu s) =
      fullSummaryKernel (B := B) eta beta p mu s :=
  fullSummaryKernel_fiber eta beta p mu hr _ _ (reduceState_representative mu _)

instance reducedKernel_markov {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (hr : 0 < r mu) : IsMarkovKernel (reducedKernel (B := B) eta beta p mu hr) where
  isProbabilityMeasure x := by
    change IsProbabilityMeasure (fullSummaryKernel (B := B) eta beta p mu (summaryRepresentative mu x))
    infer_instance

def reducedProcess {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (ω : World d B) (k : ℕ) : ReducedState mu :=
  reduceState mu (process eta beta p mu ω k)

def reducedPast {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (k : ℕ)
    (ω : World d B) : Fin (k+1) → ReducedState mu :=
  fun i => reducedProcess eta beta p mu ω i

def reducedSigma (d B : ℕ) (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (k : ℕ) :
    MeasurableSpace (World d B) := MeasurableSpace.comap (reducedPast eta beta p mu k) inferInstance

theorem reducedSigma_le_past (d B : ℕ) (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (k : ℕ) :
    reducedSigma d B eta beta p mu k ≤ pastSigma d B k := by
  have hm : @Measurable (World d B) (Fin (k+1) → ReducedState mu)
      (pastSigma d B k) inferInstance (reducedPast eta beta p mu k) := by
    letI : MeasurableSpace (World d B) := pastSigma d B k
    change Measurable (fun ω : World d B => fun i : Fin (k+1) => reducedProcess eta beta p mu ω i)
    apply Measurable.of_eval
    intro i
    exact (measurable_reduceState mu).comp
      ((process_past_measurable d B eta beta p mu i).mono
        (pastSigma_mono (Nat.le_of_lt_succ i.isLt)) le_rfl)
  exact hm.comap_le

theorem reducedProcess_history_measurable (d B : ℕ) (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (k : ℕ) :
    @Measurable (World d B) (ReducedState mu) (reducedSigma d B eta beta p mu k) inferInstance
      (fun ω => reducedProcess eta beta p mu ω k) := by
  exact (measurable_pi_apply (Fin.last k)).comp
    (show @Measurable (World d B) (Fin (k+1) → ReducedState mu)
      (reducedSigma d B eta beta p mu k) inferInstance (reducedPast eta beta p mu k) from
      measurable_iff_comap_le.mpr le_rfl)

theorem reducedKernel_integral {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (hr : 0 < r mu) (h : ReducedState mu → ℝ) (hh : Measurable h) (s : State d) :
    (∫ x, h x ∂reducedKernel (B := B) eta beta p mu hr (reduceState mu s)) =
      ∫ a, h (reduceState mu (update eta beta p mu s a)) ∂batchLaw d B p := by
  rw [reducedKernel_apply_reduceState, fullSummaryKernel_apply]
  exact integral_map_of_stronglyMeasurable
    ((measurable_reduceState mu).comp
      ((measurable_update d B eta beta p mu).comp (measurable_const.prodMk measurable_id)))
    hh.stronglyMeasurable

theorem measurable_reducedKernel_integral {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (hr : 0 < r mu) (h : ReducedState mu → ℝ) (hh : Measurable h) :
    Measurable (fun s => ∫ x, h x ∂reducedKernel (B := B) eta beta p mu hr s) := by
  apply ((measurable_reduceState mu).measurable_comp_iff_of_surjective
    (reduceState_surjective mu)).mp
  have hm : Measurable (fun z : State d × Batch d B =>
      h (reduceState mu (update eta beta p mu z.1 z.2))) :=
    hh.comp ((measurable_reduceState mu).comp (measurable_update d B eta beta p mu))
  convert (hm.stronglyMeasurable.integral_prod_right' (ν := batchLaw d B p)).measurable using 1
  funext s
  exact reducedKernel_integral eta beta p mu hr h hh s

/-- The exact coordinate drift of the reduced transition kernel, with the
paper's normalization of its three bulk entries. -/
theorem reducedKernel_drift {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (hr : 0 < r mu)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (s : State d) :
    (∫ x, x.val.2.1 ∂reducedKernel (B := B) eta beta p mu hr (reduceState mu s)) =
      beta * signalCoord mu s.2 + (1-beta) *
        (coefA p mu s.1 * signalCoord mu s.1 + coefB p mu s.1 * r mu) ∧
    (∫ x, x.val.1 ∂reducedKernel (B := B) eta beta p mu hr (reduceState mu s)) =
      signalCoord mu s.1 - eta * (beta * signalCoord mu s.2 + (1-beta) *
        (coefA p mu s.1 * signalCoord mu s.1 + coefB p mu s.1 * r mu)) ∧
    (⟨∫ x, x.val.2.2.1 ∂reducedKernel (B := B) eta beta p mu hr (reduceState mu s),
      eta^2 * ∫ x, x.val.2.2.2.1 ∂reducedKernel (B := B) eta beta p mu hr (reduceState mu s),
      eta * ∫ x, x.val.2.2.2.2 ∂reducedKernel (B := B) eta beta p mu hr (reduceState mu s)⟩ :
      SparseSGD.Moments) =
      (driftParams (B := B) eta beta p mu s.1).step
        ⟨‖bulkPart mu s.1‖^2, eta^2 * ‖bulkPart mu s.2‖^2,
          eta * inner ℝ (bulkPart mu s.1) (bulkPart mu s.2)⟩ := by
  have hm1 : Measurable (fun x : ReducedState mu => x.val.1) := measurable_subtype_coe.fst
  have hm2 : Measurable (fun x : ReducedState mu => x.val.2.1) := measurable_subtype_coe.snd.fst
  have hm3 : Measurable (fun x : ReducedState mu => x.val.2.2.1) := measurable_subtype_coe.snd.snd.fst
  have hm4 : Measurable (fun x : ReducedState mu => x.val.2.2.2.1) := measurable_subtype_coe.snd.snd.snd.fst
  have hm5 : Measurable (fun x : ReducedState mu => x.val.2.2.2.2) := measurable_subtype_coe.snd.snd.snd.snd
  rw [reducedKernel_integral eta beta p mu hr _ hm1,
    reducedKernel_integral eta beta p mu hr _ hm2,
    reducedKernel_integral eta beta p mu hr _ hm3,
    reducedKernel_integral eta beta p mu hr _ hm4,
    reducedKernel_integral eta beta p mu hr _ hm5]
  exact ⟨update_signal_momentum_integral H hB eta beta p mu s hr,
    update_signal_parameter_integral H hB eta beta p mu s hr,
    update_bulk_moment_drift H hB eta beta p mu s hr hp0 hp1⟩

/-- Exact time-homogeneous Markov reduction to the five coordinates. Conditioning
uses their entire past, and the kernel is the actual fresh-batch transition law.
This theorem needs no Stein certificate or moment hypothesis on the initial law. -/
theorem reducedProcess_markov {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (hr : 0 < r mu) (ρ : Measure (State d)) [IsProbabilityMeasure ρ] (k : ℕ)
    (h : ReducedState mu → ℝ) (hh : Measurable h) (C : ℝ) (hC : ∀ x, |h x| ≤ C) :
    (worldLaw p ρ)[fun ω : World d B => h (reducedProcess eta beta p mu ω (k+1)) |
      reducedSigma d B eta beta p mu k] =ᵐ[worldLaw p ρ]
      (fun ω => ∫ x, h x ∂reducedKernel (B := B) eta beta p mu hr
        (reducedProcess eta beta p mu ω k)) := by
  let F : State d × Batch d B → ℝ := fun z =>
    h (reduceState mu (update eta beta p mu z.1 z.2))
  have hF : Measurable F :=
    hh.comp ((measurable_reduceState mu).comp (measurable_update d B eta beta p mu))
  have hhist : Measurable (fun z : History d B k × Batch d B =>
      F (historyState eta beta p mu k z.1, z.2)) :=
    hF.comp (((measurable_historyState d B eta beta p mu k).comp measurable_fst).prodMk measurable_snd)
  have hFi : Integrable (fun z : History d B k × Batch d B =>
      F (historyState eta beta p mu k z.1, z.2))
      ((pastLaw (B := B) p ρ k).prod (batchLaw d B p)) := by
    apply Integrable.of_bound hhist.aestronglyMeasurable C
    exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hC _)
  have hfull := process_fresh_condExp eta beta p mu ρ k F hF hFi
  have heq : (fun ω : World d B => ∫ a, F (process eta beta p mu ω k, a) ∂batchLaw d B p) =
      (fun ω => ∫ x, h x ∂reducedKernel (B := B) eta beta p mu hr
        (reducedProcess eta beta p mu ω k)) := by
    funext ω
    exact (reducedKernel_integral eta beta p mu hr h hh _).symm
  rw [heq] at hfull
  have hle := reducedSigma_le_past d B eta beta p mu k
  have hamb := pastSigma_le_ambient d B k
  have hg : StronglyMeasurable[reducedSigma d B eta beta p mu k]
      (fun ω : World d B => ∫ x, h x ∂reducedKernel (B := B) eta beta p mu hr
        (reducedProcess eta beta p mu ω k)) :=
    ((measurable_reducedKernel_integral eta beta p mu hr h hh).comp
      (reducedProcess_history_measurable d B eta beta p mu k)).stronglyMeasurable
  have ht := condExp_condExp_of_le (μ := worldLaw p ρ)
    (f := fun ω : World d B => F (process eta beta p mu ω k, ω.2 k)) hle hamb
  have hc := condExp_congr_ae (m := reducedSigma d B eta beta p mu k) hfull
  rw [condExp_of_stronglyMeasurable (hle.trans hamb) hg (integrable_condExp.congr hfull)] at hc
  simpa only [F, reducedProcess, process_succ] using ht.symm.trans hc

end
end SparseSGD.Logistic
