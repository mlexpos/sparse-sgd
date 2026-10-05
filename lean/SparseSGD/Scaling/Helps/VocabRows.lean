import SparseSGD.Probability.LeastSquares.Model
import SparseSGD.Probability.LeastSquares.Trajectory
import SparseSGD.Probability.LeastSquares.Process

/-!
# v2 lem:vocab_rows: the rows of the vocabulary decouple

Model: `V` tokens with weights `p_j` (summing to one); a sample is a token `t`, a Gaussian input
`x̃` and a label noise `ζ`; the state holds row errors `e_j` and scaled momenta `q_j`.  The error
form of the minibatch gradient is `vocabGradient`, and `vocabProcess` runs the shared `(β, η)`
dynamics.

* (R1) `vocab_row_gradient`, (R2) `vocab_row_process`: deterministic row decoupling.
* (R3) `map_rowSample`, `map_rowBatch`, `map_rowWorld`: law of row `j` is the single-feature law
  with density `p_j`.
* (R4) `vocab_row_moment_trajectory` (and `_explicit`): row-`j` moments obey (L1) with
  `w_j = η ε p_j`, `u_{n,j} = η (d+2-p_j)/(2B)`, `φ = η σ² d/(2B)`.
* (R5) `vocab_excess_loss_sample`, `vocab_excess_loss_expectation`: the excess loss on a fresh
  sample is `½ Σ_j p_j ‖e_j‖²`, with expectation `½ Σ_j p_j R_{j,k}`.

Out of scope: the joint law of the rows.  The rows are dependent (the token indicators sum to
one over `j`); the tex claims only the marginal law of each row, and only that is proved.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SparseSGD.Scaling.Helps.VocabRows
open SparseSGD.Probability
open SparseSGD.Probability.LeastSquares
noncomputable section

/-! ## The vocabulary model -/

/-- A vocabulary sample: token `t`, Gaussian input `x̃`, label noise `ζ`. -/
abbrev VSample (d V : ℕ) := Fin V × ((Fin d → ℝ) × ℝ)
/-- A vocabulary minibatch. -/
abbrev VBatch (d V B : ℕ) := Fin B → VSample d V
/-- Row errors `e_j = θ_j - θ⋆_j` and scaled momenta `q_j = η m_j`. -/
abbrev VState (d V : ℕ) := (Fin V → Vec d) × (Fin V → Vec d)
/-- The vocabulary world: initial state and an infinite sequence of batches. -/
abbrev VWorld (d V B : ℕ) := VState d V × (ℕ → VBatch d V B)

/-- The token law `Σ_j p_j δ_j`. -/
def tokenLaw {V : ℕ} (ps : Fin V → unitInterval) : Measure (Fin V) :=
  ∑ j, unitInterval.toNNReal (ps j) • Measure.dirac j

/-- Law of one vocabulary sample: token, then independent Gaussian input and label noise. -/
def vSampleLaw (d : ℕ) {V : ℕ} (ps : Fin V → unitInterval) (ν : Measure ℝ) :
    Measure (VSample d V) :=
  (tokenLaw ps).prod ((standardGaussianProduct d).prod ν)

/-- Law of a minibatch of `B` i.i.d. vocabulary samples. -/
def vBatchLaw (d V B : ℕ) (ps : Fin V → unitInterval) (ν : Measure ℝ) :
    Measure (VBatch d V B) :=
  Measure.pi (fun _ => vSampleLaw d ps ν)

/-- Law of the vocabulary world: initial state `ρ` times i.i.d. batches. -/
def vWorldLaw {d V B : ℕ} (ps : Fin V → unitInterval) (ν : Measure ℝ)
    (ρ : Measure (VState d V)) : Measure (VWorld d V B) :=
  ρ.prod (Measure.infinitePi (fun _ : ℕ => vBatchLaw d V B ps ν))

/-- The error form of the minibatch gradient `G`: sample `i` contributes
`e_{t_i} (⟨x̃_i, e_{t_i}⟩ - ζ_i) x̃_i / B` to row `t_i` (the one-hot embedding of that vector). -/
def vocabGradient {d V B : ℕ} (e : Fin V → Vec d) (a : VBatch d V B) : Fin V → Vec d :=
  (B : ℝ)⁻¹ • ∑ i, Pi.single (a i).1
    ((inner ℝ (WithLp.toLp 2 (a i).2.1 : Vec d) (e (a i).1) - (a i).2.2) •
      (WithLp.toLp 2 (a i).2.1 : Vec d))

/-- One step of the vocabulary dynamics with shared `(β, η)`, as `Model.update`. -/
def vocabUpdate {d V B : ℕ} (beta eta : ℝ) (s : VState d V) (a : VBatch d V B) : VState d V :=
  let q := beta • s.2 + (eta * (1 - beta)) • vocabGradient s.1 a
  (s.1 - q, q)

/-- The vocabulary process, as `Model.process`. -/
def vocabProcess {d V B : ℕ} (beta eta : ℝ) (ω : VWorld d V B) : ℕ → VState d V
  | 0 => ω.1
  | k + 1 => vocabUpdate beta eta (vocabProcess beta eta ω k) (ω.2 k)

/-! ## Row projections -/

/-- Row `j` of a vocabulary sample, as a single-feature sample: the mask is `1[t = j]`. -/
def rowSample {d V : ℕ} (j : Fin V) (a : VSample d V) : Sample d :=
  (decide (a.1 = j), a.2)

/-- Row `j` of a vocabulary state. -/
def rowState {d V : ℕ} (j : Fin V) (s : VState d V) : State d := (s.1 j, s.2 j)

/-- Row `j` of a vocabulary world. -/
def rowWorld {d V B : ℕ} (j : Fin V) (ω : VWorld d V B) : World d B :=
  (rowState j ω.1, fun k i => rowSample j (ω.2 k i))

/-! ## (R1), (R2): deterministic row decoupling -/

/-- v2 lem:vocab_rows, per-row gradient (R1): row `j` of the vocabulary gradient is the
single-feature minibatch gradient of the row-`j` samples. -/
theorem vocab_row_gradient {d V B : ℕ} (e : Fin V → Vec d) (a : VBatch d V B) (j : Fin V) :
    vocabGradient e a j = batchGradient (e j) (fun i => rowSample j (a i)) := by
  classical
  simp only [vocabGradient, batchGradient, Pi.smul_apply, Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (a i).1 = j
  · subst h
    simp [rowSample, LeastSquares.gradient, feature]
  · have h' : j ≠ (a i).1 := fun h2 => h h2.symm
    simp [rowSample, LeastSquares.gradient, feature, h, h']

/-- v2 lem:vocab_rows, per-row update: row `j` of `vocabUpdate` is `Model.update` applied to the
row-`j` state and the row-`j` samples. -/
theorem vocab_row_update {d V B : ℕ} (beta eta : ℝ) (s : VState d V) (a : VBatch d V B)
    (j : Fin V) :
    rowState j (vocabUpdate beta eta s a) =
      update beta eta (rowState j s) (fun i => rowSample j (a i)) := by
  simp [rowState, vocabUpdate, update, vocab_row_gradient]

/-- v2 lem:vocab_rows, per-row process (R2): row `j` of the vocabulary process is the
single-feature process run on `rowWorld j ω`. Deterministic, by induction on `k`. -/
theorem vocab_row_process {d V B : ℕ} (beta eta : ℝ) (ω : VWorld d V B) (j : Fin V) (k : ℕ) :
    rowState j (vocabProcess beta eta ω k) = process beta eta (rowWorld j ω) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [vocabProcess, process, vocab_row_update, ih]
    rfl

/-! ## (R3): row marginals of the laws -/

theorem tokenLaw_isProbabilityMeasure {V : ℕ} (ps : Fin V → unitInterval)
    (hsum : ∑ j, (ps j : ℝ) = 1) : IsProbabilityMeasure (tokenLaw ps) := by
  constructor
  have h : ∑ j, unitInterval.toNNReal (ps j) = 1 := by
    apply NNReal.eq
    simpa using hsum
  simp only [tokenLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one]
  rw [← ENNReal.ofNNReal_finsetSum, h]
  simp

theorem measurable_rowSample {d V : ℕ} (j : Fin V) : Measurable (rowSample (d := d) j) :=
  ((measurable_of_finite (fun t : Fin V => decide (t = j))).comp measurable_fst).prodMk
    measurable_snd

/-- Pushing the token law through the indicator `t ↦ 1[t = j]` gives `Ber(p_j)`. -/
theorem tokenLaw_map_indicator {V : ℕ} (ps : Fin V → unitInterval)
    (hsum : ∑ j, (ps j : ℝ) = 1) (j : Fin V) :
    (tokenLaw ps).map (fun t => decide (t = j)) = bernoulliMeasure true false (ps j) := by
  classical
  have hf : Measurable (fun t : Fin V => decide (t = j)) := measurable_of_finite _
  have hS : ∑ j' ∈ Finset.univ.erase j, unitInterval.toNNReal (ps j') =
      unitInterval.toNNReal (unitInterval.symm (ps j)) := by
    apply NNReal.eq
    have h1 := Finset.add_sum_erase Finset.univ (fun j' => (ps j' : ℝ)) (Finset.mem_univ j)
    simp only [NNReal.coe_sum, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
    linarith
  unfold tokenLaw
  rw [Measure.map_finset_sum hf.aemeasurable]
  simp only [Measure.map_smul _ hf.aemeasurable, Measure.map_dirac' hf]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j), bernoulliMeasure_def, hS.symm]
  simp only [decide_true]
  congr 1
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j' hj' => ?_
  have : decide (j' = j) = false := by simpa using Finset.ne_of_mem_erase hj'
  rw [this]

/-- v2 lem:vocab_rows (R3), sample level: the row-`j` image of the vocabulary sample law is the
single-feature sample law with density `p_j`. -/
theorem map_rowSample (d : ℕ) {V : ℕ} (ps : Fin V → unitInterval)
    (hsum : ∑ j, (ps j : ℝ) = 1) (ν : Measure ℝ) [IsProbabilityMeasure ν] (j : Fin V) :
    (vSampleLaw d ps ν).map (rowSample j) = sampleLaw d (ps j) ν := by
  haveI := tokenLaw_isProbabilityMeasure ps hsum
  have hf : Measurable (fun t : Fin V => decide (t = j)) := measurable_of_finite _
  have h := Measure.map_prod_map (tokenLaw ps) ((standardGaussianProduct d).prod ν) hf
    (measurable_id : Measurable (id : ((Fin d → ℝ) × ℝ) → _))
  rw [Measure.map_id, tokenLaw_map_indicator ps hsum j] at h
  rw [sampleLaw, h]
  rfl

/-- v2 lem:vocab_rows (R3), batch level: the row-`j` image of the batch law. -/
theorem map_rowBatch (d V B : ℕ) (ps : Fin V → unitInterval)
    (hsum : ∑ j, (ps j : ℝ) = 1) (ν : Measure ℝ) [IsProbabilityMeasure ν] (j : Fin V) :
    (vBatchLaw d V B ps ν).map (fun a i => rowSample j (a i)) = batchLaw d B (ps j) ν := by
  have hm : Measurable (rowSample (d := d) j) := measurable_rowSample j
  have : ∀ _ : Fin B, SigmaFinite ((vSampleLaw d ps ν).map (rowSample (d := d) j)) := fun _ => by
    rw [map_rowSample d ps hsum ν j]; infer_instance
  have h := Measure.pi_map_pi (ι := Fin B) (μ := fun _ => vSampleLaw d ps ν)
    (f := fun _ => rowSample (d := d) j) (hμ := this) (fun _ => hm.aemeasurable)
  rw [vBatchLaw, batchLaw, h]
  simp only [map_rowSample d ps hsum ν j]

/-- v2 lem:vocab_rows (R3), world level: the row-`j` image of the vocabulary world law is the
single-feature world law with density `p_j` and initial law the row-`j` image of `ρ`. -/
theorem map_rowWorld {d V B : ℕ} (ps : Fin V → unitInterval)
    (hsum : ∑ j, (ps j : ℝ) = 1) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (ρ : Measure (VState d V)) [IsProbabilityMeasure ρ] (j : Fin V) :
    (vWorldLaw (B := B) ps ν ρ).map (rowWorld j) =
      worldLaw (B := B) (ps j) ν (ρ.map (rowState j)) := by
  have hm : Measurable (rowSample (d := d) j) := measurable_rowSample j
  have hrs : Measurable (rowState (d := d) (V := V) j) := by
    unfold rowState
    exact ((measurable_pi_apply j).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd)
  have hb : Measurable (fun (a : VBatch d V B) i => rowSample (d := d) j (a i)) :=
    Measurable.of_eval fun i => hm.comp (measurable_pi_apply i)
  have hg : Measurable (fun (x : ℕ → VBatch d V B) k => (fun i => rowSample (d := d) j (x k i))) :=
    Measurable.of_eval fun k => hb.comp (measurable_pi_apply k)
  haveI : IsProbabilityMeasure (vBatchLaw d V B ps ν) := by
    haveI : IsProbabilityMeasure (vSampleLaw d ps ν) := by
      haveI := tokenLaw_isProbabilityMeasure ps hsum
      unfold vSampleLaw; infer_instance
    unfold vBatchLaw; infer_instance
  have h := Measure.map_prod_map ρ (Measure.infinitePi (fun _ : ℕ => vBatchLaw d V B ps ν))
    hrs hg
  have h2 := Measure.infinitePi_map_pi (μ := fun _ : ℕ => vBatchLaw d V B ps ν)
    (f := fun _ => fun (a : VBatch d V B) i => rowSample (d := d) j (a i)) (fun _ => hb)
  simp only [map_rowBatch d V B ps hsum ν j] at h2
  rw [worldLaw, ← h2, h]
  rfl

/-! ## (R4): the per-row moment trajectory -/

theorem measurable_rowState {d V : ℕ} (j : Fin V) : Measurable (rowState (d := d) (V := V) j) := by
  unfold rowState
  exact ((measurable_pi_apply j).comp measurable_fst).prodMk
    ((measurable_pi_apply j).comp measurable_snd)

theorem measurable_rowWorld {d V B : ℕ} (j : Fin V) :
    Measurable (rowWorld (d := d) (V := V) (B := B) j) := by
  unfold rowWorld
  refine (measurable_rowState j |>.comp measurable_fst).prodMk ?_
  refine Measurable.of_eval fun k => Measurable.of_eval fun i => ?_
  exact (measurable_rowSample j).comp
    ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_snd))

/-- Integrating a pullback is integrating against the pushforward. -/
theorem integratedMoments_map {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {d : ℕ} (μ : Measure Ω) (g : Ω → Ω') (hg : Measurable g) (e q : Ω' → Vec d)
    (he : Measurable e) (hq : Measurable q) :
    integratedMoments μ (fun ω => e (g ω)) (fun ω => q (g ω)) =
      integratedMoments (μ.map g) e q := by
  have h1 := integral_map (μ := μ) (φ := g) hg.aemeasurable
    (f := fun y => ‖e y‖ ^ 2) (he.norm.pow_const 2).aestronglyMeasurable
  have h2 := integral_map (μ := μ) (φ := g) hg.aemeasurable
    (f := fun y => ‖q y‖ ^ 2) (hq.norm.pow_const 2).aestronglyMeasurable
  have h3 := integral_map (μ := μ) (φ := g) hg.aemeasurable
    (f := fun y => inner ℝ (e y) (q y)) (he.inner hq).aestronglyMeasurable
  simp only [integratedMoments, h1, h2, h3]

/-- v2 lem:vocab_rows (R4): row `j` of the vocabulary process under `vWorldLaw` has exactly the
single-feature moment trajectory (L1) with `w_j = η ε p_j` (here `(1-β) η p_j`),
`u_{n,j} = η (d+2-p_j)/(2B)` and `φ = η σ² d / (2B)`, i.e. `params d B (ps j) ν β η` (see
`params_explicit`), started from the row-`j` initial moments.

Scope: this is the law of each single row. The joint law of the rows is not claimed; the rows
are dependent (the token indicators `1[t_i = j]` sum to one over `j`). -/
theorem vocab_row_moment_trajectory {d V B : ℕ} (hB : 0 < B)
    (ps : Fin V → unitInterval) (hsum : ∑ j, (ps j : ℝ) = 1) (j : Fin V)
    (hpj : 0 < (ps j : ℝ)) (ν : Measure ℝ) (ρ : Measure (VState d V))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0) (beta eta : ℝ)
    (he0 : MemLp (fun s : VState d V => s.1 j) 2 ρ)
    (hq0 : MemLp (fun s : VState d V => s.2 j) 2 ρ) (k : ℕ) :
    integratedMoments (vWorldLaw (B := B) ps ν ρ)
      (fun ω : VWorld d V B => (vocabProcess beta eta ω k).1 j)
      (fun ω : VWorld d V B => (vocabProcess beta eta ω k).2 j) =
    (params d B (ps j) ν beta eta).trajectory
      (integratedMoments ρ (fun s : VState d V => s.1 j) (fun s : VState d V => s.2 j)) k := by
  have hrow (ω : VWorld d V B) : (vocabProcess beta eta ω k).1 j =
      (process beta eta (rowWorld j ω) k).1 ∧ (vocabProcess beta eta ω k).2 j =
      (process beta eta (rowWorld j ω) k).2 := by
    have := vocab_row_process beta eta ω j k
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hL : integratedMoments (vWorldLaw (B := B) ps ν ρ)
      (fun ω : VWorld d V B => (vocabProcess beta eta ω k).1 j)
      (fun ω : VWorld d V B => (vocabProcess beta eta ω k).2 j) =
      integratedMoments (vWorldLaw (B := B) ps ν ρ)
      (fun ω : VWorld d V B => (process beta eta (rowWorld j ω) k).1)
      (fun ω : VWorld d V B => (process beta eta (rowWorld j ω) k).2) := by
    simp only [fun ω => (hrow ω).1, fun ω => (hrow ω).2]
  rw [hL, integratedMoments_map (vWorldLaw (B := B) ps ν ρ) (rowWorld j) (measurable_rowWorld j)
    (fun ω : World d B => (process beta eta ω k).1) (fun ω : World d B => (process beta eta ω k).2)
    (measurable_process d B beta eta k).fst (measurable_process d B beta eta k).snd,
    map_rowWorld ps hsum ν ρ j]
  have hρ := integratedMoments_map ρ (rowState j) (measurable_rowState j)
    (fun s : State d => s.1) (fun s : State d => s.2) measurable_fst measurable_snd
  have hρ' : MemLp (fun s : State d => s.1) 2 (ρ.map (rowState j)) :=
    (memLp_map_measure_iff measurable_fst.aestronglyMeasurable
      (measurable_rowState j).aemeasurable).2 he0
  have hq' : MemLp (fun s : State d => s.2) 2 (ρ.map (rowState j)) :=
    (memLp_map_measure_iff measurable_snd.aestronglyMeasurable
      (measurable_rowState j).aemeasurable).2 hq0
  have hρ2 : integratedMoments ρ (fun s : VState d V => s.1 j) (fun s : VState d V => s.2 j) =
      integratedMoments (ρ.map (rowState j)) Prod.fst Prod.snd := hρ
  rw [hρ2]
  exact leastSquares_moment_trajectory hB (ps j) hpj ν (ρ.map (rowState j)) hz hmean beta eta
    hρ' hq' k

/-- v2 lem:vocab_rows (R4), explicit form: the row-`j` moments satisfy (L1) with the
parameters `(β, (1-β) η p_j, η (d+2-p_j)/(2B), η σ² d/(2B))` of `params_explicit`. -/
theorem vocab_row_moment_trajectory_explicit {d V B : ℕ} (hB : 0 < B)
    (ps : Fin V → unitInterval) (hsum : ∑ j, (ps j : ℝ) = 1) (j : Fin V)
    (hpj : 0 < (ps j : ℝ)) (ν : Measure ℝ) (ρ : Measure (VState d V))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0) (beta eta : ℝ)
    (he0 : MemLp (fun s : VState d V => s.1 j) 2 ρ)
    (hq0 : MemLp (fun s : VState d V => s.2 j) 2 ρ) (k : ℕ) :
    integratedMoments (vWorldLaw (B := B) ps ν ρ)
      (fun ω : VWorld d V B => (vocabProcess beta eta ω k).1 j)
      (fun ω : VWorld d V B => (vocabProcess beta eta ω k).2 j) =
    (⟨beta, eta * (1 - beta) * (ps j : ℝ), eta * (d + 2 - (ps j : ℝ)) / (2 * B),
        eta * labelVariance ν * d / (2 * B)⟩ : Params).trajectory
      (integratedMoments ρ (fun s : VState d V => s.1 j) (fun s : VState d V => s.2 j)) k := by
  rw [vocab_row_moment_trajectory hB ps hsum j hpj ν ρ hz hmean beta eta he0 hq0 k,
    params_explicit (ps j) hpj.ne' ν beta eta]

/-! ## (R5): the excess loss on a fresh sample -/

/-- Excess loss of the row errors `e` on the sample `a = (t, x̃, ζ)`: `½ ⟨x̃, e_t⟩²` (the
label noise only adds the constant `σ²/2`). -/
def vExcessLoss {d V : ℕ} (e : Fin V → Vec d) (a : VSample d V) : ℝ :=
  (1 / 2) * (inner ℝ (WithLp.toLp 2 a.2.1 : Vec d) (e a.1)) ^ 2

/-- The integral of a function of the token against the token law. -/
theorem tokenLaw_integral {V : ℕ} (ps : Fin V → unitInterval) (g : Fin V → ℝ) :
    ∫ t, g t ∂tokenLaw ps = ∑ j, (ps j : ℝ) * g j := by
  unfold tokenLaw
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul_nnreal_measure, integral_dirac' _ _ (measurable_of_finite g).stronglyMeasurable]
    rw [NNReal.smul_def, smul_eq_mul]
    rfl
  · intro j _
    exact Integrable.of_finite

/-- Second moment of a Gaussian linear form. -/
theorem gaussian_inner_sq_integral {d : ℕ} (e : Vec d) :
    ∫ x : Fin d → ℝ, (inner ℝ (WithLp.toLp 2 x : Vec d) e) ^ 2 ∂standardGaussianProduct d =
      ‖e‖ ^ 2 := by
  classical
  have hint (i j : Fin d) : Integrable (fun x : Fin d → ℝ => x i * x j) (standardGaussianProduct d) :=
    (gaussian_coord_memLp i 2 (by norm_num)).integrable_mul (gaussian_coord_memLp j 2 (by norm_num))
  have h1 : (fun x : Fin d → ℝ => (inner ℝ (WithLp.toLp 2 x : Vec d) e) ^ 2) =
      fun x => ∑ i, ∑ j, (e i * e j) * (x i * x j) := by
    funext x
    rw [euclidean_inner_eq_sum, pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1, integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hint i j).const_mul _))]
  simp_rw [integral_finsetSum _ (fun j _ => (hint _ j).const_mul _), integral_const_mul,
    standardGaussianProduct_covariance]
  rw [euclidean_norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [pow_two]

/-- v2 lem:vocab_rows (R5), fresh sample: the expected excess loss of the row errors `e` on a
fresh vocabulary sample is `½ Σ_j p_j ‖e_j‖²` (Gaussian second moment). -/
theorem vocab_excess_loss_sample (d : ℕ) {V : ℕ} (ps : Fin V → unitInterval)
    (hsum : ∑ j, (ps j : ℝ) = 1) (ν : Measure ℝ) [IsProbabilityMeasure ν] (e : Fin V → Vec d) :
    ∫ a, vExcessLoss e a ∂vSampleLaw d ps ν = (1 / 2) * ∑ j, (ps j : ℝ) * ‖e j‖ ^ 2 := by
  have := tokenLaw_isProbabilityMeasure ps hsum
  have hmeas : Measurable (vExcessLoss (d := d) e) := by
    unfold vExcessLoss
    refine measurable_const.mul (Measurable.pow_const ?_ 2)
    exact (((WithLp.measurable_toLp 2 (Fin d → ℝ)).comp measurable_snd.fst).inner
      ((measurable_of_finite e).comp measurable_fst))
  have hinner (t : Fin V) : ∫ y : (Fin d → ℝ) × ℝ, vExcessLoss e (t, y) ∂(standardGaussianProduct d).prod ν =
      (1 / 2) * ‖e t‖ ^ 2 := by
    have := integral_fun_fst (μ := standardGaussianProduct d) (ν := ν)
      (fun x : Fin d → ℝ => (1 / 2) * (inner ℝ (WithLp.toLp 2 x : Vec d) (e t)) ^ 2)
    simp only [vExcessLoss]
    rw [this, integral_const_mul, gaussian_inner_sq_integral]
    simp
  have hint (t : Fin V) : Integrable (fun y : (Fin d → ℝ) × ℝ => vExcessLoss e (t, y))
      ((standardGaussianProduct d).prod ν) := by
    have h := ((gaussian_inner_memLp (e t) 2 (by norm_num)).integrable_sq.const_mul (1 / 2)).comp_fst ν
    exact h
  have hI : Integrable (vExcessLoss e) (vSampleLaw d ps ν) := by
    unfold vSampleLaw
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    exact ⟨Filter.Eventually.of_forall hint, Integrable.of_finite⟩
  unfold vSampleLaw at hI ⊢
  rw [integral_prod _ hI]
  simp_rw [hinner]
  rw [tokenLaw_integral ps (fun t => (1 / 2) * ‖e t‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Row errors and momenta of the vocabulary process are in `L²` under the world law
(no positivity of `p_j` needed). -/
theorem vocab_row_memLp {d V B : ℕ} (hB : 0 < B)
    (ps : Fin V → unitInterval) (hsum : ∑ j, (ps j : ℝ) = 1) (j : Fin V)
    (ν : Measure ℝ) (ρ : Measure (VState d V))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0) (beta eta : ℝ)
    (he0 : MemLp (fun s : VState d V => s.1 j) 2 ρ)
    (hq0 : MemLp (fun s : VState d V => s.2 j) 2 ρ) (k : ℕ) :
    MemLp (fun ω : VWorld d V B => (vocabProcess beta eta ω k).1 j) 2
        (vWorldLaw (B := B) ps ν ρ) ∧
    MemLp (fun ω : VWorld d V B => (vocabProcess beta eta ω k).2 j) 2
        (vWorldLaw (B := B) ps ν ρ) := by
  have hρ' : MemLp (fun s : State d => s.1) 2 (ρ.map (rowState j)) :=
    (memLp_map_measure_iff measurable_fst.aestronglyMeasurable
      (measurable_rowState j).aemeasurable).2 he0
  have hq' : MemLp (fun s : State d => s.2) 2 (ρ.map (rowState j)) :=
    (memLp_map_measure_iff measurable_snd.aestronglyMeasurable
      (measurable_rowState j).aemeasurable).2 hq0
  have h := process_memLp (B := B) (ps j) ν (ρ.map (rowState j))
    (batchOracle hB (ps j) ν hz hmean) beta eta hρ' hq' k
  rw [← map_rowWorld ps hsum ν ρ j] at h
  have hw : AEMeasurable (rowWorld (d := d) (V := V) (B := B) j) (vWorldLaw (B := B) ps ν ρ) :=
    (measurable_rowWorld (d := d) (V := V) (B := B) j).aemeasurable
  have h1 := (memLp_map_measure_iff (measurable_process d B beta eta k).fst.aestronglyMeasurable
    hw).1 h.1
  have h2 := (memLp_map_measure_iff (measurable_process d B beta eta k).snd.aestronglyMeasurable
    hw).1 h.2
  refine ⟨?_, ?_⟩
  · convert h1 using 1
    funext ω
    exact congrArg Prod.fst (vocab_row_process beta eta ω j k)
  · convert h2 using 1
    funext ω
    exact congrArg Prod.snd (vocab_row_process beta eta ω j k)

/-- v2 lem:vocab_rows (R5), along the trajectory: the expected excess loss on a fresh sample,
drawn independently of the process at time `k`, is `½ Σ_j p_j R_{j,k}`, where
`R_{j,k} = E ‖e_j(k)‖²` is the first coordinate of the row-`j` moments (which satisfy (L1) by
`vocab_row_moment_trajectory`). -/
theorem vocab_excess_loss_expectation {d V B : ℕ} (hB : 0 < B)
    (ps : Fin V → unitInterval) (hsum : ∑ j, (ps j : ℝ) = 1)
    (ν : Measure ℝ) (ρ : Measure (VState d V))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hz : MemLp id 2 ν) (hmean : ∫ z, z ∂ν = 0) (beta eta : ℝ)
    (he0 : ∀ j, MemLp (fun s : VState d V => s.1 j) 2 ρ)
    (hq0 : ∀ j, MemLp (fun s : VState d V => s.2 j) 2 ρ) (k : ℕ) :
    ∫ ω, (∫ a, vExcessLoss (vocabProcess beta eta ω k).1 a ∂vSampleLaw d ps ν)
        ∂(vWorldLaw (B := B) ps ν ρ) =
      (1 / 2) * ∑ j, (ps j : ℝ) *
        (integratedMoments (vWorldLaw (B := B) ps ν ρ)
          (fun ω : VWorld d V B => (vocabProcess beta eta ω k).1 j)
          (fun ω : VWorld d V B => (vocabProcess beta eta ω k).2 j)).R := by
  simp_rw [vocab_excess_loss_sample d ps hsum ν]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    rfl
  · intro j _
    have hm := (vocab_row_memLp hB ps hsum j ν ρ hz hmean beta eta (he0 j) (hq0 j) k).1
    exact ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm).const_mul _

end
end SparseSGD.Scaling.Helps.VocabRows
