import SparseSGD.Comparison.MomentComparison
import SparseSGD.Scaling.RegularUniformConstants

/-! Regular parameter limits of the actual matrix-exponential moment flow. -/
open scoped Topology Matrix.Norms.Operator
open Filter

set_option maxHeartbeats 1500000

namespace SparseSGD
noncomputable section

/-- Six Euclidean coordinates encode `(delta,u,phi,R₀,V₀,C₀)`. -/
def regularInitial (q : Fin 6 → ℝ) : Moments := ⟨q 3, q 4, q 5⟩

def regularFlowVector (q : Fin 6 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  homogeneousFlowVector (q 0) (q 1) (q 2) (regularInitial q) t

/-- Joint continuity follows from the genuine homogeneous matrix exponential. -/
theorem regularFlowVector_continuousAt (q : Fin 6 → ℝ) (t : ℝ) (hd : q 0 ≠ 0) :
    ContinuousAt (fun z : (Fin 6 → ℝ) × ℝ => regularFlowVector z.1 z.2) (q, t) := by
  have hc (i : Fin 6) : ContinuousAt (fun z : (Fin 6 → ℝ) × ℝ => z.1 i) (q, t) :=
    (continuous_apply i).continuousAt.comp continuous_fst.continuousAt
  have hgen : ContinuousAt
      (fun z : (Fin 6 → ℝ) × ℝ => homogeneousGenerator (z.1 0) (z.1 1) (z.1 2)) (q, t) := by
    apply continuousAt_pi.2
    intro i
    apply continuousAt_pi.2
    intro j
    fin_cases i <;> fin_cases j <;> simp only [homogeneousGenerator] <;>
      fun_prop (disch := exact hd)
  have hexp : ContinuousAt
      (fun z : (Fin 6 → ℝ) × ℝ => NormedSpace.exp
        (z.2 • homogeneousGenerator (z.1 0) (z.1 1) (z.1 2))) (q, t) :=
    NormedSpace.exp_continuous.continuousAt.comp (continuous_snd.continuousAt.smul hgen)
  apply continuousAt_pi.2
  intro i
  unfold regularFlowVector homogeneousFlowVector Matrix.mulVec dotProduct
  have hm (j : Fin 4) : ContinuousAt
      (fun z : (Fin 6 → ℝ) × ℝ =>
        NormedSpace.exp (z.2 • homogeneousGenerator (z.1 0) (z.1 1) (z.1 2)) i j) (q, t) :=
    (continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hexp)
  simp only [Fin.sum_univ_four, homogeneousInitial, regularInitial, Matrix.cons_val]
  fun_prop

/-- Joint parameter limits are uniform on every compact set of times. -/
theorem regularFlowVector_tendstoUniformlyOn {ι : Type*} {l : Filter ι}
    {Q : ι → (Fin 6 → ℝ)} {q : Fin 6 → ℝ} (hQ : Tendsto Q l (𝓝 q))
    (hd : q 0 ≠ 0) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n t => regularFlowVector (Q n) t) (regularFlowVector q) l K := by
  let U : Set (Fin 6 → ℝ) := {p | p 0 ≠ 0}
  have hU : U ∈ 𝓝 q :=
    (isOpen_ne_fun (continuous_apply 0) continuous_const).mem_nhds hd
  let _ : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hc : ContinuousOn
      (fun z : (Fin 6 → ℝ) × K => regularFlowVector z.1 z.2) (U ×ˢ Set.univ) := by
    intro z hz
    have hmap : ContinuousAt (fun z : (Fin 6 → ℝ) × K => (z.1, (z.2 : ℝ))) z :=
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousAt
    have hcont := ContinuousAt.comp (f := fun z : (Fin 6 → ℝ) × K => (z.1, (z.2 : ℝ)))
      (regularFlowVector_continuousAt z.1 (z.2 : ℝ) hz.1) hmap
    exact hcont.continuousWithinAt
  have hu : TendstoUniformly (fun p (t : K) => regularFlowVector p t)
      (fun t : K => regularFlowVector q t) (𝓝 q) := hc.tendstoUniformly hU
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  exact hQ.eventually ((Metric.tendstoUniformly_iff.1 hu) ε hε)

/-- Coordinates used for joint convergence of moment triples. -/
def momentCoordinates (s : Moments) : Fin 3 → ℝ := ![s.R, s.V, s.C]

/-- All three physical moment coordinates converge uniformly on compact times. -/
theorem continuumFlow_tendstoUniformlyOn {ι : Type*} {l : Filter ι}
    {delta u phi : ι → ℝ} {s : ι → Moments}
    {delta₀ u₀ phi₀ : ℝ} {s₀ : Moments}
    (hd : Tendsto delta l (𝓝 delta₀)) (hu : Tendsto u l (𝓝 u₀))
    (hp : Tendsto phi l (𝓝 phi₀))
    (hsR : Tendsto (fun n => (s n).R) l (𝓝 s₀.R))
    (hsV : Tendsto (fun n => (s n).V) l (𝓝 s₀.V))
    (hsC : Tendsto (fun n => (s n).C) l (𝓝 s₀.C))
    (hd0 : 0 < delta₀) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun n t => momentCoordinates (continuumFlow (delta n) (u n) (phi n) (s n) t))
      (fun t => momentCoordinates (continuumFlow delta₀ u₀ phi₀ s₀ t)) l K := by
  let Q := fun n => ![delta n, u n, phi n, (s n).R, (s n).V, (s n).C]
  let q : Fin 6 → ℝ := ![delta₀, u₀, phi₀, s₀.R, s₀.V, s₀.C]
  have hQ : Tendsto Q l (𝓝 q) := by
    apply tendsto_pi_nhds.2
    intro i
    fin_cases i <;> first | exact hd | exact hu | exact hp | exact hsR | exact hsV | exact hsC
  have h := regularFlowVector_tendstoUniformlyOn hQ hd0.ne' K hK
  have hproj : UniformContinuous (fun v : Fin 4 → ℝ => fun i : Fin 3 => v i.castSucc) := by
    apply uniformContinuous_pi.2
    intro i
    exact Pi.uniformContinuous_proj (fun _ : Fin 4 => ℝ) i.castSucc
  have h' := hproj.comp_tendstoUniformlyOn h
  convert h' using 1
  · funext n t i
    fin_cases i <;> rfl
  · funext t i
    fin_cases i <;> rfl


/-- In particular the population risk coordinate converges uniformly on compact times. -/
theorem continuumFlow_risk_tendstoUniformlyOn {ι : Type*} {l : Filter ι}
    {delta u phi : ι → ℝ} {s : ι → Moments}
    {delta₀ u₀ phi₀ : ℝ} {s₀ : Moments}
    (hd : Tendsto delta l (𝓝 delta₀)) (hu : Tendsto u l (𝓝 u₀))
    (hp : Tendsto phi l (𝓝 phi₀))
    (hsR : Tendsto (fun n => (s n).R) l (𝓝 s₀.R))
    (hsV : Tendsto (fun n => (s n).V) l (𝓝 s₀.V))
    (hsC : Tendsto (fun n => (s n).C) l (𝓝 s₀.C))
    (hd0 : 0 < delta₀) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun n t => (continuumFlow (delta n) (u n) (phi n) (s n) t).R)
      (fun t => (continuumFlow delta₀ u₀ phi₀ s₀ t).R) l K := by
  have h := continuumFlow_tendstoUniformlyOn hd hu hp hsR hsV hsC hd0 K hK
  simpa only [Function.comp_def, momentCoordinates, Matrix.cons_val_zero] using
    (Pi.uniformContinuous_proj (fun _ : Fin 3 => ℝ) 0).comp_tendstoUniformlyOn h

/-- Actual chains converge on every compact time interval of their matched grid.
The stability, positive-semidefinite initial data and Nyquist assumptions are
those of the proved moment comparison theorem. -/
theorem regular_chain_grid_convergence
    (P : ℕ → Params) (s : ℕ → Moments) (delta₀ u₀ phi₀ : ℝ) (s₀ : Moments)
    (margin : ℝ) (hm : 0 < margin) (jury : External.JuryStability)
    (hchain : ∀ n, 1/2 ≤ (P n).beta ∧ (P n).beta < 1 ∧
      0 < (P n).w ∧ (P n).w < 2 * (1 + (P n).beta) ∧ (s n).psd ∧
      0 ≤ (P n).renormNoise ∧ (P n).renormNoise ≤ 1-margin ∧
      0 ≤ (P n).renormAdditive ∧
      (comparisonDeltaThreshold margin ≤ (P n).matchedDelta →
        (P n).foldedAngle ≤ Real.pi/2-margin))
    (hh : Tendsto (fun n => (P n).matchedStep) atTop (𝓝 0))
    (hd : Tendsto (fun n => (P n).matchedDelta) atTop (𝓝 delta₀))
    (hu : Tendsto (fun n => (P n).renormNoise) atTop (𝓝 u₀))
    (hp : Tendsto (fun n => (P n).renormAdditive) atTop (𝓝 phi₀))
    (hsR : Tendsto (fun n => ((P n).matchedMoments (s n)).R) atTop (𝓝 s₀.R))
    (hsV : Tendsto (fun n => ((P n).matchedMoments (s n)).V) atTop (𝓝 s₀.V))
    (hsC : Tendsto (fun n => ((P n).matchedMoments (s n)).C) atTop (𝓝 s₀.C))
    (hd0 : 0 < delta₀) (T : ℝ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ k : ℕ, (k : ℝ) * (P n).matchedStep ≤ T →
      |((P n).trajectory (s n) k).R -
        (continuumFlow delta₀ u₀ phi₀ s₀ ((k : ℝ) * (P n).matchedStep)).R| < ε := by
  obtain ⟨C, hC, hcompare⟩ := moment_comparison_risk margin hm
  have hN : Tendsto (fun n => (P n).comparisonInitialSize (s n) + (P n).renormAdditive)
      atTop (𝓝 (s₀.R + delta₀ * s₀.V + |s₀.C| + phi₀)) := by
    exact ((hsR.add (hd.mul hsV)).add hsC.abs).add hp
  have hE : Tendsto
      (fun n => C * (P n).matchedStep *
        ((P n).comparisonInitialSize (s n) + (P n).renormAdditive)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hh).mul hN
  have hflow := continuumFlow_risk_tendstoUniformlyOn hd hu hp hsR hsV hsC hd0
    (Set.Icc 0 T) isCompact_Icc
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  have hsmall := hE.eventually (eventually_lt_nhds hhalf)
  have huniform := (Metric.tendstoUniformlyOn_iff.1 hflow) (ε / 2) hhalf
  filter_upwards [hsmall, huniform] with n hn hfn
  intro k hk
  obtain ⟨hb0,hb1,hw0,hw1,hpsd,hu0,hum,hp0,hnyq⟩ := hchain n
  have htime : 0 ≤ (k : ℝ) * (P n).matchedStep :=
    mul_nonneg (Nat.cast_nonneg _) ((P n).matchedStep_pos (by linarith) hb1).le
  have hc := hcompare (P n) (s n) hb0 hb1 hw0 hw1 jury hpsd hu0 hum hp0 hnyq k
  have hf := hfn ((k : ℝ) * (P n).matchedStep) ⟨htime, hk⟩
  rw [Real.dist_eq, abs_sub_comm] at hf
  calc
    _ ≤ |((P n).trajectory (s n) k).R -
        ((P n).comparisonFlow (s n) ((k : ℝ) * (P n).matchedStep)).R| +
        |((P n).comparisonFlow (s n) ((k : ℝ) * (P n).matchedStep)).R -
          (continuumFlow delta₀ u₀ phi₀ s₀ ((k : ℝ) * (P n).matchedStep)).R| :=
      abs_sub_le _ _ _
    _ < ε := by
      have hf' : |((P n).comparisonFlow (s n) ((k : ℝ) * (P n).matchedStep)).R -
          (continuumFlow delta₀ u₀ phi₀ s₀ ((k : ℝ) * (P n).matchedStep)).R| < ε / 2 := hf
      linarith


/-- Stability upgrades compact convergence to uniform convergence on all nonnegative time. -/
theorem continuumFlow_tendstoUniformlyOn_nonneg {ι : Type*} {l : Filter ι}
    {delta u phi : ι → ℝ} {s : ι → Moments}
    {delta₀ u₀ phi₀ : ℝ} {s₀ : Moments}
    (hd : Tendsto delta l (𝓝 delta₀)) (hu : Tendsto u l (𝓝 u₀))
    (hp : Tendsto phi l (𝓝 phi₀))
    (hsR : Tendsto (fun n => (s n).R) l (𝓝 s₀.R))
    (hsV : Tendsto (fun n => (s n).V) l (𝓝 s₀.V))
    (hsC : Tendsto (fun n => (s n).C) l (𝓝 s₀.C))
    (hd0 : 0 < delta₀) (hu00 : 0 ≤ u₀) (hu01 : u₀ < 1)
    (hpositive : ∀ᶠ n in l, 0 < delta n ∧ 0 ≤ u n ∧ u n < 1 ∧ 0 ≤ phi n ∧ (s n).psd) :
    TendstoUniformlyOn
      (fun n t => regularMomentVector (continuumFlow (delta n) (u n) (phi n) (s n) t))
      (fun t => regularMomentVector (continuumFlow delta₀ u₀ phi₀ s₀ t)) l (Set.Ici 0) := by
  obtain ⟨A,lambda,hA,hl,hbound⟩ := continuumFlow_uniform_perturbation_bound delta₀ u₀ hd0 hu00 hu01
  have hbase := hsR.add (hd.mul hsV)
  have hrisk := (hbase.add hp).div (tendsto_const_nhds.sub hu) (show 1-u₀ ≠ 0 by linarith)
  have henergy : Tendsto (fun n => continuumEnergyBound (delta n) (u n) (phi n) (s n)) l
      (𝓝 (continuumEnergyBound delta₀ u₀ phi₀ s₀)) :=
    (hbase.add (((tendsto_const_nhds (x := (1 : ℝ))).add hu).mul hrisk)).add hp
  have hS : Tendsto (fun n => (1+1/delta n)*continuumEnergyBound (delta n) (u n) (phi n) (s n)) l
      (𝓝 ((1+1/delta₀)*continuumEnergyBound delta₀ u₀ phi₀ s₀)) :=
    ((tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := (1 : ℝ))).div hd hd0.ne')).mul henergy
  have hI : Tendsto (fun n => regularVectorSize (regularMomentVector (s n) - regularMomentVector s₀))
      l (𝓝 0) := by
    simpa [regularVectorSize, regularMomentVector] using
      ((hsR.sub (tendsto_const_nhds (x := s₀.R))).abs.add (hsV.sub (tendsto_const_nhds (x := s₀.V))).abs).add
        (hsC.sub (tendsto_const_nhds (x := s₀.C))).abs
  have hratU := (hu.div hd hd0.ne').sub (tendsto_const_nhds (x := u₀/delta₀))
  have hratP := (hp.div hd hd0.ne').sub (tendsto_const_nhds (x := phi₀/delta₀))
  have hdelta := hd.sub (tendsto_const_nhds (x := delta₀))
  have hB := (((hdelta.abs.const_mul 3).add (hratU.abs.const_mul 2)).mul hS).add
    (hratP.abs.const_mul 2)
  have herror : Tendsto
      (fun n => A * regularVectorSize (regularMomentVector (s n) - regularMomentVector s₀) +
        A * ((3 * |delta n-delta₀| + 2 * |u n/delta n-u₀/delta₀|) *
          ((1+1/delta n) * continuumEnergyBound (delta n) (u n) (phi n) (s n)) +
          2 * |phi n/delta n-phi₀/delta₀|) / lambda) l (𝓝 0) := by
    simpa [continuumEnergyBound, continuumRiskBound] using
      (hI.const_mul A).add ((hB.const_mul A).div_const lambda)
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  have he := herror.eventually (eventually_lt_nhds hε)
  filter_upwards [hpositive, he] with n hn hsmall
  intro t ht
  rw [dist_eq_norm, norm_sub_rev]
  exact (hbound (delta n) (u n) (phi n) phi₀ (s n) s₀ hn.1 hn.2.1 hn.2.2.1
    hn.2.2.2.1 hn.2.2.2.2 t ht).trans_lt hsmall


/-- The risk coordinate inherits convergence uniform over all nonnegative time. -/
theorem continuumFlow_risk_tendstoUniformlyOn_nonneg {ι : Type*} {l : Filter ι}
    {delta u phi : ι → ℝ} {s : ι → Moments}
    {delta₀ u₀ phi₀ : ℝ} {s₀ : Moments}
    (hd : Tendsto delta l (𝓝 delta₀)) (hu : Tendsto u l (𝓝 u₀))
    (hp : Tendsto phi l (𝓝 phi₀))
    (hsR : Tendsto (fun n => (s n).R) l (𝓝 s₀.R))
    (hsV : Tendsto (fun n => (s n).V) l (𝓝 s₀.V))
    (hsC : Tendsto (fun n => (s n).C) l (𝓝 s₀.C))
    (hd0 : 0 < delta₀) (hu00 : 0 ≤ u₀) (hu01 : u₀ < 1)
    (hpositive : ∀ᶠ n in l, 0 < delta n ∧ 0 ≤ u n ∧ u n < 1 ∧ 0 ≤ phi n ∧ (s n).psd) :
    TendstoUniformlyOn
      (fun n t => (continuumFlow (delta n) (u n) (phi n) (s n) t).R)
      (fun t => (continuumFlow delta₀ u₀ phi₀ s₀ t).R) l (Set.Ici 0) := by
  have h := continuumFlow_tendstoUniformlyOn_nonneg hd hu hp hsR hsV hsC hd0 hu00 hu01 hpositive
  simpa only [Function.comp_def, regularMomentVector, Matrix.cons_val_zero] using
    (Pi.uniformContinuous_proj (fun _ : Fin 3 => ℝ) 0).comp_tendstoUniformlyOn h

/-- The actual risk chain converges uniformly over all matched grid indices. -/
theorem regular_chain_uniform_convergence
    (P : ℕ → Params) (s : ℕ → Moments) (delta₀ u₀ phi₀ : ℝ) (s₀ : Moments)
    (margin : ℝ) (hm : 0 < margin) (jury : External.JuryStability)
    (hchain : ∀ n, 1/2 ≤ (P n).beta ∧ (P n).beta < 1 ∧
      0 < (P n).w ∧ (P n).w < 2 * (1 + (P n).beta) ∧ (s n).psd ∧
      0 ≤ (P n).renormNoise ∧ (P n).renormNoise ≤ 1-margin ∧
      0 ≤ (P n).renormAdditive ∧
      (comparisonDeltaThreshold margin ≤ (P n).matchedDelta →
        (P n).foldedAngle ≤ Real.pi/2-margin))
    (hh : Tendsto (fun n => (P n).matchedStep) atTop (𝓝 0))
    (hd : Tendsto (fun n => (P n).matchedDelta) atTop (𝓝 delta₀))
    (hu : Tendsto (fun n => (P n).renormNoise) atTop (𝓝 u₀))
    (hp : Tendsto (fun n => (P n).renormAdditive) atTop (𝓝 phi₀))
    (hsR : Tendsto (fun n => ((P n).matchedMoments (s n)).R) atTop (𝓝 s₀.R))
    (hsV : Tendsto (fun n => ((P n).matchedMoments (s n)).V) atTop (𝓝 s₀.V))
    (hsC : Tendsto (fun n => ((P n).matchedMoments (s n)).C) atTop (𝓝 s₀.C))
    (hd0 : 0 < delta₀) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ k : ℕ,
      |((P n).trajectory (s n) k).R -
        (continuumFlow delta₀ u₀ phi₀ s₀ ((k : ℝ) * (P n).matchedStep)).R| < ε := by
  obtain ⟨C, hC, hcompare⟩ := moment_comparison_risk margin hm
  have hN : Tendsto (fun n => (P n).comparisonInitialSize (s n) + (P n).renormAdditive)
      atTop (𝓝 (s₀.R + delta₀ * s₀.V + |s₀.C| + phi₀)) := by
    exact ((hsR.add (hd.mul hsV)).add hsC.abs).add hp
  have hE : Tendsto
      (fun n => C * (P n).matchedStep *
        ((P n).comparisonInitialSize (s n) + (P n).renormAdditive)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hh).mul hN
  have hu00 : 0 ≤ u₀ := ge_of_tendsto hu
    (Eventually.of_forall (fun n => (hchain n).2.2.2.2.2.1))
  have hulim : u₀ ≤ 1-margin := le_of_tendsto hu
    (Eventually.of_forall (fun n => (hchain n).2.2.2.2.2.2.1))
  have hu01 : u₀ < 1 := by linarith
  have hpositive : ∀ᶠ n in atTop, 0 < (P n).matchedDelta ∧ 0 ≤ (P n).renormNoise ∧
      (P n).renormNoise < 1 ∧ 0 ≤ (P n).renormAdditive ∧ ((P n).matchedMoments (s n)).psd := by
    apply Eventually.of_forall
    intro n
    obtain ⟨hb0,hb1,hw0,hw1,hpsd,hu0,hum,hp0,hnyq⟩ := hchain n
    exact ⟨(P n).matchedDelta_pos (by linarith) hb1 hw0 hw1, hu0, by linarith,
      hp0, (P n).matchedMoments_psd (s n) hpsd⟩
  have hflow := continuumFlow_risk_tendstoUniformlyOn_nonneg hd hu hp hsR hsV hsC hd0 hu00 hu01 hpositive
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  have hsmall := hE.eventually (eventually_lt_nhds hhalf)
  have huniform := (Metric.tendstoUniformlyOn_iff.1 hflow) (ε / 2) hhalf
  filter_upwards [hsmall, huniform] with n hn hfn
  intro k
  obtain ⟨hb0,hb1,hw0,hw1,hpsd,hu0,hum,hp0,hnyq⟩ := hchain n
  have htime : 0 ≤ (k : ℝ) * (P n).matchedStep :=
    mul_nonneg (Nat.cast_nonneg _) ((P n).matchedStep_pos (by linarith) hb1).le
  have hc := hcompare (P n) (s n) hb0 hb1 hw0 hw1 jury hpsd hu0 hum hp0 hnyq k
  have hf := hfn ((k : ℝ) * (P n).matchedStep) htime
  rw [Real.dist_eq, abs_sub_comm] at hf
  calc
    _ ≤ |((P n).trajectory (s n) k).R -
        ((P n).comparisonFlow (s n) ((k : ℝ) * (P n).matchedStep)).R| +
        |((P n).comparisonFlow (s n) ((k : ℝ) * (P n).matchedStep)).R -
          (continuumFlow delta₀ u₀ phi₀ s₀ ((k : ℝ) * (P n).matchedStep)).R| :=
      abs_sub_le _ _ _
    _ < ε := by
      have hf' : |((P n).comparisonFlow (s n) ((k : ℝ) * (P n).matchedStep)).R -
          (continuumFlow delta₀ u₀ phi₀ s₀ ((k : ℝ) * (P n).matchedStep)).R| < ε / 2 := hf
      linarith



/-- The sum norm of three coordinates is at most three times their supremum norm. -/
theorem regularVectorSize_le_three_norm (v : Fin 3 → ℝ) :
    regularVectorSize v ≤ 3 * ‖v‖ := by
  have h0 : |v 0| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 0
  have h1 : |v 1| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 1
  have h2 : |v 2| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 2
  dsimp [regularVectorSize]
  linarith

/-- The regular-limit error rate holds uniformly over all grid indices and a
positive closed interval of matched parameters. The initial error uses the
supremum norm of the three covariance coordinates. -/
theorem regular_chain_uniform_rate_interval (a b margin : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hm : 0 < margin) :
    ∃ C ≥ 0, ∀ (p : Params) (s : Moments) (delta₀ u₀ phi₀ : ℝ) (s₀ : Moments),
      1/2 ≤ p.beta → p.beta < 1 → 0 < p.w → p.w < 2*(1+p.beta) →
      External.JuryStability → s.psd →
      a ≤ p.matchedDelta → p.matchedDelta ≤ b → a ≤ delta₀ → delta₀ ≤ b →
      0 ≤ p.renormNoise → p.renormNoise ≤ 1-margin →
      0 ≤ u₀ → u₀ ≤ 1-margin → 0 ≤ p.renormAdditive → ∀ k : ℕ,
      |(p.trajectory s k).R -
        (continuumFlow delta₀ u₀ phi₀ s₀ ((k : ℝ)*p.matchedStep)).R| ≤
      C * ((p.matchedStep + |p.matchedDelta-delta₀| + |p.renormNoise-u₀|) *
        (p.comparisonInitialSize s+p.renormAdditive) + |p.renormAdditive-phi₀| +
        ‖regularMomentVector (p.matchedMoments s)-regularMomentVector s₀‖) := by
  obtain ⟨F,hF,hflow⟩ := continuumFlow_regular_uniform_rate a b margin ha hab hm
  let D := Real.sqrt b*(1+6/margin)/margin
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D+3*F,by positivity,?_⟩
  intro p s delta₀ u₀ phi₀ s₀ hb0 hb1 hw0 hw1 jury hs hd hdB hd0 hd0B hu0 hum hu00 hu0m hp k
  have htime : 0 ≤ (k : ℝ)*p.matchedStep :=
    mul_nonneg (Nat.cast_nonneg _) (p.matchedStep_pos (by linarith) hb1).le
  have hdisc := p.risk_comparison_bounded_margin hb0 hb1 hw0 hw1 jury s hs hu0 hp
    b margin hm hum hdB k
  have hf := hflow p.matchedDelta p.renormNoise p.renormAdditive delta₀ u₀ phi₀
    (p.matchedMoments s) s₀ hd hdB hd0 hd0B hu0 hum hu00 hu0m hp
    (p.matchedMoments_psd s hs) ((k : ℝ)*p.matchedStep) htime
  have hrisk : |(p.comparisonFlow s ((k : ℝ)*p.matchedStep)).R -
      (continuumFlow delta₀ u₀ phi₀ s₀ ((k : ℝ)*p.matchedStep)).R| ≤
      F * ((|p.matchedDelta-delta₀|+|p.renormNoise-u₀|)*
        (p.comparisonInitialSize s+p.renormAdditive) + |p.renormAdditive-phi₀| +
        regularVectorSize (regularMomentVector (p.matchedMoments s)-regularMomentVector s₀)) := by
    have hc := norm_le_pi_norm
      (regularMomentVector (p.comparisonFlow s ((k : ℝ)*p.matchedStep))-
        regularMomentVector (continuumFlow delta₀ u₀ phi₀ s₀ ((k : ℝ)*p.matchedStep))) 0
    have hc' : |(p.comparisonFlow s ((k : ℝ)*p.matchedStep)).R -
      (continuumFlow delta₀ u₀ phi₀ s₀ ((k : ℝ)*p.matchedStep)).R| ≤
      ‖regularMomentVector (p.comparisonFlow s ((k : ℝ)*p.matchedStep))-
        regularMomentVector (continuumFlow delta₀ u₀ phi₀ s₀ ((k : ℝ)*p.matchedStep))‖ := by
      simpa [regularMomentVector] using hc
    apply hc'.trans
    simpa [Params.comparisonFlow,Params.comparisonInitialSize] using hf
  let N := p.comparisonInitialSize s+p.renormAdditive
  let d := |p.matchedDelta-delta₀|+|p.renormNoise-u₀|
  let q := |p.renormAdditive-phi₀|
  let I := ‖regularMomentVector (p.matchedMoments s)-regularMomentVector s₀‖
  have hN : 0 ≤ N := by
    have hR := Moments.psd_R_nonneg (p.matchedMoments_psd s hs)
    have hV := Moments.psd_V_nonneg (p.matchedMoments_psd s hs)
    have hdp : 0 < p.matchedDelta := ha.trans_le hd
    dsimp [N,Params.comparisonInitialSize]
    positivity
  have hdnon : 0 ≤ d := by dsimp [d]; positivity
  have hq : 0 ≤ q := abs_nonneg _
  have hI : 0 ≤ I := norm_nonneg _
  have hh : 0 ≤ p.matchedStep := (p.matchedStep_pos (by linarith) hb1).le
  have hi := mul_le_mul_of_nonneg_left
    (regularVectorSize_le_three_norm (regularMomentVector (p.matchedMoments s)-regularMomentVector s₀)) hF
  calc
    _ ≤ |(p.trajectory s k).R-(p.comparisonFlow s ((k : ℝ)*p.matchedStep)).R| +
        |(p.comparisonFlow s ((k : ℝ)*p.matchedStep)).R -
          (continuumFlow delta₀ u₀ phi₀ s₀ ((k : ℝ)*p.matchedStep)).R| := abs_sub_le _ _ _
    _ ≤ D*p.matchedStep*N+F*(d*N+q+3*I) := by
      dsimp [D,N,d,q,I] at hi ⊢
      nlinarith only [hdisc,hrisk,hi]
    _ ≤ (D+3*F)*((p.matchedStep+|p.matchedDelta-delta₀|+|p.renormNoise-u₀|)*N+q+I) := by
      have heq : (D+3*F)*((p.matchedStep+|p.matchedDelta-delta₀|+|p.renormNoise-u₀|)*N+q+I) -
          (D*p.matchedStep*N+F*(d*N+q+3*I)) =
          D*(d*N+q+I)+F*(3*p.matchedStep*N+2*d*N+2*q) := by dsimp [d]; ring
      have hn : 0 ≤ D*(d*N+q+I)+F*(3*p.matchedStep*N+2*d*N+2*q) := by positivity
      linarith only [heq,hn]

/-- Source `cor:regular`: one constant for a compact subset of positive matched
parameters, a fixed load margin, and every time index. -/
theorem regular_chain_uniform_rate_compact (K : Set ℝ) (hK : IsCompact K)
    (hKpos : K ⊆ Set.Ioi 0) (margin : ℝ) (hm : 0 < margin) :
    ∃ C ≥ 0, ∀ (p : Params) (s : Moments) (delta₀ u₀ phi₀ : ℝ) (s₀ : Moments),
      1/2 ≤ p.beta → p.beta < 1 → 0 < p.w → p.w < 2*(1+p.beta) →
      External.JuryStability → s.psd →
      p.matchedDelta ∈ K → delta₀ ∈ K →
      0 ≤ p.renormNoise → p.renormNoise ≤ 1-margin →
      0 ≤ u₀ → u₀ ≤ 1-margin → 0 ≤ p.renormAdditive → ∀ k : ℕ,
      |(p.trajectory s k).R -
        (continuumFlow delta₀ u₀ phi₀ s₀ ((k : ℝ)*p.matchedStep)).R| ≤
      C * ((p.matchedStep + |p.matchedDelta-delta₀| + |p.renormNoise-u₀|) *
        (p.comparisonInitialSize s+p.renormAdditive) + |p.renormAdditive-phi₀| +
        ‖regularMomentVector (p.matchedMoments s)-regularMomentVector s₀‖) := by
  classical
  by_cases hne : K.Nonempty
  · obtain ⟨a,haK,hmin⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨b,hbK,hmax⟩ := hK.exists_isMaxOn hne continuous_id.continuousOn
    have ha : 0 < a := hKpos haK
    have hab : a ≤ b := hmin hbK
    obtain ⟨C,hC,hbound⟩ := regular_chain_uniform_rate_interval a b margin ha hab hm
    refine ⟨C,hC,?_⟩
    intro p s delta₀ u₀ phi₀ s₀ hb0 hb1 hw0 hw1 jury hs hd hd0 hu0 hum hu00 hu0m hp k
    exact hbound p s delta₀ u₀ phi₀ s₀ hb0 hb1 hw0 hw1 jury hs
      (hmin hd) (hmax hd) (hmin hd0) (hmax hd0) hu0 hum hu00 hu0m hp k
  · refine ⟨0,le_rfl,?_⟩
    intro p s delta₀ u₀ phi₀ s₀ hb0 hb1 hw0 hw1 jury hs hd
    exact (hne ⟨p.matchedDelta,hd⟩).elim

private theorem regular_matrix_entry_bound (A : Matrix (Fin 2) (Fin 2) ℝ)
    (i j : Fin 2) : |A i j| ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h : ‖A i j‖₊ ≤ (Finset.univ.sup fun i : Fin 2 => ∑ j : Fin 2, ‖A i j‖₊) := by
    apply le_trans (Finset.single_le_sum (fun k _ => show 0 ≤ ‖A i k‖₊ from zero_le) (Finset.mem_univ j))
    exact Finset.le_sup (f := fun i : Fin 2 => ∑ j : Fin 2, ‖A i j‖₊) (Finset.mem_univ i)
  exact_mod_cast h

/-- The covariance matrix operator norm controls all three moment errors. -/
theorem regularMomentVector_sub_norm_le_cov (s s₀ : Moments) :
    ‖regularMomentVector s-regularMomentVector s₀‖ ≤ ‖s.cov-s₀.cov‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (s.cov-s₀.cov))).2
  intro i
  fin_cases i
  · simpa [regularMomentVector,Moments.cov] using regular_matrix_entry_bound (s.cov-s₀.cov) 0 0
  · simpa [regularMomentVector,Moments.cov] using regular_matrix_entry_bound (s.cov-s₀.cov) 1 1
  · simpa [regularMomentVector,Moments.cov] using regular_matrix_entry_bound (s.cov-s₀.cov) 0 1

/-- The complete quantitative regular corollary, including a positive step
threshold and the source's matched covariance matrix error. Its supremum in
`k` is expressed equivalently as the same estimate for every `k`. -/
theorem cor_regular (K : Set ℝ) (hK : IsCompact K) (hKpos : K ⊆ Set.Ioi 0)
    (margin : ℝ) (hm : 0 < margin) :
    ∃ step₀ > 0, ∃ C > 0, ∀ (p : Params) (s : Moments)
      (delta₀ u₀ phi₀ : ℝ) (s₀ : Moments),
      0 < p.beta → p.beta < 1 → 0 < p.w → p.w < 2*(1+p.beta) →
      External.JuryStability → s.psd →
      p.matchedStep ≤ step₀ → p.matchedDelta ∈ K → delta₀ ∈ K →
      0 ≤ p.renormNoise → p.renormNoise ≤ 1-margin →
      0 ≤ u₀ → u₀ ≤ 1-margin → 0 ≤ p.renormAdditive → ∀ k : ℕ,
      |(p.trajectory s k).R -
        (continuumFlow delta₀ u₀ phi₀ s₀ ((k : ℝ)*p.matchedStep)).R| ≤
      C * ((p.matchedStep + |p.matchedDelta-delta₀| + |p.renormNoise-u₀|) *
        (p.comparisonInitialSize s+p.renormAdditive) + |p.renormAdditive-phi₀| +
        ‖(p.matchedMoments s).cov-s₀.cov‖) := by
  obtain ⟨C,hC,hbound⟩ := regular_chain_uniform_rate_compact K hK hKpos margin hm
  have hstep : 0 < -Real.log (1/2 : ℝ) := by
    apply neg_pos.mpr
    exact Real.log_neg (by norm_num) (by norm_num)
  refine ⟨-Real.log (1/2 : ℝ),hstep,C+1,by linarith,?_⟩
  intro p s delta₀ u₀ phi₀ s₀ hb0 hb1 hw0 hw1 jury hs hh hd hd0 hu0 hum hu00 hu0m hp k
  have hhalf : (1/2 : ℝ) ≤ p.beta := by
    have hexp := Real.exp_le_exp.mpr (neg_le_neg hh)
    rw [neg_neg,Real.exp_log (by norm_num : (0:ℝ) < 1/2),p.exp_neg_matchedStep hb0] at hexp
    exact hexp
  apply (hbound p s delta₀ u₀ phi₀ s₀ hhalf hb1 hw0 hw1 jury hs hd hd0
    hu0 hum hu00 hu0m hp k).trans
  have hi := regularMomentVector_sub_norm_le_cov (p.matchedMoments s) s₀
  have hN : 0 ≤ p.comparisonInitialSize s+p.renormAdditive := by
    have hR := Moments.psd_R_nonneg (p.matchedMoments_psd s hs)
    have hV := Moments.psd_V_nonneg (p.matchedMoments_psd s hs)
    have hdp : 0 < p.matchedDelta := hKpos hd
    dsimp [Params.comparisonInitialSize]
    positivity
  have hx : 0 ≤ (p.matchedStep + |p.matchedDelta-delta₀| + |p.renormNoise-u₀|) *
      (p.comparisonInitialSize s+p.renormAdditive) + |p.renormAdditive-phi₀| +
      ‖regularMomentVector (p.matchedMoments s)-regularMomentVector s₀‖ := by
    have hhp := (p.matchedStep_pos hb0 hb1).le
    positivity
  exact mul_le_mul (by linarith) (by linarith only [hi]) hx (by linarith)

end
end SparseSGD
