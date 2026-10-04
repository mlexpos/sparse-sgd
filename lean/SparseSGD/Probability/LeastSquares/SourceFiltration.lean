import SparseSGD.Probability.LeastSquares.Process
import SparseSGD.Probability.LeastSquares.Freshness

open MeasureTheory ProbabilityTheory
set_option maxHeartbeats 800000

namespace SparseSGD.Probability.LeastSquares
noncomputable section

abbrev SourceHistory (d k : ℕ) := State d × (Fin k → Vec d)

def sourcePast {d B : ℕ} (beta eta : ℝ) (k : ℕ) (ω : World d B) : SourceHistory d k :=
  (ω.1, fun i => batchGradient (process beta eta ω i).1 (ω.2 i))

def sourceSigma (d B : ℕ) (beta eta : ℝ) (k : ℕ) : MeasurableSpace (World d B) :=
  MeasurableSpace.comap (sourcePast (d := d) (B := B) beta eta k) inferInstance

private def gradientUpdate {d : ℕ} (beta eta : ℝ) (s : State d) (g : Vec d) : State d :=
  let q := beta • s.2 + (eta * (1 - beta)) • g
  (s.1 - q, q)

private def sourceState {d : ℕ} (beta eta : ℝ) : (k : ℕ) → SourceHistory d k → State d
  | 0, h => h.1
  | k+1, h => gradientUpdate beta eta
      (sourceState beta eta k (h.1, fun i => h.2 i.castSucc)) (h.2 (Fin.last k))

theorem sourcePast_pastSigma_measurable (d B : ℕ) (beta eta : ℝ) (k : ℕ) :
    @Measurable (World d B) (SourceHistory d k) (pastSigma d B k) inferInstance
      (sourcePast beta eta k) := by
  letI : MeasurableSpace (World d B) := pastSigma d B k
  have hp : Measurable (past (d := d) (B := B) k) :=
    measurable_iff_comap_le.mpr le_rfl
  apply (measurable_fst.comp (f := past k) hp).prodMk
  apply Measurable.of_eval
  intro i
  have hs : Measurable (fun ω : World d B => process beta eta ω i.val) :=
    (process_past_measurable d B beta eta i.val).mono
      (pastSigma_mono (Nat.le_of_lt i.isLt)) le_rfl
  have hb : Measurable (fun ω : World d B => ω.2 i.val) := by
    exact ((measurable_pi_apply i).comp measurable_snd).comp (f := past k) hp
  exact (measurable_batchGradient d B).comp
    (f := fun ω : World d B => ((process beta eta ω i.val).1, ω.2 i.val))
    (hs.fst.prodMk hb)

theorem measurable_sourcePast (d B : ℕ) (beta eta : ℝ) (k : ℕ) :
    Measurable (sourcePast (d := d) (B := B) beta eta k) :=
  (sourcePast_pastSigma_measurable d B beta eta k).mono
    (pastSigma_le_ambient k) le_rfl

lemma sourceSigma_le_pastSigma (d B : ℕ) (beta eta : ℝ) (k : ℕ) :
    sourceSigma d B beta eta k ≤ pastSigma d B k :=
  measurable_iff_comap_le.mp (sourcePast_pastSigma_measurable d B beta eta k)

private theorem measurable_sourceState (d : ℕ) (beta eta : ℝ) (k : ℕ) :
    Measurable (sourceState (d := d) beta eta k) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
    change Measurable (fun h : SourceHistory d (k+1) =>
      gradientUpdate beta eta
        (sourceState beta eta k (h.1, fun i => h.2 i.castSucc)) (h.2 (Fin.last k)))
    have hp : Measurable (fun h : SourceHistory d (k+1) =>
        sourceState beta eta k (h.1, fun i => h.2 i.castSucc)) := by
      apply ih.comp
      apply measurable_fst.prodMk
      exact Measurable.of_eval (fun i => (measurable_pi_apply i.castSucc).comp measurable_snd)
    have hg : Measurable (fun h : SourceHistory d (k+1) => h.2 (Fin.last k)) :=
      (measurable_pi_apply (Fin.last k)).comp measurable_snd
    dsimp [gradientUpdate]
    exact (hp.fst.sub (hp.snd.const_smul beta |>.add (hg.const_smul (eta * (1-beta))))).prodMk
      (hp.snd.const_smul beta |>.add (hg.const_smul (eta * (1-beta))))

private theorem process_eq_sourceState {d B : ℕ} (beta eta : ℝ) (ω : World d B) (k : ℕ) :
    process beta eta ω k = sourceState beta eta k (sourcePast beta eta k ω) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change update beta eta (process beta eta ω k) (ω.2 k) =
      gradientUpdate beta eta
        (sourceState beta eta k (sourcePast beta eta k ω))
        (batchGradient (process beta eta ω k).1 (ω.2 k))
    rw [← ih]
    rfl

theorem process_sourceSigma_measurable (d B : ℕ) (beta eta : ℝ) (k : ℕ) :
    @Measurable (World d B) (State d) (sourceSigma d B beta eta k) inferInstance
      (fun ω => process beta eta ω k) := by
  have h := (measurable_sourceState d beta eta k).comp
    (show @Measurable (World d B) (SourceHistory d k) (sourceSigma d B beta eta k)
      inferInstance (sourcePast beta eta k) from measurable_iff_comap_le.mpr le_rfl)
  simpa only [Function.comp_def, ← process_eq_sourceState] using h

end
end SparseSGD.Probability.LeastSquares
