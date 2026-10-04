import SparseSGD.Probability.LeastSquares.Measurability

open MeasureTheory ProbabilityTheory
namespace SparseSGD.Probability.LeastSquares
noncomputable section

def historyState {d B : ℕ} (beta eta : ℝ) : (k : ℕ) → History d B k → State d
  | 0, h => h.1
  | k+1, h => update beta eta
      (historyState beta eta k (h.1, fun i => h.2 i.castSucc)) (h.2 (Fin.last k))

theorem measurable_historyState (d B : ℕ) (beta eta : ℝ) (k : ℕ) :
    Measurable (historyState (d := d) (B := B) beta eta k) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
    change Measurable (fun h : History d B (k+1) => update beta eta
      (historyState beta eta k (h.1, fun i => h.2 i.castSucc)) (h.2 (Fin.last k)))
    apply (measurable_update d B beta eta).comp
      (f := fun h : History d B (k+1) =>
        (historyState beta eta k (h.1, fun i => h.2 i.castSucc), h.2 (Fin.last k)))
    apply Measurable.prodMk
    · apply ih.comp
      apply measurable_fst.prodMk
      exact Measurable.of_eval (fun i => (measurable_pi_apply i.castSucc).comp measurable_snd)
    · exact (measurable_pi_apply (Fin.last k)).comp measurable_snd

theorem process_eq_historyState {d B : ℕ} (beta eta : ℝ) (ω : World d B) (k : ℕ) :
    process beta eta ω k = historyState beta eta k (past k ω) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [process, historyState, past, Fin.val_castSucc, Fin.val_last] using
      (congrArg (fun s => update beta eta s (ω.2 k)) ih)

theorem process_past_measurable (d B : ℕ) (beta eta : ℝ) (k : ℕ) :
    @Measurable (World d B) (State d) (pastSigma d B k) inferInstance
      (fun ω => process beta eta ω k) := by
  have h := (measurable_historyState d B beta eta k).comp
    (show @Measurable (World d B) (History d B k) (pastSigma d B k) inferInstance
      (past k) from measurable_iff_comap_le.mpr le_rfl)
  simpa only [Function.comp_def, ← process_eq_historyState] using h

theorem empty_batch_gradient {d B : ℕ} (e : Vec d) (a : Batch d B)
    (ha : ∀ i, (a i).1 = false) : batchGradient e a = 0 := by
  simp [batchGradient, gradient, feature, ha]

theorem empty_batch_update {d B : ℕ} (beta eta : ℝ) (s : State d) (a : Batch d B)
    (ha : ∀ i, (a i).1 = false) :
    update beta eta s a = (s.1 - beta • s.2, beta • s.2) := by
  simp [update, empty_batch_gradient s.1 a ha]

theorem params_explicit {d B : ℕ} (p : unitInterval) (hp : (p : ℝ) ≠ 0)
    (ν : Measure ℝ) (beta eta : ℝ) :
    params d B p ν beta eta =
      ⟨beta, eta*(1-beta)*p, eta*(d+2-p)/(2*B), eta*labelVariance ν*d/(2*B)⟩ := by
  simp only [params, oracleParams, vinc, vadd]
  congr 1 <;> field_simp <;> ring

end
end SparseSGD.Probability.LeastSquares
