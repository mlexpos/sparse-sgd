import SparseSGD.Logistic.Model
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section

abbrev NoiseVec (d : ℕ) := Fin d → ℝ

def splitGaussianNoise {k m : ℕ} (z : NoiseVec (k+m)) : NoiseVec k × NoiseVec m :=
  (fun i => z (Fin.castAdd m i), fun j => z (Fin.natAdd k j))

theorem measurable_splitGaussianNoise (k m : ℕ) :
    Measurable (splitGaussianNoise (k := k) (m := m)) := by
  unfold splitGaussianNoise
  fun_prop

def splitGaussianSample {k m : ℕ} (a : Sample (k+m)) : Sample k × NoiseVec m :=
  ((a.1,(splitGaussianNoise a.2).1),(splitGaussianNoise a.2).2)

def splitGaussianBatch {k m B : ℕ} (a : Batch (k+m) B) : Batch k B × (Fin B → NoiseVec m) :=
  (fun i => (splitGaussianSample (a i)).1, fun i => (splitGaussianSample (a i)).2)

theorem standardGaussianProduct_split (k m : ℕ) :
    (SparseSGD.Probability.standardGaussianProduct (k+m)).map (splitGaussianNoise (k:=k) (m:=m)) =
      Measure.prod (SparseSGD.Probability.standardGaussianProduct k) (SparseSGD.Probability.standardGaussianProduct m) := by
  let γ : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  let e : Fin k ⊕ Fin m ≃ Fin (k+m) := finSumFinEquiv
  let μ : Fin k ⊕ Fin m → Measure ℝ := fun _ => γ
  have hp1 : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin k ⊕ Fin m => ℝ) e.symm)
      (Measure.pi fun i : Fin (k+m) => γ) (Measure.pi μ) := by
    simpa [μ, e] using
      (MeasureTheory.measurePreserving_piCongrLeft (fun _ : Fin k ⊕ Fin m => γ) e.symm)
  have hp2 := MeasureTheory.measurePreserving_sumPiEquivProdPi (X := fun _ : Fin k ⊕ Fin m => ℝ) μ
  have h := hp2.comp hp1
  have hfun : (fun z : Fin (k+m) → ℝ =>
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin m => ℝ))
        ((MeasurableEquiv.piCongrLeft (fun _ : Fin k ⊕ Fin m => ℝ) e.symm) z)) =
      splitGaussianNoise (k:=k) (m:=m) := by
    funext z
    apply Prod.ext <;> funext i <;> simp [splitGaussianNoise, e,
      MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft,
      Equiv.piCongrLeft, finSumFinEquiv]
  rw [show SparseSGD.Probability.standardGaussianProduct (k+m) =
      Measure.pi (fun _ : Fin (k+m) => γ) by rfl]
  calc
    Measure.map (splitGaussianNoise (k:=k) (m:=m)) (Measure.pi fun _ : Fin (k+m) => γ) =
        Measure.map (fun z => (MeasurableEquiv.sumPiEquivProdPi
          (fun _ : Fin k ⊕ Fin m => ℝ))
          ((MeasurableEquiv.piCongrLeft (fun _ : Fin k ⊕ Fin m => ℝ) e.symm) z))
          (Measure.pi fun _ : Fin (k+m) => γ) := by rw [hfun]
    _ = (Measure.pi fun i : Fin k => γ).prod (Measure.pi fun j : Fin m => γ) := h.map_eq
    _ = Measure.prod (SparseSGD.Probability.standardGaussianProduct k)
          (SparseSGD.Probability.standardGaussianProduct m) := by rfl

theorem sampleLaw_split (k m : ℕ) (p : unitInterval) :
    (sampleLaw (k+m) p).map (splitGaussianSample (k := k) (m := m)) =
      (sampleLaw k p).prod (SparseSGD.Probability.standardGaussianProduct m) := by
  let γ := SparseSGD.Probability.standardGaussianProduct
  have hn : MeasurePreserving (splitGaussianNoise (k := k) (m := m)) (γ (k+m)) ((γ k).prod (γ m)) :=
    ⟨measurable_splitGaussianNoise k m, standardGaussianProduct_split k m⟩
  have hi : MeasurePreserving (id : Bool → Bool) (bernoulliMeasure true false p) (bernoulliMeasure true false p) :=
    ⟨measurable_id, Measure.map_id⟩
  have hp := hi.prod hn
  have ha := (measurePreserving_prodAssoc (bernoulliMeasure true false p) (γ k) (γ m)).symm
  have h := ha.comp hp
  exact h.map_eq

theorem measurable_splitGaussianSample (k m : ℕ) :
    Measurable (splitGaussianSample (k := k) (m := m)) := by
  unfold splitGaussianSample
  exact (measurable_fst.prodMk ((measurable_splitGaussianNoise k m).comp measurable_snd).fst).prodMk
    ((measurable_splitGaussianNoise k m).comp measurable_snd).snd

theorem batchLaw_split (k m B : ℕ) (p : unitInterval) :
    (batchLaw (k+m) B p).map (splitGaussianBatch (k := k) (m := m) (B := B)) =
      (batchLaw k B p).prod
        (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)) := by
  have hs : MeasurePreserving (splitGaussianSample (k := k) (m := m)) (sampleLaw (k+m) p)
      ((sampleLaw k p).prod (SparseSGD.Probability.standardGaussianProduct m)) :=
    ⟨measurable_splitGaussianSample k m, sampleLaw_split k m p⟩
  have hp := measurePreserving_pi (fun _ : Fin B => sampleLaw (k+m) p)
    (fun _ : Fin B => (sampleLaw k p).prod (SparseSGD.Probability.standardGaussianProduct m))
    (fun _ => hs)
  have ha := measurePreserving_arrowProdEquivProdArrow (Sample k) (NoiseVec m) (Fin B)
    (fun _ => sampleLaw k p) (fun _ => SparseSGD.Probability.standardGaussianProduct m)
  exact (ha.comp hp).map_eq

end
end SparseSGD.Logistic
