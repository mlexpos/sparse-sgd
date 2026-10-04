import SparseSGD.Probability.GaussianNorm
import SparseSGD.Probability.MomentReduction
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.ProductMeasure

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Probability.LeastSquares
noncomputable section

abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Sample (d : ℕ) := Bool × ((Fin d → ℝ) × ℝ)
abbrev Batch (d B : ℕ) := Fin B → Sample d
abbrev State (d : ℕ) := Vec d × Vec d
abbrev World (d B : ℕ) := State d × (ℕ → Batch d B)
abbrev History (d B k : ℕ) := State d × (Fin k → Batch d B)

def feature {d : ℕ} (a : Sample d) : Vec d :=
  if a.1 then WithLp.toLp 2 a.2.1 else 0

def gradient {d : ℕ} (e : Vec d) (a : Sample d) : Vec d :=
  (inner ℝ (feature a) e - a.2.2) • feature a

def batchGradient {d B : ℕ} (e : Vec d) (a : Batch d B) : Vec d :=
  (B : ℝ)⁻¹ • ∑ i, gradient e (a i)

def sampleLaw (d : ℕ) (p : unitInterval) (ν : Measure ℝ) : Measure (Sample d) :=
  (bernoulliMeasure true false p).prod ((standardGaussianProduct d).prod ν)

def batchLaw (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) : Measure (Batch d B) :=
  Measure.pi (fun _ => sampleLaw d p ν)

def worldLaw {d B : ℕ} (p : unitInterval) (ν : Measure ℝ)
    (ρ : Measure (State d)) : Measure (World d B) :=
  ρ.prod (Measure.infinitePi (fun _ : ℕ => batchLaw d B p ν))

instance sampleLaw_probability (d : ℕ) (p : unitInterval) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (sampleLaw d p ν) := by
  unfold sampleLaw; infer_instance

instance batchLaw_probability (d B : ℕ) (p : unitInterval) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (batchLaw d B p ν) := by
  unfold batchLaw; infer_instance

instance worldLaw_probability {d B : ℕ} (p : unitInterval) (ν : Measure ℝ)
    (ρ : Measure (State d)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (worldLaw (B := B) p ν ρ) := by
  unfold worldLaw; infer_instance

def labelVariance (ν : Measure ℝ) : ℝ := ∫ z, z ^ 2 ∂ν
def vinc (d B : ℕ) (p : unitInterval) : ℝ := (p : ℝ) * (d + 2 - p) / B
def vadd (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) : ℝ :=
  labelVariance ν * (p : ℝ) * d / B

def params (d B : ℕ) (p : unitInterval) (ν : Measure ℝ) (beta eta : ℝ) : Params :=
  oracleParams beta eta p (vinc d B p) (vadd d B p ν)

def past {d B : ℕ} (k : ℕ) (ω : World d B) : History d B k :=
  (ω.1, fun i => ω.2 i)

def pastSigma (d B k : ℕ) : MeasurableSpace (World d B) :=
  MeasurableSpace.comap (past (d := d) (B := B) k) inferInstance

def update {d B : ℕ} (beta eta : ℝ) (s : State d) (a : Batch d B) : State d :=
  let q := beta • s.2 + (eta * (1 - beta)) • batchGradient s.1 a
  (s.1 - q, q)

def process {d B : ℕ} (beta eta : ℝ) (ω : World d B) : ℕ → State d
  | 0 => ω.1
  | k + 1 => update beta eta (process beta eta ω k) (ω.2 k)

end
end SparseSGD.Probability.LeastSquares
