import SparseSGD.Probability.LeastSquares.Model
import SparseSGD.Probability.GaussianProduct

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section

abbrev Vec (d : ℕ) := SparseSGD.Probability.LeastSquares.Vec d
abbrev Sample (d : ℕ) := Bool × (Fin d → ℝ)
abbrev Batch (d B : ℕ) := Fin B → Sample d
abbrev State (d : ℕ) := Vec d × Vec d
abbrev World (d B : ℕ) := State d × (ℕ → Batch d B)

def sigma (t : ℝ) : ℝ := Real.exp t / (1 + Real.exp t)
def labelReal (y : Bool) : ℝ := if y then 1 else 0

def bias (p : unitInterval) (mu : Vec d) : ℝ :=
  Real.log ((p : ℝ) / (1 - (p : ℝ))) - ‖mu‖ ^ 2 / 2

def feature {d : ℕ} (mu : Vec d) (a : Sample d) : Vec d :=
  (if a.1 then mu else 0) + WithLp.toLp 2 a.2

def gradient {d : ℕ} (p : unitInterval) (mu : Vec d) (theta : Vec d) (a : Sample d) : Vec d :=
  (sigma (inner ℝ theta (feature mu a) + bias p mu) - labelReal a.1) • feature mu a

def batchGradient {d B : ℕ} (p : unitInterval) (mu : Vec d) (theta : Vec d) (a : Batch d B) : Vec d :=
  (B : ℝ)⁻¹ • ∑ i, gradient p mu theta (a i)

def sampleLaw (d : ℕ) (p : unitInterval) : Measure (Sample d) :=
  (bernoulliMeasure true false p).prod (SparseSGD.Probability.standardGaussianProduct d)

def batchLaw (d B : ℕ) (p : unitInterval) : Measure (Batch d B) :=
  Measure.pi (fun _ => sampleLaw d p)

def worldLaw {d B : ℕ} (p : unitInterval) (ρ : Measure (State d)) : Measure (World d B) :=
  ρ.prod (Measure.infinitePi (fun _ : ℕ => batchLaw d B p))

instance sampleLaw_probability (d : ℕ) (p : unitInterval) : IsProbabilityMeasure (sampleLaw d p) := by
  unfold sampleLaw
  infer_instance

instance batchLaw_probability (d B : ℕ) (p : unitInterval) : IsProbabilityMeasure (batchLaw d B p) := by
  unfold batchLaw
  infer_instance

instance worldLaw_probability {d B : ℕ} (p : unitInterval) (ρ : Measure (State d))
    [IsProbabilityMeasure ρ] : IsProbabilityMeasure (worldLaw (B := B) p ρ) := by
  unfold worldLaw
  infer_instance

def update {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d) (a : Batch d B) : State d :=
  let m' := beta • s.2 + (1 - beta) • batchGradient p mu s.1 a
  (s.1 - eta • m', m')

def process {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (ω : World d B) : ℕ → State d
  | 0 => ω.1
  | k + 1 => update eta beta p mu (process eta beta p mu ω k) (ω.2 k)

def r {d : ℕ} (mu : Vec d) : ℝ := ‖mu‖
def signalCoord {d : ℕ} (mu theta : Vec d) : ℝ := inner ℝ theta mu / r mu
def bulkPart {d : ℕ} (mu theta : Vec d) : Vec d := theta - (signalCoord mu theta) • (r mu)⁻¹ • mu

def summary {d : ℕ} (mu : Vec d) (s : State d) : ℝ × ℝ × ℝ × ℝ × ℝ :=
  (signalCoord mu s.1, signalCoord mu s.2, ‖bulkPart mu s.1‖ ^ 2,
    ‖bulkPart mu s.2‖ ^ 2, inner ℝ (bulkPart mu s.1) (bulkPart mu s.2))

theorem update_momentum_inner {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d)
    (a : Batch d B) :
    inner ℝ (update eta beta p mu s a).2 mu =
      beta * inner ℝ s.2 mu + (1-beta) * inner ℝ (batchGradient p mu s.1 a) mu := by
  simp [update, inner_add_left, real_inner_smul_left]

theorem update_parameter_inner {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d)
    (a : Batch d B) :
    inner ℝ (update eta beta p mu s a).1 mu =
      inner ℝ s.1 mu - eta * inner ℝ (update eta beta p mu s a).2 mu := by
  change inner ℝ (s.1 - eta • (beta • s.2 + (1-beta) • batchGradient p mu s.1 a)) mu =
    inner ℝ s.1 mu - eta * inner ℝ (beta • s.2 + (1-beta) • batchGradient p mu s.1 a) mu
  simp only [inner_sub_left, real_inner_smul_left]

theorem update_signal_momentum {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) (a : Batch d B) (hr : 0 < r mu) :
    signalCoord mu (update eta beta p mu s a).2 =
      beta * signalCoord mu s.2 + (1-beta) * signalCoord mu (batchGradient p mu s.1 a) := by
  unfold signalCoord
  rw [update_momentum_inner]
  field_simp [ne_of_gt hr]

theorem update_signal_parameter {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu : Vec d) (s : State d) (a : Batch d B) (hr : 0 < r mu) :
    signalCoord mu (update eta beta p mu s a).1 =
      signalCoord mu s.1 - eta * signalCoord mu (update eta beta p mu s a).2 := by
  unfold signalCoord
  rw [update_parameter_inner]
  field_simp [ne_of_gt hr]

end
end SparseSGD.Logistic
