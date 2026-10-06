import SparseSGD.Logistic.DynamicDrift
import SparseSGD.Logistic.ConditionalDrift
import SparseSGD.Logistic.TameCoefficients
import SparseSGD.Logistic.PopulationLoss
import SparseSGD.Scaling.WindowChain

open SparseSGD
open Filter Topology

namespace SparseSGD.Logistic
noncomputable section

/-- Canonical stationary point for the actual five-coordinate dynamic-alpha
field, in coordinates `(theta,Y,R,V,C)`. -/
def dynamicCanonicalEquilibrium (r delta Phi : ℝ) : DynamicState :=
  ![positiveRoot r Phi, 0, equilibriumBulk r Phi, Phi/delta, 0]

theorem dynamicCanonicalEquilibrium_is_stationary (r delta Phi : ℝ)
    (hr : 0 < r) (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) :
    dynamicField r delta Phi (dynamicCanonicalEquilibrium r delta Phi) = 0 := by
  have hf := positiveRoot_slowField_zero r Phi hr hPhi
  have hs := (slowField_zero_iff r Phi (positiveRoot r Phi) (equilibriumBulk r Phi) hr
    (positiveRoot_spec r Phi hr hPhi).1).1 hf
  have hsig : alpha (positiveRoot r Phi) (equilibriumBulk r Phi) r * positiveRoot r Phi = r := by
    rw [g_eq_alpha_mul] at hs
    exact hs.1
  have hbulk : alpha (positiveRoot r Phi) (equilibriumBulk r Phi) r * equilibriumBulk r Phi = Phi := by
    have hh := congrArg Prod.snd hf
    simp only [slowField] at hh
    linarith
  ext i
  fin_cases i
  · change -delta * (0:ℝ) = 0; ring
  · change -(0:ℝ) + alpha (positiveRoot r Phi) (equilibriumBulk r Phi) r * positiveRoot r Phi-r=0
    linarith
  · change -2*delta*(0:ℝ)=0; ring
  · change -2*(Phi/delta)+2*alpha (positiveRoot r Phi) (equilibriumBulk r Phi) r*(0:ℝ)+2*Phi/delta=0
    ring
  · change -(0:ℝ)+alpha (positiveRoot r Phi) (equilibriumBulk r Phi) r*equilibriumBulk r Phi-
      delta*(Phi/delta)=0
    rw [hbulk]
    field_simp [ne_of_gt hdelta]
    ring

/-- Source Assumption S: the actual dynamic-alpha ODE is globally exponentially
stable, with constants uniform on every compact subset of its parameter domain. -/
def physicallyAdmissibleDynamicState (y : DynamicState) : Prop :=
  0 ≤ y 2 ∧ 0 ≤ y 3 ∧ y 4 ^ 2 ≤ y 2 * y 3

/-- Source Assumption S: the actual dynamic-alpha ODE has a global solution
from every physically admissible Gram state and converges exponentially to its
canonical equilibrium. The constants are uniform on compact parameter sets.

v1 assumption (frozen manuscript `ass:S`); superseded in v2 by the theorems
`SparseSGD.Logistic.V2.prop_S_i`, `prop_S_ii`, `prop_S_iii` (bundled as
`SparseSGD.Logistic.V2.prop_S`) and `SparseSGD.Logistic.V2.cor_recursion_tame'`.
v2 proves the compact-initial-data form (`prop_S_iii_proportional`: the constant `C`
depends on a compact set `K` of initial states), not the form stated here, which is
uniform over all physically admissible initial states. No theorem in the package
consumes this structure. -/
structure SourceAssumptionS : Prop where
  compact_uniform_exponential_stability :
    ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K →
      (∀ q ∈ K, 0 < q.1 ∧ 0 ≤ q.2.1 ∧ 0 < q.2.2) →
      ∃ C rate : ℝ, 0 < C ∧ 0 < rate ∧
        ∀ q ∈ K, ∀ y₀ : DynamicState, physicallyAdmissibleDynamicState y₀ →
          ∃ y : ℝ → DynamicState,
            y 0 = y₀ ∧
            (∀ t : ℝ, 0 ≤ t → HasDerivAt y (dynamicField q.2.2 q.1 q.2.1 (y t)) t) ∧
            ∀ t : ℝ, 0 ≤ t →
              ‖y t - dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1‖ ≤
                C * Real.exp (-rate*t) * ‖y₀ - dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1‖



/-- The actual signal subsystem of the dynamic field with a time-varying
    curvature path; keeping this path explicit avoids a frozen-alpha claim. -/
def averagedSignalField (delta r : ℝ) (alphaPath : ℝ → ℝ) (t : ℝ)
    (q : ℝ × ℝ) : ℝ × ℝ := (-delta*q.2, -q.2 + alphaPath t*q.1-r)

def averagedWindowSlowField (phiPath : ℝ → ℝ) (t S : ℝ) : ℝ := -S+2*phiPath t

/-- A family of actual logistic LR drift recursions in the large matched-Delta
    window. The state sequence is the exact five-coordinate summary recurrence
    `dynamicDriftMap`; `alphaPath` and `phiPath` record its local curvature and
    renormalized ambient temperature on the retention grid.

    v1 input data for the frozen manuscript `ass:W`; superseded in v2 together with
    `SourceAssumptionW` (see its docstring). -/
structure LRWindowInput where
  dim : ℕ → ℕ
  batch : ℕ → ℕ
  learningRate : ℕ → ℝ
  momentum : ℕ → ℝ
  prob : (j : ℕ) → unitInterval
  mu : (j : ℕ) → Vec (dim j)
  state : (j : ℕ) → ℕ → State (dim j)
  equilibrium : (j : ℕ) → State (dim j)
  state_recurrence : ∀ (j k : ℕ),
    dynamicSummary (prob j) (mu j) (state j (k+1)) =
      dynamicDriftMap (B := batch j) (learningRate j) (momentum j) (prob j) (mu j)
        (state j k).1 (dynamicSummary (prob j) (mu j) (state j k))
  equilibrium_fixed : ∀ j,
    dynamicSummary (prob j) (mu j) (equilibrium j) =
      dynamicDriftMap (B := batch j) (learningRate j) (momentum j) (prob j) (mu j)
        (equilibrium j).1 (dynamicSummary (prob j) (mu j) (equilibrium j))
  beta_range : ∀ j, 1/2 ≤ momentum j ∧ momentum j < 1
  fixed_signal_norm : ∃ r0 : ℝ, 0 < r0 ∧ ∀ j, r (mu j) = r0
  actual_parameter_domain : ∀ j, 0 < learningRate j ∧ 0 < (prob j:ℝ) ∧
    (prob j:ℝ) < 1 ∧ 0 < batch j ∧ 2 ≤ dim j ∧ 0 < r (mu j)
  physical_states : ∀ j k, physicallyAdmissibleDynamicState
    (dynamicSummary (prob j) (mu j) (state j k))
  step_tendsto_zero : Tendsto (fun j => 1-momentum j) atTop (𝓝 0)
  delta_tendsto_atTop : Tendsto (fun j => (driftParams (B := batch j) (learningRate j) (momentum j)
    (prob j) (mu j) (equilibrium j).1).matchedDelta) atTop atTop
  internal_resonance_margin : ∃ m : ℝ, 0 < m ∧ ∀ j,
    m ≤ |1+(signalCoord (mu j) (equilibrium j).1)^2-4|
  window_margin : ℝ
  window_margin_pos : 0 < window_margin
  drift_params_conditions : ∀ j,
    let P := driftParams (B := batch j) (learningRate j) (momentum j) (prob j) (mu j) (equilibrium j).1
    0 < P.w ∧ P.w < 2*(1+P.beta) ∧
    External.JuryStability ∧
    0 ≤ P.renormNoise ∧ P.renormNoise ≤ 1-window_margin ∧
    0 ≤ P.renormAdditive ∧
    windowDeltaThreshold window_margin ≤ P.matchedDelta ∧
    P.foldedAngle ≤ Real.pi/2-window_margin
  /-- The W window is a vanishing-noise regime, uniformly along the actual
      drift orbit, rather than a fixed positive-noise regime. -/
  local_noise_tendsto_zero : ∃ noiseBound : ℕ → ℝ,
    Tendsto noiseBound atTop (𝓝 0) ∧
    ∀ j k, 0 ≤ (driftParams (B := batch j) (learningRate j) (momentum j)
      (prob j) (mu j) ((state j k).1)).renormNoise ∧
      (driftParams (B := batch j) (learningRate j) (momentum j)
        (prob j) (mu j) ((state j k).1)).renormNoise ≤ noiseBound j
  /-- Loads and the initial matched bulk energy stay in a common bounded set. -/
  bounded_loads_and_initial_energy : ∃ M : ℝ, 0 < M ∧ ∀ j k,
    (driftParams (B := batch j) (learningRate j) (momentum j) (prob j) (mu j)
      ((state j k).1)).renormAdditive ≤ M ∧
      slowEnergy (driftParams (B := batch j) (learningRate j) (momentum j) (prob j) (mu j)
          ((state j k).1)).matchedDelta
        ((driftParams (B := batch j) (learningRate j) (momentum j) (prob j) (mu j)
          ((state j k).1)).matchedMoments
          (stateBulkMoments (learningRate j) (mu j) (state j 0))) ≤ M
  /-- Coefficients vary tamely on adjacent retention-grid points. -/
  source_tame_error_tendsto_zero : ∃ tameBound : ℕ → ℝ,
    Tendsto tameBound atTop (𝓝 0) ∧
    ∀ j k, tameError (prob j) (mu j) ((state j k).1) ≤ tameBound j
  /-- The coefficient paths also have small adjacent changes on the retention grid. -/
  adjacent_parameter_variation : ∃ variationBound : ℕ → ℝ,
    Tendsto variationBound atTop (𝓝 0) ∧
    ∀ j k,
      |dynamicAlpha (r (mu j)) (dynamicSummary (prob j) (mu j) (state j (k+1))) -
        dynamicAlpha (r (mu j)) (dynamicSummary (prob j) (mu j) (state j k))| ≤ variationBound j ∧
      |(driftParams (B := batch j) (learningRate j) (momentum j) (prob j) (mu j)
          (state j (k+1)).1).renormAdditive -
        (driftParams (B := batch j) (learningRate j) (momentum j) (prob j) (mu j)
          (state j k).1).renormAdditive| ≤ variationBound j
  local_window_conditions : ∀ j k,
    0 < (driftParams (B := batch j) (learningRate j) (momentum j) (prob j) (mu j)
      ((state j k).1)).w ∧
    (driftParams (B := batch j) (learningRate j) (momentum j) (prob j) (mu j)
      ((state j k).1)).w < 2*(1+(driftParams (B := batch j) (learningRate j)
        (momentum j) (prob j) (mu j) ((state j k).1)).beta) ∧
    External.JuryStability ∧
    0 ≤ (driftParams (B := batch j) (learningRate j) (momentum j) (prob j) (mu j)
      ((state j k).1)).renormNoise ∧
    (driftParams (B := batch j) (learningRate j) (momentum j) (prob j) (mu j)
      ((state j k).1)).renormNoise ≤ 1-window_margin ∧
    0 ≤ (driftParams (B := batch j) (learningRate j) (momentum j) (prob j) (mu j)
      ((state j k).1)).renormAdditive ∧
    windowDeltaThreshold window_margin ≤ (driftParams (B := batch j) (learningRate j)
      (momentum j) (prob j) (mu j) ((state j k).1)).matchedDelta ∧
    (driftParams (B := batch j) (learningRate j) (momentum j) (prob j) (mu j)
      ((state j k).1)).foldedAngle ≤ Real.pi/2-window_margin

/-- Source Assumption W. On actual high-Delta LR drift families away from the
    internal 2:1 resonance and under the explicit feedback/Nyquist margins, the
    actual excess-risk envelope has the retention rate; and the bulk slow
    energy and signal are uniformly approximated at all retention-grid times
    by the time-dependent averaged equations below.

    v1 assumption (frozen manuscript `ass:W`); superseded in v2 by v2 `prop:W1`
    (`SparseSGD.Logistic.V2.five_eigenvalues`, `equilibrium_five_eigenvalues`,
    `lambda_mu_trace`), v2 `cor:recursion` (`SparseSGD.Logistic.V2.cor_recursion_tame'`),
    v2 `prop:W2` (`SparseSGD.Logistic.V2.prop_W2_ii`, `prop_W2_iii`) and the narrowed v2
    assumption `ass:W2` (`SparseSGD.Logistic.V2.AssumptionW2`). No theorem in the package
    consumes this structure. -/
structure SourceAssumptionW : Prop where
  actual_window_and_envelope : ∀ F : LRWindowInput,
    ∃ err rate envelope : ℕ → ℝ,
      ∃ alphaPath phiPath : (j : ℕ) → ℝ → ℝ,
      ∃ S : (j : ℕ) → ℝ → ℝ,
      ∃ q : (j : ℕ) → ℝ → ℝ × ℝ,
      Tendsto err atTop (𝓝 0) ∧
      Tendsto (fun j => rate j/(1-F.momentum j)) atTop (𝓝 1) ∧
      (∀ j, 0 < rate j ∧ 0 ≤ envelope j) ∧
      (∀ j, Continuous (alphaPath j) ∧ Continuous (phiPath j)) ∧
      (∀ (j k : ℕ),
        alphaPath j ((k:ℝ)*(1-F.momentum j)) =
          dynamicAlpha (r (F.mu j)) (dynamicSummary (F.prob j) (F.mu j) (F.state j k))) ∧
      (∀ (j k : ℕ),
        phiPath j ((k:ℝ)*(1-F.momentum j)) =
          (driftParams (B := F.batch j) (F.learningRate j) (F.momentum j) (F.prob j) (F.mu j)
            (F.state j k).1).renormAdditive) ∧
      (∀ (j : ℕ) (t : ℝ), 0 ≤ t → HasDerivAt (S j)
        (averagedWindowSlowField (phiPath j) t (S j t)) t) ∧
      (∀ (j : ℕ) (t : ℝ), 0 ≤ t → HasDerivAt (q j)
        (averagedSignalField (F.learningRate j*(F.prob j:ℝ)/(1-F.momentum j))
          (r (F.mu j)) (alphaPath j) t (q j t)) t) ∧
      (∀ (j k : ℕ),
        let P := driftParams (B := F.batch j) (F.learningRate j) (F.momentum j)
          (F.prob j) (F.mu j) (F.state j k).1
        |slowEnergy P.matchedDelta
            (P.matchedMoments (stateBulkMoments (F.learningRate j) (F.mu j) (F.state j k))) -
          S j ((k:ℝ)*(1-F.momentum j))| ≤ err j) ∧
      (∀ (j k : ℕ),
        ‖q j ((k:ℝ)*(1-F.momentum j)) -
          (signalCoord (F.mu j) (F.state j k).1,
            signalCoord (F.mu j) (F.state j k).2/(F.prob j:ℝ))‖ ≤ err j) ∧
      (∀ (j k : ℕ),
        |populationLoss (F.prob j) (F.mu j) (F.state j k).1 -
          populationLoss (F.prob j) (F.mu j) (F.equilibrium j).1| ≤
            envelope j*Real.exp (-rate j*(k:ℝ))) ∧
      (∀ (j : ℕ) (t : ℝ), 0 ≤ t →
        ‖q j t - (signalCoord (F.mu j) (F.equilibrium j).1,0)‖ ≤
          envelope j*Real.exp (-t/2))

end
end SparseSGD.Logistic
