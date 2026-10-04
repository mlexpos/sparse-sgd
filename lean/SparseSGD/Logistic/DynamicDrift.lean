import SparseSGD.Logistic.DynamicField
import SparseSGD.Logistic.Drift
namespace SparseSGD.Logistic
noncomputable section
open MeasureTheory
set_option maxHeartbeats 1600000

/-- Exact drift coordinates, ordered as in LR34. -/
def dynamicSummary {d : ℕ} (p : unitInterval) (mu : Vec d) (s : State d) : DynamicState :=
  ![signalCoord mu s.1, signalCoord mu s.2 / (p : ℝ),
    ‖bulkPart mu s.1‖ ^ 2, ‖bulkPart mu s.2‖ ^ 2 / (p : ℝ)^2,
    inner ℝ (bulkPart mu s.1) (bulkPart mu s.2) / (p : ℝ)]

/-- The exact coefficient-driven normalized map. `noise` is the one-step
normalized batch second moment, before its factor `h²`. -/
def dynamicCoefficientStep (r h delta a b noise : ℝ) (y : DynamicState) : DynamicState :=
  let Yn := (1-h)*y 1+h*(a*y 0+b*r)
  let Vn := (1-h)^2*y 3+2*h*(1-h)*a*y 4+h^2*noise
  let Cn := (1-h)*y 4+h*a*y 2-delta*h*Vn
  ![y 0-delta*h*Yn, Yn,
    y 2-2*delta*h*((1-h)*y 4+h*a*y 2)+delta^2*h^2*Vn, Vn, Cn]

/-- Actual coefficients and actual finite-batch bulk second moment. -/
def dynamicDriftMap {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu theta : Vec d) (y : DynamicState) : DynamicState :=
  dynamicCoefficientStep (r mu) (1-beta) (eta*(p:ℝ)/(1-beta))
    (coefA p mu theta/(p:ℝ)) (coefB p mu theta/(p:ℝ))
    ((((d-1:ℝ)*coefD0 p mu theta+y 2*coefDtheta p mu theta)/(B:ℝ)+
      ((B:ℝ)-1)/(B:ℝ)*(coefA p mu theta)^2*y 2)/(p:ℝ)^2) y

private theorem dynamicDriftMap_bulk (d B : ℕ) (eta beta p A D0 Dt r b : ℝ)
    (y : DynamicState) (hp : p ≠ 0) (heta : eta ≠ 0) (hbeta : 1-beta ≠ 0)
    (hA : A ≠ 0) (hB : (B:ℝ) ≠ 0) :
    let P := SparseSGD.oracleParams beta eta A ((Dt-A^2)/(B:ℝ)) ((d-1:ℝ)*D0/(B:ℝ))
    let sn := P.step ⟨y 2, eta^2*p^2*y 3, eta*p*y 4⟩
    let yn := dynamicCoefficientStep r (1-beta) (eta*p/(1-beta)) (A/p) b
      ((((d-1:ℝ)*D0+y 2*Dt)/(B:ℝ)+((B:ℝ)-1)/(B:ℝ)*A^2*y 2)/p^2) y
    yn 2 = sn.R ∧ yn 3 = sn.V/(eta^2*p^2) ∧ yn 4 = sn.C/(eta*p) := by
  dsimp [SparseSGD.oracleParams, SparseSGD.Params.step, SparseSGD.Params.eps,
    dynamicCoefficientStep]
  constructor
  · field_simp [hp, heta, hbeta, hA, hB]
    <;> ring
  constructor <;> field_simp [hp, heta, hbeta, hA, hB] <;> ring

/-- The coefficient map is the actual fresh-batch integrated transition,
coordinate by coordinate. -/
theorem dynamicDriftMap_eq_integral {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d)
    (hr : 0 < r mu) (hp0 : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1)
    (heta : eta ≠ 0) (hbeta : 1-beta ≠ 0) :
    ∀ i, (∫ a : Batch d B, dynamicSummary p mu (update eta beta p mu s a) i
      ∂batchLaw d B p) =
      dynamicDriftMap (B:=B) eta beta p mu s.1 (dynamicSummary p mu s) i := by
  have hp : (p:ℝ) ≠ 0 := ne_of_gt hp0
  have hBr : (B:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hs := one_step_drift H hB eta beta p mu s hr hp0 hp1
  have hm := update_bulk_moment_drift H hB eta beta p mu s hr hp0 hp1
  have hm' : (⟨∫ a : Batch d B, ‖bulkPart mu (update eta beta p mu s a).1‖^2 ∂batchLaw d B p,
      eta^2*(∫ a : Batch d B, ‖bulkPart mu (update eta beta p mu s a).2‖^2 ∂batchLaw d B p),
      eta*(∫ a : Batch d B, inner ℝ (bulkPart mu (update eta beta p mu s a).1)
        (bulkPart mu (update eta beta p mu s a).2) ∂batchLaw d B p)⟩ : SparseSGD.Moments) =
      (driftParams (B:=B) eta beta p mu s.1).step
        ⟨dynamicSummary p mu s 2, eta^2*(p:ℝ)^2*dynamicSummary p mu s 3,
          eta*(p:ℝ)*dynamicSummary p mu s 4⟩ := by
    convert hm using 1 <;> simp [dynamicSummary] <;> field_simp <;> ring
  dsimp only [driftParams] at hm'
  have hmap := dynamicDriftMap_bulk d B eta beta (p:ℝ) (coefA p mu s.1)
    (coefD0 p mu s.1) (coefDtheta p mu s.1) (r mu) (coefB p mu s.1/(p:ℝ))
    (dynamicSummary p mu s) hp heta hbeta (ne_of_gt (coefA_pos p mu s.1 hp0 hp1)) hBr
  change dynamicDriftMap (B:=B) eta beta p mu s.1 (dynamicSummary p mu s) 2 = _ ∧
    dynamicDriftMap (B:=B) eta beta p mu s.1 (dynamicSummary p mu s) 3 = _ ∧
    dynamicDriftMap (B:=B) eta beta p mu s.1 (dynamicSummary p mu s) 4 = _ at hmap

  intro i
  fin_cases i
  · change (∫ a : Batch d B, signalCoord mu (update eta beta p mu s a).1 ∂batchLaw d B p) = _
    rw [hs.2.1]
    simp [dynamicDriftMap, dynamicCoefficientStep, dynamicSummary]
    field_simp
    <;> ring
  · change (∫ a : Batch d B, signalCoord mu (update eta beta p mu s a).2 / (p:ℝ) ∂batchLaw d B p) = _
    simp [integral_div, hs.1, dynamicDriftMap, dynamicCoefficientStep, dynamicSummary]
    field_simp
    <;> ring
  · change (∫ a : Batch d B, ‖bulkPart mu (update eta beta p mu s a).1‖^2 ∂batchLaw d B p) =
      dynamicDriftMap (B:=B) eta beta p mu s.1 (dynamicSummary p mu s) 2
    exact (congrArg SparseSGD.Moments.R hm').trans hmap.1.symm
  · change (∫ a : Batch d B, ‖bulkPart mu (update eta beta p mu s a).2‖^2 / (p:ℝ)^2 ∂batchLaw d B p) =
      dynamicDriftMap (B:=B) eta beta p mu s.1 (dynamicSummary p mu s) 3
    rw [integral_div, hmap.2.1, ← congrArg SparseSGD.Moments.V hm']
    simp only [SparseSGD.Moments.V]
    field_simp
  · change (∫ a : Batch d B, inner ℝ (bulkPart mu (update eta beta p mu s a).1)
      (bulkPart mu (update eta beta p mu s a).2) / (p:ℝ) ∂batchLaw d B p) =
      dynamicDriftMap (B:=B) eta beta p mu s.1 (dynamicSummary p mu s) 4
    rw [integral_div, hmap.2.2, ← congrArg SparseSGD.Moments.C hm']
    simp only [SparseSGD.Moments.C]
    field_simp

end
end SparseSGD.Logistic
