import SparseSGD.Discrete.Chebyshev
import SparseSGD.Foundations

namespace SparseSGD
noncomputable section

/-- The small-step discriminant in retention coordinates. -/
def smallDeltaDisc (beta Delta : ℝ) : ℝ :=
  1 - 2 * Delta * (1 + beta) + Delta^2 * (1 - beta)^2

def smallDeltaLambdaPlus (beta Delta : ℝ) : ℝ :=
  (1 + beta - Delta * (1-beta)^2 + (1-beta) * Real.sqrt (smallDeltaDisc beta Delta)) / 2

def smallDeltaLambdaMinus (beta Delta : ℝ) : ℝ :=
  (1 + beta - Delta * (1-beta)^2 - (1-beta) * Real.sqrt (smallDeltaDisc beta Delta)) / 2

def smallDeltaZ (beta Delta : ℝ) : ℝ := Delta * (1-beta)

def smallDeltaW (beta Delta : ℝ) : ℝ := Delta * (1-beta)^2

theorem smallDeltaSpectrum_strong (beta Delta : ℝ)
    (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8) :
    1/2 ≤ smallDeltaDisc beta Delta ∧
    smallDeltaLambdaPlus beta Delta - smallDeltaLambdaMinus beta Delta ≥ (1-beta)/2 ∧
    0 ≤ smallDeltaLambdaMinus beta Delta ∧
    smallDeltaLambdaMinus beta Delta ≤ beta + 2 * smallDeltaZ beta Delta ∧
    0 < smallDeltaLambdaPlus beta Delta ∧ smallDeltaLambdaPlus beta Delta < 1 ∧
    |(1-smallDeltaLambdaPlus beta Delta) - smallDeltaZ beta Delta| ≤
      8 * Delta * smallDeltaZ beta Delta ∧
    smallDeltaLambdaPlus beta Delta * smallDeltaLambdaMinus beta Delta = beta ∧
    smallDeltaLambdaPlus beta Delta + smallDeltaLambdaMinus beta Delta =
      1 + beta - smallDeltaW beta Delta ∧
    smallDeltaZ beta Delta ≤ 1-smallDeltaLambdaPlus beta Delta ∧
    1-smallDeltaLambdaPlus beta Delta ≤ smallDeltaZ beta Delta+2*Delta*smallDeltaZ beta Delta ∧
    beta ≤ smallDeltaLambdaMinus beta Delta := by
  let A := 1-Delta*(1+beta)
  let S := Real.sqrt (smallDeltaDisc beta Delta)
  have heps : 0 < 1-beta := by linarith
  have heps1 : 1-beta ≤ 1 := by linarith
  have hDlow : (1/2 : ℝ) ≤ smallDeltaDisc beta Delta := by
    unfold smallDeltaDisc
    nlinarith [sq_nonneg (Delta*(1-beta))]
  have hs0 : 0 ≤ S := Real.sqrt_nonneg _
  have hs2 : S^2 = smallDeltaDisc beta Delta := Real.sq_sqrt (by linarith)
  have hslo : (1/2 : ℝ) ≤ S := by nlinarith
  have hA : (3/4 : ℝ) ≤ A := by dsimp [A]; nlinarith
  have hidentity : A^2-S^2 = 4*beta*Delta^2 := by
    rw [hs2]
    dsimp [A,smallDeltaDisc]
    ring
  have hdiff0 : 0 ≤ A-S := by
    have hprod : 0 ≤ 4*beta*Delta^2 := by positivity
    nlinarith
  have hdiff4 : A-S ≤ 4*Delta^2 := by
    have hprod : (A-S)*(A+S) = 4*beta*Delta^2 := by nlinarith only [hidentity]
    have hh : 0 ≤ (A-S)*(A+S-1) := mul_nonneg hdiff0 (by linarith)
    have hb : beta*Delta^2 ≤ Delta^2 := by nlinarith [mul_nonneg (sq_nonneg Delta) heps.le]
    nlinarith
  have hslow : 1-smallDeltaLambdaPlus beta Delta = smallDeltaZ beta Delta+(1-beta)/2*(A-S) := by
    dsimp [smallDeltaLambdaPlus,smallDeltaZ,A,S]
    ring
  have hfast : smallDeltaLambdaMinus beta Delta = beta+beta*smallDeltaZ beta Delta+(1-beta)/2*(A-S) := by
    dsimp [smallDeltaLambdaMinus,smallDeltaZ,A,S]
    ring
  have hz : 0 < smallDeltaZ beta Delta := mul_pos hD0 heps
  have hzsmall : smallDeltaZ beta Delta ≤ 1/8 := by dsimp [smallDeltaZ]; nlinarith
  have hdsmall : 0 ≤ (1-beta)/2*(A-S) ∧
      (1-beta)/2*(A-S) ≤ 2*Delta*smallDeltaZ beta Delta := by
    constructor
    · positivity
    · have h := mul_le_mul_of_nonneg_left hdiff4 (show 0≤(1-beta)/2 by positivity)
      dsimp [smallDeltaZ]
      nlinarith only [h]
  have hDsmall : 2*Delta*smallDeltaZ beta Delta ≤ smallDeltaZ beta Delta/4 := by
    nlinarith [mul_le_mul_of_nonneg_right hD1 hz.le]
  have hpluspos : 0 < smallDeltaLambdaPlus beta Delta := by linarith [hdsmall.2]
  have hpluslt : smallDeltaLambdaPlus beta Delta < 1 := by linarith [hdsmall.1]
  have hminus0 : 0 ≤ smallDeltaLambdaMinus beta Delta := by
    have h := mul_nonneg hb0 hz.le
    linarith [hdsmall.1]
  have hminusup : smallDeltaLambdaMinus beta Delta ≤ beta+2*smallDeltaZ beta Delta := by
    have h := mul_le_mul_of_nonneg_right hb1.le hz.le
    linarith [hdsmall.2]
  have hgap : smallDeltaLambdaPlus beta Delta-smallDeltaLambdaMinus beta Delta = (1-beta)*S := by
    dsimp [smallDeltaLambdaPlus,smallDeltaLambdaMinus,S]
    ring
  have hdev : |(1-smallDeltaLambdaPlus beta Delta)-smallDeltaZ beta Delta| ≤
      8*Delta*smallDeltaZ beta Delta := by
    rw [hslow,add_sub_cancel_left,abs_of_nonneg hdsmall.1]
    nlinarith [mul_nonneg hD0.le hz.le,hdsmall.2]
  have hprod : smallDeltaLambdaPlus beta Delta*smallDeltaLambdaMinus beta Delta=beta := by
    dsimp [smallDeltaLambdaPlus,smallDeltaLambdaMinus]
    change ((1+beta-Delta*(1-beta)^2+(1-beta)*S)/2)*
      ((1+beta-Delta*(1-beta)^2-(1-beta)*S)/2)=beta
    dsimp [smallDeltaDisc] at hs2
    linear_combination -((1-beta)^2/4)*hs2
  have hsum : smallDeltaLambdaPlus beta Delta+smallDeltaLambdaMinus beta Delta=1+beta-smallDeltaW beta Delta := by
    dsimp [smallDeltaLambdaPlus,smallDeltaLambdaMinus,smallDeltaW]
    ring
  refine ⟨hDlow,?_,hminus0,hminusup,hpluspos,hpluslt,hdev,hprod,hsum,?_,?_,?_⟩
  · rw [hgap]
    nlinarith [mul_le_mul_of_nonneg_left hslo heps.le]
  · linarith [hdsmall.1]
  · linarith [hdsmall.2]
  · linarith [hdsmall.1,mul_nonneg hb0 hz.le]

theorem smallDeltaSpectrum (beta Delta : ℝ)
    (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8) :
    1/2 ≤ smallDeltaDisc beta Delta ∧
    smallDeltaLambdaPlus beta Delta - smallDeltaLambdaMinus beta Delta ≥ (1-beta)/2 ∧
    0 ≤ smallDeltaLambdaMinus beta Delta ∧
    smallDeltaLambdaMinus beta Delta ≤ beta + 2 * smallDeltaZ beta Delta ∧
    0 < smallDeltaLambdaPlus beta Delta ∧ smallDeltaLambdaPlus beta Delta < 1 ∧
    |(1-smallDeltaLambdaPlus beta Delta) - smallDeltaZ beta Delta| ≤
      8 * Delta * smallDeltaZ beta Delta ∧
    smallDeltaLambdaPlus beta Delta * smallDeltaLambdaMinus beta Delta = beta ∧
    smallDeltaLambdaPlus beta Delta + smallDeltaLambdaMinus beta Delta =
      1 + beta - smallDeltaW beta Delta := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,_⟩ := smallDeltaSpectrum_strong beta Delta hb0 hb1 hD0 hD1
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩

end
end SparseSGD
