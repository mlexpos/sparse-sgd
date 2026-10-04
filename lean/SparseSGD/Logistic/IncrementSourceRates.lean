import SparseSGD.Logistic.IncrementFullConditional
import SparseSGD.Logistic.FixedPointAsymptotics
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

def lrSourceQuadraticRate (d B : ℕ) (eta : ℝ) (p : unitInterval) : ℝ :=
  (logisticPhi d B eta)^2*eta^2*(p : ℝ)^2*(1/((B : ℝ)*(p : ℝ))+2/(d : ℝ))

theorem lr_quadratic_rate_le {d B : ℕ} (eta : ℝ) (p : unitInterval)
    (hd : 2 ≤ d) (hB : 0 < B) (hp : 0 < (p : ℝ)) :
    eta^4*complementQuadraticVariance p d B ≤ 16*lrSourceQuadraticRate d B eta p := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hdpos : (0 : ℝ) < d := by linarith
  have hd2 : (d : ℝ)^2 ≤ 4*((d : ℝ)-1)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ (d : ℝ)-2 by linarith) (show 0 ≤ 3*(d : ℝ)-2 by linarith)]
  have h1 : (d : ℝ) ≤ 8*((d : ℝ)-1)^2/(d : ℝ) := by
    apply (le_div_iff₀ hdpos).2
    nlinarith [sq_nonneg ((d : ℝ)-1)]
  have ha : eta^4*(d : ℝ)*(p : ℝ)^2/(B : ℝ)^2 ≤
      eta^4*(8*((d : ℝ)-1)^2/(d : ℝ))*(p : ℝ)^2/(B : ℝ)^2 := by
    gcongr
  have hc : eta^4*(d : ℝ)^2*(p : ℝ)/(B : ℝ)^3 ≤
      eta^4*(4*((d : ℝ)-1)^2)*(p : ℝ)/(B : ℝ)^3 := by
    gcongr
  have he : eta^4*(8*((d : ℝ)-1)^2/(d : ℝ))*(p : ℝ)^2/(B : ℝ)^2 +
      eta^4*(4*((d : ℝ)-1)^2)*(p : ℝ)/(B : ℝ)^3 =
      16*lrSourceQuadraticRate d B eta p := by
    dsimp [lrSourceQuadraticRate, logisticPhi]
    field_simp
    <;> ring
  rw [← he]
  dsimp [complementQuadraticVariance]
  convert add_le_add ha hc using 1 <;> ring
def lrSourceVariance (d B : ℕ) (eta : ℝ) (p : unitInterval) (mu : Vec d) : ℝ :=
  eta^2*(p : ℝ)/(B : ℝ)*(1+(r mu)^2)+lrSourceQuadraticRate d B eta p

def lrSourceVarianceConstant (Q K L : ℝ) : ℝ :=
  64*(stoppedDirectionBound Q K L)^2*rareProjectionConstant Q+1152*bulkQuadraticConstant Q

theorem lrIncrementVariance_le_source {d B : ℕ} (eta : ℝ) (p : unitInterval)
    (mu : Vec d) (Q K L : ℝ) (hd : 2 ≤ d) (hB : 0 < B) (hp : 0 < (p : ℝ)) :
    lrIncrementVariance eta p mu Q K L B ≤
      lrSourceVarianceConstant Q K L*lrSourceVariance d B eta p mu := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hrare : 0 ≤ rareProjectionConstant Q := by dsimp [rareProjectionConstant]; positivity
  have hbulk : 0 ≤ bulkQuadraticConstant Q := by
    dsimp [bulkQuadraticConstant,symmetricProjectionConstant]; positivity
  let c1 := 64*(stoppedDirectionBound Q K L)^2*rareProjectionConstant Q
  let c2 := 1152*bulkQuadraticConstant Q
  let v1 := eta^2*(p : ℝ)/(B : ℝ)*(1+(r mu)^2)
  let v2 := lrSourceQuadraticRate d B eta p
  have hc1 : 0 ≤ c1 := by dsimp [c1]; positivity
  have hc2 : 0 ≤ c2 := by dsimp [c2]; positivity
  have hv1 : 0 ≤ v1 := by dsimp [v1]; positivity
  have hv2 : 0 ≤ v2 := by
    dsimp [v2,lrSourceQuadraticRate]; positivity
  have hs : (1+r mu)^2 ≤ 2*(1+(r mu)^2) := by nlinarith [sq_nonneg (r mu-1)]
  have hl := mul_le_mul_of_nonneg_left hs (show 0 ≤
    32*eta^2*(stoppedDirectionBound Q K L)^2*rareProjectionConstant Q*(p : ℝ)/(B : ℝ) by positivity)
  have hq := mul_le_mul_of_nonneg_left (lr_quadratic_rate_le eta p hd hB hp)
    (show 0 ≤ 72*bulkQuadraticConstant Q by positivity)
  have hsum : lrIncrementVariance eta p mu Q K L B ≤ c1*v1+c2*v2 := by
    dsimp [lrIncrementVariance,projectionVariance,bulkQuadraticVariance,c1,c2,v1,v2]
    convert add_le_add hl hq using 1 <;> ring
  calc
    lrIncrementVariance eta p mu Q K L B ≤ c1*v1+c2*v2 := hsum
    _ ≤ (c1+c2)*(v1+v2) := by
      nlinarith [mul_nonneg hc1 hv2,mul_nonneg hc2 hv1]
    _ = lrSourceVarianceConstant Q K L*lrSourceVariance d B eta p mu := rfl
def lrSourceScale (d B : ℕ) (eta : ℝ) (mu : Vec d) : ℝ :=
  eta/(B : ℝ)*(1+r mu)*(1+logisticPhi d B eta+eta)

def lrSourceScaleConstant (Q K L : ℝ) : ℝ :=
  4*stoppedDirectionBound Q K L+384*(symmetricProjectionConstant Q 2+10)+1536

theorem lrIncrementScale_le_source {d B : ℕ} (eta : ℝ) (mu : Vec d) (Q K L : ℝ)
    (hd : 2 ≤ d) (hB : 0 < B) (heta : 0 ≤ eta)
    (hQ : 0 ≤ Q) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    lrIncrementScale eta mu Q K L B ≤ lrSourceScaleConstant Q K L*lrSourceScale d B eta mu := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hr : 0 ≤ r mu := norm_nonneg mu
  have hdm : 0 ≤ (d : ℝ)-1 := by linarith
  have hphi : 0 ≤ logisticPhi d B eta := by dsimp [logisticPhi]; positivity
  have hD : 0 ≤ stoppedDirectionBound Q K L := by dsimp [stoppedDirectionBound]; positivity
  have hC : 0 ≤ symmetricProjectionConstant Q 2+10 := by dsimp [symmetricProjectionConstant]; positivity
  have hdim : (d : ℝ) ≤ 2*((d : ℝ)-1) := by linarith
  have hdim' := mul_le_mul_of_nonneg_left hdim (show 0 ≤ eta^2/(B : ℝ)^2 by positivity)
  have hquad : eta^2*(d : ℝ)/(B : ℝ)^2 ≤ 4*(eta/(B : ℝ))*logisticPhi d B eta := by
    dsimp [logisticPhi]
    convert hdim' using 1 <;> field_simp <;> ring
  let z := lrSourceScale d B eta mu
  have h1 : eta/(B : ℝ)*(1+r mu) ≤ z := by
    dsimp [z,lrSourceScale]
    have hh := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1+logisticPhi d B eta+eta by linarith)
      (show 0 ≤ eta/(B : ℝ)*(1+r mu) by positivity)
    convert hh using 1 <;> ring
  have h2 : eta^2/(B : ℝ) ≤ z := by
    have he : eta ≤ (1+r mu)*(1+logisticPhi d B eta+eta) := by
      nlinarith [mul_nonneg hr (show 0 ≤ 1+logisticPhi d B eta+eta by positivity)]
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ eta/(B : ℝ) by positivity)
    dsimp [z,lrSourceScale]
    convert hh using 1 <;> ring
  have h3 : eta/(B : ℝ)*logisticPhi d B eta ≤ z := by
    have he : logisticPhi d B eta ≤ (1+r mu)*(1+logisticPhi d B eta+eta) := by
      nlinarith [mul_nonneg hr (show 0 ≤ 1+logisticPhi d B eta+eta by positivity)]
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ eta/(B : ℝ) by positivity)
    dsimp [z,lrSourceScale]
    convert hh using 1 <;> ring
  have ha := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 4*stoppedDirectionBound Q K L by positivity)
  have hc := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 384*(symmetricProjectionConstant Q 2+10) by positivity)
  have hquad' : eta^2*(d : ℝ)/(B : ℝ)^2 ≤ 4*z := by
    apply hquad.trans
    convert mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ 4 by norm_num) using 1 <;> ring
  have hg := mul_le_mul_of_nonneg_left hquad' (show (0 : ℝ) ≤ 384 by norm_num)
  dsimp [lrIncrementScale,projectionScale,bulkQuadraticScale,lrSourceScaleConstant]
  convert add_le_add (add_le_add ha hc) hg using 1 <;> ring
end
end SparseSGD.Logistic
