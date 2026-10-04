import SparseSGD.Logistic.IncrementAlignedBulk
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false

def bulkQuadraticScale (Q : ℝ) (d B : ℕ) : ℝ :=
  64*(symmetricProjectionConstant Q 2+9)/(B : ℝ)+64/(B : ℝ)+64*(d : ℝ)/(B : ℝ)^2

def bulkQuadraticConstant (Q : ℝ) : ℝ :=
  2048*Real.exp (8*Real.exp (2*Q^2+4))*(symmetricProjectionConstant Q 4+(symmetricProjectionConstant Q 2)^2)+
    1024*Real.exp (1/2)

def bulkQuadraticVariance (Q : ℝ) (p : unitInterval) (d B : ℕ) : ℝ :=
  2*bulkQuadraticConstant Q*complementQuadraticVariance p d B

theorem bulk_parameter_bounds (k m B : ℕ) (Q t : ℝ) (hk : k ≤ 2) (hB : 0 < B)
    (ht : |t| * bulkQuadraticScale Q ((k+1)+m) B ≤ 1) :
    |(k : ℝ)*(2*t)| ≤ projectionSquareRadius Q B ∧
    |2*t| * complementQuadraticScale m B ≤ 1 := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hc : 0 < 16*(symmetricProjectionConstant Q 2+9) := by
    dsimp [symmetricProjectionConstant]
    positivity
  have hC : 0 ≤ symmetricProjectionConstant Q 2 := by dsimp [symmetricProjectionConstant]; positivity
  have hklin : (k : ℝ) ≤ 2 := by exact_mod_cast hk
  have hlin : 64*(symmetricProjectionConstant Q 2+9)/(B : ℝ) ≤ bulkQuadraticScale Q ((k+1)+m) B := by
    dsimp [bulkQuadraticScale]
    have h1 : 0 ≤ 64/(B : ℝ) := by positivity
    have h2 : 0 ≤ 64*((k+1)+m : ℝ)/(B : ℝ)^2 := by positivity
    simp only [Nat.cast_add, Nat.cast_one] at *
    linarith
  have hh := (mul_le_mul_of_nonneg_left hlin (abs_nonneg t)).trans ht
  have hh' : 64*|t| * (symmetricProjectionConstant Q 2+9) ≤ B := by
    apply (div_le_one hb).mp
    convert hh using 1 <;> ring
  constructor
  · dsimp [projectionSquareRadius]
    apply (le_div_iff₀ hc).mpr
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg k), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hkmul := mul_le_mul_of_nonneg_right hklin (show 0 ≤ 32*|t| * (symmetricProjectionConstant Q 2+9) by positivity)
    simp only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] at *
    nlinarith
  · have hmd : (m : ℝ) ≤ (k+1)+m := by
      exact_mod_cast (show m ≤ (k+1)+m by omega)
    have hs : 2*complementQuadraticScale m B ≤ bulkQuadraticScale Q ((k+1)+m) B := by
      have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmd (by norm_num : (0 : ℝ) ≤ 64)) (sq_nonneg (B : ℝ))
      have hx : 0 ≤ 64*(symmetricProjectionConstant Q 2+9)/(B : ℝ) := by positivity
      dsimp [complementQuadraticScale, bulkQuadraticScale]
      simp only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] at *
      nlinarith
    have hh := (mul_le_mul_of_nonneg_left hs (abs_nonneg t)).trans ht
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    convert hh using 1 <;> ring

/-- The active and complement terms fit the source's rare quadratic
variance orders uniformly in the constructed frame dimension. -/
theorem bulk_exponent_bound (k m B : ℕ) (p : unitInterval) (Q t : ℝ) (hk : k ≤ 2) :
    Real.exp (8*Real.exp (2*Q^2+4))*projectionSquareVariance Q p B*((k : ℝ)*(2*t))^2+
      256*Real.exp (1/2)*complementQuadraticVariance p m B*(2*t)^2 ≤
      bulkQuadraticConstant Q*complementQuadraticVariance p ((k+1)+m) B*t^2 := by
  let D : ℝ := ((k+1)+m : ℕ)
  let V := complementQuadraticVariance p ((k+1)+m) B
  have hd : 1 ≤ D := by dsimp [D]; exact_mod_cast (show 1 ≤ (k+1)+m by omega)
  have hm : (m : ℝ) ≤ D := by dsimp [D]; exact_mod_cast (show m ≤ (k+1)+m by omega)
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hp : 0 ≤ (p : ℝ) := p.property.1
  have hV : 0 ≤ V := by dsimp [V, complementQuadraticVariance]; positivity
  have hC2 : 0 ≤ symmetricProjectionConstant Q 2 := by dsimp [symmetricProjectionConstant]; positivity
  have hC4 : 0 ≤ symmetricProjectionConstant Q 4 := by dsimp [symmetricProjectionConstant]; positivity
  have hd2 : 1 ≤ D^2 := by nlinarith
  have hsmall1 : (p : ℝ)/(B : ℝ)^3 ≤ V := by
    have hh := mul_le_mul_of_nonneg_right hd2 (show 0 ≤ (p : ℝ)/(B : ℝ)^3 by positivity)
    have hx : 0 ≤ D*(p : ℝ)^2/(B : ℝ)^2 := by positivity
    dsimp [V, complementQuadraticVariance]
    dsimp [D] at hh hx
    simp only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] at *
    nlinarith
  have hsmall2 : (p : ℝ)^2/(B : ℝ)^2 ≤ V := by
    have hh := mul_le_mul_of_nonneg_right hd (show 0 ≤ (p : ℝ)^2/(B : ℝ)^2 by positivity)
    have hx : 0 ≤ D^2*(p : ℝ)/(B : ℝ)^3 := by positivity
    dsimp [V, complementQuadraticVariance]
    dsimp [D] at hh hx
    simp only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] at *
    nlinarith
  have hproj : projectionSquareVariance Q p B ≤
      128*(symmetricProjectionConstant Q 4+(symmetricProjectionConstant Q 2)^2)*V := by
    have h1 := mul_le_mul_of_nonneg_left hsmall1 hC4
    have h2 := mul_le_mul_of_nonneg_left hsmall2 (sq_nonneg (symmetricProjectionConstant Q 2))
    dsimp [projectionSquareVariance]
    simp only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] at *
    nlinarith
  have hcomp : complementQuadraticVariance p m B ≤ V := by
    have hm2 : (m : ℝ)^2 ≤ D^2 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hm (show 0 ≤ (p : ℝ)^2/(B : ℝ)^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_right hm2 (show 0 ≤ (p : ℝ)/(B : ℝ)^3 by positivity)
    dsimp [complementQuadraticVariance, V]
    dsimp [D] at h1 h2
    simp only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] at *
    nlinarith
  have hksq : ((k : ℝ)*(2*t))^2 ≤ 16*t^2 := by
    have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    have hh := mul_le_mul_of_nonneg_right (show (k : ℝ)^2 ≤ 4 by nlinarith) (sq_nonneg t)
    simp only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] at *
    nlinarith
  have hactive := mul_le_mul hproj hksq (sq_nonneg ((k : ℝ)*(2*t)))
    (show 0 ≤ 128*(symmetricProjectionConstant Q 4+(symmetricProjectionConstant Q 2)^2)*V by positivity)
  have hactive' := mul_le_mul_of_nonneg_left hactive (Real.exp_pos (8*Real.exp (2*Q^2+4))).le
  have hrest := mul_le_mul_of_nonneg_right hcomp (show 0 ≤ 256*Real.exp (1/2)*(2*t)^2 by positivity)
  dsimp [bulkQuadraticConstant]
  nlinarith
/-- Actual centered full bulk-square MGF: the active frame is constructed
from the given state, its Gaussian law is proved, and both rare quadratic
variance orders are retained. -/
theorem tame_bulk_square_mgf {d B : ℕ}
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (J : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : SparseSGD.External.GaussianSteinCertificate d)
    (p : unitInterval) (mu theta momentum : Vec d) (Q t : ℝ)
    (hB : 0 < B) (hp : 0 < (p : ℝ)) (hr : 0 < r mu)
    (htame : tameError p mu theta ≤ 1/2) (hθ : ‖theta‖ ≤ Q)
    (ht : |t| * bulkQuadraticScale Q d B < 1) :
    Integrable (fun a : Batch d B => Real.exp (t*centeredBulkSquare p mu theta a)) (batchLaw d B p) ∧
    (∫ a : Batch d B, Real.exp (t*centeredBulkSquare p mu theta a) ∂batchLaw d B p) ≤
      Real.exp (t^2*bulkQuadraticVariance Q p d B/(2*(1-|t| * bulkQuadraticScale Q d B))) := by
  obtain ⟨k,m,hk,hd,O,i0,hi0,hmu,htheta,hmom⟩ := exists_two_bulk_logistic_frame mu theta momentum hr
  subst d
  have hi : i0=(⟨0,by omega⟩ : Fin ((k+1)+m)) := Fin.ext hi0
  rw [hi] at hmu
  have hthetaC : frameComplement (O theta)=0 := frameComplement_of_support _ htheta
  have hparams := bulk_parameter_bounds k m B Q t hk hB ht.le
  have hh := aligned_bulk_square_mgf (H (k+1)) (J (k+1)) G S O p mu theta Q t hB hp hr hmu hthetaC
    htame hθ hparams.1 hparams.2
  refine ⟨hh.1, hh.2.trans ?_⟩
  apply Real.exp_le_exp.mpr
  have hb := bulk_exponent_bound k m B p Q t hk
  refine hb.trans ?_
  have hs : 0 ≤ bulkQuadraticScale Q ((k+1)+m) B := by
    dsimp [bulkQuadraticScale, symmetricProjectionConstant]
    positivity
  have hv : 0 ≤ bulkQuadraticVariance Q p ((k+1)+m) B := by
    dsimp [bulkQuadraticVariance, bulkQuadraticConstant, complementQuadraticVariance, symmetricProjectionConstant]
    positivity
  have hd : 0 < 2*(1-|t| * bulkQuadraticScale Q ((k+1)+m) B) := by linarith
  have hden : 2*(1-|t| * bulkQuadraticScale Q ((k+1)+m) B) ≤ 2 := by nlinarith [abs_nonneg t]
  have hdiv := div_le_div_of_nonneg_left
    (show 0 ≤ t^2*bulkQuadraticVariance Q p ((k+1)+m) B by positivity) hd hden
  exact (show bulkQuadraticConstant Q*complementQuadraticVariance p ((k+1)+m) B*t^2 =
      t^2*bulkQuadraticVariance Q p ((k+1)+m) B/2 by dsimp [bulkQuadraticVariance]; ring).le.trans hdiv

end
end SparseSGD.Logistic
