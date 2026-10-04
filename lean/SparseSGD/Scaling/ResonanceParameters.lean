import SparseSGD.Scaling.IntegerRounding
import SparseSGD.Scaling.LeastSquaresParameters

namespace SparseSGD.Scaling
noncomputable section

/-- Actual least-squares noise load on the critical noise exponent alpha=1-sigma. -/
def resonantNoiseLoad (etaStar bStar sigma : ℝ) (p : ℕ → unitInterval) (d : ℕ) : ℝ :=
  scaledLearningRate etaStar (1-sigma) d * ((d:ℝ)+2-(p d:ℝ)) /
    (2*(scaledBatch bStar sigma d:ℝ))

def resonantAdditiveLoad (etaStar bStar sigma variance : ℝ) (d : ℕ) : ℝ :=
  scaledLearningRate etaStar (1-sigma) d * variance * (d:ℝ) /
    (2*(scaledBatch bStar sigma d:ℝ))

theorem actualLSParams_resonant_noise_eq
    (pStar kappa bStar sigma epsStar gamma etaStar : ℝ)
    (p : ℕ → unitInterval) (ν : MeasureTheory.Measure ℝ) (d : ℕ)
    (hp : (p d:ℝ) ≠ 0) :
    (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar (1-sigma) p ν d).noise =
      resonantNoiseLoad etaStar bStar sigma p d := by
  rw [actualLSParams]
  rw [SparseSGD.Probability.LeastSquares.params_explicit (p d) hp ν
    (scaledMomentum epsStar gamma d) (scaledLearningRate etaStar (1-sigma) d)]
  rfl

theorem actualLSParams_resonant_additive_eq
    (pStar kappa bStar sigma epsStar gamma etaStar : ℝ)
    (p : ℕ → unitInterval) (ν : MeasureTheory.Measure ℝ) (d : ℕ)
    (hp : (p d:ℝ) ≠ 0) :
    (actualLSParams pStar kappa bStar sigma epsStar gamma etaStar (1-sigma) p ν d).additive =
      resonantAdditiveLoad etaStar bStar sigma (SparseSGD.Probability.LeastSquares.labelVariance ν) d := by
  rw [actualLSParams]
  rw [SparseSGD.Probability.LeastSquares.params_explicit (p d) hp ν
    (scaledMomentum epsStar gamma d) (scaledLearningRate etaStar (1-sigma) d)]
  rfl

theorem resonantNoiseLoad_ratio_identity
    (etaStar bStar sigma : ℝ) (p : ℕ → unitInterval) (d : ℕ)
    (hd : 0 < d) (heta : etaStar ≠ 0) (hb : bStar ≠ 0) :
    resonantNoiseLoad etaStar bStar sigma p d / (etaStar/(2*bStar)) =
      (bStar*(d:ℝ)^sigma/(scaledBatch bStar sigma d:ℝ)) * (((d:ℝ)+2-(p d:ℝ))/(d:ℝ)) := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hB : (scaledBatch bStar sigma d:ℝ) ≠ 0 := by
    exact_mod_cast (integerBatch_pos bStar sigma d).ne'
  unfold resonantNoiseLoad scaledLearningRate
  rw [show -(1-sigma)=sigma-1 by ring,
    show sigma-1=sigma+(-1:ℝ) by ring, Real.rpow_add hdR,
    Real.rpow_neg (le_of_lt hdR), Real.rpow_one]
  field_simp [heta,hb,hB,(Real.rpow_pos_of_pos hdR sigma).ne']
  <;> ring

theorem resonantAdditiveLoad_ratio_identity
    (etaStar bStar sigma variance : ℝ) (d : ℕ)
    (hd : 0 < d) (heta : etaStar ≠ 0) (hb : bStar ≠ 0) (hvar : variance ≠ 0) :
    resonantAdditiveLoad etaStar bStar sigma variance d / (variance*(etaStar/(2*bStar))) =
      bStar*(d:ℝ)^sigma/(scaledBatch bStar sigma d:ℝ) := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hB : (scaledBatch bStar sigma d:ℝ) ≠ 0 := by
    exact_mod_cast (integerBatch_pos bStar sigma d).ne'
  unfold resonantAdditiveLoad scaledLearningRate
  rw [show -(1-sigma)=sigma-1 by ring,
    show sigma-1=sigma+(-1:ℝ) by ring, Real.rpow_add hdR,
    Real.rpow_neg (le_of_lt hdR), Real.rpow_one]
  field_simp [heta,hb,hB,(Real.rpow_pos_of_pos hdR sigma).ne']
  <;> ring

theorem resonantNoiseLoad_error_bound
    (etaStar bStar sigma : ℝ) (p : ℕ → unitInterval) (d : ℕ)
    (hd : 1 ≤ d) (heta : 0 < etaStar) (hb : 0 < bStar)
    (hbatch : 2 ≤ bStar*(d:ℝ)^sigma) :
    |resonantNoiseLoad etaStar bStar sigma p d-etaStar/(2*bStar)| ≤
      (etaStar/(2*bStar))*(4/(d:ℝ)+2/(bStar*(d:ℝ)^sigma)) := by
  have hd0 : 0 < d := by omega
  have hdR : (0:ℝ)<d := by exact_mod_cast hd0
  have hBpos : 0 < (scaledBatch bStar sigma d:ℝ) := by
    exact_mod_cast integerBatch_pos bStar sigma d
  let x := bStar*(d:ℝ)^sigma
  let A := x/(scaledBatch bStar sigma d:ℝ)
  let Q := ((d:ℝ)+2-(p d:ℝ))/(d:ℝ)
  have hAerr : |A-1| ≤ 2/x := by
    dsimp [A,x]
    exact integerBatch_inverse_relative_error bStar sigma d hbatch
  have hAone : 1 ≤ A := by
    obtain ⟨hlo,_⟩ := integerBatch_floor_error bStar sigma d (by linarith)
    have hgap : 0 ≤ x-(scaledBatch bStar sigma d:ℝ) := by simpa [x,scaledBatch] using hlo
    have hAeq : A-1 = (x-(scaledBatch bStar sigma d:ℝ))/(scaledBatch bStar sigma d:ℝ) := by dsimp [A]; field_simp
    rw [← sub_nonneg, hAeq]
    exact div_nonneg hgap hBpos.le
  have hp0 : 0 ≤ (p d:ℝ) := (p d).property.1
  have hp1 : (p d:ℝ) ≤ 1 := (p d).property.2
  have hQlo : 1 ≤ Q := by dsimp [Q]; rw [le_div_iff₀ hdR]; simp; linarith
  have hQhi : Q ≤ 1+2/(d:ℝ) := by
    dsimp [Q]
    field_simp [ne_of_gt hdR]
    nlinarith [hp0]
  have hAhi : A ≤ 1+2/x := by
    have := (abs_le.mp hAerr).2
    dsimp [A,x] at *
    linarith
  have hid : resonantNoiseLoad etaStar bStar sigma p d/(etaStar/(2*bStar)) = A*Q := by
    dsimp [A,Q,x]
    rw [resonantNoiseLoad_ratio_identity etaStar bStar sigma p d hd0 heta.ne' hb.ne']
  have hratio : 0 ≤ resonantNoiseLoad etaStar bStar sigma p d/(etaStar/(2*bStar))-1 := by rw [hid]; nlinarith
  have hratiohi : resonantNoiseLoad etaStar bStar sigma p d/(etaStar/(2*bStar))-1 ≤ 4/(d:ℝ)+2/x := by
    rw [hid]
    have hcross : 4/(x*(d:ℝ)) ≤ 2/(d:ℝ) := by
      rw [div_le_div_iff₀ (mul_pos (by dsimp [x]; positivity) hdR) hdR]
      have hx : 2 ≤ x := by dsimp [x]; exact hbatch
      nlinarith
    have hAstep : A*Q-1 = (A-1)+A*(Q-1) := by ring
    rw [hAstep]
    have hQerr : Q-1 ≤ 2/(d:ℝ) := by linarith
    calc
      (A-1)+A*(Q-1) ≤ 2/x + (1+2/x)*(2/(d:ℝ)) := by
        apply add_le_add
        · exact (abs_le.mp hAerr).2
        · exact mul_le_mul hAhi hQerr (by positivity) (by linarith [hQlo])
      _ = 2/x + 2/(d:ℝ) + 4/(x*(d:ℝ)) := by field_simp; ring
      _ ≤ 2/x+4/(d:ℝ) := by
        calc
          _ = 4/(x*(d:ℝ))+2/x+2/(d:ℝ) := by ring
          _ ≤ 2/(d:ℝ)+2/x+2/(d:ℝ) := by
            have H := add_le_add_right hcross (2/x+2/(d:ℝ))
            simpa [add_assoc, add_comm, add_left_comm] using H
          _ = 2/x+4/(d:ℝ) := by ring

      _ = 4/(d:ℝ)+2/x := by ring
  have hAbs : |resonantNoiseLoad etaStar bStar sigma p d/(etaStar/(2*bStar))-1| ≤
      4/(d:ℝ)+2/x := by rw [abs_of_nonneg hratio]; exact hratiohi
  have hc : 0 < etaStar/(2*bStar) := by positivity
  rw [show resonantNoiseLoad etaStar bStar sigma p d-etaStar/(2*bStar) =
    (etaStar/(2*bStar))*(resonantNoiseLoad etaStar bStar sigma p d/(etaStar/(2*bStar))-1) by field_simp]
  rw [abs_mul, abs_of_pos hc]
  simpa [x] using mul_le_mul_of_nonneg_left hAbs hc.le

theorem resonantAdditiveLoad_error_bound
    (etaStar bStar sigma variance : ℝ) (d : ℕ)
    (hd : 1 ≤ d) (heta : 0 < etaStar) (hb : 0 < bStar)
    (hvar : 0 ≤ variance) (hbatch : 2 ≤ bStar*(d:ℝ)^sigma) :
    |resonantAdditiveLoad etaStar bStar sigma variance d-variance*(etaStar/(2*bStar))| ≤
      (variance*(etaStar/(2*bStar)))*(2/(bStar*(d:ℝ)^sigma)) := by
  have hd0 : 0 < d := by omega
  have hBpos : 0 < (scaledBatch bStar sigma d:ℝ) := by exact_mod_cast integerBatch_pos bStar sigma d
  let x := bStar*(d:ℝ)^sigma
  have hAerr : |x/(scaledBatch bStar sigma d:ℝ)-1| ≤ 2/x := by
    dsimp [x]
    exact integerBatch_inverse_relative_error bStar sigma d hbatch
  have hid : resonantAdditiveLoad etaStar bStar sigma variance d =
      variance*(etaStar/(2*bStar))*(x/(scaledBatch bStar sigma d:ℝ)) := by
    unfold resonantAdditiveLoad scaledLearningRate
    rw [show -(1-sigma)=sigma-1 by ring,
      show sigma-1=sigma+(-1:ℝ) by ring, Real.rpow_add (by positivity : (0:ℝ)<d),
      Real.rpow_neg (by positivity : (0:ℝ)≤d), Real.rpow_one]
    field_simp [ne_of_gt (mul_pos (by norm_num : (0:ℝ)<2) hBpos), ne_of_gt hb,
      (Real.rpow_pos_of_pos (by positivity : (0:ℝ)<d) sigma).ne']
    <;> ring
  have hAlo : 1 ≤ x/(scaledBatch bStar sigma d:ℝ) := by
    obtain ⟨hlo,_⟩ := integerBatch_floor_error bStar sigma d (by linarith)
    have hgap : 0 ≤ x-(scaledBatch bStar sigma d:ℝ) := by simpa [x,scaledBatch] using hlo
    have hB : (scaledBatch bStar sigma d:ℝ) > 0 := hBpos
    rw [le_div_iff₀ hB]
    dsimp [x]
    linarith [hgap]
  have hdiff : |x/(scaledBatch bStar sigma d:ℝ)-1| = x/(scaledBatch bStar sigma d:ℝ)-1 :=
    abs_of_nonneg (sub_nonneg.mpr hAlo)
  rw [hid, show variance*(etaStar/(2*bStar))*(x/(scaledBatch bStar sigma d:ℝ))-
      variance*(etaStar/(2*bStar)) = variance*(etaStar/(2*bStar))*(x/(scaledBatch bStar sigma d:ℝ)-1) by ring,
    abs_mul, abs_of_nonneg (mul_nonneg hvar (by positivity)), hdiff]
  have hAerr' : x/(scaledBatch bStar sigma d:ℝ)-1 ≤ 2/x := (abs_le.mp hAerr).2
  calc
    variance*(etaStar/(2*bStar))*(x/(scaledBatch bStar sigma d:ℝ)-1) ≤
      variance*(etaStar/(2*bStar))*(2/x) := mul_le_mul_of_nonneg_left hAerr' (mul_nonneg hvar (by positivity))
    _ = _ := by dsimp [x]

end
end SparseSGD.Scaling
