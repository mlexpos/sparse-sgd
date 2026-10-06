import SparseSGD.Logistic.FixedPoint
import SparseSGD.Logistic.TameCoefficients

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1000000

private theorem relative_error_bound (x scale eps C : ℝ) (hs : 0 < scale)
    (h : |x-scale| ≤ C*scale*eps) : |x/scale-1| ≤ C*eps := by
  rw [div_sub_one hs.ne', abs_div, abs_of_pos hs]
  apply (div_le_iff₀ hs).mpr
  nlinarith

private theorem linear_balance_error (a b x y E F c : ℝ)
    (hc : 0 < c) (ha : c ≤ a) (hy : 0 ≤ y)
    (hA : |a-1| ≤ E) (hB : |b-1| ≤ F) (hbal : a*x=b*y) :
    c*|x-y| ≤ (E+F)*y := by
  have hprod : a*(x-y) = (b-a)*y := by nlinarith only [hbal]
  have hab : |b-a| ≤ E+F := by
    calc
      _ = |(b-1)-(a-1)| := by congr 1; ring
      _ ≤ |b-1|+|a-1| := abs_sub _ _
      _ ≤ _ := by linarith
  have hh := congrArg abs hprod
  rw [abs_mul,abs_mul,abs_of_nonneg (hc.le.trans ha),abs_of_nonneg hy] at hh
  exact (mul_le_mul_of_nonneg_right ha (abs_nonneg _)).trans
    (hh.le.trans (mul_le_mul_of_nonneg_right hab hy))

/-- Quantitative signal fixed-point asymptotics for the actual Gaussian
coefficients. The small absolute threshold makes the implicit denominator safe. -/
theorem tame_signal_fixedPoint {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hp : 0 < (p : ℝ)) (ht : tameError p mu theta ≤ 1/12)
    (hbalance : coefA p mu theta*signalCoord mu theta+coefB p mu theta*r mu=0) :
    |gaussianAlpha mu theta*signalCoord mu theta-r mu| ≤ 16*r mu*tameError p mu theta := by
  let e := tameError p mu theta
  let a := coefA p mu theta/((p : ℝ)*gaussianAlpha mu theta)
  let b := -coefB p mu theta/(p : ℝ)
  have halpha := gaussianAlpha_pos mu theta
  have hscale : 0 < (p : ℝ)*gaussianAlpha mu theta := mul_pos hp halpha
  have h := tame_coefficients p mu theta hp (by linarith : tameError p mu theta ≤ 1/2)
  have hA : |a-1| ≤ 6*e := relative_error_bound _ _ _ _ hscale (by simpa only [e, mul_assoc] using h.1)
  have hB : |b-1| ≤ 2*e := by
    apply relative_error_bound _ _ _ _ hp
    simpa only [show -coefB p mu theta-(p : ℝ) = -(coefB p mu theta+(p : ℝ)) by ring,abs_neg] using h.2.1
  have ha : (1/2 : ℝ) ≤ a := by have := (abs_le.mp hA).1; dsimp [e] at *; linarith
  have hb : a*(gaussianAlpha mu theta*signalCoord mu theta)=b*r mu := by
    dsimp [a,b]
    field_simp
    nlinarith [hbalance]
  have hh := linear_balance_error a b (gaussianAlpha mu theta*signalCoord mu theta)
    (r mu) (6*e) (2*e) (1/2) (by norm_num) ha (norm_nonneg _) hA hB hb
  dsimp [e] at hh
  nlinarith

/-- The bulk fixed-point expansion retains the total-feedback error, including a
possibly signed noise coefficient. -/
theorem tame_bulk_fixedPoint {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (Phi R u : ℝ) (hp : 0 < (p : ℝ)) (ht : tameError p mu theta ≤ 1/12)
    (hPhi : 0 ≤ Phi) (hu : |u| ≤ 1/2)
    (hbalance : coefA p mu theta*(1-u)*R = Phi*coefD0 p mu theta) :
    |gaussianAlpha mu theta*R-Phi| ≤ 48*Phi*(tameError p mu theta+|u|) := by
  let e := tameError p mu theta
  let a := coefA p mu theta/((p : ℝ)*gaussianAlpha mu theta)
  let b := coefD0 p mu theta/(p : ℝ)
  have halpha := gaussianAlpha_pos mu theta
  have hscale : 0 < (p : ℝ)*gaussianAlpha mu theta := mul_pos hp halpha
  have h := tame_coefficients p mu theta hp (by linarith : tameError p mu theta ≤ 1/2)
  have hA : |a-1| ≤ 6*e := relative_error_bound _ _ _ _ hscale (by simpa only [e, mul_assoc] using h.1)
  have hB : |b-1| ≤ 6*e := relative_error_bound _ _ _ _ hp h.2.2.1
  have ha : (1/2 : ℝ) ≤ a ∧ a ≤ 3/2 := by
    have := abs_le.mp hA
    dsimp [e] at *
    constructor <;> linarith
  have hu' := abs_le.mp hu
  have ha0 : 0 ≤ a := by linarith [ha.1]
  have hden : (1/4 : ℝ) ≤ a*(1-u) := by nlinarith [mul_le_mul ha.1 (show (1/2:ℝ)≤1-u by linarith) (by norm_num : (0:ℝ)≤1/2) ha0]
  have hdenerr : |a*(1-u)-1| ≤ 6*e+(3/2)*|u| := by
    rw [show a*(1-u)-1=(a-1)-a*u by ring]
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg ha0]
    nlinarith [mul_le_mul_of_nonneg_right ha.2 (abs_nonneg u)]
  have hb : (a*(1-u))*(gaussianAlpha mu theta*R)=b*Phi := by
    dsimp [a,b]
    field_simp
    nlinarith [hbalance]
  have hh := linear_balance_error (a*(1-u)) b (gaussianAlpha mu theta*R) Phi
    (6*e+(3/2)*|u|) (6*e) (1/4) (by norm_num) hden hPhi hdenerr hB hb
  dsimp [e] at hh
  nlinarith [mul_nonneg hPhi (abs_nonneg u)]

/-- Signal estimate starting from equality of the actual transition expectations. -/
theorem actual_tame_fixedPoint_signal {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d)
    (hr : 0 < r mu) (heta : eta ≠ 0) (hbeta : beta ≠ 1)
    (hp : 0 < (p : ℝ)) (ht : tameError p mu s.1 ≤ 1/12)
    (hsignal : (∫ a : Batch d B, signalCoord mu (update eta beta p mu s a).1
      ∂batchLaw d B p) = signalCoord mu s.1)
    (hmomentum : (∫ a : Batch d B, signalCoord mu (update eta beta p mu s a).2
      ∂batchLaw d B p) = signalCoord mu s.2) :
    |gaussianAlpha mu s.1*signalCoord mu s.1-r mu| ≤ 16*r mu*tameError p mu s.1 :=
  tame_signal_fixedPoint p mu s.1 hp ht
    (actual_drift_fixedPoint_signal H hB eta beta p mu s hr heta hbeta hsignal hmomentum).2

/-- Source ambient temperature before division by curvature. -/
def logisticPhi (d B : ℕ) (eta : ℝ) : ℝ := eta*((d : ℝ)-1)/(2*(B : ℝ))

theorem logisticPhi_nonneg (d B : ℕ) (eta : ℝ) (hd : 1 ≤ d) (heta : 0 ≤ eta) :
    0 ≤ logisticPhi d B eta := by
  unfold logisticPhi
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  positivity

/-- The moment fixed point implies the exact coefficient balance used in the
quantitative bulk expansion. -/
theorem logistic_fixedPoint_coefficient_balance {d B : ℕ}
    (eta beta : ℝ) (p : unitInterval) (mu theta : Vec d) (s : SparseSGD.Moments)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (heta : eta ≠ 0)
    (hbeta : beta ≠ 1) (hb : 1+beta ≠ 0)
    (hfixed : (driftParams (B := B) eta beta p mu theta).step s = s) :
    coefA p mu theta*(1-(driftParams (B := B) eta beta p mu theta).totalLoad)*s.R =
      logisticPhi d B eta*coefD0 p mu theta := by
  have hA := (coefA_pos p mu theta hp hp1).ne'
  have heps : 1-beta ≠ 0 := sub_ne_zero.mpr hbeta.symm
  have hw : (driftParams (B := B) eta beta p mu theta).w ≠ 0 :=
    mul_ne_zero (mul_ne_zero heta heps) hA
  have h := moment_fixedPoint_balance _ s hw heps hb hfixed
  have hh : (1-(driftParams (B := B) eta beta p mu theta).totalLoad)*s.R =
      (driftParams (B := B) eta beta p mu theta).additive := by
    unfold SparseSGD.Params.totalLoad
    linarith
  rw [mul_assoc,hh,(driftParams_loads (B := B) eta beta p mu theta).2.1]
  unfold logisticPhi
  by_cases hB : (B : ℝ)=0
  · simp [hB]
  · field_simp

theorem logistic_tame_fixedPoint_bulk {d B : ℕ}
    (eta beta : ℝ) (p : unitInterval) (mu theta : Vec d) (s : SparseSGD.Moments)
    (hd : 1 ≤ d) (hp : 0 < (p : ℝ)) (heta : 0 < eta)
    (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (ht : tameError p mu theta ≤ 1/12)
    (hu : |(driftParams (B := B) eta beta p mu theta).totalLoad| ≤ 1/2)
    (hfixed : (driftParams (B := B) eta beta p mu theta).step s = s) :
    |gaussianAlpha mu theta*s.R-logisticPhi d B eta| ≤
      48*logisticPhi d B eta*(tameError p mu theta+
        (driftParams (B := B) eta beta p mu theta).w+
        |(driftParams (B := B) eta beta p mu theta).noise|) := by
  have hp1 : (p : ℝ)<1 := by linarith [tameError_ge_probability p mu theta]
  have h := tame_bulk_fixedPoint p mu theta (logisticPhi d B eta) s.R
    (driftParams (B := B) eta beta p mu theta).totalLoad hp ht
    (logisticPhi_nonneg d B eta hd heta.le) hu
    (logistic_fixedPoint_coefficient_balance eta beta p mu theta s hp hp1 heta.ne'
      (ne_of_lt hb1) (by linarith) hfixed)
  have hw : 0 ≤ (driftParams (B := B) eta beta p mu theta).w := by
    change 0 ≤ eta*(1-beta)*coefA p mu theta
    exact mul_nonneg (mul_nonneg heta.le (by linarith)) (coefA_pos p mu theta hp hp1).le
  have hc : 0 ≤ (driftParams (B := B) eta beta p mu theta).curvature := by
    unfold SparseSGD.Params.curvature
    exact div_nonneg hw (by change 0≤2*(1+beta); positivity)
  have hcw : (driftParams (B := B) eta beta p mu theta).curvature ≤
      (driftParams (B := B) eta beta p mu theta).w := by
    unfold SparseSGD.Params.curvature
    apply (div_le_iff₀ (show 0 < 2*(1+(driftParams (B := B) eta beta p mu theta).beta) by change 0<2*(1+beta); positivity)).mpr
    change (driftParams (B := B) eta beta p mu theta).w ≤
      (driftParams (B := B) eta beta p mu theta).w*(2*(1+beta))
    nlinarith [mul_nonneg hw hb0]
  have hu' : |(driftParams (B := B) eta beta p mu theta).totalLoad| ≤
      |(driftParams (B := B) eta beta p mu theta).noise|+
      (driftParams (B := B) eta beta p mu theta).w := by
    unfold SparseSGD.Params.totalLoad
    calc
      _ ≤ |(driftParams (B := B) eta beta p mu theta).noise|+
          |(driftParams (B := B) eta beta p mu theta).curvature| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg hc]; linarith
  apply h.trans
  apply mul_le_mul_of_nonneg_left (by linarith only [hu'])
  exact mul_nonneg (by norm_num) (logisticPhi_nonneg d B eta hd heta.le)

/-- Bulk asymptotics for a fixed point of the actual transition expectation. -/
theorem actual_tame_fixedPoint_bulk {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d)
    (hd : 1 ≤ d) (hr : 0 < r mu) (heta : 0 < eta)
    (hb0 : 0 ≤ beta) (hb1 : beta < 1) (hp : 0 < (p : ℝ))
    (ht : tameError p mu s.1 ≤ 1/12)
    (hu : |(driftParams (B := B) eta beta p mu s.1).totalLoad| ≤ 1/2)
    (hbulk : integratedGram (batchLaw d B p)
      (fun a => bulkPart mu (update eta beta p mu s a).1)
      (fun a => eta • bulkPart mu (update eta beta p mu s a).2) =
        SparseSGD.gramMoments (bulkPart mu s.1) (eta • bulkPart mu s.2)) :
    |gaussianAlpha mu s.1*‖bulkPart mu s.1‖^2-logisticPhi d B eta| ≤
      48*logisticPhi d B eta*(tameError p mu s.1+
        (driftParams (B := B) eta beta p mu s.1).w+
        |(driftParams (B := B) eta beta p mu s.1).noise|) := by
  have hp1 : (p : ℝ)<1 := by linarith [tameError_ge_probability p mu s.1]
  rw [update_bulk_integratedGram H hB eta beta p mu s hr
    (coefA_pos p mu s.1 hp hp1).ne'] at hbulk
  exact logistic_tame_fixedPoint_bulk eta beta p mu s.1 _ hd hp heta hb0 hb1 ht hu hbulk

/-- The raw momentum covariance vanishes in a rare-class limit with bounded
curvature-weighted bulk energy. `w → 0` alone does not give this conclusion. -/
theorem tame_fixedPoint_covariance_bound {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (beta C R P : ℝ) (hp : 0 < (p : ℝ)) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (ht : tameError p mu theta ≤ 1/12) (hR : 0 ≤ R)
    (henergy : gaussianAlpha mu theta*R ≤ P)
    (hcov : C = -(1-beta)*coefA p mu theta*R/(1+beta)) :
    |C| ≤ (3/2)*(p : ℝ)*P := by
  have hp1 : (p : ℝ)<1 := by linarith [tameError_ge_probability p mu theta]
  have hA0 := (coefA_pos p mu theta hp hp1).le
  have halpha := (gaussianAlpha_pos mu theta).le
  have hA := (abs_le.mp (tame_coefficients p mu theta hp (by linarith : tameError p mu theta≤1/2)).1).2
  have ha : coefA p mu theta ≤ (3/2)*(p : ℝ)*gaussianAlpha mu theta := by
    have hh := mul_le_mul_of_nonneg_left ht (show 0≤6*(p : ℝ)*gaussianAlpha mu theta by positivity)
    nlinarith
  have hCP : |C| ≤ coefA p mu theta*R := by
    rw [hcov,abs_div,abs_mul,abs_mul,abs_neg,abs_of_nonneg (sub_nonneg.mpr hb1),
      abs_of_nonneg hA0,abs_of_nonneg hR,abs_of_nonneg (show 0≤1+beta by linarith)]
    apply (div_le_iff₀ (show 0<1+beta by linarith)).mpr
    nlinarith [mul_nonneg (mul_nonneg hA0 hR) hb0]
  apply hCP.trans
  have hh := mul_le_mul_of_nonneg_right ha hR
  have he := mul_le_mul_of_nonneg_left henergy (show 0≤(3/2)*(p : ℝ) by positivity)
  nlinarith

/-- An explicit rare-class specialization of the raw covariance limit. -/
theorem tame_fixedPoint_covariance_tendsto {dim : ℕ → ℕ}
    (p : ℕ → unitInterval) (mu theta : (n : ℕ) → Vec (dim n))
    (beta C R : ℕ → ℝ) (P : ℝ)
    (hp : ∀ n, 0 < (p n : ℝ))
    (hb : ∀ n, 0 ≤ beta n ∧ beta n ≤ 1)
    (ht : ∀ n, tameError (p n) (mu n) (theta n) ≤ 1/12)
    (hR : ∀ n, 0 ≤ R n)
    (henergy : ∀ n, gaussianAlpha (mu n) (theta n)*R n ≤ P)
    (hcov : ∀ n, C n = -(1-beta n)*coefA (p n) (mu n) (theta n)*R n/(1+beta n))
    (hrare : Filter.Tendsto (fun n => (p n : ℝ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto C Filter.atTop (nhds 0) := by
  apply squeeze_zero_norm
  · intro n
    simpa only [Real.norm_eq_abs] using tame_fixedPoint_covariance_bound (p n) (mu n) (theta n)
      (beta n) (C n) (R n) P (hp n) (hb n).1 (hb n).2 (ht n) (hR n) (henergy n) (hcov n)
  · simpa using (hrare.const_mul (3/2)).mul_const P

end
end SparseSGD.Logistic
