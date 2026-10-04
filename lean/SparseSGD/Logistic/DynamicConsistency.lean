import SparseSGD.Logistic.DynamicDrift
import SparseSGD.Logistic.TameCoefficients

namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 1200000

/-- A polynomial increment with separate curvature and noise coefficients.
Coordinates 0--4 are the state; 5--12 are h,delta,kappa,a,b,d0,nu,rho. -/
def dynamicIncrement (r : ℝ) (q : Fin 13 → ℝ) : DynamicState :=
  let Yn := q 1+q 5*(-q 1+q 8*q 0+q 9*r)
  let dV := (-2+q 5)*q 3+2*(1-q 5)*q 8*q 4+q 7*q 10+
    q 5*q 8^2*q 12*q 2+q 11*q 2
  let Vn := q 3+q 5*dV
  ![-q 6*Yn, -q 1+q 8*q 0+q 9*r,
    -2*q 6*((1-q 5)*q 4+q 5*q 8*q 2)+q 6^2*q 5*Vn,
    dV, -q 4+q 8*q 2-q 6*Vn]

def dynamicIncrementData (y : DynamicState) (h delta kappa a b d0 nu rho : ℝ) :
    Fin 13 → ℝ :=
  ![y 0,y 1,y 2,y 3,y 4,h,delta,kappa,a,b,d0,nu,rho]

/-- The exact map is Euler plus the polynomial increment; no asymptotics
or coefficient estimate is used here. -/
theorem dynamicCoefficientStep_eq_increment (r h delta a b noise kappa d0 nu rho : ℝ)
    (y : DynamicState)
    (hn : h*noise=kappa*d0+h*a^2*rho*y 2+nu*y 2) :
    dynamicCoefficientStep r h delta a b noise y = y+h •
      dynamicIncrement r (dynamicIncrementData y h delta kappa a b d0 nu rho) := by
  have hv : (1-h)^2*y 3+2*h*(1-h)*a*y 4+h^2*noise =
      y 3+h*((-2+h)*y 3+2*(1-h)*a*y 4+kappa*d0+h*a^2*rho*y 2+nu*y 2) := by
    have hn2 := congrArg (fun x : ℝ => h*x) hn
    nlinarith only [hn2]
  ext i
  fin_cases i <;> simp [dynamicCoefficientStep, dynamicIncrement, dynamicIncrementData]
  all_goals try rw [hv]
  all_goals nlinarith only [hv]

theorem dynamicIncrement_zero_eq_field (r delta Phi rho : ℝ) (y : DynamicState) :
    dynamicIncrement r (dynamicIncrementData y 0 delta (2*Phi/delta)
      (dynamicAlpha r y) (-1) 1 0 rho) = dynamicField r delta Phi y := by
  ext i
  fin_cases i <;> simp [dynamicIncrement, dynamicIncrementData, dynamicField] <;> ring

theorem contDiff_dynamicIncrement (r : ℝ) : ContDiff ℝ ⊤ (dynamicIncrement r) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [dynamicIncrement] <;> fun_prop

/-- Compact coefficient sets give a genuine uniform Lipschitz constant for
all one-step increments. -/
theorem dynamicIncrement_lipschitz_closedBall (r M : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K (dynamicIncrement r) (Metric.closedBall 0 M) := by
  exact (contDiff_dynamicIncrement r).contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall 0 M) (isCompact_closedBall 0 M)

private theorem dynamicIncrementData_distance (y : DynamicState)
    (h delta kappa a b d0 nu rho alpha : ℝ) :
    ‖dynamicIncrementData y h delta kappa a b d0 nu rho -
      dynamicIncrementData y 0 delta kappa alpha (-1) 1 0 rho‖ ≤
      |h|+|a-alpha|+|b+1|+|d0-1|+|nu| := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i <;> simp [dynamicIncrementData, Real.norm_eq_abs]
  all_goals linarith [abs_nonneg h, abs_nonneg (a-alpha), abs_nonneg (b+1),
    abs_nonneg (d0-1), abs_nonneg nu]

/-- A uniform local consistency estimate, with explicit coefficient errors.
The constants arise from the smooth actual one-step increment. -/
theorem dynamicCoefficientStep_consistency (r M : ℝ) :
    ∃ K : ℝ≥0, ∀ (h delta Phi a b noise d0 nu rho : ℝ) (y : DynamicState),
      h*noise=(2*Phi/delta)*d0+h*a^2*rho*y 2+nu*y 2 →
      ‖dynamicIncrementData y h delta (2*Phi/delta) a b d0 nu rho‖ ≤ M →
      ‖dynamicIncrementData y 0 delta (2*Phi/delta) (dynamicAlpha r y) (-1) 1 0 rho‖ ≤ M →
      ‖dynamicCoefficientStep r h delta a b noise y - (y+h • dynamicField r delta Phi y)‖ ≤
        |h| *(K:ℝ)*(|h|+|a-dynamicAlpha r y|+|b+1|+|d0-1|+|nu|) := by
  obtain ⟨K,hK⟩ := dynamicIncrement_lipschitz_closedBall r M
  refine ⟨K,?_⟩
  intro h delta Phi a b noise d0 nu rho y hn hq hq0
  rw [dynamicCoefficientStep_eq_increment r h delta a b noise (2*Phi/delta) d0 nu rho y hn]
  rw [← dynamicIncrement_zero_eq_field r delta Phi rho y]
  have hbound := hK.norm_sub_le
    (by simpa using hq) (by simpa using hq0)
  have hd := dynamicIncrementData_distance y h delta (2*Phi/delta) a b d0 nu rho (dynamicAlpha r y)
  calc
    _ = |h| * ‖dynamicIncrement r (dynamicIncrementData y h delta (2*Phi/delta) a b d0 nu rho)-
      dynamicIncrement r (dynamicIncrementData y 0 delta (2*Phi/delta) (dynamicAlpha r y) (-1) 1 0 rho)‖ := by
      rw [add_sub_add_left_eq_sub, ← smul_sub]
      simp [norm_smul, Real.norm_eq_abs]
    _ ≤ |h| *((K:ℝ)*‖dynamicIncrementData y h delta (2*Phi/delta) a b d0 nu rho-
      dynamicIncrementData y 0 delta (2*Phi/delta) (dynamicAlpha r y) (-1) 1 0 rho‖) :=
      mul_le_mul_of_nonneg_left hbound (abs_nonneg h)
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd K.coe_nonneg) (abs_nonneg h)

/-- The field's curvature is the actual Gaussian curvature in the normalized coordinates. -/
theorem dynamicAlpha_summary {d : ℕ} (p : unitInterval) (mu : Vec d) (s : State d)
    (hr : 0 < r mu) :
    dynamicAlpha (r mu) (dynamicSummary p mu s) = gaussianAlpha mu s.1 := by
  have hg := bulkPart_norm_sq mu s.1 hr
  simp [dynamicAlpha, dynamicSummary, gaussianAlpha, signalCoord, r] at *
  congr 1
  rw [div_pow]
  linarith

/-- The batch-noise coefficient has the source load normalization. -/
def dynamicNoiseRate (d B : ℕ) (h p : ℝ) : ℝ := h*(d-1:ℝ)/((B:ℝ)*p)

def dynamicSourceLoad (d B : ℕ) (eta : ℝ) : ℝ := eta*(d-1:ℝ)/(2*(B:ℝ))

theorem dynamicNoiseRate_eq_source (d B : ℕ) (eta h p : ℝ)
    (heta : eta ≠ 0) (hh : h ≠ 0) (hp : p ≠ 0) (hB : (B:ℝ) ≠ 0) :
    dynamicNoiseRate d B h p = 2*dynamicSourceLoad d B eta/(eta*p/h) := by
  simp only [dynamicNoiseRate, dynamicSourceLoad]
  field_simp

/-- Zeroth coefficient errors, after the actual LR34 normalization. -/
theorem dynamic_normalized_coefficient_errors {d B : ℕ} (p : unitInterval)
    (mu theta : Vec d) (h : ℝ) (hp : 0 < (p:ℝ)) (hh : 0 ≤ h)
    (hB : 0 < B) (hd : 2 ≤ d) (htame : tameError p mu theta ≤ 1/2) :
    |coefA p mu theta/(p:ℝ)-gaussianAlpha mu theta| ≤
      6*gaussianAlpha mu theta*tameError p mu theta ∧
    |coefB p mu theta/(p:ℝ)+1| ≤ 2*tameError p mu theta ∧
    |coefD0 p mu theta/(p:ℝ)-1| ≤ 6*tameError p mu theta ∧
    |h*coefDtheta p mu theta/((B:ℝ)*(p:ℝ)^2)| ≤
      12*dynamicNoiseRate d B h (p:ℝ)*tameError p mu theta := by
  have hc := tame_coefficients p mu theta hp htame
  have he : 0 ≤ tameError p mu theta := (tameError_ge_probability p mu theta).trans' hp.le
  have hBr : 0 < (B:ℝ) := by exact_mod_cast hB
  have hdR : 1 ≤ (d-1:ℝ) := by
    have hd2 : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hpos : 0 < (B:ℝ)*(p:ℝ)^2 := by positivity
  constructor
  · have hi : coefA p mu theta/(p:ℝ)-gaussianAlpha mu theta =
        (coefA p mu theta-(p:ℝ)*gaussianAlpha mu theta)/(p:ℝ) := by field_simp <;> ring
    rw [hi, abs_div, abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    nlinarith [hc.1]
  constructor
  · have hi : coefB p mu theta/(p:ℝ)+1 = (coefB p mu theta+(p:ℝ))/(p:ℝ) := by field_simp
    rw [hi, abs_div, abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    nlinarith [hc.2.1]
  constructor
  · have hi : coefD0 p mu theta/(p:ℝ)-1 = (coefD0 p mu theta-(p:ℝ))/(p:ℝ) := by field_simp
    rw [hi, abs_div, abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    nlinarith [hc.2.2.1]
  · rw [abs_div, abs_mul, abs_of_nonneg hh, abs_of_pos hpos]
    calc
      _ ≤ h*(12*(p:ℝ)*tameError p mu theta)/((B:ℝ)*(p:ℝ)^2) := by gcongr; exact hc.2.2.2
      _ = 12*(h/((B:ℝ)*(p:ℝ)))*tameError p mu theta := by field_simp <;> ring
      _ ≤ 12*dynamicNoiseRate d B h (p:ℝ)*tameError p mu theta := by
        unfold dynamicNoiseRate
        have hd' : h/((B:ℝ)*(p:ℝ)) ≤ h*(d-1:ℝ)/((B:ℝ)*(p:ℝ)) := by
          gcongr
          nlinarith only [hdR,hh]
        gcongr

/-- A coefficient-driven state need only have the physical parameter geometry;
momentum moments do not enter the logistic coefficients. -/
theorem dynamicAlpha_of_geometry {d : ℕ} (mu theta : Vec d) (y : DynamicState)
    (hq : ‖theta‖^2=y 0^2+y 2) :
    dynamicAlpha (r mu) y = gaussianAlpha mu theta := by
  simp only [dynamicAlpha, gaussianAlpha, r, hq]

/-- The actual batch moment satisfies the polynomial increment's noise identity. -/
theorem dynamicDrift_noise_identity {d B : ℕ} (p : unitInterval)
    (mu theta : Vec d) (y : DynamicState) (h : ℝ) (hp : (p:ℝ) ≠ 0)
    (hB : (B:ℝ) ≠ 0) :
    h*((((d-1:ℝ)*coefD0 p mu theta+y 2*coefDtheta p mu theta)/(B:ℝ)+
      ((B:ℝ)-1)/(B:ℝ)*(coefA p mu theta)^2*y 2)/(p:ℝ)^2) =
    dynamicNoiseRate d B h (p:ℝ)*(coefD0 p mu theta/(p:ℝ))+
      h*(coefA p mu theta/(p:ℝ))^2*(((B:ℝ)-1)/(B:ℝ))*y 2+
      (h*coefDtheta p mu theta/((B:ℝ)*(p:ℝ)^2))*y 2 := by
  unfold dynamicNoiseRate
  field_simp
  <;> ring

/-- A uniform local error for the actual Gaussian logistic drift. The two
closed-ball hypotheses specify the compact coefficient tube, rather than
assuming a consistency conclusion. -/
theorem dynamicDriftMap_consistency (r0 M : ℝ) :
    ∃ K : ℝ≥0, ∀ {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
      (mu theta : Vec d) (y : DynamicState),
      r mu=r0 → 0 < (p:ℝ) → 0 < B → 2 ≤ d → eta ≠ 0 → 0 < 1-beta →
      tameError p mu theta ≤ 1/2 → ‖theta‖^2=y 0^2+y 2 →
      let h := 1-beta
      let delta := eta*(p:ℝ)/h
      let Phi := dynamicSourceLoad d B eta
      let kappa := dynamicNoiseRate d B h (p:ℝ)
      let a := coefA p mu theta/(p:ℝ)
      let b := coefB p mu theta/(p:ℝ)
      let d0 := coefD0 p mu theta/(p:ℝ)
      let nu := h*coefDtheta p mu theta/((B:ℝ)*(p:ℝ)^2)
      let rho := ((B:ℝ)-1)/(B:ℝ)
      ‖dynamicIncrementData y h delta kappa a b d0 nu rho‖ ≤ M →
      ‖dynamicIncrementData y 0 delta kappa (dynamicAlpha r0 y) (-1) 1 0 rho‖ ≤ M →
      ‖dynamicDriftMap (B:=B) eta beta p mu theta y-(y+h • dynamicField r0 delta Phi y)‖ ≤
        h*(K:ℝ)*(h+(6*dynamicAlpha r0 y+8+12*kappa)*tameError p mu theta) := by
  obtain ⟨K,hK⟩ := dynamicCoefficientStep_consistency r0 M
  refine ⟨K,?_⟩
  intro d B eta beta p mu theta y hr hp hB hd heta hh htame hgeom
  dsimp only
  intro hq hq0
  have hBr : (B:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hload := dynamicNoiseRate_eq_source d B eta (1-beta) (p:ℝ) heta hh.ne' hp.ne' hBr
  have ha : dynamicAlpha r0 y=gaussianAlpha mu theta := by
    rw [← hr]
    exact dynamicAlpha_of_geometry mu theta y hgeom
  have hc := dynamic_normalized_coefficient_errors (B:=B) p mu theta (1-beta)
    hp hh.le hB hd htame
  rw [← ha] at hc
  have hn := dynamicDrift_noise_identity (B:=B) p mu theta y (1-beta) hp.ne' hBr
  rw [hload] at hn hq hq0 hc
  have hb := hK (1-beta) (eta*(p:ℝ)/(1-beta)) (dynamicSourceLoad d B eta)
    (coefA p mu theta/(p:ℝ)) (coefB p mu theta/(p:ℝ))
    ((((d-1:ℝ)*coefD0 p mu theta+y 2*coefDtheta p mu theta)/(B:ℝ)+
      ((B:ℝ)-1)/(B:ℝ)*(coefA p mu theta)^2*y 2)/(p:ℝ)^2)
    (coefD0 p mu theta/(p:ℝ)) ((1-beta)*coefDtheta p mu theta/((B:ℝ)*(p:ℝ)^2))
    (((B:ℝ)-1)/(B:ℝ)) y hn hq hq0
  rw [abs_of_pos hh] at hb
  unfold dynamicDriftMap
  rw [hr]
  apply hb.trans
  rw [← hload] at hc
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hh.le K.coe_nonneg)
  nlinarith only [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

end
end SparseSGD.Logistic
