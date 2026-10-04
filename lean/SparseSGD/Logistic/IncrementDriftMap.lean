import SparseSGD.Logistic.IncrementFullConditional
import SparseSGD.Logistic.ScalarCoefficients
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

/-- Exact matched-coordinate step for scalar population coefficients and
centered bulk batch variance. Coordinate order is `(theta,Y,R,C,V)`. -/
def matchedCoefficientStep (r eta beta A b z : ℝ) (y : Fin 5 → ℝ) : Fin 5 → ℝ :=
  let eps := 1-beta
  let a := 1-eta*eps*A
  let u := beta*y 1+eta*(A*y 0+b*r)
  ![y 0-eps*u, u,
    a^2*y 2+beta^2*eps^2*y 4-2*beta*eps*a*y 3+eta^2*eps^2*z,
    a*(beta*y 3+eta*A*y 2)-beta*eps*(beta*y 4+eta*A*y 3)-eta^2*eps*z,
    beta^2*y 4+eta^2*A^2*y 2+2*beta*eta*A*y 3+eta^2*z]

/-- The actual population drift, defined on the entire coordinate space.
On physical states `q = theta_parallel² + R` is nonnegative. -/
def matchedDriftMap {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (y : Fin 5 → ℝ) : Fin 5 → ℝ :=
  let q := (y 0)^2+y 2
  let A := scalarCoefA p (r mu) (y 0) q
  let b := scalarCoefB p (r mu) (y 0) q
  let D0 := scalarCoefD0 p (r mu) (y 0) q
  let Dt := scalarCoefDtheta p (r mu) (y 0) q
  let z := (((d : ℝ)-1)*D0+y 2*(Dt-A^2))/(B : ℝ)
  matchedCoefficientStep (r mu) eta beta A b z y

theorem matchedSummary_variance {d : ℕ} (eta beta : ℝ) (mu : Vec d) (s : State d)
    (hr : 0 < r mu) :
    (matchedSummary eta beta mu s 0)^2+matchedSummary eta beta mu s 2 = ‖s.1‖^2 := by
  have h := bulkPart_norm_sq mu s.1 hr
  simp only [matchedSummary, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
  dsimp [signalCoord]
  rw [div_pow]
  linarith

private theorem matchedCoefficientStep_bulk (d B : ℕ) (r eta beta A b D0 Dt : ℝ)
    (y : Fin 5 → ℝ) (hA : A ≠ 0) (hB : (B : ℝ) ≠ 0) (heps : 1-beta ≠ 0) :
    let P := SparseSGD.oracleParams beta eta A ((Dt-A^2)/(B : ℝ)) (((d : ℝ)-1)*D0/(B : ℝ))
    let sn := P.step ⟨y 2,(1-beta)^2*y 4,(1-beta)*y 3⟩
    let yn := matchedCoefficientStep r eta beta A b
      ((((d : ℝ)-1)*D0+y 2*(Dt-A^2))/(B : ℝ)) y
    yn 2 = sn.R ∧ yn 3 = sn.C/(1-beta) ∧ yn 4 = sn.V/(1-beta)^2 := by
  dsimp [matchedCoefficientStep,SparseSGD.oracleParams,SparseSGD.Params.step,SparseSGD.Params.eps]
  constructor
  · field_simp [hA,hB,heps] <;> ring
  constructor <;> field_simp [hA,hB,heps] <;> ring

/-- Scalar-coordinate population drift agrees with the actual fresh-batch
conditional mean. All sample moment identities are discharged. -/
theorem matchedDriftMap_summary {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d)
    (hr : 0 < r mu) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (heps : 1-beta ≠ 0) :
    matchedDriftMap (B := B) eta beta p mu (matchedSummary eta beta mu s) =
      matchedDrift (B := B) eta beta p mu s := by
  have hA : coefA p mu s.1 ≠ 0 := ne_of_gt (coefA_pos p mu s.1 hp0 hp1)
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hs := one_step_drift H hB eta beta p mu s hr hp0 hp1
  have hm := update_bulk_moment_drift H hB eta beta p mu s hr hp0 hp1
  have hm' : (⟨∫ a : Batch d B, ‖bulkPart mu (update eta beta p mu s a).1‖^2 ∂batchLaw d B p,
      eta^2*(∫ a : Batch d B, ‖bulkPart mu (update eta beta p mu s a).2‖^2 ∂batchLaw d B p),
      eta*(∫ a : Batch d B, inner ℝ (bulkPart mu (update eta beta p mu s a).1)
        (bulkPart mu (update eta beta p mu s a).2) ∂batchLaw d B p)⟩ : SparseSGD.Moments) =
      (driftParams (B := B) eta beta p mu s.1).step
        ⟨matchedSummary eta beta mu s 2,(1-beta)^2*matchedSummary eta beta mu s 4,
          (1-beta)*matchedSummary eta beta mu s 3⟩ := by
    convert hm using 1 <;> simp [matchedSummary] <;> field_simp [heps] <;> ring
  dsimp only [driftParams] at hm'
  have hmap := matchedCoefficientStep_bulk d B (r mu) eta beta (coefA p mu s.1)
    (coefB p mu s.1) (coefD0 p mu s.1) (coefDtheta p mu s.1)
    (matchedSummary eta beta mu s) hA hb heps
  have he : matchedDriftMap (B := B) eta beta p mu (matchedSummary eta beta mu s) =
      matchedCoefficientStep (r mu) eta beta (coefA p mu s.1) (coefB p mu s.1)
        ((((d : ℝ)-1)*coefD0 p mu s.1+matchedSummary eta beta mu s 2*(coefDtheta p mu s.1-(coefA p mu s.1)^2))/(B : ℝ))
        (matchedSummary eta beta mu s) := by
    unfold matchedDriftMap
    rw [matchedSummary_variance eta beta mu s hr]
    dsimp only
    have hca : scalarCoefA p (r mu) (matchedSummary eta beta mu s 0) (‖s.1‖^2) = coefA p mu s.1 := (coefA_eq_scalar p mu s.1 hr).symm
    have hcb : scalarCoefB p (r mu) (matchedSummary eta beta mu s 0) (‖s.1‖^2) = coefB p mu s.1 := (coefB_eq_scalar p mu s.1 hr).symm
    have hcd : scalarCoefD0 p (r mu) (matchedSummary eta beta mu s 0) (‖s.1‖^2) = coefD0 p mu s.1 := (coefD0_eq_scalar p mu s.1 hr).symm
    have hct : scalarCoefDtheta p (r mu) (matchedSummary eta beta mu s 0) (‖s.1‖^2) = coefDtheta p mu s.1 := (coefDtheta_eq_scalar p mu s.1 hr).symm
    rw [hca,hcb,hcd,hct]
  rw [he]
  ext i
  fin_cases i
  · change _ = ∫ a : Batch d B, signalCoord mu (update eta beta p mu s a).1 ∂batchLaw d B p
    rw [hs.2.1]
    simp [matchedCoefficientStep,matchedSummary]
    field_simp [heps] <;> ring
  · change _ = ∫ a : Batch d B, eta/(1-beta)*signalCoord mu (update eta beta p mu s a).2 ∂batchLaw d B p
    rw [integral_const_mul,hs.1]
    simp [matchedCoefficientStep,matchedSummary]
    field_simp [heps] <;> ring
  · exact hmap.1.trans (congrArg SparseSGD.Moments.R hm').symm
  · change _ = ∫ a : Batch d B, eta/(1-beta)*inner ℝ (bulkPart mu (update eta beta p mu s a).1)
      (bulkPart mu (update eta beta p mu s a).2) ∂batchLaw d B p
    apply hmap.2.1.trans
    rw [← congrArg SparseSGD.Moments.C hm',integral_const_mul]
    simp only [SparseSGD.Moments.C]
    field_simp [heps] <;> ring
  · change _ = ∫ a : Batch d B, (eta/(1-beta))^2*‖bulkPart mu (update eta beta p mu s a).2‖^2 ∂batchLaw d B p
    apply hmap.2.2.trans
    rw [← congrArg SparseSGD.Moments.V hm',integral_const_mul]
    simp only [SparseSGD.Moments.V]
    field_simp [heps] <;> ring
private theorem measurable_gaussianAverage_comp (f : ℝ → ℝ) (hf : Continuous f)
    (c q : (Fin 5 → ℝ) → ℝ) (hc : Measurable c) (hq : Measurable q) :
    Measurable (fun y => SparseSGD.Probability.gaussianAverage f (c y) (q y)) := by
  have hF : Measurable (fun z : (Fin 5 → ℝ) × ℝ => f (Real.sqrt (q z.1)*z.2+c z.1)) :=
    hf.measurable.comp (((hq.comp measurable_fst).sqrt.mul measurable_snd).add (hc.comp measurable_fst))
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_matchedDriftMap {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) :
    Measurable (matchedDriftMap (B := B) eta beta p mu) := by
  let q := fun y : Fin 5 → ℝ => (y 0)^2+y 2
  have hq : Measurable q := ((measurable_pi_apply 0).pow_const 2).add (measurable_pi_apply 2)
  have ht : Measurable (fun y : Fin 5 → ℝ => r mu*y 0+scalarBias p (r mu)) := by fun_prop
  have hA : Measurable (fun y : Fin 5 → ℝ => scalarCoefA p (r mu) (y 0) (q y)) :=
    ((measurable_gaussianAverage_comp sigmaPrime sigmaPrime_continuous _ q measurable_const hq).const_mul _).add
      ((measurable_gaussianAverage_comp sigmaPrime sigmaPrime_continuous _ q ht hq).const_mul _)
  have hb : Measurable (fun y : Fin 5 → ℝ => scalarCoefB p (r mu) (y 0) (q y)) :=
    ((measurable_gaussianAverage_comp sigma sigma_continuous _ q ht hq).sub_const 1).const_mul _
  have hD0 : Measurable (fun y : Fin 5 → ℝ => scalarCoefD0 p (r mu) (y 0) (q y)) :=
    ((measurable_gaussianAverage_comp (fun x => sigma x^2) (by fun_prop) _ q measurable_const hq).const_mul _).add
      ((measurable_gaussianAverage_comp (fun x => (1-sigma x)^2) (by fun_prop) _ q ht hq).const_mul _)
  have hDt : Measurable (fun y : Fin 5 → ℝ => scalarCoefDtheta p (r mu) (y 0) (q y)) :=
    ((measurable_gaussianAverage_comp sigmaSqSecond sigmaSqSecond_continuous _ q measurable_const hq).const_mul _).add
      ((measurable_gaussianAverage_comp oneMinusSigmaSqSecond oneMinusSigmaSqSecond_continuous _ q ht hq).const_mul _)
  have hz : Measurable (fun y : Fin 5 → ℝ =>
      (((d : ℝ)-1)*scalarCoefD0 p (r mu) (y 0) (q y)+y 2*(scalarCoefDtheta p (r mu) (y 0) (q y)-(scalarCoefA p (r mu) (y 0) (q y))^2))/(B : ℝ)) := by
    exact ((hD0.const_mul _).add ((measurable_pi_apply 2).mul (hDt.sub (hA.pow_const 2)))).div_const _
  have hfast : Measurable (fun y : Fin 5 → ℝ => beta*y 1+eta*(scalarCoefA p (r mu) (y 0) (q y)*y 0+scalarCoefB p (r mu) (y 0) (q y)*r mu)) := by
    exact ((measurable_pi_apply 1).const_mul _).add (((hA.mul (measurable_pi_apply 0)).add (hb.mul_const _)).const_mul _)
  have ha : Measurable (fun y : Fin 5 → ℝ => 1-eta*(1-beta)*scalarCoefA p (r mu) (y 0) (q y)) :=
    measurable_const.sub (hA.const_mul _)
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> simp only [matchedDriftMap,matchedCoefficientStep,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four]
  · exact (measurable_pi_apply 0).sub (hfast.const_mul _)
  · exact hfast
  · convert (((((ha.pow_const 2).mul (measurable_pi_apply 2)).add ((measurable_pi_apply 4).const_mul (beta^2*(1-beta)^2))).sub
      ((ha.mul (measurable_pi_apply 3)).const_mul (2*beta*(1-beta)))).add (hz.const_mul (eta^2*(1-beta)^2))) using 1
    ext y
    dsimp [q]
    ring
  · convert (((ha.mul (((measurable_pi_apply 3).const_mul beta).add ((hA.mul (measurable_pi_apply 2)).const_mul eta))).sub
      ((((measurable_pi_apply 4).const_mul beta).add ((hA.mul (measurable_pi_apply 3)).const_mul eta)).const_mul (beta*(1-beta)))).sub (hz.const_mul (eta^2*(1-beta)))) using 1
    ext y
    dsimp [q]
    ring
  · convert (((((measurable_pi_apply 4).const_mul (beta^2)).add (((hA.pow_const 2).mul (measurable_pi_apply 2)).const_mul (eta^2))).add
      ((hA.mul (measurable_pi_apply 3)).const_mul (2*beta*eta))).add (hz.const_mul (eta^2))) using 1
    ext y
    dsimp [q]
    ring
end
end SparseSGD.Logistic
