import SparseSGD.Logistic.Drift
import SparseSGD.Discrete.Equilibrium

/-! Exact fixed-point identities for the logistic drift recursion. -/
namespace SparseSGD.Logistic
noncomputable section

/-- A fixed point of the moment recursion has the manuscript's covariance ratios. -/
theorem moment_fixedPoint_coordinates (P : SparseSGD.Params) (s : SparseSGD.Moments)
    (hb : 1 + P.beta ≠ 0) (hfixed : P.step s = s) :
    s.V = 2 * P.w * s.R / (1 + P.beta) ∧
      s.C = -P.w * s.R / (1 + P.beta) := by
  have hR := congrArg SparseSGD.Moments.R hfixed
  have hV := congrArg SparseSGD.Moments.V hfixed
  have hC := congrArg SparseSGD.Moments.C hfixed
  simp only [SparseSGD.Params.step] at hR hV hC
  have hVC : s.V + 2 * s.C = 0 := by
    linear_combination -hR - hV - 2 * hC
  have hbal : P.w * s.R + (1 + P.beta) * s.C = 0 := by
    linear_combination hV + hC + hVC
  constructor
  · apply (eq_div_iff hb).2
    linear_combination (1 + P.beta) * hVC - 2 * hbal
  · apply (eq_div_iff hb).2
    linear_combination hbal

/-- Every nondegenerate fixed point obeys the exact bulk balance equation. -/
theorem moment_fixedPoint_balance (P : SparseSGD.Params) (s : SparseSGD.Moments)
    (hw : P.w ≠ 0) (heps : P.eps ≠ 0) (hb : 1 + P.beta ≠ 0)
    (hfixed : P.step s = s) :
    P.noise * s.R + P.additive = (1 - P.curvature) * s.R := by
  obtain ⟨hV, hC⟩ := moment_fixedPoint_coordinates P s hb hfixed
  have hv := congrArg SparseSGD.Moments.V hfixed
  simp only [SparseSGD.Params.step] at hv
  rw [hV, hC] at hv
  have hden : 2 * (1 + P.beta) ≠ 0 := mul_ne_zero (by norm_num) hb
  have hprod : (2 * P.w * P.eps) *
      (P.noise * s.R + P.additive - (1 - P.curvature) * s.R) = 0 := by
    unfold SparseSGD.Params.curvature
    field_simp
    simp only [SparseSGD.Params.eps] at hv ⊢
    field_simp at hv
    linear_combination P.w * hv
  have hscale : 2 * P.w * P.eps ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hw) heps
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hscale)

/-- The nondegenerate moment recursion has exactly the previously constructed fixed point. -/
theorem moment_fixedPoint_eq_equilibrium (P : SparseSGD.Params) (s : SparseSGD.Moments)
    (hw : P.w ≠ 0) (heps : P.eps ≠ 0) (hb : 1 + P.beta ≠ 0)
    (hu : P.totalLoad ≠ 1) (hfixed : P.step s = s) : s = P.equilibrium := by
  obtain ⟨hV, hC⟩ := moment_fixedPoint_coordinates P s hb hfixed
  have hbal := moment_fixedPoint_balance P s hw heps hb hfixed
  have hR : s.R = P.additive / (1 - P.totalLoad) := by
    apply (eq_div_iff (sub_ne_zero.mpr hu.symm)).2
    simp only [SparseSGD.Params.totalLoad]
    linear_combination -hbal
  apply SparseSGD.Moments.ext
  · exact hR
  · simpa only [SparseSGD.Params.equilibrium, ← hR] using hV
  · simpa only [SparseSGD.Params.equilibrium, ← hR] using hC

/-- The frozen logistic noise and additive loads do not involve momentum. -/
theorem driftParams_loads {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu theta : Vec d) :
    (driftParams (B := B) eta beta p mu theta).noise =
      eta * (coefDtheta p mu theta - coefA p mu theta ^ 2) / (2 * (B : ℝ) * coefA p mu theta) ∧
    (driftParams (B := B) eta beta p mu theta).additive =
      eta * (d - 1 : ℝ) * coefD0 p mu theta / (2 * (B : ℝ) * coefA p mu theta) ∧
    (driftParams (B := B) eta beta p mu theta).curvature =
      eta * (1 - beta) * coefA p mu theta / (2 * (1 + beta)) := by
  rw [driftParams_explicit]
  exact ⟨rfl, rfl, rfl⟩

/-- The exact floor as a function of a separately supplied curvature load. -/
def frozenLogisticFloor (d B : ℕ) (eta A Dtheta D0 curvatureLoad : ℝ) : ℝ :=
  (eta * (d - 1 : ℝ) * D0 / (2 * (B : ℝ) * A)) /
    (1 - (eta * (Dtheta - A ^ 2) / (2 * (B : ℝ) * A) + curvatureLoad))

/-- At frozen coefficients all momentum dependence in the floor is through `u_c`. -/
theorem driftParams_equilibrium_R {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu theta : Vec d) :
    (driftParams (B := B) eta beta p mu theta).equilibrium.R =
      frozenLogisticFloor d B eta (coefA p mu theta) (coefDtheta p mu theta)
        (coefD0 p mu theta) (eta * (1 - beta) * coefA p mu theta / (2 * (1 + beta))) := by
  rw [driftParams_explicit]
  rfl

/-- Any actual logistic moment-drift fixed point has the exact bulk floor and covariance. -/
theorem logistic_moment_fixedPoint {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu theta : Vec d) (s : SparseSGD.Moments) (heta : eta ≠ 0)
    (hbeta : beta ≠ 1) (hb : 1 + beta ≠ 0)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hu : (driftParams (B := B) eta beta p mu theta).totalLoad ≠ 1)
    (hfixed : (driftParams (B := B) eta beta p mu theta).step s = s) :
    s.R = frozenLogisticFloor d B eta (coefA p mu theta) (coefDtheta p mu theta)
        (coefD0 p mu theta) (eta * (1 - beta) * coefA p mu theta / (2 * (1 + beta))) ∧
    s.C = -eta * (1 - beta) * coefA p mu theta * s.R / (1 + beta) ∧
    s.V = 2 * eta * (1 - beta) * coefA p mu theta * s.R / (1 + beta) := by
  have hA := ne_of_gt (coefA_pos p mu theta hp0 hp1)
  have heps : 1 - beta ≠ 0 := sub_ne_zero.mpr hbeta.symm
  have hw : (driftParams (B := B) eta beta p mu theta).w ≠ 0 :=
    mul_ne_zero (mul_ne_zero heta heps) hA
  have hEq := moment_fixedPoint_eq_equilibrium _ s hw heps hb hu hfixed
  have hsR := congrArg SparseSGD.Moments.R hEq
  have hcoords := moment_fixedPoint_coordinates _ s hb hfixed
  refine ⟨hsR.trans (driftParams_equilibrium_R eta beta p mu theta), ?_, ?_⟩
  · convert hcoords.2 using 1
    simp only [driftParams, SparseSGD.oracleParams]
    ring
  · convert hcoords.1 using 1
    simp only [driftParams, SparseSGD.oracleParams]
    ring

/-- A fixed point of the actual five-coordinate drift has zero mean signal gradient.
The hypotheses are equality of the actual transition expectations, not assumed source formulas. -/
theorem actual_drift_fixedPoint_signal {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d)
    (hr : 0 < r mu) (heta : eta ≠ 0) (hbeta : beta ≠ 1)
    (hsignal : (∫ a : Batch d B, signalCoord mu (update eta beta p mu s a).1
      ∂batchLaw d B p) = signalCoord mu s.1)
    (hmomentum : (∫ a : Batch d B, signalCoord mu (update eta beta p mu s a).2
      ∂batchLaw d B p) = signalCoord mu s.2) :
    signalCoord mu s.2 = 0 ∧
      coefA p mu s.1 * signalCoord mu s.1 + coefB p mu s.1 * r mu = 0 := by
  rw [update_signal_parameter_integral H hB eta beta p mu s hr] at hsignal
  rw [update_signal_momentum_integral H hB eta beta p mu s hr] at hmomentum
  have hprod : eta * (beta * signalCoord mu s.2 + (1 - beta) *
      (coefA p mu s.1 * signalCoord mu s.1 + coefB p mu s.1 * r mu)) = 0 := by
    linarith
  have hzero := (mul_eq_zero.mp hprod).resolve_left heta
  have hm : signalCoord mu s.2 = 0 := by linarith
  refine ⟨hm, ?_⟩
  rw [hm, mul_zero, zero_add] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hbeta.symm)


/-- The actual transition expectation at a bulk fixed point gives the exact floor. -/
theorem actual_drift_fixedPoint_bulk {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d)
    (hr : 0 < r mu) (heta : eta ≠ 0) (hbeta : beta ≠ 1) (hb : 1 + beta ≠ 0)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hu : (driftParams (B := B) eta beta p mu s.1).totalLoad ≠ 1)
    (hbulk : integratedGram (batchLaw d B p)
      (fun a => bulkPart mu (update eta beta p mu s a).1)
      (fun a => eta • bulkPart mu (update eta beta p mu s a).2) =
        SparseSGD.gramMoments (bulkPart mu s.1) (eta • bulkPart mu s.2)) :
    ‖bulkPart mu s.1‖ ^ 2 =
      frozenLogisticFloor d B eta (coefA p mu s.1) (coefDtheta p mu s.1)
        (coefD0 p mu s.1) (eta * (1 - beta) * coefA p mu s.1 / (2 * (1 + beta))) ∧
    eta * inner ℝ (bulkPart mu s.1) (bulkPart mu s.2) =
      -eta * (1 - beta) * coefA p mu s.1 * ‖bulkPart mu s.1‖ ^ 2 / (1 + beta) ∧
    eta ^ 2 * ‖bulkPart mu s.2‖ ^ 2 =
      2 * eta * (1 - beta) * coefA p mu s.1 * ‖bulkPart mu s.1‖ ^ 2 / (1 + beta) := by
  rw [update_bulk_integratedGram H hB eta beta p mu s hr
    (ne_of_gt (coefA_pos p mu s.1 hp0 hp1))] at hbulk
  have h := logistic_moment_fixedPoint eta beta p mu s.1 _ heta hbeta hb hp0 hp1 hu hbulk
  simpa only [SparseSGD.gramMoments, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right] using h

/-- The manuscript's normalized covariance identity follows from the exact recursion. -/
theorem logistic_fixedPoint_normalized_covariance {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu theta : Vec d) (s : SparseSGD.Moments) (hbeta : beta ≠ 1) (hb : 1 + beta ≠ 0)
    (hfixed : (driftParams (B := B) eta beta p mu theta).step s = s) :
    s.C / (1 - beta) = -eta * coefA p mu theta * s.R / (1 + beta) := by
  have hC := (moment_fixedPoint_coordinates _ s hb hfixed).2
  rw [hC]
  simp only [driftParams, SparseSGD.oracleParams]
  field_simp [sub_ne_zero.mpr hbeta.symm]


end
end SparseSGD.Logistic
