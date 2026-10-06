import SparseSGD.Logistic.Bounds

/-! Local calculus for the logistic slow field. -/
namespace SparseSGD.Logistic
noncomputable section
open scoped Topology

/-- The Jacobian claimed for the slow field, represented on `ℝ × ℝ`. -/
def equilibriumJacobian (a theta R : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  ((-(a * (1 + theta ^ 2))) • (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      (-(a * theta / 2)) • (ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
    ((-(2 * a * theta * R)) • (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      (-(a * (2 + R))) • (ContinuousLinearMap.snd ℝ ℝ ℝ))

/-- The exponential curvature factor has the claimed two-coordinate derivative. -/
theorem hasFDerivAt_alpha (r theta R : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => alpha p.1 p.2 r)
      ((alpha theta R r * theta) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (alpha theta R r / 2) • ContinuousLinearMap.snd ℝ ℝ ℝ) (theta, R) := by
  have ht : HasFDerivAt (fun p : ℝ × ℝ => p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (theta, R) := hasFDerivAt_fst
  have hR : HasFDerivAt (fun p : ℝ × ℝ => p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (theta, R) := hasFDerivAt_snd
  have harg : HasFDerivAt (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 - r ^ 2) / 2)
      (theta • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (theta, R) := by
    convert (((ht.mul ht).add hR).sub_const (r ^ 2)).const_mul (1 / 2 : ℝ) using 1
    · funext p
      change (p.1 ^ 2 + p.2 - r ^ 2) / 2 = (1 / 2 : ℝ) * (p.1 * p.1 + p.2 - r ^ 2)
      ring
    · apply ContinuousLinearMap.ext
      intro p
      simp
      ring
  convert harg.exp using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro p
    simp [alpha]
    ring

/-- The displayed Jacobian is the derivative of the actual slow field, at every point. -/
theorem hasFDerivAt_slowField (r Phi theta R : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => slowField r Phi p.1 p.2)
      (equilibriumJacobian (alpha theta R r) theta R) (theta, R) := by
  have ht : HasFDerivAt (fun p : ℝ × ℝ => p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (theta, R) := hasFDerivAt_fst
  have hR : HasFDerivAt (fun p : ℝ × ℝ => p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (theta, R) := hasFDerivAt_snd
  have ha := hasFDerivAt_alpha r theta R
  have h1 := (ha.mul ht).const_sub r
  have h2 := ((ha.mul hR).const_sub Phi).const_mul 2
  convert h1.prodMk h2 using 1
  · ext p <;> rfl
  · apply ContinuousLinearMap.ext
    intro p
    apply Prod.ext <;> simp [equilibriumJacobian] <;> ring

/-- Matrix of the slow derivative in the coordinate basis. -/
def equilibriumJacobianMatrix (a theta R : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(a * (1 + theta ^ 2)), -(a * theta / 2);
      -(2 * a * theta * R), -(a * (2 + R))]

@[simp] theorem equilibriumJacobian_apply (a theta R : ℝ) (p : ℝ × ℝ) :
    equilibriumJacobian a theta R p =
      (-(a * (1 + theta ^ 2)) * p.1 - (a * theta / 2) * p.2,
       -(2 * a * theta * R) * p.1 - (a * (2 + R)) * p.2) := by
  ext <;> simp [equilibriumJacobian] <;> ring

/-- The matrix records the images of both coordinate vectors. -/
theorem equilibriumJacobianMatrix_columns (a theta R : ℝ) :
    equilibriumJacobian a theta R (1, 0) =
      (equilibriumJacobianMatrix a theta R 0 0,
       equilibriumJacobianMatrix a theta R 1 0) ∧
    equilibriumJacobian a theta R (0, 1) =
      (equilibriumJacobianMatrix a theta R 0 1,
       equilibriumJacobianMatrix a theta R 1 1) := by
  simp [equilibriumJacobianMatrix]

@[simp] theorem equilibriumJacobianMatrix_trace (a theta R : ℝ) :
    (equilibriumJacobianMatrix a theta R).trace = -a * (3 + theta ^ 2 + R) := by
  rw [Matrix.trace_fin_two]
  simp [equilibriumJacobianMatrix]
  ring

@[simp] theorem equilibriumJacobianMatrix_det (a theta R : ℝ) :
    (equilibriumJacobianMatrix a theta R).det = a ^ 2 * (2 + 2 * theta ^ 2 + R) := by
  rw [Matrix.det_fin_two]
  simp [equilibriumJacobianMatrix]
  ring

theorem equilibriumJacobianMatrix_trace_neg (a theta R : ℝ) (ha : 0 < a)
    (hR : 0 ≤ R) : (equilibriumJacobianMatrix a theta R).trace < 0 := by
  rw [equilibriumJacobianMatrix_trace]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos ha) (by positivity)

theorem equilibriumJacobianMatrix_det_pos (a theta R : ℝ) (ha : 0 < a)
    (hR : 0 ≤ R) : 0 < (equilibriumJacobianMatrix a theta R).det := by
  rw [equilibriumJacobianMatrix_det]
  exact mul_pos (sq_pos_of_pos ha) (by positivity)

/-- The actual slow field has negative divergence on the nonnegative bulk half-plane. -/
theorem slowField_divergence_neg (r Phi theta R : ℝ) (hR : 0 ≤ R) :
    ((fderiv ℝ (fun p : ℝ × ℝ => slowField r Phi p.1 p.2) (theta, R)) (1, 0)).1 +
      ((fderiv ℝ (fun p : ℝ × ℝ => slowField r Phi p.1 p.2) (theta, R)) (0, 1)).2 < 0 := by
  rw [(hasFDerivAt_slowField r Phi theta R).fderiv]
  simp only [equilibriumJacobian_apply]
  have h := equilibriumJacobianMatrix_trace_neg (alpha theta R r) theta R
    (Real.exp_pos _) hR
  rw [equilibriumJacobianMatrix_trace] at h
  convert h using 1
  ring

/-- At a nonnegative-temperature equilibrium the logarithmic curvature is small. -/
theorem equilibrium_log_alpha_bounds (r Phi theta R : ℝ) (hr : 0 < r)
    (hPhi : 0 ≤ Phi) (htheta : 0 < theta)
    (hfield : slowField r Phi theta R = (0, 0)) :
    0 ≤ Real.log (alpha theta R r) ∧ Real.log (alpha theta R r) ≤ Phi / 2 := by
  obtain ⟨hroot, hR⟩ := (slowField_zero_iff r Phi theta R hr htheta).1 hfield
  have ht := positive_root_le_r r Phi theta hr hPhi htheta hroot
  have hb := (bulk_bounds_of_phi_le r Phi theta Phi hr hPhi htheta hroot le_rfl).2
  rw [← hR] at hb
  constructor
  · apply Real.log_nonneg
    rw [equilibrium_alpha r Phi theta R htheta hfield]
    exact (le_div_iff₀ htheta).2 (by simpa using ht)
  · rw [alpha, Real.log_exp]
    have hsq : theta ^ 2 ≤ r ^ 2 := by nlinarith
    linarith

/-- The signal is exactly the exponentially attenuated reference signal. -/
theorem equilibrium_signal_exp_log (r Phi theta R : ℝ)
    (hfield : slowField r Phi theta R = (0, 0)) :
    theta = r * Real.exp (-Real.log (alpha theta R r)) := by
  have ha : 0 < alpha theta R r := Real.exp_pos _
  have hs : alpha theta R r * theta = r := by
    have h := congrArg Prod.fst hfield
    simp only [slowField] at h
    linarith
  rw [Real.exp_neg, Real.exp_log ha, ← div_eq_mul_inv]
  exact (eq_div_iff ha.ne').2 (by simpa [mul_comm] using hs)

/-- Quantitative form of Proposition D(ii), with a uniform quadratic remainder. -/
theorem equilibrium_log_alpha_bulk_error (r Phi theta R : ℝ) (hr : 0 < r)
    (hPhi : 0 ≤ Phi) (hPhi1 : Phi ≤ 1) (htheta : 0 < theta)
    (hfield : slowField r Phi theta R = (0, 0)) :
    |Real.log (alpha theta R r) - R / (2 * (1 + r ^ 2))| ≤
      (r ^ 2 / (2 * (1 + r ^ 2))) * Phi ^ 2 := by
  let L := Real.log (alpha theta R r)
  have hL := equilibrium_log_alpha_bounds r Phi theta R hr hPhi htheta hfield
  change 0 ≤ L ∧ L ≤ Phi / 2 at hL
  have hnorm : ‖-2 * L‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonpos (by nlinarith)]
    nlinarith
  have he := Real.norm_exp_sub_one_sub_id_le hnorm
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at he
  have hexp : theta ^ 2 = r ^ 2 * Real.exp (-2 * L) := by
    rw [equilibrium_signal_exp_log r Phi theta R hfield, mul_pow]
    congr 1
    have h := Real.exp_nat_mul (-L) 2
    simpa using h.symm
  have hid : 2 * L = theta ^ 2 + R - r ^ 2 := by
    dsimp [L]
    rw [alpha, Real.log_exp]
    ring
  have hdiff : L - R / (2 * (1 + r ^ 2)) =
      r ^ 2 / (2 * (1 + r ^ 2)) * (Real.exp (-2 * L) - 1 - (-2 * L)) := by
    have hden : (2 * (1 + r ^ 2)) ≠ 0 := by positivity
    field_simp
    rw [show -(L * 2) = -2 * L by ring]
    nlinarith [hid, hexp]
  have hc : 0 ≤ r ^ 2 / (2 * (1 + r ^ 2)) := by positivity
  rw [show Real.log (alpha theta R r) = L from rfl, hdiff, abs_mul,
    abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  calc
    |Real.exp (-2 * L) - 1 - (-2 * L)| ≤ |-2 * L| ^ 2 := he
    _ ≤ Phi ^ 2 := by
      rw [abs_of_nonpos (by nlinarith)]
      nlinarith [hL.1, hL.2]


/-- Bulk temperature differs from its input by at most a quadratic term. -/
theorem equilibrium_bulk_load_error (r Phi theta R : ℝ) (hr : 0 < r)
    (hPhi : 0 ≤ Phi) (htheta : 0 < theta)
    (hfield : slowField r Phi theta R = (0, 0)) :
    |R - Phi| ≤ Phi ^ 2 / 2 := by
  obtain ⟨hroot, hR⟩ := (slowField_zero_iff r Phi theta R hr htheta).1 hfield
  have hb := (bulk_bounds_of_phi_le r Phi theta Phi hr hPhi htheta hroot le_rfl).2
  rw [← hR] at hb
  have hL := equilibrium_log_alpha_bounds r Phi theta R hr hPhi htheta hfield
  have hRexp : R = Phi * Real.exp (-Real.log (alpha theta R r)) := by
    calc
      R = Phi * theta / r := hR
      _ = Phi * (r * Real.exp (-Real.log (alpha theta R r))) / r := by
        rw [← equilibrium_signal_exp_log r Phi theta R hfield]
      _ = Phi * Real.exp (-Real.log (alpha theta R r)) := by field_simp
  have he := mul_le_mul_of_nonneg_left
    (Real.add_one_le_exp (-Real.log (alpha theta R r))) hPhi
  rw [← hRexp] at he
  rw [abs_of_nonpos (sub_nonpos.mpr hb)]
  have hl := mul_le_mul_of_nonneg_left hL.2 hPhi
  nlinarith

/-- Equivalent expansion in terms of the input temperature, with a simple remainder constant. -/
theorem equilibrium_log_alpha_load_error (r Phi theta R : ℝ) (hr : 0 < r)
    (hPhi : 0 ≤ Phi) (hPhi1 : Phi ≤ 1) (htheta : 0 < theta)
    (hfield : slowField r Phi theta R = (0, 0)) :
    |Real.log (alpha theta R r) - Phi / (2 * (1 + r ^ 2))| ≤ Phi ^ 2 := by
  have hbulk := equilibrium_log_alpha_bulk_error r Phi theta R hr hPhi hPhi1 htheta hfield
  have hload := equilibrium_bulk_load_error r Phi theta R hr hPhi htheta hfield
  have hden : 0 < 2 * (1 + r ^ 2) := by positivity
  have hnonneg : 0 ≤ Phi ^ 2 := sq_nonneg _
  calc
    |Real.log (alpha theta R r) - Phi / (2 * (1 + r ^ 2))| ≤
        |Real.log (alpha theta R r) - R / (2 * (1 + r ^ 2))| +
        |(R - Phi) / (2 * (1 + r ^ 2))| := by
      convert abs_add_le (Real.log (alpha theta R r) - R / (2 * (1 + r ^ 2)))
        ((R - Phi) / (2 * (1 + r ^ 2))) using 1
      congr 1
      ring
    _ ≤ (r ^ 2 / (2 * (1 + r ^ 2))) * Phi ^ 2 +
        (Phi ^ 2 / 2) / (2 * (1 + r ^ 2)) := by
      rw [abs_div, abs_of_pos hden]
      exact add_le_add hbulk (div_le_div_of_nonneg_right hload hden.le)
    _ ≤ Phi ^ 2 := by
      rw [div_mul_eq_mul_div, ← add_div]
      apply (div_le_iff₀ hden).2
      nlinarith [sq_nonneg r, mul_nonneg (sq_nonneg r) hnonneg]

/-- The canonical root uses the proved existence and uniqueness theorem. -/
def positiveRoot (r Phi : ℝ) : ℝ :=
  if h : 0 < r ∧ 0 ≤ Phi then
    (exists_unique_positive_root r Phi h.1 h.2).exists.choose
  else r

theorem positiveRoot_spec (r Phi : ℝ) (hr : 0 < r) (hPhi : 0 ≤ Phi) :
    0 < positiveRoot r Phi ∧ g r Phi (positiveRoot r Phi) = r := by
  simp only [positiveRoot, dite_eq_left (And.intro hr hPhi)]
  exact (exists_unique_positive_root r Phi hr hPhi).exists.choose_spec

/-- Bulk and logarithmic curvature at the canonical equilibrium. -/
def equilibriumBulk (r Phi : ℝ) : ℝ := Phi * positiveRoot r Phi / r

def equilibriumLogAlpha (r Phi : ℝ) : ℝ :=
  Real.log (alpha (positiveRoot r Phi) (equilibriumBulk r Phi) r)

theorem positiveRoot_slowField_zero (r Phi : ℝ) (hr : 0 < r) (hPhi : 0 ≤ Phi) :
    slowField r Phi (positiveRoot r Phi) (equilibriumBulk r Phi) = (0, 0) := by
  have hs := positiveRoot_spec r Phi hr hPhi
  exact (slowField_zero_iff r Phi (positiveRoot r Phi) (equilibriumBulk r Phi) hr hs.1).2
    ⟨hs.2, rfl⟩

theorem equilibriumLogAlpha_load_error (r Phi : ℝ) (hr : 0 < r)
    (hPhi : 0 ≤ Phi) (hPhi1 : Phi ≤ 1) :
    |equilibriumLogAlpha r Phi - Phi / (2 * (1 + r ^ 2))| ≤ Phi ^ 2 := by
  exact equilibrium_log_alpha_load_error r Phi (positiveRoot r Phi) (equilibriumBulk r Phi)
    hr hPhi hPhi1 (positiveRoot_spec r Phi hr hPhi).1
    (positiveRoot_slowField_zero r Phi hr hPhi)


/-- Proposition D(ii) as a one-sided asymptotic statement at zero temperature. -/
theorem equilibriumLogAlpha_bulk_isBigO (r : ℝ) (hr : 0 < r) :
    Asymptotics.IsBigO (𝓝[Set.Ici 0] 0)
      (fun Phi : ℝ => equilibriumLogAlpha r Phi - equilibriumBulk r Phi / (2 * (1 + r ^ 2)))
      (fun Phi : ℝ => Phi ^ 2) := by
  apply Asymptotics.IsBigO.of_bound (r ^ 2 / (2 * (1 + r ^ 2)))
  have hn : ∀ᶠ Phi : ℝ in 𝓝[Set.Ici 0] 0, 0 ≤ Phi := self_mem_nhdsWithin
  have h1 : ∀ᶠ Phi : ℝ in 𝓝[Set.Ici 0] 0, Phi < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hn, h1] with Phi hPhi hPhi1
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg Phi)]
  exact equilibrium_log_alpha_bulk_error r Phi (positiveRoot r Phi) (equilibriumBulk r Phi)
    hr hPhi hPhi1.le (positiveRoot_spec r Phi hr hPhi).1
    (positiveRoot_slowField_zero r Phi hr hPhi)

/-- The input-temperature expansion is also uniform at zero. -/
theorem equilibriumLogAlpha_load_isBigO (r : ℝ) (hr : 0 < r) :
    Asymptotics.IsBigO (𝓝[Set.Ici 0] 0)
      (fun Phi : ℝ => equilibriumLogAlpha r Phi - Phi / (2 * (1 + r ^ 2)))
      (fun Phi : ℝ => Phi ^ 2) := by
  apply Asymptotics.IsBigO.of_bound 1
  have hn : ∀ᶠ Phi : ℝ in 𝓝[Set.Ici 0] 0, 0 ≤ Phi := self_mem_nhdsWithin
  have h1 : ∀ᶠ Phi : ℝ in 𝓝[Set.Ici 0] 0, Phi < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hn, h1] with Phi hPhi hPhi1
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg Phi), one_mul] using
    equilibriumLogAlpha_load_error r Phi hr hPhi hPhi1.le


end
end SparseSGD.Logistic
