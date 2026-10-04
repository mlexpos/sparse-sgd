import SparseSGD.Foundations

/-! Scalar and two-coordinate equilibrium identities for the logistic slow field. -/
namespace SparseSGD.Logistic
noncomputable section

def alpha (theta R r : ℝ) : ℝ := Real.exp ((theta ^ 2 + R - r ^ 2) / 2)

def g (r Phi theta : ℝ) : ℝ :=
  theta * Real.exp ((theta ^ 2 - r ^ 2 + Phi * theta / r) / 2)

def slowField (r Phi theta R : ℝ) : ℝ × ℝ :=
  (r - alpha theta R r * theta, 2 * (Phi - alpha theta R r * R))

theorem g_strictMonoOn_pos (r Phi : ℝ) (hr : 0 < r) (hPhi : 0 ≤ Phi) :
    StrictMonoOn (g r Phi) (Set.Ioi 0) := by
  intro x hx y hy hxy
  unfold g
  have hxpos : 0 < x := hx
  have hypos : 0 < y := hy
  have hpow : x ^ 2 + Phi * x / r < y ^ 2 + Phi * y / r := by
    have hx2 : x ^ 2 < y ^ 2 := by
      have hprod : 0 < (y - x) * (y + x) :=
        mul_pos (sub_pos.mpr hxy) (add_pos hypos hxpos)
      nlinarith
    have hlin : Phi * x / r ≤ Phi * y / r := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hr)
      nlinarith
    linarith
  have hexp :
      Real.exp ((x ^ 2 - r ^ 2 + Phi * x / r) / 2) <
        Real.exp ((y ^ 2 - r ^ 2 + Phi * y / r) / 2) := by
    apply Real.exp_lt_exp.mpr
    linarith
  calc
    x * Real.exp ((x ^ 2 - r ^ 2 + Phi * x / r) / 2) <
        y * Real.exp ((x ^ 2 - r ^ 2 + Phi * x / r) / 2) :=
      mul_lt_mul_of_pos_right hxy (Real.exp_pos _)
    _ < y * Real.exp ((y ^ 2 - r ^ 2 + Phi * y / r) / 2) :=
      mul_lt_mul_of_pos_left hexp hypos

theorem g_at_r (r Phi : ℝ) (hr : 0 < r) :
    g r Phi r = r * Real.exp (Phi / 2) := by
  unfold g
  congr 1
  field_simp [hr.ne']
  ring

theorem positive_root_le_r (r Phi theta : ℝ) (hr : 0 < r) (hPhi : 0 ≤ Phi)
    (hθ : 0 < theta) (hroot : g r Phi theta = r) : theta ≤ r := by
  by_contra h
  have hrt : r < theta := lt_of_not_ge h
  have hmono := g_strictMonoOn_pos r Phi hr hPhi
  have hgr : r ≤ g r Phi r := by
    rw [g_at_r r Phi hr]
    calc
      r = r * 1 := by ring
      _ ≤ r * Real.exp (Phi / 2) :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr (by positivity)) hr.le
  have : g r Phi r < g r Phi theta := hmono (Set.mem_Ioi.mpr hr) (Set.mem_Ioi.mpr hθ) hrt
  linarith

theorem g_continuous (r Phi : ℝ) : Continuous (g r Phi) := by
  unfold g
  fun_prop

@[simp] theorem g_at_zero (r Phi : ℝ) : g r Phi 0 = 0 := by
  simp [g]

theorem exists_unique_positive_root (r Phi : ℝ) (hr : 0 < r) (hPhi : 0 ≤ Phi) :
    ∃! theta : ℝ, 0 < theta ∧ g r Phi theta = r := by
  have hgr : r ≤ g r Phi r := by
    rw [g_at_r r Phi hr]
    calc
      r = r * 1 := by ring
      _ ≤ r * Real.exp (Phi / 2) :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr (by positivity)) hr.le
  obtain ⟨theta, htheta, hroot⟩ :=
    intermediate_value_Icc hr.le (g_continuous r Phi).continuousOn
      (show r ∈ Set.Icc (g r Phi 0) (g r Phi r) by
        simpa only [g_at_zero, Set.mem_Icc] using And.intro hr.le hgr)
  have hpos : 0 < theta := by
    by_contra h
    have hz : theta = 0 := le_antisymm (le_of_not_gt h) htheta.1
    subst theta
    simp only [g_at_zero] at hroot
    linarith
  refine ⟨theta, ⟨hpos, hroot⟩, ?_⟩
  intro other hother
  exact (g_strictMonoOn_pos r Phi hr hPhi).injOn
    (Set.mem_Ioi.mpr hother.1) (Set.mem_Ioi.mpr hpos) (hother.2.trans hroot.symm)

theorem positive_root_lt_r (r Phi theta : ℝ) (hr : 0 < r) (hPhi : 0 < Phi)
    (hθ : 0 < theta) (hroot : g r Phi theta = r) : theta < r := by
  have hle := positive_root_le_r r Phi theta hr hPhi.le hθ hroot
  have hgr : r < g r Phi r := by
    rw [g_at_r r Phi hr]
    calc
      r = r * 1 := by ring
      _ < r * Real.exp (Phi / 2) :=
        mul_lt_mul_of_pos_left (Real.one_lt_exp_iff.mpr (by positivity)) hr
  exact lt_of_le_of_ne hle (by intro h; subst theta; linarith)

theorem g_eq_alpha_mul (r Phi theta : ℝ) :
    g r Phi theta = alpha theta (Phi * theta / r) r * theta := by
  unfold g alpha
  rw [mul_comm theta]
  congr 1
  ring

theorem slowField_zero_iff (r Phi theta R : ℝ) (hr : 0 < r) (_hθ : 0 < theta) :
    slowField r Phi theta R = (0, 0) ↔
      g r Phi theta = r ∧ R = Phi * theta / r := by
  constructor
  · intro hfield
    have hsignal : alpha theta R r * theta = r := by
      have h := congrArg Prod.fst hfield
      simp only [slowField] at h
      linarith
    have hbulk : alpha theta R r * R = Phi := by
      have h := congrArg Prod.snd hfield
      simp only [slowField] at h
      linarith
    have hR : R = Phi * theta / r := by
      apply (eq_div_iff hr.ne').2
      calc
        R * r = R * (alpha theta R r * theta) := by rw [hsignal]
        _ = (alpha theta R r * R) * theta := by ring
        _ = Phi * theta := by rw [hbulk]
    refine ⟨?_, hR⟩
    rw [g_eq_alpha_mul, ← hR]
    exact hsignal
  · rintro ⟨hroot, hR⟩
    have hsignal : alpha theta R r * theta = r := by
      rw [g_eq_alpha_mul, ← hR] at hroot
      exact hroot
    have hbulk : alpha theta R r * R = Phi := by
      rw [hR]
      calc
        alpha theta (Phi * theta / r) r * (Phi * theta / r) =
            Phi * (alpha theta (Phi * theta / r) r * theta) / r := by ring
        _ = Phi * r / r := by rw [← hR, hsignal]
        _ = Phi := by field_simp
    apply Prod.ext
    · simp only [slowField]
      linarith
    · simp only [slowField]
      linarith

theorem equilibrium_alpha (r Phi theta R : ℝ) (hθ : 0 < theta)
    (hfield : slowField r Phi theta R = (0, 0)) : alpha theta R r = r / theta := by
  apply (eq_div_iff hθ.ne').2
  have h := congrArg Prod.fst hfield
  simp only [slowField] at h
  linarith

end

end SparseSGD.Logistic
