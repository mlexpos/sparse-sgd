import SparseSGD.Logistic.DynamicField

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000

/-- A coercive energy for the full dynamic-alpha ODE, including additive noise. -/
def dynamicEnergy (r delta : ℝ) (y : DynamicState) : ℝ :=
  dynamicAlpha r y-r*y 0+delta/2*((y 1)^2+y 3)

theorem hasDerivAt_dynamicEnergy (r delta Phi : ℝ) (y : ℝ → DynamicState) (t : ℝ)
    (hdelta : delta ≠ 0)
    (hy : HasDerivAt y (dynamicField r delta Phi (y t)) t) :
    HasDerivAt (fun s => dynamicEnergy r delta (y s))
      (Phi-delta*((y t 1)^2+y t 3)) t := by
  have hc := hasDerivAt_pi.mp hy
  have ha := (((hc 0).pow 2).add (hc 2)).sub_const (r^2)
  have halpha := (ha.div_const 2).exp
  convert ((halpha.sub ((hc 0).const_mul r)).add
    ((((hc 1).pow 2).add (hc 3)).const_mul (delta/2))) using 1
  · rfl
  · dsimp [dynamicField,dynamicAlpha]
    field_simp
    <;> ring

/-- The potential part confines both the signal and bulk position; the
remaining kinetic energy is nonnegative on physical states. -/
theorem dynamicEnergy_coercive (r delta : ℝ) (y : DynamicState) :
    1+(y 0)^2/4+y 2/2+delta/2*((y 1)^2+y 3) ≤ dynamicEnergy r delta y+3*r^2/2 := by
  have he := Real.add_one_le_exp (((y 0)^2+y 2-r^2)/2)
  have hs := sq_nonneg (y 0/2-r)
  dsimp [dynamicEnergy,dynamicAlpha]
  nlinarith

/-- Energy can grow at most linearly on every physical solution interval. -/
theorem dynamicEnergy_finite_horizon_bound (r delta Phi T : ℝ)
    (hdelta : 0 < delta) (y : ℝ → DynamicState)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hV : ∀ t ∈ Set.Icc 0 T, 0 ≤ y t 3) :
    ∀ t ∈ Set.Icc 0 T, dynamicEnergy r delta (y t) ≤ dynamicEnergy r delta (y 0)+Phi*t := by
  intro t ht
  let f := fun t => dynamicEnergy r delta (y t)-Phi*t
  have hd : ∀ s ∈ Set.Icc 0 t, HasDerivAt f (-delta*((y s 1)^2+y s 3)) s := by
    intro s hs
    have hst : s ∈ Set.Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
    convert (hasDerivAt_dynamicEnergy r delta Phi y s hdelta.ne' (hy s hst)).sub
      ((hasDerivAt_id s).const_mul Phi) using 1 <;> first | rfl | ring
  have hf : AntitoneOn f (Set.Icc 0 t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hd s (interior_subset hs)).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (add_nonneg (sq_nonneg _) (hV s ⟨(interior_subset hs).1,(interior_subset hs).2.trans ht.2⟩))
  have hh := hf (show (0 : ℝ)∈Set.Icc 0 t by exact ⟨le_rfl,ht.1⟩)
    (show t∈Set.Icc 0 t by exact ⟨ht.1,le_rfl⟩) ht.1
  dsimp [f] at hh
  linarith

/-- Physical energy sublevels are bounded, uniformly over the five coordinates. -/
theorem dynamicEnergy_controls_norm (r delta E : ℝ) (y : DynamicState)
    (hd : 0 < delta) (hR : 0 ≤ y 2) (hV : 0 ≤ y 3)
    (hC : (y 4)^2 ≤ y 2*y 3) (hE : dynamicEnergy r delta y ≤ E) :
    ‖y‖ ≤ 4*(|E|+2*r^2+1)*(1+1/delta)+1 := by
  let B := |E|+2*r^2+1
  let K := 4*B*(1+1/delta)+1
  have hB : 1 ≤ B := by dsimp [B]; nlinarith [abs_nonneg E,sq_nonneg r]
  have hB0 : 0 ≤ B := by linarith
  have hKeq : K = 4*B+4*(B/delta)+1 := by dsimp [K]; ring
  have hK1 : 1 ≤ K := by rw [hKeq]; nlinarith [div_nonneg hB0 hd.le]
  have hK0 : 0 ≤ K := by linarith
  have hco := (dynamicEnergy_coercive r delta y).trans (add_le_add hE (le_refl (3*r^2/2)))
  have hEB : E+3*r^2/2 ≤ B := by dsimp [B]; nlinarith [le_abs_self E,sq_nonneg r]
  have hcoB := hco.trans hEB
  have hkin : 0 ≤ delta/2*((y 1)^2+y 3) := by positivity
  have hth : (y 0)^2 ≤ 4*B := by nlinarith
  have hR' : y 2 ≤ 2*B := by nlinarith [sq_nonneg (y 0)]
  have hY : (y 1)^2 ≤ 2*B/delta := by
    apply (le_div_iff₀ hd).2
    nlinarith [sq_nonneg (y 0)]
  have hV' : y 3 ≤ 2*B/delta := by
    apply (le_div_iff₀ hd).2
    nlinarith [sq_nonneg (y 0),sq_nonneg (y 1)]
  have hKbig : 4*B ≤ K := by rw [hKeq]; nlinarith [div_nonneg hB0 hd.le]
  have hKbig' : 4*B/delta ≤ K := by rw [hKeq]; simp only [div_eq_mul_inv]; nlinarith
  have hKsum : 2*B+2*B/delta ≤ K := by rw [hKeq]; simp only [div_eq_mul_inv]; nlinarith [mul_nonneg hB0 (inv_nonneg.mpr hd.le)]
  simp only [div_eq_mul_inv] at hY hV' hKbig' hKsum
  apply (pi_norm_le_iff_of_nonneg hK0).2
  intro i
  fin_cases i
  · change |y 0| ≤ K
    nlinarith [sq_abs (y 0)]
  · change |y 1| ≤ K
    nlinarith [sq_abs (y 1),div_nonneg hB0 hd.le]
  · change |y 2| ≤ K
    rw [abs_of_nonneg hR]
    linarith
  · change |y 3| ≤ K
    rw [abs_of_nonneg hV]
    linarith [div_nonneg hB0 hd.le]
  · change |y 4| ≤ K
    have hab : |y 4| ≤ y 2+y 3 := by
      nlinarith [sq_abs (y 4),sq_nonneg (y 2-y 3),abs_nonneg (y 4)]
    linarith

end
end SparseSGD.Logistic
