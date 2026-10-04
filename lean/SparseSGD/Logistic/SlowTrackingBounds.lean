import SparseSGD.Logistic.SlowTracking
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

def slowFastStep (h z Phi a d0 xi rho R : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  let beta := 1-h
  let Wn := beta^2*v.2+2*beta*z*a*v.1+h*(2*Phi*d0+z*a^2*rho*R+xi*R)
  (beta*v.1+h*a*R-h*Wn,Wn)

def slowFrozenVarianceError (h z Phi a d0 xi rho curvature R : ℝ) : ℝ :=
  2*(1-h)*z*a*(slowFastTarget (1-h) Phi curvature R).1+
    h*(2*Phi*(d0-1)+z*a^2*rho*R+xi*R)

/-- The nonconstant forcing in the fast target is computed exactly. -/
theorem slowFastStep_target_error (h z Phi a d0 xi rho curvature R : ℝ) (hh1 : h ≤ 1) :
    slowFastStep h z Phi a d0 xi rho R (slowFastTarget (1-h) Phi curvature R)-
      slowFastTarget (1-h) Phi curvature R =
    (h*(a-curvature)*R-h*slowFrozenVarianceError h z Phi a d0 xi rho curvature R,
      slowFrozenVarianceError h z Phi a d0 xi rho curvature R) := by
  have hn : 1+(1-h) ≠ 0 := by linarith
  ext <;> simp [slowFastStep,slowFastTarget,slowFrozenVarianceError] <;> field_simp <;> ring

/-- The nonlinear fast map's difference at fixed slow state is exactly the
homogeneous operator whose retention contraction was proved. -/
theorem slowFastStep_sub (h z Phi a d0 xi rho R : ℝ) (v w : ℝ × ℝ) :
    slowFastStep h z Phi a d0 xi rho R v-slowFastStep h z Phi a d0 xi rho R w =
      slowFastLinear h z a (v-w) := by
  ext <;> simp [slowFastStep,slowFastLinear] <;> ring

/-- A moving-target tracking estimate for the actual fast-pair map. -/
theorem slowFastStep_tracking (h z Phi a d0 xi rho curvature R curvature' R' : ℝ)
    (v : ℝ × ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hsmall : 12*z*a ≤ h) :
    slowFastNorm (slowFastStep h z Phi a d0 xi rho R v-slowFastTarget (1-h) Phi curvature' R') ≤
      (1-h/2)*slowFastNorm (v-slowFastTarget (1-h) Phi curvature R)+
      slowFastNorm (slowFastStep h z Phi a d0 xi rho R (slowFastTarget (1-h) Phi curvature R)-
        slowFastTarget (1-h) Phi curvature R)+|curvature*R-curvature'*R'| := by
  have hid : slowFastStep h z Phi a d0 xi rho R v-slowFastTarget (1-h) Phi curvature' R' =
      slowFastLinear h z a (v-slowFastTarget (1-h) Phi curvature R)+
        (slowFastStep h z Phi a d0 xi rho R (slowFastTarget (1-h) Phi curvature R)-
          slowFastTarget (1-h) Phi curvature R)+
        (slowFastTarget (1-h) Phi curvature R-slowFastTarget (1-h) Phi curvature' R') := by
    rw [← slowFastStep_sub]
    abel
  rw [hid]
  calc
    _ ≤ slowFastNorm (slowFastLinear h z a (v-slowFastTarget (1-h) Phi curvature R))+
      slowFastNorm (slowFastStep h z Phi a d0 xi rho R (slowFastTarget (1-h) Phi curvature R)-
        slowFastTarget (1-h) Phi curvature R)+
      slowFastNorm (slowFastTarget (1-h) Phi curvature R-slowFastTarget (1-h) Phi curvature' R') :=
      (slowFastNorm_add _ _).trans (add_le_add (slowFastNorm_add _ _) le_rfl)
    _ ≤ _ := by
      have hc := slowFastLinear_contract h z a (v-slowFastTarget (1-h) Phi curvature R) hh hh1 hz ha hsmall
      have hd : slowFastNorm (slowFastTarget (1-h) Phi curvature R-
          slowFastTarget (1-h) Phi curvature' R')=|curvature*R-curvature'*R'| := by
        simp [slowFastTarget,slowFastNorm]
      rw [hd]
      linarith

/-- The actual finite-batch mixed variance coefficient is tame in the LR2
units, with the floor retained alongside the exponential remainder. -/
theorem slow_mixed_noise_tame {d B : ℕ} (eta : ℝ) (p : unitInterval)
    (mu theta : Vec d) (heta : 0 ≤ eta) (hp : 0 < (p:ℝ)) (hB : 0 < B)
    (hd : 2 ≤ d) (htame : tameError p mu theta ≤ 1/2) :
    |eta*coefDtheta p mu theta/((B:ℝ)*(p:ℝ))| ≤
      24*dynamicSourceLoad d B eta*tameError p mu theta := by
  have he : 0 ≤ tameError p mu theta := hp.le.trans (tameError_ge_probability p mu theta)
  have hBr : 0 < (B:ℝ) := by exact_mod_cast hB
  have hd1 : 1 ≤ (d-1:ℝ) := by
    have hd2 : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hc := (tame_coefficients p mu theta hp htame).2.2.2
  rw [abs_div,abs_mul,abs_of_nonneg heta,abs_of_pos (mul_pos hBr hp)]
  calc
    _ ≤ eta*(12*(p:ℝ)*tameError p mu theta)/((B:ℝ)*(p:ℝ)) := by gcongr
    _ = 12*(eta/(B:ℝ))*tameError p mu theta := by field_simp <;> ring
    _ ≤ 12*(eta*(d-1:ℝ)/(B:ℝ))*tameError p mu theta := by
      gcongr
      nlinarith only [hd1,heta]
    _ = _ := by unfold dynamicSourceLoad; ring

/-- The frozen target residual is bounded by its explicit variance forcing. -/
theorem slowFastStep_target_bound (h z Phi a d0 xi rho curvature R : ℝ)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    slowFastNorm (slowFastStep h z Phi a d0 xi rho R (slowFastTarget (1-h) Phi curvature R)-
      slowFastTarget (1-h) Phi curvature R) ≤
      h*|a-curvature| *|R|+(h+2)*|slowFrozenVarianceError h z Phi a d0 xi rho curvature R| := by
  rw [slowFastStep_target_error h z Phi a d0 xi rho curvature R hh1]
  dsimp [slowFastNorm]
  have hc := abs_sub (h*(a-curvature)*R) (h*slowFrozenVarianceError h z Phi a d0 xi rho curvature R)
  simp only [abs_mul,abs_of_nonneg hh] at hc
  nlinarith only [hc]

end
end SparseSGD.Logistic
