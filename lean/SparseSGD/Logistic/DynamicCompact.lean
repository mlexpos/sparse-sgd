import SparseSGD.Logistic.DynamicConsistency
namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 1200000

/-- Curvature is bounded uniformly on a state ball. -/
theorem dynamicAlpha_le_closedBall (r M : ℝ) (y : DynamicState)
    (hM : 0 ≤ M) (hy : ‖y‖ ≤ M) :
    dynamicAlpha r y ≤ Real.exp ((M^2+M)/2) := by
  have h0 : |y 0| ≤ M := by simpa using (norm_le_pi_norm y 0).trans hy
  have h2 : |y 2| ≤ M := by simpa using (norm_le_pi_norm y 2).trans hy
  unfold dynamicAlpha
  apply Real.exp_le_exp.mpr
  have hs : y 0 ^ 2 ≤ M^2 := by nlinarith [sq_abs (y 0), abs_nonneg (y 0)]
  nlinarith [le_abs_self (y 2), sq_nonneg r]

private theorem data_norm_bound (y : DynamicState) (h delta kappa a b d0 nu rho M H D N A B D0 Nu P : ℝ)
    (hy : ‖y‖ ≤ M) (hh : |h| ≤ H) (hdelta : |delta| ≤ D) (hk : |kappa| ≤ N)
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hd0 : |d0| ≤ D0) (hn : |nu| ≤ Nu) (hp : |rho| ≤ P) :
    ‖dynamicIncrementData y h delta kappa a b d0 nu rho‖ ≤ M+H+D+N+A+B+D0+Nu+P := by
  have hm : 0 ≤ M := (norm_nonneg y).trans hy
  have hH : 0 ≤ H := (abs_nonneg h).trans hh
  have hD : 0 ≤ D := (abs_nonneg delta).trans hdelta
  have hN : 0 ≤ N := (abs_nonneg kappa).trans hk
  have hA : 0 ≤ A := (abs_nonneg a).trans ha
  have hB : 0 ≤ B := (abs_nonneg b).trans hb
  have hD0 : 0 ≤ D0 := (abs_nonneg d0).trans hd0
  have hNu : 0 ≤ Nu := (abs_nonneg nu).trans hn
  have hP : 0 ≤ P := (abs_nonneg rho).trans hp
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hyi : ∀ j, |y j| ≤ M := fun j => by simpa using (norm_le_pi_norm y j).trans hy
  fin_cases i <;> simp [dynamicIncrementData, Real.norm_eq_abs]
  all_goals linarith [hyi 0,hyi 1,hyi 2,hyi 3,hyi 4]

/-- Actual coefficient-data bounds follow from a state ball and bounded
nominal parameters. There is no assumption on derivative errors. -/
theorem dynamicDriftMap_uniform_consistency (r0 M D N : ℝ)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
      (mu theta : Vec d) (y : DynamicState),
      r mu=r0 → 0 < (p:ℝ) → 0 < B → 2 ≤ d → eta ≠ 0 →
      0 < 1-beta → 1-beta ≤ 1 → tameError p mu theta ≤ 1/2 →
      ‖theta‖^2=y 0^2+y 2 → ‖y‖ ≤ M →
      |eta*(p:ℝ)/(1-beta)| ≤ D → dynamicNoiseRate d B (1-beta) (p:ℝ) ≤ N →
      ‖dynamicDriftMap (B:=B) eta beta p mu theta y-
        (y+(1-beta) • dynamicField r0 (eta*(p:ℝ)/(1-beta)) (dynamicSourceLoad d B eta) y)‖ ≤
          C*(1-beta)*((1-beta)+tameError p mu theta) := by
  let E := Real.exp ((M^2+M)/2)
  let S := M+1+D+N+4*E+2+4+6*N+1
  obtain ⟨K,hK⟩ := dynamicDriftMap_consistency r0 S
  refine ⟨(K:ℝ)*(6*E+9+12*N),by positivity,?_⟩
  intro d B eta beta p mu theta y hr hp hB hd heta hh hh1 htame hgeom hy hdelta hk
  have he : 0 ≤ tameError p mu theta := hp.le.trans (tameError_ge_probability p mu theta)
  have hBr : 0 < (B:ℝ) := by exact_mod_cast hB
  have hdR : 0 ≤ (d-1:ℝ) := by
    have hd2 : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hk0 : 0 ≤ dynamicNoiseRate d B (1-beta) (p:ℝ) := by unfold dynamicNoiseRate; positivity
  have hka : |dynamicNoiseRate d B (1-beta) (p:ℝ)| ≤ N := by rw [abs_of_nonneg hk0]; exact hk
  have hha : |1-beta| ≤ 1 := by rw [abs_of_pos hh]; exact hh1
  have halpha : dynamicAlpha r0 y ≤ E := dynamicAlpha_le_closedBall r0 M y hM hy
  have halpha0 : 0 ≤ dynamicAlpha r0 y := (Real.exp_pos _).le
  have haeq : gaussianAlpha mu theta=dynamicAlpha r0 y := by
    rw [← hr]; exact (dynamicAlpha_of_geometry mu theta y hgeom).symm
  have hc := dynamic_normalized_coefficient_errors (B:=B) p mu theta (1-beta) hp hh.le hB hd htame
  rw [haeq] at hc
  have ha : |coefA p mu theta/(p:ℝ)| ≤ 4*E := by
    have hs := abs_add_le (coefA p mu theta/(p:ℝ)-dynamicAlpha r0 y) (dynamicAlpha r0 y)
    rw [sub_add_cancel, abs_of_nonneg halpha0] at hs
    nlinarith [hc.1]
  have hb : |coefB p mu theta/(p:ℝ)| ≤ 2 := by
    have hs := abs_sub (coefB p mu theta/(p:ℝ)+1) 1
    norm_num at hs
    nlinarith [hc.2.1]
  have hd0 : |coefD0 p mu theta/(p:ℝ)| ≤ 4 := by
    have hs := abs_add_le (coefD0 p mu theta/(p:ℝ)-1) 1
    norm_num at hs
    nlinarith [hc.2.2.1]
  have hn : |(1-beta)*coefDtheta p mu theta/((B:ℝ)*(p:ℝ)^2)| ≤ 6*N := by
    nlinarith [hc.2.2.2]
  have hrho : |((B:ℝ)-1)/(B:ℝ)| ≤ 1 := by
    have hB1 : (1:ℝ) ≤ B := by exact_mod_cast (Nat.succ_le_iff.mpr hB)
    rw [abs_of_nonneg (div_nonneg (by linarith) hBr.le)]
    apply (div_le_iff₀ hBr).mpr
    linarith
  have hq := data_norm_bound y (1-beta) (eta*(p:ℝ)/(1-beta))
    (dynamicNoiseRate d B (1-beta) (p:ℝ)) (coefA p mu theta/(p:ℝ)) (coefB p mu theta/(p:ℝ))
    (coefD0 p mu theta/(p:ℝ)) ((1-beta)*coefDtheta p mu theta/((B:ℝ)*(p:ℝ)^2))
    (((B:ℝ)-1)/(B:ℝ)) M 1 D N (4*E) 2 4 (6*N) 1
    hy hha hdelta hka ha hb hd0 hn hrho
  have hq0 := data_norm_bound y 0 (eta*(p:ℝ)/(1-beta))
    (dynamicNoiseRate d B (1-beta) (p:ℝ)) (dynamicAlpha r0 y) (-1) 1 0
    (((B:ℝ)-1)/(B:ℝ)) M 1 D N (4*E) 2 4 (6*N) 1
    hy (by norm_num) hdelta hka (by rw [abs_of_nonneg halpha0]; nlinarith)
    (by norm_num) (by norm_num) (by simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hN) hrho
  have hbnd := hK eta beta p mu theta y hr hp hB hd heta hh htame hgeom hq hq0
  apply hbnd.trans
  have hhK : 0 ≤ (1-beta)*(K:ℝ) := mul_nonneg hh.le K.coe_nonneg
  have hE : 0 ≤ E := (Real.exp_pos _).le
  calc
    _ ≤ (1-beta)*(K:ℝ)*((6*E+9+12*N)*((1-beta)+tameError p mu theta)) := by
      apply mul_le_mul_of_nonneg_left _ hhK
      have h1 : (6*dynamicAlpha r0 y+8+12*dynamicNoiseRate d B (1-beta) (p:ℝ))*tameError p mu theta ≤
          (6*E+8+12*N)*tameError p mu theta := by gcongr
      nlinarith
    _ = _ := by ring

end
end SparseSGD.Logistic
