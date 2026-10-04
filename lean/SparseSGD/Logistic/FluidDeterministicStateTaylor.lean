import SparseSGD.Logistic.FluidDeterministicScalarTaylor
import SparseSGD.Logistic.FluidDeterministicPhysical
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000

def matchedScalarState (i : Fin 4) (p : unitInterval) (r : ℝ) (y : Fin 5 → ℝ) : ℝ :=
  matchedScalarJet i 0 0 p r (y 0) ((y 0)^2+y 2)

def matchedScalarStateDerivative (i : Fin 4) (p : unitInterval) (r : ℝ)
    (y : Fin 5 → ℝ) : (Fin 5 → ℝ) →L[ℝ] ℝ :=
  (matchedScalarJet i 1 0 p r (y 0) ((y 0)^2+y 2)+
      2*y 0*matchedScalarJet i 0 1 p r (y 0) ((y 0)^2+y 2)) • ContinuousLinearMap.proj 0 +
    (matchedScalarJet i 0 1 p r (y 0) ((y 0)^2+y 2)) • ContinuousLinearMap.proj 2

private theorem matchedPhysical_variance_bound (y : Fin 5 → ℝ) (M : ℝ)
    (hy : matchedPhysical y) (hyn : ‖y‖≤M) :
    0≤(y 0)^2+y 2 ∧ (y 0)^2+y 2≤M^2+M := by
  have h0 : |y 0|≤M := by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y 0).trans hyn
  have h2 : |y 2|≤M := by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y 2).trans hyn
  exact ⟨matchedPhysical_variance hy,by nlinarith [(abs_le.mp h0).1,(abs_le.mp h0).2,le_abs_self (y 2)]⟩

/-- Actual coefficient Taylor estimates along physical Gram segments and a
bounded matched-state tube. Constants retain their O(p) scale. -/
theorem matchedScalarState_taylor_bound
    (S : SparseSGD.External.GaussianSteinCertificate 1) (r M : ℝ) (hM : 0≤M) :
    ∃ C : ℝ, 0≤C ∧ ∀ (i : Fin 4) (p : unitInterval) (x y : Fin 5 → ℝ),
      0<(p:ℝ) → (p:ℝ)≤1/2 → matchedPhysical x → matchedPhysical y →
      ‖x‖≤M → ‖y‖≤M →
      ‖matchedScalarStateDerivative i p r x‖≤C*(p:ℝ) ∧
      |matchedScalarState i p r y-matchedScalarState i p r x-
        matchedScalarStateDerivative i p r x (y-x)|≤C*(p:ℝ)*‖y-x‖^2 := by
  obtain ⟨Cj,hCj,hj⟩ := matchedScalarJet_uniform_bound r (M^2+M)
  obtain ⟨Ct,hCt,ht⟩ := matchedScalarJet_rectangle_taylor S r (M^2+M)
  let C := Cj*(2*M+2)+(Ct*(2*M+2)^2+Cj)
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro i p x y hp hh hx hy hxn hyn
  have hxq := matchedPhysical_variance_bound x M hx hxn
  have hyq := matchedPhysical_variance_bound y M hy hyn
  have hx0 : |x 0|≤M := by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x 0).trans hxn
  have hy0 : |y 0|≤M := by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y 0).trans hyn
  have hj10 := hj i 1 0 p (x 0) ((x 0)^2+x 2) hp hh hxq.1 hxq.2
  have hj01 := hj i 0 1 p (x 0) ((x 0)^2+x 2) hp hh hxq.1 hxq.2
  change |matchedScalarJet i 1 0 p r (x 0) ((x 0)^2+x 2)|≤Cj*(p:ℝ) at hj10
  change |matchedScalarJet i 0 1 p r (x 0) ((x 0)^2+x 2)|≤Cj*(p:ℝ) at hj01
  have hd : ‖matchedScalarStateDerivative i p r x‖≤Cj*(2*M+2)*(p:ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have hv0 : |v 0|≤‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0
    have hv2 : |v 2|≤‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 2
    have hinner : |matchedScalarJet i 1 0 p r (x 0) ((x 0)^2+x 2)+
        2*x 0*matchedScalarJet i 0 1 p r (x 0) ((x 0)^2+x 2)|≤Cj*(p:ℝ)*(1+2*M) := by
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
      have H := mul_le_mul_of_nonneg_left (mul_le_mul hx0 hj01 (abs_nonneg _) hM) (by norm_num : (0:ℝ)≤2)
      nlinarith
    change |(matchedScalarJet i 1 0 p r (x 0) ((x 0)^2+x 2)+
      2*x 0*matchedScalarJet i 0 1 p r (x 0) ((x 0)^2+x 2))*v 0+
        matchedScalarJet i 0 1 p r (x 0) ((x 0)^2+x 2)*v 2|≤_
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    have H0 := mul_le_mul hinner hv0 (abs_nonneg _) (by positivity : 0≤Cj*(p:ℝ)*(1+2*M))
    have H2 := mul_le_mul hj01 hv2 (abs_nonneg _) (by positivity : 0≤Cj*(p:ℝ))
    nlinarith
  have hdC : Cj*(2*M+2)≤C := by dsimp [C]; nlinarith [sq_nonneg (2*M+2)]
  have htC : Ct*(2*M+2)^2+Cj≤C := by dsimp [C]; nlinarith
  refine ⟨hd.trans (mul_le_mul_of_nonneg_right hdC p.property.1),?_⟩
  have hdx : |y 0-x 0|≤‖y-x‖ := by simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (y-x) 0
  have hdR : |y 2-x 2|≤‖y-x‖ := by simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (y-x) 2
  have H := variance_lift_taylor_bound (matchedScalarJet i 0 0 p r)
    (matchedScalarJet i 1 0 p r (x 0) ((x 0)^2+x 2))
    (matchedScalarJet i 0 1 p r (x 0) ((x 0)^2+x 2))
    (x 0) (y 0) (x 2) (y 2) M (Ct*(p:ℝ)) (Cj*(p:ℝ)) ‖y-x‖ hM
    (mul_nonneg hCt p.property.1) (mul_nonneg hCj p.property.1) hx0 hy0 hdx hdR hj01
    (ht i p (x 0) (y 0) ((x 0)^2+x 2) ((y 0)^2+y 2) hp hh hxq.1 hyq.1 hxq.2 hyq.2)
  have H' : (Ct*(p:ℝ)*(2*M+2)^2+Cj*(p:ℝ))*‖y-x‖^2≤C*(p:ℝ)*‖y-x‖^2 := by
    have Hb := mul_le_mul_of_nonneg_right htC (mul_nonneg p.property.1 (sq_nonneg ‖y-x‖))
    convert Hb using 1 <;> ring
  convert H.trans H' using 1
  congr 1
  simp [matchedScalarState,matchedScalarStateDerivative]
  ring
def matchedNormalizedScalarState (i : Fin 4) (p : unitInterval) (r : ℝ)
    (y : Fin 5→ℝ) : ℝ := matchedScalarState i p r y/(p:ℝ)

def matchedNormalizedScalarDerivative (i : Fin 4) (p : unitInterval) (r : ℝ)
    (y : Fin 5→ℝ) : (Fin 5→ℝ) →L[ℝ] ℝ :=
  (p:ℝ)⁻¹ • matchedScalarStateDerivative i p r y

/-- Values, first jets and quadratic remainders of all normalized actual
coefficients are uniformly bounded on a physical matched-state tube. -/
theorem matchedNormalizedScalar_controls
    (S : SparseSGD.External.GaussianSteinCertificate 1) (r M : ℝ) (hM : 0≤M) :
    ∃ C : ℝ, 0≤C ∧ ∀ (i : Fin 4) (p : unitInterval) (x y : Fin 5→ℝ),
      0<(p:ℝ) → (p:ℝ)≤1/2 → matchedPhysical x → matchedPhysical y →
      ‖x‖≤M → ‖y‖≤M →
      |matchedNormalizedScalarState i p r x|≤C ∧
      ‖matchedNormalizedScalarDerivative i p r x‖≤C ∧
      |matchedNormalizedScalarState i p r y-matchedNormalizedScalarState i p r x-
        matchedNormalizedScalarDerivative i p r x (y-x)|≤C*‖y-x‖^2 := by
  obtain ⟨Cs,hCs,hs⟩ := matchedScalarState_taylor_bound S r M hM
  obtain ⟨Cv,hCv,hv⟩ := matchedScalarJet_uniform_bound r (M^2+M)
  refine ⟨Cs+Cv,add_nonneg hCs hCv,?_⟩
  intro i p x y hp hh hx hy hxn hyn
  have hq := matchedPhysical_variance_bound x M hx hxn
  have hvalue := hv i 0 0 p (x 0) ((x 0)^2+x 2) hp hh hq.1 hq.2
  have hj := hs i p x y hp hh hx hy hxn hyn
  have hvalue' : |matchedScalarState i p r x|≤Cv*(p:ℝ) := by simpa [matchedScalarState] using hvalue
  refine ⟨?_,?_,?_⟩
  · unfold matchedNormalizedScalarState
    rw [abs_div,abs_of_pos hp]
    exact ((div_le_iff₀ hp).mpr hvalue').trans (by linarith)
  · unfold matchedNormalizedScalarDerivative
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),← div_eq_inv_mul]
    exact ((div_le_iff₀ hp).mpr hj.1).trans (by linarith)
  · have he : matchedNormalizedScalarState i p r y-matchedNormalizedScalarState i p r x-
        matchedNormalizedScalarDerivative i p r x (y-x) =
        (matchedScalarState i p r y-matchedScalarState i p r x-
          matchedScalarStateDerivative i p r x (y-x))/(p:ℝ) := by
      simp [matchedNormalizedScalarState,matchedNormalizedScalarDerivative,div_eq_mul_inv]
      ring
    rw [he,abs_div,abs_of_pos hp]
    have H : |matchedScalarState i p r y-matchedScalarState i p r x-
      matchedScalarStateDerivative i p r x (y-x)|/(p:ℝ)≤Cs*‖y-x‖^2 := by
      apply (div_le_iff₀ hp).mpr
      convert hj.2 using 1 <;> ring
    exact H.trans (mul_le_mul_of_nonneg_right (by linarith : Cs≤Cs+Cv) (sq_nonneg _))
end
end SparseSGD.Logistic
