import SparseSGD.Logistic.ScalarCoefficients
import SparseSGD.Logistic.TameDerivativeBounds

open SparseSGD.Probability
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

def scalarJetFactor {d : ℕ} (a b : ℕ) (mu : Vec d) : ℝ := (r mu)^a * (1/2 : ℝ)^b

theorem scalarJetFactor_nonneg {d : ℕ} (a b : ℕ) (mu : Vec d) : 0 ≤ scalarJetFactor a b mu := by
  unfold scalarJetFactor r
  positivity

theorem scalarJetFactor_le {d : ℕ} (a b : ℕ) (mu : Vec d) :
    scalarJetFactor a b mu ≤ (1+r mu)^(a+b) := by
  have hr : 0 ≤ r mu := norm_nonneg mu
  have hhalf : (1/2 : ℝ)^b ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp : (r mu)^a ≤ (1+r mu)^a := pow_le_pow_left₀ hr (by linarith) a
  have h1 : (1 : ℝ) ≤ (1+r mu)^b := one_le_pow₀ (by linarith)
  unfold scalarJetFactor
  calc
    _ ≤ (r mu)^a * 1 := mul_le_mul_of_nonneg_left hhalf (pow_nonneg hr a)
    _ ≤ (1+r mu)^a * (1+r mu)^b := mul_le_mul hp h1 (by norm_num) (by positivity)
    _ = _ := (pow_add _ _ _).symm

private theorem factor_abs_bound {f z C u : ℝ} (hf : 0 ≤ f) (h : |u| ≤ C*z) :
    |f*u| ≤ C*f*z := by
  rw [abs_mul, abs_of_nonneg hf]
  calc
    f*|u| ≤ f*(C*z) := mul_le_mul_of_nonneg_left h hf
    _ = _ := by ring

/-- Pure variance derivatives of A retain the leading `(1/2)^b p α` term. -/
theorem tame_scalarCoefA_variance_jet (b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d : ℕ} (p : unitInterval) (mu theta : Vec d),
      0 < r mu → 0 < (p : ℝ) → tameError p mu theta ≤ 1/2 →
      |scalarCoefAJet 0 b p (r mu) (signalCoord mu theta) (‖theta‖^2) -
        (1/2 : ℝ)^b * (p : ℝ) * gaussianAlpha mu theta| ≤
        C*(1/2 : ℝ)^b*(p : ℝ)*gaussianAlpha mu theta*tameError p mu theta := by
  obtain ⟨C,hC,h⟩ := tame_sigma_mixture_derivative (1+0+2*b)
  refine ⟨C,hC,fun {d} p mu theta hr hp ht => ?_⟩
  unfold scalarCoefAJet
  rw [scalarGaussianJet_eq_actual _ _ _ _ _ p mu theta hr]
  simp only [pow_zero, one_mul, ite_true]
  rw [show (1/2 : ℝ)^b * ((1-(p : ℝ))*gaussianAverage (sigmaDerivative (1+0+2*b))
      (bias p mu) (‖theta‖^2)+(p : ℝ)*gaussianAverage (sigmaDerivative (1+0+2*b))
      (inner ℝ theta mu+bias p mu) (‖theta‖^2)) - (1/2 : ℝ)^b*(p : ℝ)*gaussianAlpha mu theta =
      (1/2 : ℝ)^b * ((1-(p : ℝ))*gaussianAverage (sigmaDerivative (1+0+2*b))
      (bias p mu) (‖theta‖^2)+(p : ℝ)*gaussianAverage (sigmaDerivative (1+0+2*b))
      (inner ℝ theta mu+bias p mu) (‖theta‖^2)-(p : ℝ)*gaussianAlpha mu theta) by ring]
  have hh := factor_abs_bound (by positivity : 0 ≤ (1/2 : ℝ)^b) (h p mu theta hp ht)
  convert hh using 1 <;> (try simp only [scalarJetFactor]) <;> ring

theorem tame_scalarCoefA_signal_jet (a b : ℕ) (ha : a ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d : ℕ} (p : unitInterval) (mu theta : Vec d),
      0 < r mu → 0 < (p : ℝ) → tameError p mu theta ≤ 1/2 →
      |scalarCoefAJet a b p (r mu) (signalCoord mu theta) (‖theta‖^2)| ≤
        C*scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta := by
  obtain ⟨C,hC,h⟩ := tame_sigma_positive_derivative (1+a+2*b)
  refine ⟨C,hC,fun {d} p mu theta hr hp ht => ?_⟩
  unfold scalarCoefAJet
  rw [scalarGaussianJet_eq_actual _ _ _ _ _ p mu theta hr]
  simp only [ha, ite_false, zero_add]
  have hh := factor_abs_bound (scalarJetFactor_nonneg a b mu) (h p mu theta hp ht)
  simp only [scalarJetFactor] at hh
  convert hh using 1 <;> (try simp only [scalarJetFactor]) <;> ring

theorem tame_scalarCoefB_jet (a b : ℕ) (hab : a+b ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d : ℕ} (p : unitInterval) (mu theta : Vec d),
      0 < r mu → 0 < (p : ℝ) → tameError p mu theta ≤ 1/2 →
      |scalarCoefBJet a b p (r mu) (signalCoord mu theta) (‖theta‖^2)| ≤
        C*scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta := by
  obtain ⟨C,hC,h⟩ := tame_sigma_positive_derivative (0+a+2*b)
  refine ⟨C,hC,fun {d} p mu theta hr hp ht => ?_⟩
  simp only [scalarCoefBJet, hab, ite_false, sub_zero]
  rw [scalarGaussianJet_eq_actual _ _ _ _ _ p mu theta hr]
  simp only [scalar_gaussianAverage_zero, mul_zero, ite_self, zero_add]
  have hh := factor_abs_bound (scalarJetFactor_nonneg a b mu) (h p mu theta hp ht)
  simp only [scalarJetFactor] at hh
  convert hh using 1 <;> (try simp only [scalarJetFactor]) <;> ring

theorem tame_scalarSquareJet (base a b : ℕ) (hn : base+a+2*b ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d : ℕ} (p : unitInterval) (mu theta : Vec d),
      0 < r mu → 0 < (p : ℝ) → tameError p mu theta ≤ 1/2 →
      |scalarGaussianJet sigmaSquareDerivative oneMinusSigmaSquareDerivative base a b
        p (r mu) (signalCoord mu theta) (‖theta‖^2)| ≤
        C*scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta := by
  obtain ⟨C,hC,h⟩ := tame_square_mixture_derivative (base+a+2*b) hn
  obtain ⟨D,hD,h'⟩ := tame_square_positive_derivative (base+a+2*b) hn
  refine ⟨C+D,by positivity,fun {d} p mu theta hr hp ht => ?_⟩
  rw [scalarGaussianJet_eq_actual _ _ _ _ _ p mu theta hr]
  have hz : 0 ≤ scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta := by
    exact mul_nonneg (mul_nonneg (scalarJetFactor_nonneg a b mu) hp.le) (p.property.1.trans (tameError_ge_probability p mu theta))
  by_cases ha : a = 0
  · simp only [ha, ite_true]
    have hh := factor_abs_bound (scalarJetFactor_nonneg a b mu) (h p mu theta hp ht)
    simp only [scalarJetFactor] at hh
    have he : |((r mu)^a*(1/2 : ℝ)^b)*((1-(p : ℝ))*gaussianAverage (sigmaSquareDerivative (base+a+2*b))
        (bias p mu) (‖theta‖^2)+(p : ℝ)*gaussianAverage (oneMinusSigmaSquareDerivative (base+a+2*b))
        (inner ℝ theta mu+bias p mu) (‖theta‖^2))| ≤
        C*scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta := by
      convert hh using 1 <;> (try simp only [scalarJetFactor]) <;> ring
    have he' : C*scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta ≤
        (C+D)*scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta := by nlinarith [mul_nonneg hD hz]
    simpa only [ha] using he.trans he'
  · simp only [ha, ite_false, zero_add]
    have hh := factor_abs_bound (scalarJetFactor_nonneg a b mu) (h' p mu theta hp ht)
    simp only [scalarJetFactor] at hh
    have he : |((r mu)^a*(1/2 : ℝ)^b)*((p : ℝ)*gaussianAverage
        (oneMinusSigmaSquareDerivative (base+a+2*b)) (inner ℝ theta mu+bias p mu) (‖theta‖^2))| ≤
        D*scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta := by convert hh using 1 <;> (try simp only [scalarJetFactor]) <;> ring
    exact he.trans (by nlinarith [mul_nonneg hC hz])

theorem tame_scalarCoefD0_jet (a b : ℕ) (hab : a+b ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d : ℕ} (p : unitInterval) (mu theta : Vec d),
      0 < r mu → 0 < (p : ℝ) → tameError p mu theta ≤ 1/2 →
      |scalarCoefD0Jet a b p (r mu) (signalCoord mu theta) (‖theta‖^2)| ≤
        C*scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta :=
  tame_scalarSquareJet 0 a b (by omega)

theorem tame_scalarCoefDtheta_jet (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d : ℕ} (p : unitInterval) (mu theta : Vec d),
      0 < r mu → 0 < (p : ℝ) → tameError p mu theta ≤ 1/2 →
      |scalarCoefDthetaJet a b p (r mu) (signalCoord mu theta) (‖theta‖^2)| ≤
        C*scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta :=
  tame_scalarSquareJet 2 a b (by omega)

/-- All actual jet estimates. The pure-q A derivatives keep their exponential
main term; signal derivatives and the other coefficient derivatives are small. -/
def TameScalarJetBounds {d : ℕ} (a b : ℕ) (C : ℝ) (p : unitInterval) (mu theta : Vec d) : Prop :=
  |scalarCoefAJet a b p (r mu) (signalCoord mu theta) (‖theta‖^2) -
    (if a = 0 then scalarJetFactor a b mu*(p : ℝ)*gaussianAlpha mu theta else 0)| ≤
    C*scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta*(if a = 0 then gaussianAlpha mu theta else 1) ∧
  |scalarCoefBJet a b p (r mu) (signalCoord mu theta) (‖theta‖^2)| ≤
    C*scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta ∧
  |scalarCoefD0Jet a b p (r mu) (signalCoord mu theta) (‖theta‖^2)| ≤
    C*scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta ∧
  |scalarCoefDthetaJet a b p (r mu) (signalCoord mu theta) (‖theta‖^2)| ≤
    C*scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta

private theorem tame_A_jet_all (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d : ℕ} (p : unitInterval) (mu theta : Vec d),
      0 < r mu → 0 < (p : ℝ) → tameError p mu theta ≤ 1/2 →
      |scalarCoefAJet a b p (r mu) (signalCoord mu theta) (‖theta‖^2) -
        (if a = 0 then scalarJetFactor a b mu*(p : ℝ)*gaussianAlpha mu theta else 0)| ≤
        C*scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta*(if a = 0 then gaussianAlpha mu theta else 1) := by
  by_cases ha : a = 0
  · subst a
    obtain ⟨C,hC,h⟩ := tame_scalarCoefA_variance_jet b
    refine ⟨C,hC,fun {d} p mu theta hr hp ht => ?_⟩
    simpa only [scalarJetFactor, pow_zero, one_mul, ite_true, mul_assoc,
      mul_comm (tameError p mu theta) (gaussianAlpha mu theta)] using h p mu theta hr hp ht
  · obtain ⟨C,hC,h⟩ := tame_scalarCoefA_signal_jet a b ha
    refine ⟨C,hC,fun {d} p mu theta hr hp ht => ?_⟩
    simpa only [ha, ite_false, sub_zero, mul_one] using h p mu theta hr hp ht

private theorem tameJetBounds_mono {d : ℕ} {a b : ℕ} {C D : ℝ} {p : unitInterval} {mu theta : Vec d}
    (hCD : C ≤ D) (h : TameScalarJetBounds a b C p mu theta) : TameScalarJetBounds a b D p mu theta := by
  have hz : 0 ≤ scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta :=
    mul_nonneg (mul_nonneg (scalarJetFactor_nonneg a b mu) p.property.1)
      (p.property.1.trans (tameError_ge_probability p mu theta))
  have halpha : 0 ≤ (if a = 0 then gaussianAlpha mu theta else (1 : ℝ)) := by
    split_ifs
    · exact (gaussianAlpha_pos mu theta).le
    · norm_num
  rcases h with ⟨hA,hB,hD0,hDtheta⟩
  refine ⟨hA.trans ?_,hB.trans ?_,hD0.trans ?_,hDtheta.trans ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hCD (mul_nonneg hz halpha)]
  all_goals nlinarith [mul_le_mul_of_nonneg_right hCD hz]

/-- For each derivative multi-index, the constant is universal over dimensions
and all actual tame states. This includes every mixed derivative order. -/
theorem tame_scalarJets (a b : ℕ) (hab : a+b ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d : ℕ} (p : unitInterval) (mu theta : Vec d),
      0 < r mu → 0 < (p : ℝ) → tameError p mu theta ≤ 1/2 → TameScalarJetBounds a b C p mu theta := by
  obtain ⟨A,hA,HA⟩ := tame_A_jet_all a b
  obtain ⟨B,hB,HB⟩ := tame_scalarCoefB_jet a b hab
  obtain ⟨D,hD,HD⟩ := tame_scalarCoefD0_jet a b hab
  obtain ⟨T,hT,HT⟩ := tame_scalarCoefDtheta_jet a b
  refine ⟨A+B+D+T,by positivity,fun {d} p mu theta hr hp ht => ?_⟩
  have hz : 0 ≤ scalarJetFactor a b mu*(p : ℝ)*tameError p mu theta :=
    mul_nonneg (mul_nonneg (scalarJetFactor_nonneg a b mu) hp.le)
      (p.property.1.trans (tameError_ge_probability p mu theta))
  have halpha : 0 ≤ (if a = 0 then gaussianAlpha mu theta else (1 : ℝ)) := by
    split_ifs
    · exact (gaussianAlpha_pos mu theta).le
    · norm_num
  refine ⟨(HA p mu theta hr hp ht).trans ?_, (HB p mu theta hr hp ht).trans ?_,
    (HD p mu theta hr hp ht).trans ?_, (HT p mu theta hr hp ht).trans ?_⟩
  · nlinarith [mul_nonneg (by positivity : 0 ≤ B+D+T) (mul_nonneg hz halpha)]
  · nlinarith [mul_nonneg (by positivity : 0 ≤ A+D+T) hz]
  · nlinarith [mul_nonneg (by positivity : 0 ≤ A+B+T) hz]
  · nlinarith [mul_nonneg (by positivity : 0 ≤ A+B+D) hz]

/-- A single absolute constant controls all first and second partial
derivatives of all four coefficients, in every dimension. In particular the
leading terms of A_q and A_qq are `(1/2)p α` and `(1/4)p α`. -/
theorem tame_scalarJets_first_second :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℕ, 1 ≤ a+b → a+b ≤ 2 →
      ∀ {d : ℕ} (p : unitInterval) (mu theta : Vec d),
        0 < r mu → 0 < (p : ℝ) → tameError p mu theta ≤ 1/2 → TameScalarJetBounds a b C p mu theta := by
  classical
  have hex (i : Fin 3 × Fin 3) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ {d : ℕ} (p : unitInterval) (mu theta : Vec d),
        0 < r mu → 0 < (p : ℝ) → tameError p mu theta ≤ 1/2 →
          i.1.val+i.2.val ≠ 0 → TameScalarJetBounds i.1.val i.2.val C p mu theta := by
    by_cases hi : i.1.val+i.2.val = 0
    · exact ⟨0,le_rfl,fun _ _ _ _ _ _ h => (h hi).elim⟩
    · obtain ⟨C,hC,h⟩ := tame_scalarJets i.1.val i.2.val hi
      exact ⟨C,hC,fun p mu theta hr hp ht _ => h p mu theta hr hp ht⟩
  choose c hc hbound using hex
  refine ⟨∑ i, c i, Finset.sum_nonneg (fun i _ => hc i), ?_⟩
  intro a b hab hab2 d p mu theta hr hp ht
  let i : Fin 3 × Fin 3 := (⟨a,by omega⟩,⟨b,by omega⟩)
  have hci : c i ≤ ∑ i, c i := Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)
  exact tameJetBounds_mono hci (hbound i p mu theta hr hp ht (by dsimp [i]; omega))

end
end SparseSGD.Logistic
