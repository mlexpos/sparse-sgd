import SparseSGD.Logistic.PopulationLoss
import SparseSGD.Logistic.Drift
import SparseSGD.Logistic.TameCoefficients
import SparseSGD.Logistic.EquilibriumAnalysis

open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

/-- The potential whose derivative is the leading tame population gradient. -/
def gaussianLossApprox {d : ℕ} (p : unitInterval) (mu theta : Vec d) : ℝ :=
  (p : ℝ) * (gaussianAlpha mu theta-1-inner ℝ mu (theta-mu))

private theorem populationLoss_line_hasDerivAt {d : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (p : unitInterval)
    (mu theta v : Vec d) (t : ℝ) :
    HasDerivAt (fun t : ℝ => populationLoss p mu (theta+t • v))
      (coefA p mu (theta+t • v)*inner ℝ (theta+t • v) v+
        coefB p mu (theta+t • v)*inner ℝ mu v) t := by
  have ht : HasDerivAt (fun t : ℝ => theta+t • v) v t :=
    by simpa only [id_eq,one_smul] using
      (((hasDerivAt_id t).smul_const v).const_add theta)
  have h := (hasFDerivAt_populationLoss p mu (theta+t • v)).comp_hasDerivAt t ht
  convert h using 1
  · rfl
  · simp only [innerSL_apply_apply,populationGradient,gradient_integral H,
      inner_add_left,real_inner_smul_left]

private theorem gaussianLossApprox_line_hasDerivAt {d : ℕ} (p : unitInterval)
    (mu theta v : Vec d) (t : ℝ) :
    HasDerivAt (fun t : ℝ => gaussianLossApprox p mu (theta+t • v))
      ((p : ℝ)*(gaussianAlpha mu (theta+t • v)*inner ℝ (theta+t • v) v-inner ℝ mu v)) t := by
  have ht : HasDerivAt (fun t : ℝ => theta+t • v) v t :=
    by simpa only [id_eq,one_smul] using
      (((hasDerivAt_id t).smul_const v).const_add theta)
  have he := (((ht.norm_sq).sub_const (‖mu‖^2)).div_const 2).exp
  have hi := (innerSL ℝ mu).hasFDerivAt.comp_hasDerivAt t (ht.sub_const mu)
  have h := ((he.sub_const 1).sub hi).const_mul (p : ℝ)
  convert h using 1
  · rfl
  · simp only [innerSL_apply_apply,gaussianAlpha]
    ring

/-- A quantitative loss estimate from coefficient errors along the actual
straight parameter path. It is a theorem about the population integral,
not an assumed loss expansion. -/
theorem populationLoss_gaussianApprox_bound {d : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d)
    (p : unitInterval) (mu theta : Vec d) (A B : ℝ)
    (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hcoefA : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |coefA p mu (mu+t • (theta-mu))-(p : ℝ)*gaussianAlpha mu (mu+t • (theta-mu))| ≤ A)
    (hcoefB : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |coefB p mu (mu+t • (theta-mu))+(p : ℝ)| ≤ B) :
    |excessLoss p mu theta-gaussianLossApprox p mu theta| ≤
      A*(|inner ℝ mu (theta-mu)|+‖theta-mu‖^2)+B*|inner ℝ mu (theta-mu)| := by
  let v := theta-mu
  let z := fun t : ℝ => mu+t • v
  let F := fun t : ℝ => populationLoss p mu (z t)-gaussianLossApprox p mu (z t)
  let D := fun t : ℝ =>
    (coefA p mu (z t)-(p : ℝ)*gaussianAlpha mu (z t))*inner ℝ (z t) v +
      (coefB p mu (z t)+(p : ℝ))*inner ℝ mu v
  have hderiv : ∀ t, HasDerivAt F (D t) t := by
    intro t
    have h := (populationLoss_line_hasDerivAt H p mu mu v t).sub
      (gaussianLossApprox_line_hasDerivAt p mu mu v t)
    convert h using 1
    dsimp [D,z]
    ring
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖D t‖ ≤ A*(|inner ℝ mu v|+‖v‖^2)+B*|inner ℝ mu v| := by
    intro t ht
    have htcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1,ht.2.le⟩
    have ha := hcoefA t htcc
    have hb := hcoefB t htcc
    have hin : |inner ℝ (z t) v| ≤ |inner ℝ mu v|+‖v‖^2 := by
      dsimp [z]
      rw [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
      calc
        _ ≤ |inner ℝ mu v|+|t*‖v‖^2| := abs_add_le _ _
        _ ≤ _ := by
          rw [abs_mul,abs_of_nonneg ht.1,abs_pow,abs_of_nonneg (norm_nonneg v)]
          exact add_le_add le_rfl (mul_le_of_le_one_left (sq_nonneg ‖v‖) ht.2.le)
    rw [Real.norm_eq_abs]
    dsimp [D]
    calc
      _ ≤ |(coefA p mu (z t)-(p : ℝ)*gaussianAlpha mu (z t))*inner ℝ (z t) v|+
          |(coefB p mu (z t)+(p : ℝ))*inner ℝ mu v| := abs_add_le _ _
      _ ≤ A*(|inner ℝ mu v|+‖v‖^2)+B*|inner ℝ mu v| := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul ha hin (abs_nonneg _) hA)
          (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hderiv t).hasDerivWithinAt) hbound
  have h0 : gaussianLossApprox p mu mu = 0 := by
    simp [gaussianLossApprox,gaussianAlpha]
  dsimp only [F,z] at h
  simp only [zero_smul,add_zero,one_smul,h0,sub_zero,Real.norm_eq_abs] at h
  have hz1 : mu+v = theta := by dsimp [v]; abel
  rw [hz1] at h
  unfold excessLoss
  convert h using 1
  congr 1
  ring

/-- A uniform bound for the actual tame error on a bounded parameter domain. -/
def populationTameConstant (M : ℝ) : ℝ :=
  Real.exp (2*M^2)+Real.exp (3*M^2/2)+(1+Real.exp (M^2/2))*Real.exp (M^2)

theorem populationTameConstant_pos (M : ℝ) : 0 < populationTameConstant M := by
  unfold populationTameConstant
  positivity

private theorem parameter_line_norm_bound {d : ℕ} (mu theta : Vec d) (M t : ℝ)
    (hmu : ‖mu‖ ≤ M) (htheta : ‖theta‖ ≤ M) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖mu+t • (theta-mu)‖ ≤ M := by
  have heq : mu+t • (theta-mu) = (1-t) • mu+t • theta := by module
  rw [heq]
  calc
    _ ≤ ‖(1-t) • mu‖+‖t • theta‖ := norm_add_le _ _
    _ = (1-t)*‖mu‖+t*‖theta‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1,
        abs_of_nonneg (sub_nonneg.mpr ht.2)]
    _ ≤ (1-t)*M+t*M := add_le_add
      (mul_le_mul_of_nonneg_left hmu (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left htheta ht.1)
    _ = M := by ring

private theorem tameError_bounded_domain {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (M : ℝ) (hM : 0 ≤ M) (hmu : ‖mu‖ ≤ M) (htheta : ‖theta‖ ≤ M) :
    tameError p mu theta ≤ (p : ℝ)*populationTameConstant M := by
  have hs : ‖theta‖^2 ≤ M^2 := by nlinarith [norm_nonneg theta]
  have hinner : |inner ℝ theta mu| ≤ M^2 := by
    have h := norm_inner_le_norm (𝕜 := ℝ) theta mu
    rw [Real.norm_eq_abs] at h
    exact h.trans (by nlinarith [mul_le_mul htheta hmu (norm_nonneg mu) hM])
  unfold tameError populationTameConstant
  apply mul_le_mul_of_nonneg_left _ p.property.1
  apply add_le_add
  · exact add_le_add (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖mu‖]))
      (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖mu‖]))
  · apply mul_le_mul
    · apply add_le_add le_rfl
      unfold gaussianAlpha
      exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖mu‖])
    · exact Real.exp_le_exp.mpr hinner
    · exact (Real.exp_pos _).le
    · positivity

/-- Tame asymptotics for the actual population loss, with the actual endpoint
`epsilon_B` retained. The bounded-domain smallness condition guarantees
that the whole interpolation path is tame. -/
theorem populationLoss_tame_approximation {d : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d)
    (p : unitInterval) (mu theta : Vec d) (M : ℝ) (hM : 0 ≤ M)
    (hp0 : 0 < (p : ℝ)) (hmu : ‖mu‖ ≤ M) (htheta : ‖theta‖ ≤ M)
    (htame : (p : ℝ)*populationTameConstant M ≤ 1/2) :
    |excessLoss p mu theta-gaussianLossApprox p mu theta| ≤
      ((6*Real.exp (M^2/2)+2)*populationTameConstant M) *
        (p : ℝ)*tameError p mu theta *
        (|inner ℝ mu (theta-mu)|+‖theta-mu‖^2) := by
  let E := Real.exp (M^2/2)
  let K := populationTameConstant M
  let e := (p : ℝ)*K
  have hE : 0 < E := Real.exp_pos _
  have hK : 0 < K := populationTameConstant_pos M
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |coefA p mu (mu+t • (theta-mu))-(p : ℝ)*gaussianAlpha mu (mu+t • (theta-mu))| ≤
        6*(p : ℝ)*E*e ∧ |coefB p mu (mu+t • (theta-mu))+(p : ℝ)| ≤ 2*(p : ℝ)*e := by
    intro t ht
    have hn := parameter_line_norm_bound mu theta M t hmu htheta ht
    have herr := tameError_bounded_domain p mu (mu+t • (theta-mu)) M hM hmu hn
    have htame' : tameError p mu (mu+t • (theta-mu)) ≤ 1/2 := herr.trans htame
    have hc := tame_coefficients p mu (mu+t • (theta-mu)) hp0 htame'
    have halpha : gaussianAlpha mu (mu+t • (theta-mu)) ≤ E := by
      unfold gaussianAlpha E
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg ‖mu‖,norm_nonneg (mu+t • (theta-mu))]
    constructor
    · apply hc.1.trans
      exact mul_le_mul (mul_le_mul_of_nonneg_left halpha (by positivity)) herr
        (p.property.1.trans (tameError_ge_probability p mu _)) (by positivity)
    · exact hc.2.1.trans (mul_le_mul_of_nonneg_left herr (by positivity))
  have h := populationLoss_gaussianApprox_bound H p mu theta (6*(p : ℝ)*E*e) (2*(p : ℝ)*e)
    (by positivity) (by positivity) (fun t ht => (hpath t ht).1) (fun t ht => (hpath t ht).2)
  apply h.trans
  have hprob := tameError_ge_probability p mu theta
  have hsize : |inner ℝ mu (theta-mu)| ≤ |inner ℝ mu (theta-mu)|+‖theta-mu‖^2 :=
    le_add_of_nonneg_right (sq_nonneg _)
  have hmain := mul_le_mul_of_nonneg_left hprob
    (show 0 ≤ (6*E+2)*K*(p : ℝ)*(|inner ℝ mu (theta-mu)|+‖theta-mu‖^2) by positivity)
  have hinner := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 2*(p : ℝ)*e by positivity)
  dsimp [e,E,K] at hmain hinner ⊢
  nlinarith only [hmain,hinner]

/-- The loss path estimate needs only a probability bound; the actual tame
remainder can be large on the path, because it is kept in the error bound. -/
theorem populationLoss_probability_path_approximation {d : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d)
    (p : unitInterval) (mu theta : Vec d) (E eps : ℝ)
    (hp0 : 0 < (p : ℝ)) (hphalf : (p : ℝ) ≤ 1/2)
    (hE : 0 ≤ E) (heps : 0 ≤ eps)
    (hpathA : ∀ t ∈ Set.Icc (0 : ℝ) 1, gaussianAlpha mu (mu+t • (theta-mu)) ≤ E)
    (hpathE : ∀ t ∈ Set.Icc (0 : ℝ) 1, tameError p mu (mu+t • (theta-mu)) ≤ eps) :
    |excessLoss p mu theta-gaussianLossApprox p mu theta| ≤
      (6*E+2)*(p : ℝ)*eps*(|inner ℝ mu (theta-mu)|+‖theta-mu‖^2) := by
  have hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |coefA p mu (mu+t • (theta-mu))-(p : ℝ)*gaussianAlpha mu (mu+t • (theta-mu))| ≤ 6*(p : ℝ)*E*eps ∧
      |coefB p mu (mu+t • (theta-mu))+(p : ℝ)| ≤ 2*(p : ℝ)*eps := by
    intro t ht
    have hc := tame_coefficients_of_probability_le_half p mu (mu+t • (theta-mu)) hp0 hphalf
    constructor
    · exact hc.1.trans (mul_le_mul (mul_le_mul_of_nonneg_left (hpathA t ht) (by positivity))
        (hpathE t ht) (p.property.1.trans (tameError_ge_probability p mu _)) (by positivity))
    · exact hc.2.1.trans (mul_le_mul_of_nonneg_left (hpathE t ht) (by positivity))
  have h := populationLoss_gaussianApprox_bound H p mu theta (6*(p : ℝ)*E*eps) (2*(p : ℝ)*eps)
    (by positivity) (by positivity) (fun t ht => (hpath t ht).1) (fun t ht => (hpath t ht).2)
  apply h.trans
  have hs : |inner ℝ mu (theta-mu)| ≤ |inner ℝ mu (theta-mu)|+‖theta-mu‖^2 :=
    le_add_of_nonneg_right (sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*(p : ℝ)*eps by positivity)
  nlinarith only [hb]

end
end SparseSGD.Logistic
