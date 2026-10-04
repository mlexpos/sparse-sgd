import SparseSGD.Logistic.PopulationApproximation
import SparseSGD.Logistic.PopulationCalculus
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1200000

private theorem equilibrium_scalar_potential_error (r Phi t R : ℝ) (hr : 0 < r)
    (hPhi : 0 ≤ Phi) (hPhi1 : Phi ≤ 1) (ht : 0 < t)
    (hf : slowField r Phi t R = (0,0)) :
    |alpha t R r-1+r*(r-t)-Phi/2| ≤ (2+r^2)*Phi^2 := by
  let L := Real.log (alpha t R r)
  have hl := equilibrium_log_alpha_bounds r Phi t R hr hPhi ht hf
  have hL0 : 0 ≤ L := hl.1
  have hL1 : L ≤ 1 := by dsimp [L]; linarith [hl.2]
  have hLphi : L ≤ Phi/2 := hl.2
  have hexp : Real.exp L = alpha t R r := Real.exp_log (Real.exp_pos _)
  have hrem := Real.exp_bound (n := 2) (show |L| ≤ 1 by rw [abs_of_nonneg hL0]; exact hL1) (by norm_num)
  norm_num [Finset.sum_range_succ] at hrem
  have hrem' : |alpha t R r-1-L| ≤ 3/4*L^2 := by
    rw [hexp] at hrem
    convert hrem using 1
    · congr 1
      ring
    · ring
  have hroot := ((slowField_zero_iff r Phi t R hr ht).1 hf).1
  have htr := positive_root_le_r r Phi t hr hPhi ht hroot
  have hgap : r-t ≤ r*L := by
    have hs := equilibrium_signal_exp_log r Phi t R hf
    have he := Real.one_sub_le_exp_neg L
    change t = r*Real.exp (-L) at hs
    nlinarith [mul_le_mul_of_nonneg_left he hr.le]
  have hgap0 : 0 ≤ r-t := sub_nonneg.mpr htr
  have hgapSq : (r-t)^2 ≤ r^2*L^2 := by nlinarith [mul_self_le_mul_self hgap0 hgap]
  have hLsq : L^2 ≤ Phi^2/4 := by nlinarith [mul_self_le_mul_self hL0 hLphi]
  have hid : alpha t R r-1+r*(r-t)-R/2 = (alpha t R r-1-L)+(r-t)^2/2 := by
    have hLeq : L = (t^2+R-r^2)/2 := by simp [L,alpha]
    nlinarith only [hLeq]
  have herrR : |alpha t R r-1+r*(r-t)-R/2| ≤ (1+r^2)*Phi^2 := by
    rw [hid]
    calc
      _ ≤ |alpha t R r-1-L|+|(r-t)^2/2| := abs_add_le _ _
      _ ≤ 3/4*L^2+(r-t)^2/2 := by
        rw [abs_of_nonneg (by positivity : 0 ≤ (r-t)^2/2)]
        exact add_le_add hrem' le_rfl
      _ ≤ _ := by
        have hscaled := mul_le_mul_of_nonneg_left hLsq (sq_nonneg r)
        nlinarith only [hgapSq,hLsq,hscaled,sq_nonneg Phi,mul_nonneg (sq_nonneg r) (sq_nonneg Phi)]
  have hload := equilibrium_bulk_load_error r Phi t R hr hPhi ht hf
  have hhalf : |R/2-Phi/2| ≤ Phi^2/4 := by
    rw [← sub_div,abs_div]
    norm_num
    linarith
  calc
    _ ≤ |alpha t R r-1+r*(r-t)-R/2|+|R/2-Phi/2| := abs_sub_le _ _ _
    _ ≤ _ := by nlinarith only [herrR,hhalf,sq_nonneg Phi]

private theorem equilibrium_parameter_size {d : ℕ} (mu theta : Vec d)
    (r Phi t R : ℝ) (hr : 0 < r) (hPhi : 0 ≤ Phi) (hPhi1 : Phi ≤ 1)
    (ht : 0 < t) (hf : slowField r Phi t R = (0,0))
    (hmu : ‖mu‖ = r) (hinner : inner ℝ theta mu = r*t)
    (hnorm : ‖theta‖^2 = t^2+R) :
    ‖theta‖ ≤ r+1 ∧
      |inner ℝ mu (theta-mu)|+‖theta-mu‖^2 ≤ (1+r^2)*Phi := by
  obtain ⟨hroot,hR⟩ := (slowField_zero_iff r Phi t R hr ht).1 hf
  have htr := positive_root_le_r r Phi t hr hPhi ht hroot
  have hRb := (bulk_bounds_of_phi_le r Phi t Phi hr hPhi ht hroot le_rfl).2
  rw [← hR] at hRb
  have hL := equilibrium_log_alpha_bounds r Phi t R hr hPhi ht hf
  have hs := equilibrium_signal_exp_log r Phi t R hf
  have he := Real.one_sub_le_exp_neg (Real.log (alpha t R r))
  have hgap : r-t ≤ r*Phi/2 := by
    have hp := mul_le_mul_of_nonneg_left he hr.le
    have hl := mul_le_mul_of_nonneg_left hL.2 hr.le
    nlinarith only [hs,hp,hl]
  have hgap0 : 0 ≤ r-t := sub_nonneg.mpr htr
  have hgapSq : (r-t)^2 ≤ r^2*Phi^2/4 := by
    have h := mul_self_le_mul_self hgap0 hgap
    nlinarith only [h]
  have hPhiSq : Phi^2 ≤ Phi := by nlinarith only [hPhi,hPhi1]
  have hinner' : inner ℝ mu (theta-mu) = r*t-r^2 := by
    rw [inner_sub_right,real_inner_comm theta mu,hinner,real_inner_self_eq_norm_sq,hmu]
  have habs : |inner ℝ mu (theta-mu)| = r*(r-t) := by
    rw [hinner',abs_of_nonpos (by nlinarith only [htr,hr])]
    ring
  have hdiff : ‖theta-mu‖^2 = (r-t)^2+R := by
    rw [norm_sub_sq_real,hnorm,hinner,hmu]
    ring
  constructor
  · have htSq : t^2 ≤ r^2 := by nlinarith only [ht,htr,hr]
    nlinarith only [hnorm,htSq,hRb,hPhi1,hr,norm_nonneg theta]
  · rw [habs,hdiff]
    have hscaled := mul_le_mul_of_nonneg_left hPhiSq (sq_nonneg r)
    have hsignal := mul_le_mul_of_nonneg_left hgap hr.le
    nlinarith only [hsignal,hgapSq,hscaled,hRb,hPhi,mul_nonneg (sq_nonneg r) hPhi]

private theorem equilibrium_segment_bounds {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (r Phi t R : ℝ) (hr : 0 < r) (hPhi : 0 ≤ Phi) (hPhi1 : Phi ≤ 1)
    (ht : 0 < t) (hf : slowField r Phi t R = (0,0))
    (hmu : ‖mu‖ = r) (hinner : inner ℝ theta mu = r*t)
    (hnorm : ‖theta‖^2 = t^2+R) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      gaussianAlpha mu (mu+x • (theta-mu)) ≤ Real.exp (1/2) ∧
      tameError p mu (mu+x • (theta-mu)) ≤ Real.exp (r^2/2)*tameError p mu theta := by
  intro x hx
  let z := mu+x • (theta-mu)
  have hL := equilibrium_log_alpha_bounds r Phi t R hr hPhi ht hf
  have hlog : Real.log (alpha t R r) = (‖theta‖^2-r^2)/2 := by simp only [alpha,Real.log_exp,hnorm]
  have hmuNorm : ‖mu‖ ≤ ‖theta‖ := by rw [hmu]; nlinarith [hL.1,hlog,norm_nonneg theta]
  have hzNorm : ‖z‖ ≤ ‖theta‖ := by
    have heq : z = (1-x) • mu+x • theta := by dsimp [z]; module
    rw [heq]
    calc
      _ ≤ ‖(1-x) • mu‖+‖x • theta‖ := norm_add_le _ _
      _ = (1-x)*‖mu‖+x*‖theta‖ := by
        simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hx.1,
          abs_of_nonneg (sub_nonneg.mpr hx.2)]
      _ ≤ (1-x)*‖theta‖+x*‖theta‖ := add_le_add
        (mul_le_mul_of_nonneg_left hmuNorm (sub_nonneg.mpr hx.2)) le_rfl
      _ = ‖theta‖ := by ring
  have hsq : ‖z‖^2 ≤ ‖theta‖^2 := by nlinarith [norm_nonneg z,norm_nonneg theta]
  have halpha : gaussianAlpha mu z ≤ gaussianAlpha mu theta := by
    unfold gaussianAlpha
    exact Real.exp_le_exp.mpr (by linarith)
  have halphaEndpoint : gaussianAlpha mu theta ≤ Real.exp (1/2) := by
    unfold gaussianAlpha
    rw [hmu]
    apply Real.exp_le_exp.mpr
    rw [hlog] at hL
    linarith [hL.2]
  refine ⟨halpha.trans halphaEndpoint,?_⟩
  have hroot := ((slowField_zero_iff r Phi t R hr ht).1 hf).1
  have htr := positive_root_le_r r Phi t hr hPhi ht hroot
  have hg0 : 0 ≤ r-t := sub_nonneg.mpr htr
  have hs := equilibrium_signal_exp_log r Phi t R hf
  have hexp := Real.one_sub_le_exp_neg (Real.log (alpha t R r))
  have hgap : r*(r-t) ≤ r^2/2 := by
    have hp := mul_le_mul_of_nonneg_left hexp hr.le
    have hl := mul_le_mul_of_nonneg_left hL.2 hr.le
    have hg : r-t ≤ r*Phi/2 := by nlinarith only [hs,hp,hl]
    have h := mul_le_mul_of_nonneg_left hg hr.le
    nlinarith only [h,hPhi1,mul_le_mul_of_nonneg_left hPhi1 (sq_nonneg r)]
  have hiz : inner ℝ z mu = r^2-x*(r*(r-t)) := by
    dsimp [z]
    rw [inner_add_left,real_inner_smul_left,inner_sub_left,hinner,real_inner_self_eq_norm_sq,hmu]
    ring
  have hzInner : 0 ≤ inner ℝ z mu ∧ inner ℝ z mu ≤ r^2 := by
    rw [hiz]
    have hprod0 : 0 ≤ r*(r-t) := mul_nonneg hr.le hg0
    have hprod : x*(r*(r-t)) ≤ r*(r-t) := mul_le_of_le_one_left hprod0 hx.2
    constructor <;> nlinarith only [hprod,mul_nonneg hx.1 hprod0,mul_pos hr ht]
  have hinnerExp : Real.exp |inner ℝ z mu| ≤ Real.exp |inner ℝ theta mu| *Real.exp (r^2/2) := by
    rw [abs_of_nonneg hzInner.1,hinner,abs_of_pos (mul_pos hr ht),← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hzInner.2,hgap])
  let C := Real.exp (r^2/2)
  have hC : 1 ≤ C := Real.one_le_exp (by positivity)
  have hX : Real.exp (2*‖z‖^2-‖mu‖^2) ≤ C*Real.exp (2*‖theta‖^2-‖mu‖^2) := by
    apply (Real.exp_le_exp.mpr (by linarith : 2*‖z‖^2-‖mu‖^2 ≤ 2*‖theta‖^2-‖mu‖^2)).trans
    exact le_mul_of_one_le_left (Real.exp_pos _).le hC
  have hY : Real.exp ((3*‖z‖^2-‖mu‖^2)/2) ≤ C*Real.exp ((3*‖theta‖^2-‖mu‖^2)/2) := by
    apply (Real.exp_le_exp.mpr (by linarith : (3*‖z‖^2-‖mu‖^2)/2 ≤ (3*‖theta‖^2-‖mu‖^2)/2)).trans
    exact le_mul_of_one_le_left (Real.exp_pos _).le hC
  have hZ : (1+gaussianAlpha mu z)*Real.exp |inner ℝ z mu| ≤
      C*((1+gaussianAlpha mu theta)*Real.exp |inner ℝ theta mu|) := by
    have h := mul_le_mul (add_le_add le_rfl halpha) hinnerExp (Real.exp_pos _).le
      (show 0 ≤ 1+gaussianAlpha mu theta by have h := gaussianAlpha_pos mu theta; positivity)
    convert h using 1
    dsimp [C]
    ring
  have hsum := add_le_add (add_le_add hX hY) hZ
  have h := mul_le_mul_of_nonneg_left hsum p.property.1
  unfold tameError
  dsimp [z,C] at h
  nlinarith only [h]

/-- Corrected Proposition D(iv) for the actual population loss at a slow
system equilibrium: the relative remainder retains both `epsilon_B` and
`Phi`. No population-risk or KL expansion is assumed. -/
theorem populationLoss_equilibrium_floor {d : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d)
    (p : unitInterval) (mu theta : Vec d) (r Phi t R : ℝ)
    (hr : 0 < r) (hPhi : 0 ≤ Phi) (hPhi1 : Phi ≤ 1) (ht : 0 < t)
    (hf : slowField r Phi t R = (0,0))
    (hmu : ‖mu‖ = r) (hinner : inner ℝ theta mu = r*t)
    (hnorm : ‖theta‖^2 = t^2+R) (hp0 : 0 < (p : ℝ))
    (htame : tameError p mu theta ≤ 1/2) :
    |excessLoss p mu theta-(p : ℝ)*Phi/2| ≤
      (((6*Real.exp (1/2)+2)*Real.exp (r^2/2))*(1+r^2)+(2+r^2)) *
        (p : ℝ)*Phi*(tameError p mu theta+Phi) := by
  have hsize := equilibrium_parameter_size mu theta r Phi t R hr hPhi hPhi1 ht hf hmu hinner hnorm
  have heps : 0 ≤ tameError p mu theta :=
    p.property.1.trans (tameError_ge_probability p mu theta)
  have hpath := equilibrium_segment_bounds p mu theta r Phi t R hr hPhi hPhi1 ht hf hmu hinner hnorm
  have hphalf : (p : ℝ) ≤ 1/2 := (tameError_ge_probability p mu theta).trans htame
  have hpathLoss := populationLoss_probability_path_approximation H p mu theta
    (Real.exp (1/2)) (Real.exp (r^2/2)*tameError p mu theta)
    hp0 hphalf (Real.exp_pos _).le (by positivity)
    (fun x hx => (hpath x hx).1) (fun x hx => (hpath x hx).2)
  let C := (6*Real.exp (1/2)+2)*Real.exp (r^2/2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have h : |excessLoss p mu theta-gaussianLossApprox p mu theta| ≤
      C*(p : ℝ)*tameError p mu theta*(|inner ℝ mu (theta-mu)|+‖theta-mu‖^2) := by
    convert hpathLoss using 1
    dsimp [C]
    ring
  have happrox : |excessLoss p mu theta-gaussianLossApprox p mu theta| ≤
      C*(p : ℝ)*tameError p mu theta*((1+r^2)*Phi) := by
    apply h.trans
    exact mul_le_mul_of_nonneg_left hsize.2 (by positivity)
  have halpha : gaussianAlpha mu theta = alpha t R r := by
    simp only [gaussianAlpha,alpha,hmu,hnorm]
  have hinner' : inner ℝ mu (theta-mu) = r*t-r^2 := by
    rw [inner_sub_right,real_inner_comm theta mu,hinner,real_inner_self_eq_norm_sq,hmu]
  have hpotential : gaussianLossApprox p mu theta = (p : ℝ)*(alpha t R r-1+r*(r-t)) := by
    rw [gaussianLossApprox,halpha,hinner']
    ring
  have hs := equilibrium_scalar_potential_error r Phi t R hr hPhi hPhi1 ht hf
  have hscalar : |gaussianLossApprox p mu theta-(p : ℝ)*Phi/2| ≤
      (2+r^2)*(p : ℝ)*Phi^2 := by
    rw [hpotential,show (p : ℝ)*(alpha t R r-1+r*(r-t))-(p : ℝ)*Phi/2 =
      (p : ℝ)*(alpha t R r-1+r*(r-t)-Phi/2) by ring,abs_mul,abs_of_pos hp0]
    convert mul_le_mul_of_nonneg_left hs hp0.le using 1 <;> ring
  calc
    _ ≤ |excessLoss p mu theta-gaussianLossApprox p mu theta|+
        |gaussianLossApprox p mu theta-(p : ℝ)*Phi/2| := abs_sub_le _ _ _
    _ ≤ _ := by
      have hn : 0 ≤ C*(1+r^2)*(p : ℝ)*Phi^2+(2+r^2)*(p : ℝ)*Phi*tameError p mu theta := by positivity
      dsimp [C] at happrox hn ⊢
      nlinarith only [happrox,hscalar,hn]

/-- The equivalent curvature-weighted floor formula from Proposition D(iv). -/
theorem populationLoss_equilibrium_alpha_floor {d : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d)
    (p : unitInterval) (mu theta : Vec d) (r Phi t R : ℝ)
    (hr : 0 < r) (hPhi : 0 ≤ Phi) (hPhi1 : Phi ≤ 1) (ht : 0 < t)
    (hf : slowField r Phi t R = (0,0))
    (hmu : ‖mu‖ = r) (hinner : inner ℝ theta mu = r*t)
    (hnorm : ‖theta‖^2 = t^2+R) (hp0 : 0 < (p : ℝ))
    (htame : tameError p mu theta ≤ 1/2) :
    |excessLoss p mu theta-(p : ℝ)*alpha t R r*R/2| ≤
      (((6*Real.exp (1/2)+2)*Real.exp (r^2/2))*(1+r^2)+(2+r^2)) *
        (p : ℝ)*Phi*(tameError p mu theta+Phi) := by
  have hbulk : alpha t R r*R = Phi := by
    have h := congrArg Prod.snd hf
    simp only [slowField] at h
    linarith
  rw [show (p : ℝ)*alpha t R r*R/2 = (p : ℝ)*Phi/2 by rw [mul_assoc,hbulk]]
  exact populationLoss_equilibrium_floor H p mu theta r Phi t R hr hPhi hPhi1 ht hf
    hmu hinner hnorm hp0 htame

/-- Application to the actual signal and bulk coordinates of the unique
positive-root equilibrium, with the Bayes vector's actual norm. -/
theorem populationLoss_canonical_equilibrium_floor {d : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d)
    (p : unitInterval) (mu theta : Vec d) (Phi : ℝ)
    (hr : 0 < r mu) (hPhi : 0 ≤ Phi) (hPhi1 : Phi ≤ 1)
    (hsignal : signalCoord mu theta = positiveRoot (r mu) Phi)
    (hbulk : ‖bulkPart mu theta‖^2 = equilibriumBulk (r mu) Phi)
    (hp0 : 0 < (p : ℝ))
    (htame : tameError p mu theta ≤ 1/2) :
    |excessLoss p mu theta-(p : ℝ)*Phi/2| ≤
      (((6*Real.exp (1/2)+2)*Real.exp ((r mu)^2/2))*(1+(r mu)^2)+(2+(r mu)^2)) *
        (p : ℝ)*Phi*(tameError p mu theta+Phi) := by
  have hinner : inner ℝ theta mu = r mu*positiveRoot (r mu) Phi := by
    change inner ℝ theta mu/r mu = positiveRoot (r mu) Phi at hsignal
    have h := (div_eq_iff hr.ne').1 hsignal
    simpa only [mul_comm] using h
  have hnorm : ‖theta‖^2 = (positiveRoot (r mu) Phi)^2+equilibriumBulk (r mu) Phi := by
    have h := bulkPart_norm_sq mu theta hr
    rw [hbulk,hinner] at h
    have hdiv : (r mu*positiveRoot (r mu) Phi)^2/(r mu)^2 = (positiveRoot (r mu) Phi)^2 := by
      field_simp
    rw [hdiv] at h
    linarith
  exact populationLoss_equilibrium_floor H p mu theta (r mu) Phi (positiveRoot (r mu) Phi)
    (equilibriumBulk (r mu) Phi) hr hPhi hPhi1 (positiveRoot_spec (r mu) Phi hr hPhi).1
    (positiveRoot_slowField_zero (r mu) Phi hr hPhi) rfl hinner hnorm hp0 htame

/-- A dimensionless version of the corrected excess-risk expansion. The
constant depends on the fixed signal norm, exactly as in the source's
logistic co-scaling convention. -/
theorem populationLoss_canonical_equilibrium_relative_error {d : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d)
    (p : unitInterval) (mu theta : Vec d) (Phi : ℝ)
    (hr : 0 < r mu) (hPhi : 0 < Phi) (hPhi1 : Phi ≤ 1)
    (hsignal : signalCoord mu theta = positiveRoot (r mu) Phi)
    (hbulk : ‖bulkPart mu theta‖^2 = equilibriumBulk (r mu) Phi)
    (hp0 : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2) :
    |2*excessLoss p mu theta/((p : ℝ)*Phi)-1| ≤
      2*(((6*Real.exp (1/2)+2)*Real.exp ((r mu)^2/2))*(1+(r mu)^2)+(2+(r mu)^2)) *
        (tameError p mu theta+Phi) := by
  have hb := populationLoss_canonical_equilibrium_floor H p mu theta Phi hr hPhi.le hPhi1
    hsignal hbulk hp0 htame
  have hden : 0 < (p : ℝ)*Phi := mul_pos hp0 hPhi
  rw [div_sub_one hden.ne',abs_div,abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  rw [show 2*excessLoss p mu theta-(p : ℝ)*Phi =
    2*(excessLoss p mu theta-(p : ℝ)*Phi/2) by ring,abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  convert mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring

end
end SparseSGD.Logistic
