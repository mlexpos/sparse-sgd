import SparseSGD.Scaling.MatchingApproximation
import SparseSGD.Scaling.RegularLimit

open scoped Matrix.Norms.Operator Topology
open Filter
namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

/-- Joint continuity of the genuine oscillator matrix exponential. -/
theorem continuumMeanFlow_joint_continuous :
    Continuous (fun z : ℝ × ℝ => continuumMeanFlow z.1 z.2) := by
  have hgen : Continuous (fun z : ℝ × ℝ => continuumMeanGenerator z.1) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j <;> simp only [continuumMeanGenerator] <;> fun_prop
  exact NormedSpace.exp_continuous.comp (continuous_snd.smul hgen)

/-- A uniform second-order matrix Taylor bound on a compact curvature interval. -/
theorem continuumMeanFlow_quadratic_bound (a b : ℝ) :
    ∃ C > 0, ∀ d ∈ Set.Icc a b, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖continuumMeanFlow d t-1-t • continuumMeanGenerator d‖ ≤ C*t^2 := by
  have hgen : Continuous (fun z : ℝ × ℝ => continuumMeanGenerator z.1) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j <;> simp only [continuumMeanGenerator] <;> fun_prop
  have hc := (continuumMeanFlow_joint_continuous.mul hgen).mul hgen
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) hc.continuousOn
  refine ⟨max C 0+1,by positivity,?_⟩
  intro d hd t ht
  let A := continuumMeanGenerator d
  have hder (x : ℝ) := ((continuumMeanFlow_hasDerivAt d x).mul_const A).sub_const A
  have hfirst (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) t) :
      ‖continuumMeanFlow d x*A-A‖ ≤ (max C 0+1)*t := by
    have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := Set.Icc (0 : ℝ) t) (C := max C 0+1)
      (fun s _ => (hder s).hasDerivWithinAt)
      (fun s hs => (hC (d,s) ⟨hd,hs.1,hs.2.trans ht.2⟩).trans (by linarith [le_max_left C 0]))
      (convex_Icc 0 t) (show (0 : ℝ) ∈ Set.Icc 0 t from ⟨le_rfl,ht.1⟩) hx
    simp only [continuumMeanFlow_zero,one_mul,sub_self,sub_zero,Real.norm_eq_abs,abs_of_nonneg hx.1] at H
    exact H.trans (mul_le_mul_of_nonneg_left hx.2 (by positivity))
  have hrem (x : ℝ) := ((continuumMeanFlow_hasDerivAt d x).sub_const 1).sub
    ((hasDerivAt_id x).smul_const A)
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.Icc (0 : ℝ) t) (C := (max C 0+1)*t)
    (fun s _ => (hrem s).hasDerivWithinAt) (by simpa only [one_smul] using hfirst) (convex_Icc 0 t)
    (show (0 : ℝ) ∈ Set.Icc 0 t from ⟨le_rfl,ht.1⟩) (show t ∈ Set.Icc 0 t from ⟨ht.1,le_rfl⟩)
  simpa [continuumMeanFlow_zero,Real.norm_eq_abs,abs_of_nonneg ht.1,pow_two,mul_assoc,A] using H

/-- Every individual matrix entry is bounded by the row-sum operator norm. -/
theorem matrix_two_entry_le_norm (A : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    |A i j| ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h : ‖A i j‖₊ ≤ (Finset.univ.sup fun i : Fin 2 => ∑ j : Fin 2, ‖A i j‖₊) := by
    apply le_trans (Finset.single_le_sum (fun k _ => show 0 ≤ ‖A i k‖₊ from zero_le) (Finset.mem_univ j))
    exact Finset.le_sup (f := fun i : Fin 2 => ∑ j : Fin 2, ‖A i j‖₊) (Finset.mem_univ i)
  exact_mod_cast h

/-- The two entries that determine the cold-start coordinate change have a
uniform quadratic remainder. -/
theorem continuumMeanFlow_first_row_quadratic (a b : ℝ) :
    ∃ C > 0, ∀ d ∈ Set.Icc a b, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |continuumMeanFlow d t 0 0-1| ≤ C*t^2 ∧
      |continuumMeanFlow d t 0 1+d*t| ≤ C*t^2 := by
  obtain ⟨C,hC,H⟩ := continuumMeanFlow_quadratic_bound a b
  refine ⟨C,hC,?_⟩
  intro d hd t ht
  have H0 := (matrix_two_entry_le_norm (continuumMeanFlow d t-1-t • continuumMeanGenerator d) 0 0).trans (H d hd t ht)
  have H1 := (matrix_two_entry_le_norm (continuumMeanFlow d t-1-t • continuumMeanGenerator d) 0 1).trans (H d hd t ht)
  simpa [continuumMeanGenerator,sub_eq_add_neg,mul_comm] using And.intro H0 H1

/-- Exact covariance of a cold start in normalized matching coordinates. -/
theorem Params.cold_matchedMoments (p : Params) (R : ℝ)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) :
    p.matchedMoments ⟨R,0,0⟩ =
      ⟨R,R*(-p.matchingMatrix 1 0/p.matchingMatrix 1 1)^2,
        R*(-p.matchingMatrix 1 0/p.matchingMatrix 1 1)⟩ := by
  let P := p.matchingMatrix
  have hdet := p.matchingMatrix_det_ne_zero hb0 hb1 hw0 hw1
  have h11 : P 1 1 ≠ 0 := by
    simpa [P,Params.matchingMatrix,matchingP,Matrix.det_fin_two] using hdet
  have hP : P = !![1,0;P 1 0,P 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hinv : P⁻¹ = !![1,0;-P 1 0/P 1 1,1/P 1 1] := by
    apply Matrix.inv_eq_left_inv
    rw [hP]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two,h11]
    field_simp
    <;> ring
  unfold Params.matchedMoments Params.matchedCovariance
  change _ = (⟨R,R*(-P 1 0/P 1 1)^2,R*(-P 1 0/P 1 1)⟩ : Moments)
  change (⟨(P⁻¹ * (⟨R,0,0⟩ : Moments).cov * (P⁻¹).transpose) 0 0,
    (P⁻¹ * (⟨R,0,0⟩ : Moments).cov * (P⁻¹).transpose) 1 1,
    (P⁻¹ * (⟨R,0,0⟩ : Moments).cov * (P⁻¹).transpose) 0 1⟩ : Moments) = _
  rw [hinv]
  simp [Moments.cov,Matrix.mul_apply,Fin.sum_univ_two]
  <;> ring

/-- Cold-start mixing is first order in the matched time step, uniformly on
compact positive matched curvature sets and bounded raw curvature. -/
theorem cold_matching_ratio_bound (a b M : ℝ) (ha : 0 < a) (hM : 0 ≤ M) :
    ∃ h0 > 0, ∃ L > 0, ∀ p : Params,
      1/2 ≤ p.beta → p.beta < 1 → 0 < p.w → p.w ≤ 1/16 →
      p.w ≤ M*p.eps^2 → p.matchedDelta ∈ Set.Icc a b → p.matchedStep ≤ h0 →
      |-p.matchingMatrix 1 0/p.matchingMatrix 1 1| ≤ L*p.matchedStep := by
  obtain ⟨C,hC,H⟩ := continuumMeanFlow_first_row_quadratic a b
  let L := 2*(M+C)/a
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨min 1 (a/(2*C)),lt_min (by norm_num) (by positivity),L,hL,?_⟩
  intro p hb0 hb1 hw0 hw1 hwM hd hh
  obtain ⟨he,he1,heh,_,_,_,_⟩ := p.small_step_bounds hb0 hb1
  have hhp : 0 < p.matchedStep := he.trans_le heh
  have hht : p.matchedStep ∈ Set.Icc (0 : ℝ) 1 := ⟨hhp.le,hh.trans (min_le_left _ _)⟩
  have hhC : C*p.matchedStep ≤ a/2 := by
    have HH := (le_div_iff₀ (show 0 < 2*C by positivity)).mp (hh.trans (min_le_right _ _))
    linarith
  have hquad := mul_le_mul_of_nonneg_right hhC hhp.le
  obtain ⟨HG0,HG1⟩ := H p.matchedDelta hd p.matchedStep hht
  change |p.matchedMeanFlow 0 0-1| ≤ C*p.matchedStep^2 at HG0
  change |p.matchedMeanFlow 0 1+p.matchedDelta*p.matchedStep| ≤ C*p.matchedStep^2 at HG1
  have hden : a*p.matchedStep/2 ≤ |p.matchedMeanFlow 0 1| := by
    have HD := mul_le_mul_of_nonneg_right hd.1 hhp.le
    have HG := (abs_le.mp HG1).2
    have Hneg : p.matchedMeanFlow 0 1 ≤ -a*p.matchedStep/2 := by nlinarith only [hquad,HD,HG]
    have HGneg : p.matchedMeanFlow 0 1 ≤ 0 := by nlinarith [ha,hhp]
    rw [abs_of_nonpos HGneg]
    linarith only [Hneg]
  have hdenPos : 0 < |p.matchedMeanFlow 0 1| := (by positivity : 0 < a*p.matchedStep/2).trans_le hden
  have hnum : |1-p.w-p.matchedMeanFlow 0 0| ≤ (M+C)*p.matchedStep^2 := by
    have HN := abs_add_le p.w (p.matchedMeanFlow 0 0-1)
    have heh2 := (sq_le_sq₀ he.le hhp.le).mpr heh
    have HM := mul_le_mul_of_nonneg_left heh2 hM
    rw [abs_of_pos hw0] at HN
    have Hid : |1-p.w-p.matchedMeanFlow 0 0|=|p.w+(p.matchedMeanFlow 0 0-1)| := by
      rw [← abs_neg]
      congr 1
      ring
    rw [Hid]
    nlinarith only [HN,HG0,hwM,HM]
  have hsign : p.matchingSign=1 := by
    have Hq := (p.small_step_trace hb0 hb1 hw0.le hw1).1
    simp [Params.matchingSign,Hq.le]
  have Hid : -p.matchingMatrix 1 0/p.matchingMatrix 1 1 =
      (1-p.w-p.matchedMeanFlow 0 0)/p.matchedMeanFlow 0 1 := by
    simp only [Params.matchingMatrix,matchingP,Matrix.of_apply,
      Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.cons_val_fin_one,hsign,one_mul]
    field_simp
  rw [Hid,abs_div]
  apply (div_le_iff₀ hdenPos).mpr
  have HL := mul_le_mul_of_nonneg_left hden (show 0 ≤ L*p.matchedStep by positivity)
  have HLid : L*p.matchedStep*(a*p.matchedStep/2)=(M+C)*p.matchedStep^2 := by
    dsimp [L]
    field_simp
    <;> ring
  rw [HLid] at HL
  exact hnum.trans HL

/-- Cold-start covariance error and initial energy size, with constants derived
from the actual matching matrix. No convergence of initial data is assumed. -/
theorem cold_matching_initial_bounds (a b M : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hM : 0 ≤ M) :
    ∃ h0 > 0, ∃ C > 0, ∀ (p : Params) (R : ℝ),
      1/2 ≤ p.beta → p.beta < 1 → 0 < p.w → p.w ≤ 1/16 →
      p.w ≤ M*p.eps^2 → p.matchedDelta ∈ Set.Icc a b → p.matchedStep ≤ h0 → 0 ≤ R →
      ‖regularMomentVector (p.matchedMoments ⟨R,0,0⟩)-regularMomentVector ⟨R,0,0⟩‖ ≤ C*R*p.matchedStep ∧
      p.comparisonInitialSize ⟨R,0,0⟩ ≤ C*R := by
  obtain ⟨h0,hh0,L,hL,HL⟩ := cold_matching_ratio_bound a b M ha hM
  let C := 1+b*L^2+L+L^2
  have hb : 0 < b := ha.trans_le hab
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨min h0 1,lt_min hh0 (by norm_num),C,hC,?_⟩
  intro p R hb0 hb1 hw0 hw1 hwM hd hh hR
  have hhp := (p.matchedStep_pos (by linarith) hb1)
  have hh1 := hh.trans (min_le_right _ _)
  have hqr := HL p hb0 hb1 hw0 hw1 hwM hd (hh.trans (min_le_left _ _))
  let q := -p.matchingMatrix 1 0/p.matchingMatrix 1 1
  have hq : |q| ≤ L*p.matchedStep := hqr
  have hq2 : q^2 ≤ L^2*p.matchedStep := by
    have H := (sq_le_sq₀ (abs_nonneg q) (by positivity : 0 ≤ L*p.matchedStep)).mpr hq
    rw [sq_abs,mul_pow] at H
    have HH := mul_le_mul_of_nonneg_left (show p.matchedStep^2 ≤ p.matchedStep by nlinarith) (sq_nonneg L)
    exact H.trans HH
  have hq1 : |q| ≤ L := hq.trans (by nlinarith only [hh1,hL])
  have hq21 : q^2 ≤ L^2 := hq2.trans (by simpa using mul_le_mul_of_nonneg_left hh1 (sq_nonneg L))
  have hCq : L^2 ≤ C := by dsimp [C]; nlinarith [mul_nonneg hb.le (sq_nonneg L)]
  have hCl : L ≤ C := by dsimp [C]; nlinarith [mul_nonneg hb.le (sq_nonneg L)]
  have hmatch := p.cold_matchedMoments R hb0 hb1 hw0 (by linarith)
  change p.matchedMoments ⟨R,0,0⟩=⟨R,R*q^2,R*q⟩ at hmatch
  constructor
  · rw [hmatch]
    apply (pi_norm_le_iff_of_nonneg (show 0 ≤ C*R*p.matchedStep by positivity)).mpr
    intro i
    fin_cases i
    · simp [regularMomentVector]
      positivity
    · change ‖R*q^2-0‖ ≤ C*R*p.matchedStep
      rw [sub_zero,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hR (sq_nonneg q))]
      have H := mul_le_mul_of_nonneg_left hq2 hR
      have HC := mul_le_mul_of_nonneg_right hCq (show 0 ≤ R*p.matchedStep by positivity)
      nlinarith only [H,HC]
    · change ‖R*q-0‖ ≤ C*R*p.matchedStep
      rw [sub_zero,Real.norm_eq_abs,abs_mul,abs_of_nonneg hR]
      have H := mul_le_mul_of_nonneg_left hq hR
      have HC := mul_le_mul_of_nonneg_right hCl (show 0 ≤ R*p.matchedStep by positivity)
      nlinarith only [H,HC]
  · unfold Params.comparisonInitialSize
    rw [hmatch]
    simp only [abs_mul,abs_of_nonneg hR]
    have hD0 : 0 ≤ p.matchedDelta := (ha.trans_le hd.1).le
    have H := mul_le_mul hd.2 hq21 (sq_nonneg q) hb.le
    have HR := mul_le_mul_of_nonneg_right H hR
    have HC := mul_le_mul_of_nonneg_left hq1 hR
    have HRL : 0 ≤ R*L^2 := by positivity
    dsimp [C]
    nlinarith only [HR,HC,HRL]

end
end SparseSGD
