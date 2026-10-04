import SparseSGD.Scaling.ColdMatching

open scoped Matrix.Norms.Operator Topology
open Filter
namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

theorem coldMoments_psd (R : ℝ) (hR : 0 ≤ R) : (⟨R,0,0⟩ : Moments).psd := by
  change (!![R,0;0,0] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef
  have H : (!![R,0;0,0] : Matrix (Fin 2) (Fin 2) ℝ)=Matrix.diagonal ![R,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [H]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> simp [hR]

/-- The regular cold-start approximation, in raw curvature parameters.
The initial covariance error is proved from the matching map. -/
theorem regular_cold_raw_rate (D margin : ℝ) (hD : 0 < D) (hm : 0 < margin) :
    ∃ eps0 > 0, ∃ C > 0, ∀ (p : Params) (R u phi : ℝ),
      1/2 ≤ p.beta → p.beta < 1 → 0 < p.w → p.w ≤ 1/16 →
      p.w=D*p.eps^2 → p.eps ≤ eps0 → External.JuryStability → 0 ≤ R →
      0 ≤ p.renormNoise → p.renormNoise ≤ 1-margin →
      0 ≤ u → u ≤ 1-margin → 0 ≤ p.renormAdditive → ∀ k : ℕ,
      |(p.trajectory ⟨R,0,0⟩ k).R-
        (continuumFlow D u phi ⟨R,0,0⟩ ((k : ℝ)*p.matchedStep)).R| ≤
      C*(p.eps+|p.renormNoise-u|+|p.renormAdditive-phi|)*(R+p.renormAdditive+1) := by
  let K := 128*D^2+10*D+7
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨h0,hh0,A,hA,hinit⟩ := cold_matching_initial_bounds (D/2) (2*D) D
    (by positivity) (by linarith) hD.le
  obtain ⟨F,hF,hflow⟩ := regular_chain_uniform_rate_interval (D/2) (2*D) margin
    (by positivity) (by linarith) hm
  let C := (F+1)*((3+K)*(A+1)+2*A+2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨min (h0/2) (D/(2*K)),lt_min (by positivity) (by positivity),C,hC,?_⟩
  intro p R u phi hb0 hb1 hw0 hw1 hw heps jury hR hun hum hu0 hu1 hphi k
  obtain ⟨he,_,_,_,hh2,_,_⟩ := p.small_step_bounds hb0 hb1
  have herr : |p.matchedDelta-D| ≤ K*p.eps := p.small_step_matchedDelta D hb0 hb1 hD hw hw1
  have hsmall : K*p.eps ≤ D/2 := by
    have H := (le_div_iff₀ (show 0 < 2*K by positivity)).mp (heps.trans (min_le_right _ _))
    linarith
  have hd : p.matchedDelta ∈ Set.Icc (D/2) (2*D) := by
    have H := abs_le.mp herr
    constructor <;> linarith
  have hh : p.matchedStep ≤ h0 := by
    have H := heps.trans (min_le_left _ _)
    linarith
  obtain ⟨hi,hN⟩ := hinit p R hb0 hb1 hw0 hw1 (by rw [hw]) hd hh hR
  have H := hflow p ⟨R,0,0⟩ D u phi ⟨R,0,0⟩ hb0 hb1 hw0 (by linarith) jury
    (coldMoments_psd R hR) hd.1 hd.2 (by linarith) (by linarith) hun hum hu0 hu1 hphi k
  let E := p.eps+|p.renormNoise-u|+|p.renormAdditive-phi|
  let N := R+p.renormAdditive+1
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have hEe : p.eps ≤ E := by dsimp [E]; linarith [abs_nonneg (p.renormNoise-u),abs_nonneg (p.renormAdditive-phi)]
  have hEu : |p.renormNoise-u| ≤ E := by dsimp [E]; linarith [abs_nonneg (p.renormAdditive-phi)]
  have hEp : |p.renormAdditive-phi| ≤ E := by dsimp [E]; linarith [abs_nonneg (p.renormNoise-u)]
  have hRN : R ≤ N := by dsimp [N]; linarith
  have hN1 : 1 ≤ N := by dsimp [N]; linarith
  have henergy : p.comparisonInitialSize ⟨R,0,0⟩+p.renormAdditive ≤ (A+1)*N := by
    have HN := mul_le_mul_of_nonneg_left hRN hA.le
    dsimp [N] at HN ⊢
    nlinarith only [hN,HN,hR]
  have hfactor : p.matchedStep+|p.matchedDelta-D|+|p.renormNoise-u| ≤ (3+K)*E := by
    have HK := mul_le_mul_of_nonneg_left hEe hK.le
    nlinarith only [hh2,herr,hEe,hEu,HK]
  have henergy0 : 0 ≤ p.comparisonInitialSize ⟨R,0,0⟩+p.renormAdditive := by
    have Hpsd := p.matchedMoments_psd ⟨R,0,0⟩ (coldMoments_psd R hR)
    have HR := Moments.psd_R_nonneg Hpsd
    have HV := Moments.psd_V_nonneg Hpsd
    have HD : 0 ≤ p.matchedDelta := by linarith [hd.1]
    unfold Params.comparisonInitialSize
    positivity
  have hproduct := mul_le_mul hfactor henergy henergy0 (by positivity : 0 ≤ (3+K)*E)
  have hinitial : ‖regularMomentVector (p.matchedMoments ⟨R,0,0⟩)-regularMomentVector ⟨R,0,0⟩‖ ≤
      2*A*E*N := by
    have HH := mul_le_mul_of_nonneg_left hh2 (show 0 ≤ A*R by positivity)
    have HRN := mul_le_mul hEe hRN hR hE
    have HN := mul_le_mul_of_nonneg_left HRN (show 0 ≤ 2*A by positivity)
    nlinarith only [hi,HH,HN]
  have hadd : |p.renormAdditive-phi| ≤ E*N := hEp.trans (le_mul_of_one_le_right hE hN1)
  have htotal : (p.matchedStep+|p.matchedDelta-D|+|p.renormNoise-u|)*
      (p.comparisonInitialSize ⟨R,0,0⟩+p.renormAdditive)+|p.renormAdditive-phi|+
      ‖regularMomentVector (p.matchedMoments ⟨R,0,0⟩)-regularMomentVector ⟨R,0,0⟩‖ ≤
      ((3+K)*(A+1)+2*A+2)*E*N := by
    have HEN : 0 ≤ E*N := mul_nonneg hE hN0
    nlinarith only [hproduct,hinitial,hadd,HEN]
  apply H.trans
  have Hmul := mul_le_mul_of_nonneg_left htotal hF
  have HC : F*((3+K)*(A+1)+2*A+2)*E*N ≤ C*E*N := by
    have Hnon : 0 ≤ ((3+K)*(A+1)+2*A+2)*E*N := by positivity
    dsimp [C]
    nlinarith only [Hnon]
  exact Hmul.trans (by convert HC using 1 <;> ring)

end
end SparseSGD
