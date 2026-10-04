import SparseSGD.Scaling.RegularPerturbation

open scoped Topology Matrix.Norms.Operator
open Filter Set
namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

/-- Explicit amplitude for exponential stability in Euclidean coordinates. -/
def regularExplicitAmplitude (delta u : ℝ) : ℝ :=
  (1+1/delta) * (2*continuumStabilityComparison delta u/continuumStabilityGap u) * (2*(1+delta))

private theorem regular_psd_norm_energy {delta : ℝ} (hd : 0 < delta) (s : Moments) (hs : s.psd) :
    ‖regularMomentVector s‖ ≤ (1+1/delta)*(s.R+delta*s.V) := by
  have hR := Moments.psd_R_nonneg hs
  have hV := Moments.psd_V_nonneg hs
  have hc : |s.C| ≤ s.R+s.V := by
    have h := Moments.psd_cross_energy_bound 1 (by norm_num) s hs
    norm_num at h
    linarith [abs_nonneg s.C]
  have hb : s.R+s.V ≤ (1+1/delta)*(s.R+delta*s.V) := by
    have hid : (1+1/delta)*(s.R+delta*s.V) - (s.R+s.V) = s.R/delta+delta*s.V := by
      field_simp
      ring
    have hn : 0 ≤ s.R/delta+delta*s.V := by positivity
    linarith
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  fin_cases i
  · change ‖s.R‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg hR]
    exact (show s.R ≤ s.R+s.V by linarith).trans hb
  · change ‖s.V‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg hV]
    exact (show s.V ≤ s.R+s.V by linarith).trans hb
  · change ‖s.C‖ ≤ _
    rw [Real.norm_eq_abs]
    exact hc.trans hb

private theorem regular_psd_semigroup_decay {delta u : ℝ} (hd : 0 < delta) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (s : Moments) (hs : s.psd) {t : ℝ} (ht : 0 ≤ t) :
    ‖(regularSemigroup delta u t).mulVec (regularMomentVector s)‖ ≤
      ((1+1/delta)*(2*continuumStabilityComparison delta u/continuumStabilityGap u)) *
        (s.R+delta*s.V) * Real.exp (-continuumStabilityRate delta u*t) := by
  rw [← regularSemigroup_flow delta u s ht]
  have hn := regular_psd_norm_energy hd _ (continuumFlow_psd hd hu0 le_rfl s hs ht)
  have he := mul_le_mul_of_nonneg_left (continuumFlow_energy_exp_bound hd hu0 hu1 s hs ht)
    (show 0 ≤ 1+1/delta by positivity)
  exact hn.trans (by convert he using 1 <;> ring)

/-- The semigroup bound has explicit continuous constants on the subcritical parameter set. -/
theorem regularSemigroup_explicit_decay {delta u : ℝ} (hd : 0 < delta) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (v : Fin 3 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖(regularSemigroup delta u t).mulVec v‖ ≤
      regularExplicitAmplitude delta u * regularVectorSize v *
        Real.exp (-continuumStabilityRate delta u*t) := by
  let J := (1+1/delta)*(2*continuumStabilityComparison delta u/continuumStabilityGap u)
  let e := Real.exp (-continuumStabilityRate delta u*t)
  have hJ : 0 ≤ J := by
    dsimp [J,continuumStabilityComparison,continuumStabilityGap]
    positivity
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hr : (Moments.mk 1 0 0).psd := by
    change (Moments.mk 1 0 0).cov.PosSemidef
    convert Matrix.PosSemidef.diagonal (d := ![(1:ℝ),0]) (by intro i; fin_cases i <;> norm_num) using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Moments.cov,Matrix.diagonal]
  have hv : (Moments.mk 0 1 0).psd := by
    change (Moments.mk 0 1 0).cov.PosSemidef
    convert Matrix.PosSemidef.diagonal (d := ![(0:ℝ),1]) (by intro i; fin_cases i <;> norm_num) using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Moments.cov,Matrix.diagonal]
  have hp : (Moments.mk 1 1 1).psd := by
    change (Moments.mk 1 1 1).cov.PosSemidef
    convert Matrix.posSemidef_vecMulVec_self_star ![(1:ℝ),1] using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Moments.cov,Matrix.vecMulVec]
  have hq : (Moments.mk 1 1 0).psd := by
    change (Moments.mk 1 1 0).cov.PosSemidef
    convert Matrix.PosSemidef.diagonal (d := ![(1:ℝ),1]) (by intro i; fin_cases i <;> norm_num) using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Moments.cov,Matrix.diagonal]
  have h0 := regular_psd_semigroup_decay hd hu0 hu1 _ hr ht
  have h1 := regular_psd_semigroup_decay hd hu0 hu1 _ hv ht
  have hplus := regular_psd_semigroup_decay hd hu0 hu1 _ hp ht
  have hdiag := regular_psd_semigroup_decay hd hu0 hu1 _ hq ht
  change ‖(regularSemigroup delta u t).mulVec ![1,0,0]‖ ≤ J*(1+delta*0)*e at h0
  change ‖(regularSemigroup delta u t).mulVec ![0,1,0]‖ ≤ J*(0+delta*1)*e at h1
  change ‖(regularSemigroup delta u t).mulVec ![1,1,1]‖ ≤ J*(1+delta*1)*e at hplus
  change ‖(regularSemigroup delta u t).mulVec ![1,1,0]‖ ≤ J*(1+delta*1)*e at hdiag
  have h2 : ‖(regularSemigroup delta u t).mulVec ![0,0,1]‖ ≤ J*(2*(1+delta))*e := by
    have hdiff : ![(0:ℝ),0,1] = ![1,1,1]-![1,1,0] := by ext i; fin_cases i <;> norm_num
    rw [hdiff,Matrix.mulVec_sub]
    have hn := norm_sub_le ((regularSemigroup delta u t).mulVec ![1,1,1])
      ((regularSemigroup delta u t).mulVec ![1,1,0])
    nlinarith
  have hJe : 0 ≤ J*e := mul_nonneg hJ he
  have hdJe : 0 ≤ delta*(J*e) := mul_nonneg hd.le hJe
  have h0' : ‖(regularSemigroup delta u t).mulVec ![1,0,0]‖ ≤ J*(2*(1+delta))*e := by nlinarith
  have h1' : ‖(regularSemigroup delta u t).mulVec ![0,1,0]‖ ≤ J*(2*(1+delta))*e := by nlinarith
  have hdec : v = v 0 • ![1,0,0] + v 1 • ![0,1,0] + v 2 • ![0,0,1] := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hdec,Matrix.mulVec_add,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,Matrix.mulVec_smul]
  have hb0 := mul_le_mul_of_nonneg_left h0' (abs_nonneg (v 0))
  have hb1 := mul_le_mul_of_nonneg_left h1' (abs_nonneg (v 1))
  have hb2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg (v 2))
  calc
    _ ≤ (‖v 0 • (regularSemigroup delta u t).mulVec ![1,0,0]‖ +
          ‖v 1 • (regularSemigroup delta u t).mulVec ![0,1,0]‖) +
          ‖v 2 • (regularSemigroup delta u t).mulVec ![0,0,1]‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ |v 0| * (J*(2*(1+delta))*e) + |v 1| * (J*(2*(1+delta))*e) +
        |v 2| * (J*(2*(1+delta))*e) := by
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (add_le_add hb0 hb1) hb2
    _ = _ := by unfold regularExplicitAmplitude regularVectorSize; dsimp [J,e]; ring

/-- A common exponential semigroup estimate on a compact delta interval and a stability margin. -/
theorem regularSemigroup_uniform_decay (a b margin : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (hm : 0 < margin) :
    ∃ A lambda : ℝ, 0 < A ∧ 0 < lambda ∧ ∀ delta u : ℝ,
      a ≤ delta → delta ≤ b → 0 ≤ u → u ≤ 1-margin →
      ∀ v : Fin 3 → ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖(regularSemigroup delta u t).mulVec v‖ ≤ A*regularVectorSize v*Real.exp (-lambda*t) := by
  let M := 1+1/a+1/2
  let G := margin/2
  let A := (1+1/a)*(2*M/G)*(2*(1+b))
  let lambda := G/M
  have hM : 0 < M := by dsimp [M]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hb : 0 < b := ha.trans_le hab
  refine ⟨A,lambda,by dsimp [A]; positivity,by dsimp [lambda]; positivity,?_⟩
  intro delta u hd hdB hu0 hum v t ht
  have hd0 : 0 < delta := ha.trans_le hd
  have hu1 : u < 1 := by linarith
  have hinv : 1/delta ≤ 1/a := div_le_div_of_nonneg_left zero_le_one ha hd
  have hone : 1/(1+u) ≤ 1 := (div_le_one (by linarith : 0 < 1+u)).2 (by linarith)
  have hcomp : continuumStabilityComparison delta u ≤ M := by
    dsimp [continuumStabilityComparison,M]
    linarith
  have hgap : G ≤ continuumStabilityGap u := by
    dsimp [continuumStabilityGap]
    apply (le_div_iff₀ (by linarith : 0 < 1+u)).2
    dsimp [G]
    nlinarith
  have hcompp : 0 < continuumStabilityComparison delta u := by
    dsimp [continuumStabilityComparison]
    positivity
  have hgapp : 0 < continuumStabilityGap u := hG.trans_le hgap
  have hF : 2*continuumStabilityComparison delta u/continuumStabilityGap u ≤ 2*M/G := by
    gcongr
  have hAmp : regularExplicitAmplitude delta u ≤ A := by
    dsimp [regularExplicitAmplitude,A]
    have hF0 : 0 ≤ 2*continuumStabilityComparison delta u/continuumStabilityGap u := by positivity
    have hstep := mul_le_mul (show 1+1/delta ≤ 1+1/a by linarith) hF hF0
      (show 0 ≤ 1+1/a by positivity)
    exact mul_le_mul hstep (by linarith : 2*(1+delta) ≤ 2*(1+b))
      (by positivity) (by positivity)
  have hrate : lambda ≤ continuumStabilityRate delta u := by
    dsimp [lambda,continuumStabilityRate]
    gcongr
  have hdec := regularSemigroup_explicit_decay hd0 hu0 hu1 v ht
  apply hdec.trans
  have hsize : 0 ≤ regularVectorSize v := by unfold regularVectorSize; positivity
  have he : Real.exp (-continuumStabilityRate delta u*t) ≤ Real.exp (-lambda*t) :=
    Real.exp_le_exp.2 (by nlinarith)
  exact mul_le_mul (mul_le_mul_of_nonneg_right hAmp hsize) he
    (Real.exp_pos _).le (by dsimp [A]; positivity)


private theorem regular_ratio_difference_bound (a delta delta₀ x x₀ : ℝ) (ha : 0 < a)
    (hd : a ≤ delta) (hd0 : a ≤ delta₀) :
    |x/delta-x₀/delta₀| ≤ |x-x₀|/a + |x₀| * |delta-delta₀|/a^2 := by
  have hdp : 0 < delta := ha.trans_le hd
  have hd0p : 0 < delta₀ := ha.trans_le hd0
  have hid : x/delta-x₀/delta₀ = (x-x₀)/delta + x₀*(delta₀-delta)/(delta*delta₀) := by
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ |(x-x₀)/delta| + |x₀*(delta₀-delta)/(delta*delta₀)| := abs_add_le _ _
    _ = |x-x₀|/delta + |x₀| * |delta-delta₀|/(delta*delta₀) := by
      rw [abs_div,abs_div,abs_mul,abs_of_pos hdp,abs_of_pos (mul_pos hdp hd0p),abs_sub_comm delta₀ delta]
    _ ≤ _ := by
      apply add_le_add
      · exact div_le_div_of_nonneg_left (abs_nonneg _) ha hd
      · apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ha)
        nlinarith [mul_le_mul hd hd0 ha.le (by linarith : 0 ≤ delta)]

private theorem regular_energy_margin_bound (delta u phi : ℝ) (s : Moments)
    (hd : 0 < delta) (hu0 : 0 ≤ u) (hp : 0 ≤ phi) (hs : s.psd)
    (margin : ℝ) (hm : 0 < margin) (hum : u ≤ 1-margin) :
    continuumEnergyBound delta u phi s ≤
      (1+2/margin) * (s.R+delta*s.V+|s.C|+phi) := by
  let N := s.R+delta*s.V+|s.C|+phi
  have hR := Moments.psd_R_nonneg hs
  have hV := Moments.psd_V_nonneg hs
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hgap : 0 < 1-u := by linarith
  have hRn : 0 ≤ continuumRiskBound delta u phi s := by
    dsimp [continuumRiskBound]
    positivity
  have hRisk : continuumRiskBound delta u phi s ≤ N/margin := by
    have hnum : s.R+delta*s.V+phi ≤ N := by dsimp [N]; linarith [abs_nonneg s.C]
    change (s.R+delta*s.V+phi)/(1-u) ≤ N/margin
    apply le_trans (div_le_div_of_nonneg_right hnum hgap.le)
    exact div_le_div_of_nonneg_left hN hm (by linarith)
  have hscaled := mul_le_mul_of_nonneg_left hRisk (show 0 ≤ 1+u by linarith)
  have hcoeff : (1+u)*(N/margin) ≤ 2*(N/margin) := by
    apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  dsimp [continuumEnergyBound]
  have hid : (1+2/margin)*N = N+2*(N/margin) := by ring
  rw [hid]
  dsimp [N] at *
  linarith [abs_nonneg s.C]

/-- Uniform Lipschitz dependence of the flow on a compact positive delta interval.
The error is uniform over all `t ≥ 0` and has the source corollary's load weights. -/
theorem continuumFlow_regular_uniform_rate (a b margin : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (hm : 0 < margin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (delta u phi delta₀ u₀ phi₀ : ℝ) (s s₀ : Moments),
      a ≤ delta → delta ≤ b → a ≤ delta₀ → delta₀ ≤ b →
      0 ≤ u → u ≤ 1-margin → 0 ≤ u₀ → u₀ ≤ 1-margin → 0 ≤ phi → s.psd →
      ∀ t : ℝ, 0 ≤ t →
      ‖regularMomentVector (continuumFlow delta u phi s t) -
        regularMomentVector (continuumFlow delta₀ u₀ phi₀ s₀ t)‖ ≤
      C * ((|delta-delta₀|+|u-u₀|) * (s.R+delta*s.V+|s.C|+phi) +
        |phi-phi₀| + regularVectorSize (regularMomentVector s-regularMomentVector s₀)) := by
  obtain ⟨A,lambda,hA,hl,hsemigroup⟩ := regularSemigroup_uniform_decay a b margin ha hab hm
  let E := (1+1/a)*(1+2/margin)
  let D := 3+2/a+2/a^2
  let H := D*E+2/a^2
  let C := A+(A/lambda)*(H+2/a)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro delta u phi delta₀ u₀ phi₀ s s₀ hd hdB hd0 hd0B hu0 hum hu00 hu0m hp hs t ht
  have hdp : 0 < delta := ha.trans_le hd
  have hd0p : 0 < delta₀ := ha.trans_le hd0
  have hu1 : u < 1 := by linarith
  let N := s.R+delta*s.V+|s.C|+phi
  let d := |delta-delta₀|+|u-u₀|
  let I := regularVectorSize (regularMomentVector s-regularMomentVector s₀)
  have hN : 0 ≤ N := by
    have hR := Moments.psd_R_nonneg hs
    have hV := Moments.psd_V_nonneg hs
    dsimp [N]
    positivity
  have hdnon : 0 ≤ d := by dsimp [d]; positivity
  have hI : 0 ≤ I := by dsimp [I,regularVectorSize]; positivity
  have hNP : phi ≤ N := by
    have hR := Moments.psd_R_nonneg hs
    have hV := Moments.psd_V_nonneg hs
    have hz : 0 ≤ s.R+delta*s.V+|s.C| := by positivity
    dsimp [N]
    linarith
  have hrU := regular_ratio_difference_bound a delta delta₀ u u₀ ha hd hd0
  have huabs : |u₀| ≤ 1 := by rw [abs_of_nonneg hu00]; linarith
  have hrU' : |u/delta-u₀/delta₀| ≤ |u-u₀|/a+|delta-delta₀|/a^2 := by
    apply hrU.trans
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ (sq_nonneg a)
    simpa using mul_le_mul_of_nonneg_right huabs (abs_nonneg (delta-delta₀))
  have hrP := regular_ratio_difference_bound a delta₀ delta phi₀ phi ha hd0 hd
  rw [abs_sub_comm (phi₀/delta₀) (phi/delta),abs_sub_comm phi₀ phi,abs_sub_comm delta₀ delta,
    abs_of_nonneg hp] at hrP
  have hS : (1+1/delta)*continuumEnergyBound delta u phi s ≤ E*N := by
    have hEn : 0 ≤ continuumEnergyBound delta u phi s := by
      have hcoords := regularFlow_coordinate_bound hdp hu0 hu1 hp s hs (t := 0) le_rfl 0
      have hz : 0 < 1+1/delta := by positivity
      nlinarith [abs_nonneg (regularMomentVector (continuumFlow delta u phi s 0) 0)]
    have hinv : 1/delta ≤ 1/a := div_le_div_of_nonneg_left zero_le_one ha hd
    have hb := regular_energy_margin_bound delta u phi s hdp hu0 hp hs margin hm hum
    have h := mul_le_mul (show 1+1/delta ≤ 1+1/a by linarith) hb hEn
      (show 0 ≤ 1+1/a by positivity)
    dsimp [E,N]
    convert h using 1 <;> ring
  have hforce : ∀ x, 0 ≤ x → regularVectorSize (regularParameterForcing delta u phi delta₀ u₀ phi₀ s x) ≤
      H*d*N+(2/a)*|phi-phi₀| := by
    intro x hx
    apply (regularParameterForcing_bound hdp hu0 hu1 hp s hs delta₀ u₀ phi₀ hx).trans
    have hcoeff : 3*|delta-delta₀|+2*|u/delta-u₀/delta₀| ≤ D*d := by
      dsimp [D,d]
      have ha1 : 0 ≤ 2/a := by positivity
      have ha2 : 0 ≤ 2/a^2 := by positivity
      have hdabs := abs_nonneg (delta-delta₀)
      have huabs' := abs_nonneg (u-u₀)
      simp only [div_eq_mul_inv] at hrU' ha1 ha2 ⊢
      nlinarith only [hrU',huabs',mul_nonneg ha1 hdabs,mul_nonneg ha2 huabs']
    have hsprod := mul_le_mul hcoeff hS
      (show 0 ≤ (1+1/delta)*continuumEnergyBound delta u phi s from
        le_trans (abs_nonneg _) (regularFlow_coordinate_bound hdp hu0 hu1 hp s hs (t := 0) le_rfl 0))
      (mul_nonneg hD hdnon)
    have hphiN := mul_le_mul_of_nonneg_left hNP
      (show 0 ≤ 2*|delta-delta₀|/a^2 by positivity)
    have hdN := mul_le_mul_of_nonneg_right (show |delta-delta₀| ≤ d by dsimp [d]; linarith [abs_nonneg (u-u₀)]) hN
    dsimp [H]
    have hdscaled := mul_le_mul_of_nonneg_left hdN (show 0 ≤ 2/a^2 by positivity)
    simp only [div_eq_mul_inv,one_mul] at hrP hphiN hdscaled hsprod ⊢
    nlinarith only [hsprod,hrP,hphiN,hdscaled]
  have hBn : 0 ≤ H*d*N+(2/a)*|phi-phi₀| := by positivity
  have hb := regular_duhamel_uniform_bound delta₀ u₀ A lambda hA hl
    (hsemigroup delta₀ u₀ hd0 hd0B hu00 hu0m)
    (fun t => regularMomentVector (continuumFlow delta u phi s t)-
      regularMomentVector (continuumFlow delta₀ u₀ phi₀ s₀ t))
    (regularParameterForcing delta u phi delta₀ u₀ phi₀ s)
    (regularFlowDifference_hasDerivAt delta u phi delta₀ u₀ phi₀ s s₀)
    (regularParameterForcing_continuous delta u phi delta₀ u₀ phi₀ s)
    _ hBn hforce t ht
  simp only [continuumFlow_initial] at hb
  apply hb.trans
  change A*I+A*(H*d*N+(2/a)*|phi-phi₀|)/lambda ≤ C*(d*N+|phi-phi₀|+I)
  have hAl : 0 ≤ A/lambda := by positivity
  have heq : C*(d*N+|phi-phi₀|+I) - (A*I+A*(H*d*N+(2/a)*|phi-phi₀|)/lambda) =
      A*(d*N+|phi-phi₀|) + (A/lambda)*(H * |phi-phi₀|+H*I+(2/a)*(d*N)+(2/a)*I) := by
    dsimp [C]
    ring
  have hnon : 0 ≤ A*(d*N+|phi-phi₀|) +
      (A/lambda)*(H * |phi-phi₀|+H*I+(2/a)*(d*N)+(2/a)*I) := by positivity
  linarith only [heq,hnon]

end
end SparseSGD
