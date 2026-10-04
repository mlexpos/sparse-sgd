import SparseSGD.Scaling.GeometricKernel
import SparseSGD.Scaling.SmallDeltaSpectrum
import Mathlib.Analysis.SpecialFunctions.Exp

namespace SparseSGD.Scaling
open SparseSGD
noncomputable section

theorem smallDelta_slow_location (beta Delta : ℝ) (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8) :
    smallDeltaZ beta Delta ≤ 1-smallDeltaLambdaPlus beta Delta ∧
      1-smallDeltaLambdaPlus beta Delta ≤ smallDeltaZ beta Delta+2*Delta*smallDeltaZ beta Delta := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hlo,hhi,_⟩ :=
    smallDeltaSpectrum_strong beta Delta hb0 hb1 hD0 hD1
  exact ⟨hlo,hhi⟩

/-- The elementary exponential remainder estimate, valid also at x=0. -/
theorem exp_neg_linear_remainder (x : ℝ) (hx : 0 ≤ x) :
    |Real.exp (-x)-(1-x)| ≤ x^2 := by
  have hlo : 1-x ≤ Real.exp (-x) := by
    have h := Real.add_one_le_exp (-x)
    linarith
  have hpoly : 0 < 1-x+x^2 := by nlinarith [sq_nonneg (x-(1/2 : ℝ))]
  have hexp : 1+x ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hmul : 1 ≤ (1-x+x^2)*Real.exp x := by
    have h := mul_le_mul_of_nonneg_right hexp hpoly.le
    nlinarith [sq_nonneg x]
  have hhi : Real.exp (-x) ≤ 1-x+x^2 := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀' (Real.exp_pos x)]
    nlinarith [hmul]
  rw [abs_le]
  constructor <;> nlinarith

def smallDeltaRho (beta Delta : ℝ) : ℝ := Real.exp (-2*smallDeltaZ beta Delta)

set_option maxHeartbeats 1000000 in
theorem smallDelta_slow_kernel_bounds (beta Delta : ℝ) (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8) :
    let a := smallDeltaLambdaPlus beta Delta
    let z := smallDeltaZ beta Delta
    let rho := smallDeltaRho beta Delta
    0 ≤ a^2 ∧ a^2 < 1 ∧ 0 < rho ∧ rho < 1 ∧
    |a^2-rho| ≤ 40*Delta*z ∧
    1-max (a^2) rho ≥ z/2 := by
  change 0 ≤ (smallDeltaLambdaPlus beta Delta)^2 ∧
    (smallDeltaLambdaPlus beta Delta)^2 < 1 ∧ 0 < smallDeltaRho beta Delta ∧
    smallDeltaRho beta Delta < 1 ∧
    |(smallDeltaLambdaPlus beta Delta)^2-smallDeltaRho beta Delta| ≤
      40*Delta*smallDeltaZ beta Delta ∧
    1-max ((smallDeltaLambdaPlus beta Delta)^2) (smallDeltaRho beta Delta) ≥
      smallDeltaZ beta Delta/2
  obtain ⟨hdisc,hgapEig,hminus0,hminusup,hplus0,hplus1,habs,hprod,hsum,
      hslowlo,hslowhi,hminuslo⟩ := smallDeltaSpectrum_strong beta Delta hb0 hb1 hD0 hD1
  have ha0 := hplus0
  have ha1 := hplus1
  have hz : 0 < smallDeltaZ beta Delta := by
    unfold smallDeltaZ
    exact mul_pos hD0 (by linarith)
  have hzleDelta : smallDeltaZ beta Delta ≤ Delta := by
    unfold smallDeltaZ
    nlinarith
  have hzsmall : smallDeltaZ beta Delta ≤ 1/8 := by nlinarith
  have ha2 : 0 ≤ (smallDeltaLambdaPlus beta Delta)^2 := sq_nonneg _
  have ha2lt : (smallDeltaLambdaPlus beta Delta)^2 < 1 := by nlinarith
  have hrho0 : 0 < smallDeltaRho beta Delta := by
    unfold smallDeltaRho
    exact Real.exp_pos _
  have hrho1 : smallDeltaRho beta Delta < 1 := by
    unfold smallDeltaRho
    rw [Real.exp_lt_one_iff]
    nlinarith [hz]
  let d := 1-smallDeltaLambdaPlus beta Delta
  have hdlo : smallDeltaZ beta Delta ≤ d := by simpa [d] using hslowlo
  have hdhi : d ≤ smallDeltaZ beta Delta+2*Delta*smallDeltaZ beta Delta := by simpa [d] using hslowhi
  have hd0 : 0 ≤ d := by linarith
  have hdle : d ≤ (5/4 : ℝ)*smallDeltaZ beta Delta := by
    nlinarith [mul_le_mul_of_nonneg_right hD1 hz.le, hdhi]
  have hdSq : d^2 ≤ 2*Delta*smallDeltaZ beta Delta := by
    have hsquare := mul_le_mul hdle hdle hd0 (by positivity : 0 ≤ (5/4 : ℝ)*smallDeltaZ beta Delta)
    nlinarith [sq_nonneg (smallDeltaZ beta Delta), mul_le_mul_of_nonneg_right hzleDelta hz.le]
  have hidentity : (smallDeltaLambdaPlus beta Delta)^2-(1-2*smallDeltaZ beta Delta) =
      -2*(d-smallDeltaZ beta Delta)+d^2 := by dsimp [d]; ring
  have hdelta : |(smallDeltaLambdaPlus beta Delta)^2-(1-2*smallDeltaZ beta Delta)| ≤
      6*Delta*smallDeltaZ beta Delta := by
    rw [hidentity, abs_le]
    have hremlo : 0 ≤ d-smallDeltaZ beta Delta := by linarith
    constructor <;> nlinarith [hremlo, hdhi, hdSq]
  have hexp := exp_neg_linear_remainder (2*smallDeltaZ beta Delta) (by positivity)
  have hrhoapprox : |smallDeltaRho beta Delta-(1-2*smallDeltaZ beta Delta)| ≤
      4*(smallDeltaZ beta Delta)^2 := by
    have hx : (2*smallDeltaZ beta Delta)^2 = 4*(smallDeltaZ beta Delta)^2 := by ring
    rw [hx] at hexp
    simpa [smallDeltaRho] using hexp
  have hzsq : (smallDeltaZ beta Delta)^2 ≤ Delta*smallDeltaZ beta Delta := by
    nlinarith [mul_le_mul_of_nonneg_right hzleDelta hz.le]
  have habserr : |(smallDeltaLambdaPlus beta Delta)^2-smallDeltaRho beta Delta| ≤
      40*Delta*smallDeltaZ beta Delta := by
    calc
      |(smallDeltaLambdaPlus beta Delta)^2-smallDeltaRho beta Delta|
          ≤ |(smallDeltaLambdaPlus beta Delta)^2-(1-2*smallDeltaZ beta Delta)|+
            |(1-2*smallDeltaZ beta Delta)-smallDeltaRho beta Delta| := abs_sub_le _ _ _
      _ ≤ 6*Delta*smallDeltaZ beta Delta+4*(smallDeltaZ beta Delta)^2 :=
        add_le_add hdelta (by simpa [abs_sub_comm] using hrhoapprox)
      _ ≤ 40*Delta*smallDeltaZ beta Delta := by nlinarith [hzsq]
  have hgapA : 1-(smallDeltaLambdaPlus beta Delta)^2 ≥ smallDeltaZ beta Delta := by
    have hprodpos : 0 ≤ (1-smallDeltaLambdaPlus beta Delta)*smallDeltaLambdaPlus beta Delta :=
      mul_nonneg (by linarith) ha0.le
    nlinarith [hslowlo,hprodpos]
  have hgapR : 1-smallDeltaRho beta Delta ≥ smallDeltaZ beta Delta := by
    have hup := (abs_le.mp hrhoapprox).2
    have hzz : (smallDeltaZ beta Delta)^2 ≤ smallDeltaZ beta Delta/8 := by
      nlinarith [mul_le_mul_of_nonneg_right hzsmall hz.le]
    nlinarith [hup,hzz]
  have hmax : max ((smallDeltaLambdaPlus beta Delta)^2) (smallDeltaRho beta Delta) ≤
      1-smallDeltaZ beta Delta := max_le_iff.mpr ⟨by linarith,by linarith⟩
  exact ⟨ha2,ha2lt,hrho0,hrho1,habserr,by linarith⟩

theorem smallDelta_slow_power_error (beta Delta : ℝ) (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8) (k : ℕ) :
    |(smallDeltaLambdaPlus beta Delta ^ 2)^k - smallDeltaRho beta Delta^k| ≤ 80*Delta := by
  obtain ⟨ha0,ha1,hr0,hr1,herr,hgap⟩ :=
    smallDelta_slow_kernel_bounds beta Delta hb0 hb1 hD0 hD1
  have hz : 0 < smallDeltaZ beta Delta := by unfold smallDeltaZ; positivity
  have hpow := pow_sub_le_of_unit_interval (smallDeltaLambdaPlus beta Delta ^ 2)
    (smallDeltaRho beta Delta) ha0 (le_of_lt hr0) ha1 hr1 k
  have hden : 0 < 1-max (smallDeltaLambdaPlus beta Delta ^ 2) (smallDeltaRho beta Delta) := by
    linarith
  have herr' : |smallDeltaLambdaPlus beta Delta ^ 2-smallDeltaRho beta Delta| /
      (1-max (smallDeltaLambdaPlus beta Delta ^ 2) (smallDeltaRho beta Delta)) ≤ 80*Delta := by
    rw [div_le_iff₀ hden]
    have h := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 80*Delta by positivity)
    nlinarith [herr,h]
  exact hpow.trans herr'

theorem smallDelta_slow_geom_tv (beta Delta : ℝ) (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (hD0 : 0 < Delta) (hD1 : Delta ≤ 1/8) :
    Summable (fun n => |geomLag (smallDeltaLambdaPlus beta Delta ^ 2) n -
      geomLag (smallDeltaRho beta Delta) n|) ∧
    ∑' n, |geomLag (smallDeltaLambdaPlus beta Delta ^ 2) n -
      geomLag (smallDeltaRho beta Delta) n| ≤ 160*Delta := by
  obtain ⟨ha0,ha1,hr0,hr1,herr,hgap⟩ :=
    smallDelta_slow_kernel_bounds beta Delta hb0 hb1 hD0 hD1
  have htv := geomLag_tv_bound (smallDeltaLambdaPlus beta Delta ^ 2)
    (smallDeltaRho beta Delta) ha0 (le_of_lt hr0) ha1 hr1
  have hz : 0 < smallDeltaZ beta Delta := by unfold smallDeltaZ; positivity
  have hden : 0 < 1-max (smallDeltaLambdaPlus beta Delta ^ 2) (smallDeltaRho beta Delta) := by
    linarith
  refine ⟨htv.1, ?_⟩
  have hratio : 2*|smallDeltaLambdaPlus beta Delta ^ 2-smallDeltaRho beta Delta| /
      (1-max (smallDeltaLambdaPlus beta Delta ^ 2) (smallDeltaRho beta Delta)) ≤ 160*Delta := by
    rw [div_le_iff₀ hden]
    have h := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 80*Delta by positivity)
    nlinarith [herr,h]
  exact htv.2.trans hratio

end
end SparseSGD.Scaling
