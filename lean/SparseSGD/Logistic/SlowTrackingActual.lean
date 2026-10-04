import SparseSGD.Logistic.SlowTrackingCompact
namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 1600000

/-- The compact tracking and slow residual estimates apply to the actual
finite-batch logistic drift, with its actual geometric curvature and mixed
variance coefficient. -/
theorem slowDriftMap_compact_bounds (r0 Phi M : ℝ) (hPhi : 0 ≤ Phi) (hM : 0 ≤ M)
    (L : ℝ≥0) (hLip : LipschitzOnWith L (slowTargetMap r0) (Metric.closedBall 0 M))
    {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu theta : Vec d) (y : DynamicState)
    (hr : r mu=r0) (hload : dynamicSourceLoad d B eta=Phi)
    (hp : 0 < (p:ℝ)) (hB : 0 < B) (hd : 2 ≤ d) (heta : 0 ≤ eta)
    (hh : 0 < 1-beta) (hh1 : 1-beta ≤ 1) (hz1 : eta*(p:ℝ) ≤ 1)
    (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1/2) (htame : tameError p mu theta ≤ e)
    (hgeom : ‖theta‖^2=y 0^2+y 2) (hy : ‖slowPosition y‖ ≤ M)
    (hsmall : 48*(eta*(p:ℝ))*slowCompactCurvature M ≤ 1-beta) :
    let yn := slowDriftMap (B:=B) eta beta p mu theta y
    let z := eta*(p:ℝ)
    let h := 1-beta
    let K := slowCompactMovement r0 Phi M
    let Cg := slowCompactSignalError r0 M
    let Cf := slowFrozenConstant (slowCompactCurvature M) M Phi
    ‖slowPosition yn-slowPosition y‖ ≤ z*K*(1+slowTrackingError r0 h Phi y) ∧
    ‖slowPosition yn-(slowPosition y+z • slowField r0 Phi (y 0) (y 2))‖ ≤
      z*(3*slowTrackingError r0 h Phi y+(Cg+12*slowCompactCurvature M*M+Cf)*e+Cf*z) ∧
    (‖slowPosition yn‖ ≤ M → 8*(L:ℝ)*z*K ≤ h →
      slowTrackingError r0 h Phi yn ≤ (1-h/4)*slowTrackingError r0 h Phi y+
        (Cg+Cf+2*(L:ℝ)*K)*(z+h*e)) := by
  have hc := dynamic_normalized_coefficient_errors (B:=B) p mu theta (1-beta)
    hp hh.le hB hd (htame.trans he1)
  have haeq : gaussianAlpha mu theta=alpha (y 0) (y 2) r0 := by
    have hs := dynamicAlpha_of_geometry mu theta y hgeom
    rw [hr] at hs
    exact hs.symm
  rw [haeq] at hc
  have hxi := slow_mixed_noise_tame (B:=B) eta p mu theta heta hp hB hd (htame.trans he1)
  rw [hload] at hxi
  have hprob : (p:ℝ)<1 := by
    have hh := (tameError_ge_probability p mu theta).trans htame
    linarith
  have ha0 : 0 ≤ coefA p mu theta/(p:ℝ) := div_nonneg (coefA_pos p mu theta hp hprob).le hp.le
  have hrho : |((B:ℝ)-1)/(B:ℝ)| ≤ 1 := by
    have hBr : 0 < (B:ℝ) := by exact_mod_cast hB
    have hB1 : (1:ℝ) ≤ B := by exact_mod_cast Nat.succ_le_iff.mpr hB
    rw [abs_of_nonneg (div_nonneg (by linarith) hBr.le)]
    exact (div_le_iff₀ hBr).mpr (by linarith)
  have hcurv0 : 0 ≤ alpha (y 0) (y 2) r0 := (Real.exp_pos _).le
  have hs := slowCoefficientStep_compact_bounds r0 Phi M hPhi hM L hLip
    (1-beta) (eta*(p:ℝ)) (coefA p mu theta/(p:ℝ)) (coefB p mu theta/(p:ℝ))
    (coefD0 p mu theta/(p:ℝ)) (eta*coefDtheta p mu theta/((B:ℝ)*(p:ℝ)))
    (((B:ℝ)-1)/(B:ℝ)) e y hh hh1 (mul_nonneg heta hp.le) hz1 he he1 ha0
    (hc.1.trans (by gcongr)) (hc.2.1.trans (by gcongr)) (hc.2.2.1.trans (by gcongr))
    (hxi.trans (by gcongr)) hrho hy hsmall
  simpa only [slowDriftMap,hr,hload] using hs

end
end SparseSGD.Logistic
