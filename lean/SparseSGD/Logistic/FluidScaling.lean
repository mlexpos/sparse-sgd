import SparseSGD.Logistic.IncrementSourceRates
import SparseSGD.Logistic.FluidDomain

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

theorem eta_div_batch_le_phi {d B : ℕ} (eta : ℝ) (hd : 2 ≤ d)
    (hB : 0 < B) (heta : 0 ≤ eta) :
    eta/(B : ℝ) ≤ 4*logisticPhi d B eta/(d : ℝ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  unfold logisticPhi
  rw [div_le_div_iff₀ hb (by linarith : (0 : ℝ)<d)]
  field_simp
  nlinarith [mul_nonneg heta (show 0 ≤ (d : ℝ)-2 by linarith)]

/-- The source variance accumulated on a finite learning horizon has the
claimed cubic load factor, proved from the actual finite-batch Phi identity. -/
theorem lrSourceVariance_horizon_bound {d B : ℕ}
    (eta : ℝ) (p : unitInterval) (mu : Vec d) (N : ℕ) (T : ℝ)
    (hd : 2 ≤ d) (hB : 0 < B) (hp : 0 < (p : ℝ)) (heta : 0 ≤ eta)
    (hz : eta*(p : ℝ) ≤ 1) (hT : (N : ℝ)*(eta*(p : ℝ)) ≤ T) :
    (N : ℝ)*lrSourceVariance d B eta p mu ≤
      10*T*(1+logisticPhi d B eta)^3*(1+(r mu)^2)/(d : ℝ) := by
  let Phi := logisticPhi d B eta
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hdminus : 0 ≤ (d : ℝ)-1 := by linarith
  have hphi : 0 ≤ Phi := by dsimp [Phi,logisticPhi]; positivity
  have hTp : 0 ≤ T := (by positivity : 0 ≤ (N : ℝ)*(eta*(p : ℝ))).trans hT
  have hstep := eta_div_batch_le_phi eta hd hB heta
  change eta/(B : ℝ) ≤ 4*Phi/(d : ℝ) at hstep
  have hidentity : (N : ℝ)*lrSourceVariance d B eta p mu =
      ((N : ℝ)*(eta*(p : ℝ)))*
        (eta/(B : ℝ)*(1+(r mu)^2)+Phi^2*(eta/(B : ℝ)+2*eta*(p : ℝ)/(d : ℝ))) := by
    dsimp [lrSourceVariance,lrSourceQuadraticRate,Phi]
    field_simp
    <;> ring
  have hz' : 2*eta*(p : ℝ)/(d : ℝ) ≤ 2/(d : ℝ) := by
    apply div_le_div_of_nonneg_right _ hdp.le
    nlinarith
  have hpoly : 4*Phi*(1+(r mu)^2)+Phi^2*(4*Phi+2) ≤
      10*(1+Phi)^3*(1+(r mu)^2) := by
    have h1 : Phi ≤ (1+Phi)^3 := by nlinarith [sq_nonneg Phi, pow_nonneg hphi 3]
    have h2 : 4*Phi^3+2*Phi^2 ≤ 6*(1+Phi)^3 := by nlinarith [sq_nonneg Phi,pow_nonneg hphi 3]
    have H1 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ 4*(1+(r mu)^2) by positivity)
    have H2 := mul_le_mul_of_nonneg_left (show 1 ≤ 1+(r mu)^2 by nlinarith [sq_nonneg (r mu)])
      (show 0 ≤ 6*(1+Phi)^3 by positivity)
    nlinarith only [h2,H1,H2]
  have hbracket : eta/(B : ℝ)*(1+(r mu)^2)+Phi^2*(eta/(B : ℝ)+2*eta*(p : ℝ)/(d : ℝ)) ≤
      10*(1+Phi)^3*(1+(r mu)^2)/(d : ℝ) := by
    calc
      _ ≤ (4*Phi/(d : ℝ))*(1+(r mu)^2)+Phi^2*(4*Phi/(d : ℝ)+2/(d : ℝ)) := by gcongr
      _ = (4*Phi*(1+(r mu)^2)+Phi^2*(4*Phi+2))/(d : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hpoly hdp.le
  rw [hidentity]
  have H := mul_le_mul hT hbracket (by positivity)
    (show 0 ≤ T from hTp)
  convert H using 1 <;> ring

end
end SparseSGD.Logistic
