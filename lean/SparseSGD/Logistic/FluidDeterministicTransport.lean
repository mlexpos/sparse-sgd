import SparseSGD.Logistic.FluidDeterministicRealization
import SparseSGD.Logistic.DynamicSource
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000

def dynamicToMatched (delta : ℝ) (x : DynamicState) : Fin 5→ℝ :=
  ![x 0,delta*x 1,x 2,delta*x 4,delta^2*x 3]
def matchedToDynamic (delta : ℝ) (y : Fin 5→ℝ) : DynamicState :=
  ![y 0,y 1/delta,y 2,y 4/delta^2,y 3/delta]
theorem dynamicToMatched_matchedToDynamic (delta : ℝ) (hd : delta≠0) (y : Fin 5→ℝ) :
    dynamicToMatched delta (matchedToDynamic delta y)=y := by
  ext i;fin_cases i <;> simp [dynamicToMatched,matchedToDynamic,hd] <;> field_simp [hd]
theorem matchedToDynamic_dynamicToMatched (delta : ℝ) (hd : delta≠0) (y : DynamicState) :
    matchedToDynamic delta (dynamicToMatched delta y)=y := by
  ext i;fin_cases i <;> simp [dynamicToMatched,matchedToDynamic,hd] <;> field_simp [hd]

theorem matchedToDynamic_drift {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu theta : Vec d) (y : Fin 5→ℝ) (hr : 0<r mu) (hp : (p:ℝ)≠0)
    (heta : eta≠0) (heps : 1-beta≠0) (hB : (B:ℝ)≠0)
    (ht : signalCoord mu theta=y 0) (hq : ‖theta‖^2=(y 0)^2+y 2) :
    matchedToDynamic (eta*(p:ℝ)/(1-beta)) (matchedDriftMap (B:=B) eta beta p mu y)=
      dynamicDriftMap (B:=B) eta beta p mu theta
        (matchedToDynamic (eta*(p:ℝ)/(1-beta)) y) := by
  have hA : scalarCoefA p (r mu) (y 0) ((y 0)^2+y 2)=coefA p mu theta := by
    rw [coefA_eq_scalar p mu theta hr,ht,hq]
  have hb : scalarCoefB p (r mu) (y 0) ((y 0)^2+y 2)=coefB p mu theta := by
    rw [coefB_eq_scalar p mu theta hr,ht,hq]
  have hD : scalarCoefD0 p (r mu) (y 0) ((y 0)^2+y 2)=coefD0 p mu theta := by
    rw [coefD0_eq_scalar p mu theta hr,ht,hq]
  have hDt : scalarCoefDtheta p (r mu) (y 0) ((y 0)^2+y 2)=coefDtheta p mu theta := by
    rw [coefDtheta_eq_scalar p mu theta hr,ht,hq]
  unfold matchedDriftMap
  dsimp only
  rw [hA,hb,hD,hDt]
  ext i
  fin_cases i <;> simp [matchedToDynamic,matchedCoefficientStep,dynamicDriftMap,dynamicCoefficientStep]
  all_goals field_simp [hp,heta,heps,hB] <;> ring

theorem dynamicToMatched_norm_bound (delta M : ℝ) (y : DynamicState)
    (hM : 0≤M) (hy : ‖y‖≤M) :
    ‖dynamicToMatched delta y‖≤(1+|delta|+delta^2)*M := by
  have hc (i : Fin 5) : |y i|≤M := by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y i).trans hy
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i <;> simp [dynamicToMatched,Real.norm_eq_abs,abs_mul,abs_pow]
  all_goals nlinarith [hc 0,hc 1,hc 2,hc 3,hc 4,abs_nonneg delta,sq_nonneg delta]
end
end SparseSGD.Logistic
