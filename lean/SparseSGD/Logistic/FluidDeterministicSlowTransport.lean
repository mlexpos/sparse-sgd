import SparseSGD.Logistic.FluidDeterministicTransport
import SparseSGD.Logistic.SlowLimitSource
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000

def slowToMatched (delta : ℝ) (x : DynamicState) : Fin 5→ℝ :=
  ![x 0,delta*x 1,x 2,delta*x 4,delta*x 3]
def matchedToSlow (delta : ℝ) (y : Fin 5→ℝ) : DynamicState :=
  ![y 0,y 1/delta,y 2,y 4/delta,y 3/delta]
theorem slowToMatched_matchedToSlow (delta : ℝ) (hd : delta≠0) (y : Fin 5→ℝ) :
    slowToMatched delta (matchedToSlow delta y)=y := by
  ext i;fin_cases i <;> simp [slowToMatched,matchedToSlow] <;> field_simp [hd]
theorem matchedToSlow_eq_normalize (delta : ℝ) (hd : delta≠0) (y : Fin 5→ℝ) :
    matchedToSlow delta y=slowNormalize delta (matchedToDynamic delta y) := by
  ext i;fin_cases i <;> simp [matchedToSlow,slowNormalize,matchedToDynamic] <;> field_simp [hd]

theorem matchedToSlow_drift {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu theta : Vec d) (y : Fin 5→ℝ) (hr : 0<r mu) (hp : (p:ℝ)≠0)
    (heta : eta≠0) (heps : 1-beta≠0) (hB : (B:ℝ)≠0)
    (ht : signalCoord mu theta=y 0) (hq : ‖theta‖^2=(y 0)^2+y 2) :
    matchedToSlow (eta*(p:ℝ)/(1-beta)) (matchedDriftMap (B:=B) eta beta p mu y)=
      slowDriftMap (B:=B) eta beta p mu theta
        (matchedToSlow (eta*(p:ℝ)/(1-beta)) y) := by
  have hd : eta*(p:ℝ)/(1-beta)≠0 := div_ne_zero (mul_ne_zero heta hp) heps
  rw [matchedToSlow_eq_normalize _ hd,matchedToDynamic_drift eta beta p mu theta y hr hp heta heps hB ht hq,
    slowDriftMap_eq_dynamic eta beta p mu theta _ hp hB heps,← matchedToSlow_eq_normalize _ hd]

theorem slowToMatched_norm_bound (delta M : ℝ) (y : DynamicState)
    (hM : 0≤M) (hy : ‖y‖≤M) :
    ‖slowToMatched delta y‖≤(1+|delta|)*M := by
  have hc (i : Fin 5) : |y i|≤M := by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y i).trans hy
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i <;> simp [slowToMatched,Real.norm_eq_abs,abs_mul]
  all_goals nlinarith [hc 0,hc 1,hc 2,hc 3,hc 4,abs_nonneg delta]
end
end SparseSGD.Logistic
