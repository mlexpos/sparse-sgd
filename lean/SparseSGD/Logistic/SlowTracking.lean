import SparseSGD.Logistic.DynamicRank
namespace SparseSGD.Logistic
noncomputable section
open MeasureTheory
set_option maxHeartbeats 1600000

/-- LR2 units: `(theta,m_parallel/p,R,delta*V_perp/p²,C_perp/p)`.
The learning step is `z=eta*p` and the retention step is `h=1-beta`. -/
def slowCoefficientStep (r h z Phi a b d0 xi rho : ℝ) (y : DynamicState) : DynamicState :=
  let beta := 1-h
  let Yn := beta*y 1+h*(a*y 0+b*r)
  let Wn := beta^2*y 3+2*beta*z*a*y 4+h*(2*Phi*d0+z*a^2*rho*y 2+xi*y 2)
  let Cn := beta*y 4+h*a*y 2-h*Wn
  ![y 0-z*Yn, Yn, y 2-2*z*beta*y 4-2*z*h*a*y 2+z*h*Wn,Wn,Cn]

/-- The normalization changes only the momentum variance coordinate. -/
def slowNormalize (delta : ℝ) (y : DynamicState) : DynamicState :=
  ![y 0,y 1,y 2,delta*y 3,y 4]

theorem slowCoefficientStep_eq_dynamic (r h delta Phi a b d0 xi rho noise : ℝ)
    (y : DynamicState)
    (hn : delta*h*noise=2*Phi*d0+(delta*h)*a^2*rho*y 2+xi*y 2) :
    slowNormalize delta (dynamicCoefficientStep r h delta a b noise y) =
      slowCoefficientStep r h (delta*h) Phi a b d0 xi rho (slowNormalize delta y) := by
  have hv : delta*((1-h)^2*y 3+2*h*(1-h)*a*y 4+h^2*noise) =
      (1-h)^2*(delta*y 3)+2*(1-h)*(delta*h)*a*y 4+
        h*(2*Phi*d0+(delta*h)*a^2*rho*y 2+xi*y 2) := by
    have hn' := congrArg (fun x : ℝ => h*x) hn
    nlinarith only [hn']
  ext i
  fin_cases i <;> simp [slowNormalize,dynamicCoefficientStep,slowCoefficientStep]
  all_goals try rw [← hv]
  all_goals nlinarith only [hv]

/-- The leading frozen fast target at a fixed slow position. -/
def slowFastTarget (beta Phi curvature R : ℝ) : ℝ × ℝ :=
  (curvature*R-2*Phi/(1+beta),2*Phi/(1+beta))

def slowFastNorm (v : ℝ × ℝ) : ℝ := |v.1|+2*|v.2|

def slowFastLinear (h z a : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  let beta := 1-h
  let Wn := beta^2*v.2+2*beta*z*a*v.1
  (beta*v.1-h*Wn,Wn)

/-- The homogeneous fast pair contracts uniformly on the retention clock,
including beta=0. The only step constraint is a small learning/retention ratio. -/
theorem slowFastLinear_contract (h z a : ℝ) (v : ℝ × ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hsmall : 12*z*a ≤ h) :
    slowFastNorm (slowFastLinear h z a v) ≤ (1-h/2)*slowFastNorm v := by
  let beta := 1-h
  have hbeta : 0 ≤ beta := by dsimp [beta]; linarith
  have hbeta1 : beta ≤ 1 := by dsimp [beta]; linarith
  have hW : |beta^2*v.2+2*beta*z*a*v.1| ≤
      beta^2*|v.2|+2*beta*z*a*|v.1| := by
    calc
      _ ≤ |beta^2*v.2|+|2*beta*z*a*v.1| := abs_add_le _ _
      _ = _ := by simp [abs_mul,abs_of_nonneg hbeta,abs_of_nonneg hz,abs_of_nonneg ha]
  have hC := abs_sub (beta*v.1) (h*(beta^2*v.2+2*beta*z*a*v.1))
  rw [abs_mul,abs_of_nonneg hbeta,abs_mul,abs_of_pos hh] at hC
  change |beta*v.1-h*(beta^2*v.2+2*beta*z*a*v.1)|+
    2*|beta^2*v.2+2*beta*z*a*v.1| ≤ (1-h/2)*(|v.1|+2*|v.2|)
  have hpre : |beta*v.1-h*(beta^2*v.2+2*beta*z*a*v.1)|+
      2*|beta^2*v.2+2*beta*z*a*v.1| ≤
        (beta+(h+2)*2*beta*z*a)*|v.1|+(h+2)*beta^2*|v.2| := by
    have hwmul := mul_le_mul_of_nonneg_left hW (show 0 ≤ h+2 by linarith)
    nlinarith only [hC,hwmul]
  have hc : beta+(h+2)*2*beta*z*a ≤ 1-h/2 := by
    have ht : (h+2)*2*beta*z*a ≤ 6*z*a := by
      have hleft : (h+2)*2*beta ≤ 6 := by nlinarith
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hleft (mul_nonneg hz ha)
    dsimp [beta] at *
    nlinarith only [ht,hsmall]
  have hv : (h+2)*beta^2 ≤ 2*(1-h/2) := by
    dsimp [beta]
    have hs : h^2 ≤ 1 := by nlinarith
    have hp : 0 ≤ h*(2-h^2) := mul_nonneg hh.le (by linarith)
    nlinarith only [hp]
  apply hpre.trans
  have hc' := mul_le_mul_of_nonneg_right hc (abs_nonneg v.1)
  have hv' := mul_le_mul_of_nonneg_right hv (abs_nonneg v.2)
  nlinarith only [hc',hv']

/-- The weighted fast norm obeys the triangle inequality. -/
theorem slowFastNorm_add (u v : ℝ × ℝ) :
    slowFastNorm (u+v) ≤ slowFastNorm u+slowFastNorm v := by
  dsimp [slowFastNorm]
  have h1 := abs_add_le u.1 v.1
  have h2 := abs_add_le u.2 v.2
  nlinarith only [h1,h2]

/-- Actual logistic coefficients in the LR2 normalization. -/
def slowDriftMap {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu theta : Vec d) (y : DynamicState) : DynamicState :=
  slowCoefficientStep (r mu) (1-beta) (eta*(p:ℝ)) (dynamicSourceLoad d B eta)
    (coefA p mu theta/(p:ℝ)) (coefB p mu theta/(p:ℝ))
    (coefD0 p mu theta/(p:ℝ)) (eta*coefDtheta p mu theta/((B:ℝ)*(p:ℝ)))
    (((B:ℝ)-1)/(B:ℝ)) y

/-- The LR2 map is exactly the actual LR34 coefficient map expressed in
its fast-tracking units, at every finite learning and retention step. -/
theorem slowDriftMap_eq_dynamic {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
    (mu theta : Vec d) (y : DynamicState) (hp : (p:ℝ) ≠ 0)
    (hB : (B:ℝ) ≠ 0) (hh : 1-beta ≠ 0) :
    slowNormalize (eta*(p:ℝ)/(1-beta)) (dynamicDriftMap (B:=B) eta beta p mu theta y) =
      slowDriftMap (B:=B) eta beta p mu theta (slowNormalize (eta*(p:ℝ)/(1-beta)) y) := by
  have hz : eta*(p:ℝ)/(1-beta)*(1-beta)=eta*(p:ℝ) := div_mul_cancel₀ _ hh
  have hn : (eta*(p:ℝ)/(1-beta))*(1-beta)*
      ((((d-1:ℝ)*coefD0 p mu theta+y 2*coefDtheta p mu theta)/(B:ℝ)+
        ((B:ℝ)-1)/(B:ℝ)*(coefA p mu theta)^2*y 2)/(p:ℝ)^2) =
      2*(dynamicSourceLoad d B eta)*(coefD0 p mu theta/(p:ℝ))+
        ((eta*(p:ℝ)/(1-beta))*(1-beta))*(coefA p mu theta/(p:ℝ))^2*
          (((B:ℝ)-1)/(B:ℝ))*y 2+
        (eta*coefDtheta p mu theta/((B:ℝ)*(p:ℝ)))*y 2 := by
    unfold dynamicSourceLoad
    field_simp
    <;> ring
  have h := slowCoefficientStep_eq_dynamic (r mu) (1-beta) (eta*(p:ℝ)/(1-beta))
    (dynamicSourceLoad d B eta) (coefA p mu theta/(p:ℝ)) (coefB p mu theta/(p:ℝ))
    (coefD0 p mu theta/(p:ℝ)) (eta*coefDtheta p mu theta/((B:ℝ)*(p:ℝ)))
    (((B:ℝ)-1)/(B:ℝ))
    ((((d-1:ℝ)*coefD0 p mu theta+y 2*coefDtheta p mu theta)/(B:ℝ)+
      ((B:ℝ)-1)/(B:ℝ)*(coefA p mu theta)^2*y 2)/(p:ℝ)^2) y hn
  simpa only [hz,slowDriftMap,dynamicDriftMap] using h

/-- A retention contraction tracks a moving target with a finite geometric
initial layer. This estimate does not require h to tend to zero. -/
theorem slow_tracking_geometric (e : ℕ → ℝ) (h G : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hG : 0 ≤ G)
    (hrec : ∀ k, e (k+1) ≤ (1-h/2)*e k+G) :
    ∀ k, e k ≤ (1-h/2)^k*e 0+2*G/h := by
  have hq : 0 ≤ 1-h/2 := by linarith
  intro k
  induction k with
  | zero => simp; positivity
  | succ k ih =>
    apply (hrec k).trans
    have hb := mul_le_mul_of_nonneg_left ih hq
    have hg : (1-h/2)*(2*G/h)+G=2*G/h := by field_simp; ring
    calc
      _ ≤ (1-h/2)*((1-h/2)^k*e 0+2*G/h)+G := add_le_add hb le_rfl
      _ = _ := by rw [pow_succ]; nlinarith only [hg]

/-- The cumulative learning-clock cost of the cold-start initial layer is
bounded by twice the learning/retention ratio. -/
theorem slow_initial_layer_sum (h z : ℝ) (N : ℕ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hz : 0 ≤ z) :
    z*(∑ k ∈ Finset.range N, (1-h/2)^k) ≤ 2*z/h := by
  have hq : 0 ≤ 1-h/2 := by linarith
  have hid : ∀ n, (h/2)*(∑ k ∈ Finset.range n, (1-h/2)^k)=1-(1-h/2)^n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,pow_succ]; nlinarith only [ih]
  have hb : (h/2)*(∑ k ∈ Finset.range N, (1-h/2)^k) ≤ 1 := by
    rw [hid]
    linarith [pow_nonneg hq N]
  apply (le_div_iff₀ hh).mpr
  have hz' := mul_le_mul_of_nonneg_left hb hz
  nlinarith only [hz']

/-- The LR2 coordinate map is the actual integrated logistic transition. -/
theorem slowDriftMap_eq_integral {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0 < B)
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (s : State d)
    (hr : 0 < r mu) (hp0 : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1)
    (heta : eta ≠ 0) (hh : 1-beta ≠ 0) :
    ∀ i, (∫ a : Batch d B, slowNormalize (eta*(p:ℝ)/(1-beta))
      (dynamicSummary p mu (update eta beta p mu s a)) i ∂batchLaw d B p) =
      slowDriftMap (B:=B) eta beta p mu s.1
        (slowNormalize (eta*(p:ℝ)/(1-beta)) (dynamicSummary p mu s)) i := by
  have hd := dynamicDriftMap_eq_integral H hB eta beta p mu s hr hp0 hp1 heta hh
  have hBr : (B:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  rw [← slowDriftMap_eq_dynamic eta beta p mu s.1 (dynamicSummary p mu s) hp0.ne' hBr hh]
  intro i
  fin_cases i
  · exact hd 0
  · exact hd 1
  · exact hd 2
  · change (∫ a : Batch d B, (eta*(p:ℝ)/(1-beta))*dynamicSummary p mu (update eta beta p mu s a) 3
        ∂batchLaw d B p) = (eta*(p:ℝ)/(1-beta))*dynamicDriftMap (B:=B) eta beta p mu s.1 (dynamicSummary p mu s) 3
    rw [MeasureTheory.integral_const_mul,hd 3]
  · exact hd 4

/-- The bulk slow residual separates the fast-pair tracking error from the
actual curvature error. This is the exact finite-step algebra. -/
theorem slow_bulk_residual_identity (r h z Phi a b d0 xi rho curvature : ℝ)
    (y : DynamicState) (hh1 : h ≤ 1) :
    slowCoefficientStep r h z Phi a b d0 xi rho y 2-y 2-z*(2*Phi-2*curvature*y 2) =
      z*(-2*(1-h)*(y 4-(slowFastTarget (1-h) Phi curvature (y 2)).1)-
        2*h*(a-curvature)*y 2+
        h*(slowCoefficientStep r h z Phi a b d0 xi rho y 3-
          (slowFastTarget (1-h) Phi curvature (y 2)).2)) := by
  have hn : 1+(1-h) ≠ 0 := by linarith
  simp [slowCoefficientStep,slowFastTarget]
  field_simp
  <;> ring

/-- Exact signal slow residual, before the tracking estimate is applied. -/
theorem slow_signal_residual_identity (r h z Phi a b d0 xi rho curvature : ℝ)
    (y : DynamicState) :
    slowCoefficientStep r h z Phi a b d0 xi rho y 0-y 0-z*(r-curvature*y 0) =
      -z*(slowCoefficientStep r h z Phi a b d0 xi rho y 1-(curvature*y 0-r)) := by
  simp [slowCoefficientStep]
  ring

end
end SparseSGD.Logistic
