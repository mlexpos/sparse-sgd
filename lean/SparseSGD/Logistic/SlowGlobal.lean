import SparseSGD.Logistic.SlowPositivity

namespace SparseSGD.Logistic
open Filter Topology
noncomputable section
set_option maxHeartbeats 1000000

/-- Uniform scalar dissipation on a half-line implies convergence to zero. -/
theorem scalar_dissipation_tendsto (D D' : ℝ → ℝ) (c a : ℝ) (hc : 0 < c)
    (hD : ∀ t, a ≤ t → 0 ≤ D t)
    (hderiv : ∀ t, a ≤ t → HasDerivAt D (D' t) t)
    (hdiss : ∀ t, a ≤ t → D' t ≤ -c*D t) :
    Tendsto D atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => c*(t-a)) atTop atTop :=
    (show Tendsto (fun t : ℝ => t-a) atTop atTop from by
      simpa only [sub_eq_add_neg,id_eq] using
        (tendsto_id.atTop_add (show Tendsto (fun _ : ℝ => -a) atTop (𝓝 (-a)) from tendsto_const_nhds))).const_mul_atTop hc
  have he : Tendsto (fun t : ℝ => Real.exp (-c*(t-a))*D a) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_mul,zero_mul,mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).mul_const (D a)
  apply squeeze_zero' _ _ he
  · filter_upwards [eventually_ge_atTop a] with t ht
    exact hD t ht
  · filter_upwards [eventually_ge_atTop a] with t ht
    exact scalar_dissipation_bound D D' c a t
      (fun s hs => hderiv s hs.1) (fun s hs => hdiss s hs.1) ht

/-- Zero-temperature convergence includes solutions starting on the zero-bulk boundary. -/
theorem slow_zero_tendsto (r a : ℝ) (y : ℝ → ℝ × ℝ) (hy0 : 0 ≤ (y a).2)
    (hy : ∀ t, a ≤ t → HasDerivAt y (slowField r 0 (y t).1 (y t).2) t) :
    Tendsto y atTop (𝓝 (r,0)) := by
  have hR := slow_bulk_nonnegative r 0 a y le_rfl hy0 hy
  let D := fun t => ((y t).1-r)^2+(y t).2
  let D' := fun t => 2*((y t).1-r)*(r-alpha (y t).1 (y t).2 r*(y t).1)-
    2*alpha (y t).1 (y t).2 r*(y t).2
  have hderiv (t : ℝ) (ht : a ≤ t) : HasDerivAt D (D' t) t := by
    have Hfst : HasDerivAt (fun s => (y s).1) (slowField r 0 (y t).1 (y t).2).1 t :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hy t ht)
    have Hsnd : HasDerivAt (fun s => (y s).2) (slowField r 0 (y t).1 (y t).2).2 t :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hy t ht)
    convert ((Hfst.sub_const r).pow 2).add Hsnd using 1 <;> dsimp [D',slowField] <;> ring
  have hnonneg (t : ℝ) (ht : a ≤ t) : 0 ≤ D t := by
    dsimp [D]
    exact add_nonneg (sq_nonneg _) (hR t ht).1
  have hdiss (t : ℝ) (ht : a ≤ t) : D' t ≤ -(2*Real.exp (-r^2/2))*D t := by
    have heq : alpha r 0 r*r=r := by simp [alpha]
    have H := sqrtBulk_zero_slow_dissipation r (y t).1 (Real.sqrt (y t).2) r heq
    rw [Real.sq_sqrt (hR t ht).1] at H
    have Hsq := Real.sq_sqrt (hR t ht).1
    dsimp [D,D']
    have Hmul := congrArg (fun z : ℝ => (2*alpha (y t).1 (y t).2 r)*z) Hsq
    nlinarith only [H,Hmul]
  have hD := scalar_dissipation_tendsto D D' (2*Real.exp (-r^2/2)) a (by positivity) hnonneg hderiv hdiss
  have hroot : Tendsto (fun t => Real.sqrt (D t)) atTop (𝓝 0) := by simpa using hD.sqrt
  have htheta : Tendsto (fun t => (y t).1) atTop (𝓝 r) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) _ hroot
    filter_upwards [eventually_ge_atTop a] with t ht
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    dsimp [D]
    linarith [(hR t ht).1]
  have hbulk : Tendsto (fun t => (y t).2) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hD
    · filter_upwards [eventually_ge_atTop a] with t ht
      exact (hR t ht).1
    · exact Eventually.of_forall fun t => by dsimp [D]; nlinarith [sq_nonneg ((y t).1-r)]
  exact htheta.prodMk_nhds hbulk

theorem positiveRoot_zero_load (r : ℝ) (hr : 0 < r) : positiveRoot r 0=r := by
  have H := positiveRoot_spec r 0 hr le_rfl
  have Hl := root_lower_bound r 0 (positiveRoot r 0) hr le_rfl H.1 H.2
  have Hu := positive_root_le_r r 0 (positiveRoot r 0) hr le_rfl H.1 H.2
  simp only [zero_div,Real.exp_zero,div_one] at Hl
  linarith

/-- Global convergence of every actual slow trajectory from nonnegative bulk,
including positive forcing from zero bulk and the zero-temperature boundary. -/
theorem slow_global_convergence (r Phi a : ℝ) (y : ℝ → ℝ × ℝ)
    (hr : 0 < r) (hPhi : 0 ≤ Phi) (hy0 : 0 ≤ (y a).2)
    (hy : ∀ t, a ≤ t → HasDerivAt y (slowField r Phi (y t).1 (y t).2) t) :
    Tendsto y atTop (𝓝 (positiveRoot r Phi,equilibriumBulk r Phi)) := by
  rcases hPhi.eq_or_lt with hzero | hpositive
  · have hPhi0 : Phi=0 := hzero.symm
    subst Phi
    simpa only [positiveRoot_zero_load r hr,equilibriumBulk,zero_mul,zero_div] using
      slow_zero_tendsto r a y hy0 hy
  · have htheta := (positiveRoot_spec r Phi hr hpositive.le).1
    have hbulk : 0 < equilibriumBulk r Phi := by dsimp [equilibriumBulk]; positivity
    have hX : 0 < Real.sqrt (equilibriumBulk r Phi) := Real.sqrt_pos.mpr hbulk
    have hfield := positiveRoot_slowField_zero r Phi hr hpositive.le
    simp only [slowField,Prod.mk.injEq] at hfield
    have heq1 : alpha (positiveRoot r Phi) ((Real.sqrt (equilibriumBulk r Phi))^2) r*
        positiveRoot r Phi=r := by rw [Real.sq_sqrt hbulk.le]; linarith [hfield.1]
    have heq2 : alpha (positiveRoot r Phi) ((Real.sqrt (equilibriumBulk r Phi))^2) r*
        (Real.sqrt (equilibriumBulk r Phi))^2=Phi := by rw [Real.sq_sqrt hbulk.le]; linarith [hfield.2]
    have hR := slow_bulk_nonnegative r Phi a y hpositive.le hy0 hy
    have H := slow_positive_tendsto r Phi (positiveRoot r Phi) (Real.sqrt (equilibriumBulk r Phi)) (a+1) y
      hpositive.le hX heq1 heq2 (fun t ht => hy t (by linarith))
      (fun t ht => (hR t (by linarith)).2 hpositive (by linarith))
    simpa only [Real.sq_sqrt hbulk.le] using H

end
end SparseSGD.Logistic
