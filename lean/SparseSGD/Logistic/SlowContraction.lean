import SparseSGD.Logistic.EquilibriumAnalysis

namespace SparseSGD.Logistic
open Filter Topology
noncomputable section
set_option maxHeartbeats 1000000

/-- A dimension-free positive lower curvature for the square-root bulk variables. -/
theorem sqrtBulk_alpha_lower (r theta X : ℝ) :
    Real.exp (-r^2/2) ≤ alpha theta (X^2) r := by
  unfold alpha
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg theta,sq_nonneg X]

/-- The radial exponential gradient is uniformly strongly monotone. -/
theorem sqrtBulk_radial_monotone (r theta X theta' X' : ℝ) :
    Real.exp (-r^2/2)*((theta-theta')^2+(X-X')^2) ≤
      (theta-theta')*(alpha theta (X^2) r*theta-alpha theta' (X'^2) r*theta')+
      (X-X')*(alpha theta (X^2) r*X-alpha theta' (X'^2) r*X') := by
  let a := alpha theta (X^2) r
  let b := alpha theta' (X'^2) r
  have ha := sqrtBulk_alpha_lower r theta X
  have hb := sqrtBulk_alpha_lower r theta' X'
  have hprod : 0 ≤ (a-b)*(theta^2+X^2-(theta'^2+X'^2)) := by
    by_cases H : theta'^2+X'^2 ≤ theta^2+X^2
    · have Hexp : b ≤ a := by
        apply Real.exp_le_exp.mpr
        linarith
      exact mul_nonneg (sub_nonneg.mpr Hexp) (sub_nonneg.mpr H)
    · have Hexp : a ≤ b := by
        apply Real.exp_le_exp.mpr
        linarith
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hid : (theta-theta')*(a*theta-b*theta')+(X-X')*(a*X-b*X')=
      (a+b)/2*((theta-theta')^2+(X-X')^2)+
      (a-b)/2*(theta^2+X^2-(theta'^2+X'^2)) := by ring
  change Real.exp (-r^2/2)*((theta-theta')^2+(X-X')^2)≤
    (theta-theta')*(a*theta-b*theta')+(X-X')*(a*X-b*X')
  rw [hid]
  have hbase : Real.exp (-r^2/2) ≤ (a+b)/2 := by linarith
  have H := mul_le_mul_of_nonneg_right hbase
    (show 0≤(theta-theta')^2+(X-X')^2 by positivity)
  nlinarith only [H,hprod]

/-- Positive-temperature square-root slow dynamics contract toward their equilibrium. -/
theorem sqrtBulk_slow_dissipation (r Phi theta X theta' X' : ℝ)
    (hPhi : 0 ≤ Phi) (hX : 0 < X) (hX' : 0 < X')
    (heq1 : alpha theta' (X'^2) r*theta'=r)
    (heq2 : alpha theta' (X'^2) r*X'^2=Phi) :
    2*(theta-theta')*(r-alpha theta (X^2) r*theta)+
      2*(X-X')*(Phi/X-alpha theta (X^2) r*X) ≤
      -2*Real.exp (-r^2/2)*((theta-theta')^2+(X-X')^2) := by
  have H := sqrtBulk_radial_monotone r theta X theta' X'
  have heq2' : alpha theta' (X'^2) r*X'=Phi/X' := by
    apply (eq_div_iff hX'.ne').mpr
    nlinarith only [heq2]
  have hlog : (X-X')*(Phi/X-Phi/X') ≤ 0 := by
    have hid : (X-X')*(Phi/X-Phi/X')= -Phi*(X-X')^2/(X*X') := by field_simp; ring
    rw [hid]
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [sq_nonneg (X-X')]
    · positivity
  rw [heq1,heq2'] at H
  nlinarith only [H,hlog]

/-- At zero temperature the boundary X=0 is regular, and the same contraction holds. -/
theorem sqrtBulk_zero_slow_dissipation (r theta X theta' : ℝ)
    (heq : alpha theta' 0 r*theta'=r) :
    2*(theta-theta')*(r-alpha theta (X^2) r*theta)+
      2*X*(-alpha theta (X^2) r*X) ≤
      -2*Real.exp (-r^2/2)*((theta-theta')^2+X^2) := by
  have H := sqrtBulk_radial_monotone r theta X theta' 0
  simpa only [zero_pow (by decide : (2:ℕ)≠0),mul_zero,sub_zero,heq] using
    (show 2*(theta-theta')*(r-alpha theta (X^2) r*theta)+2*X*(-alpha theta (X^2) r*X)≤
      -2*Real.exp (-r^2/2)*((theta-theta')^2+X^2) by
        simp only [zero_pow (by decide : (2:ℕ)≠0),mul_zero,sub_zero,heq] at H
        nlinarith only [H])

/-- Scalar integrating-factor estimate on a closed interval. -/
theorem scalar_dissipation_bound (D D' : ℝ → ℝ) (c a b : ℝ)
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt D (D' t) t)
    (hdiss : ∀ t ∈ Set.Icc a b, D' t ≤ -c*D t) (hab : a ≤ b) :
    D b ≤ Real.exp (-c*(b-a))*D a := by
  let f := fun t => Real.exp (c*(t-a))*D t
  let f' := fun t => Real.exp (c*(t-a))*(c*D t+D' t)
  have hf (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt f (f' t) t := by
    have H := (((hasDerivAt_id t).sub_const a).const_mul c).exp.mul (hderiv t ht)
    convert H using 1
    · rfl
    · dsimp [f']
      ring
  have hant : AntitoneOn f (Set.Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    · intro t ht
      exact (hf t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hf t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      dsimp [f']
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have H := hdiss t (interior_subset ht)
      linarith
  have H := hant ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  dsimp [f] at H
  simp only [sub_self,mul_zero,Real.exp_zero,one_mul] at H
  have Hmul := mul_le_mul_of_nonneg_left H (Real.exp_pos (-c*(b-a))).le
  have he : Real.exp (-c*(b-a))*Real.exp (c*(b-a))=1 := by rw [←Real.exp_add]; ring_nf; simp
  simpa only [←mul_assoc,he,one_mul] using Hmul

/-- Distance in signal and square-root bulk coordinates. -/
def slowSqrtDistance (y : ℝ × ℝ) (theta X : ℝ) : ℝ :=
  (y.1-theta)^2+(Real.sqrt y.2-X)^2

theorem slowSqrtDistance_nonneg (y : ℝ × ℝ) (theta X : ℝ) :
    0 ≤ slowSqrtDistance y theta X := by dsimp [slowSqrtDistance]; positivity

/-- The square-root change of variables for an actual positive-bulk solution. -/
theorem slow_sqrt_hasDerivAt (r Phi t : ℝ) (y : ℝ → ℝ × ℝ)
    (hy : HasDerivAt y (slowField r Phi (y t).1 (y t).2) t) (hR : 0 < (y t).2) :
    HasDerivAt (fun s => Real.sqrt (y s).2)
      (Phi/Real.sqrt (y t).2-alpha (y t).1 (y t).2 r*Real.sqrt (y t).2) t := by
  have Hsnd : HasDerivAt (fun s => (y s).2) (slowField r Phi (y t).1 (y t).2).2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hy
  have H := Hsnd.sqrt hR.ne'
  convert H using 1
  · dsimp [slowField]
    have hs := Real.sq_sqrt hR.le
    have hs0 : Real.sqrt (y t).2 ≠ 0 := (Real.sqrt_pos.mpr hR).ne'
    field_simp
    rw [hs]
    ring

/-- Quantitative exponential contraction for actual slow solutions with
positive bulk, proved without a planar limit-set certificate. -/
theorem slow_positive_contraction (r Phi theta X a b : ℝ) (y : ℝ → ℝ × ℝ)
    (hPhi : 0 ≤ Phi) (hX : 0 < X) (hab : a ≤ b)
    (heq1 : alpha theta (X^2) r*theta=r) (heq2 : alpha theta (X^2) r*X^2=Phi)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (slowField r Phi (y t).1 (y t).2) t)
    (hR : ∀ t ∈ Set.Icc a b, 0 < (y t).2) :
    slowSqrtDistance (y b) theta X ≤
      Real.exp (-2*Real.exp (-r^2/2)*(b-a))*slowSqrtDistance (y a) theta X := by
  let D := fun t => slowSqrtDistance (y t) theta X
  let D' := fun t => 2*((y t).1-theta)*(r-alpha (y t).1 (y t).2 r*(y t).1)+
    2*(Real.sqrt (y t).2-X)*(Phi/Real.sqrt (y t).2-alpha (y t).1 (y t).2 r*Real.sqrt (y t).2)
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt D (D' t) t := by
    have Hfst : HasDerivAt (fun s => (y s).1) (slowField r Phi (y t).1 (y t).2).1 t :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hy t ht)
    have h1 := (Hfst.sub_const theta).pow 2
    have h2 := ((slow_sqrt_hasDerivAt r Phi t y (hy t ht) (hR t ht)).sub_const X).pow 2
    convert h1.add h2 using 1
    · rfl
    · dsimp [D',slowField]
      ring
  have hdiss (t : ℝ) (ht : t ∈ Set.Icc a b) : D' t ≤ -(2*Real.exp (-r^2/2))*D t := by
    have H := sqrtBulk_slow_dissipation r Phi (y t).1 (Real.sqrt (y t).2) theta X hPhi
      (Real.sqrt_pos.mpr (hR t ht)) hX heq1 heq2
    rw [Real.sq_sqrt (hR t ht).le] at H
    convert H using 1 <;> dsimp [D,D',slowSqrtDistance] <;> ring
  have H := scalar_dissipation_bound D D' (2*Real.exp (-r^2/2)) a b hderiv hdiss hab
  simpa only [D,neg_mul] using H

/-- Every global positive-bulk slow solution converges to its equilibrium. -/
theorem slow_positive_tendsto (r Phi theta X a : ℝ) (y : ℝ → ℝ × ℝ)
    (hPhi : 0 ≤ Phi) (hX : 0 < X)
    (heq1 : alpha theta (X^2) r*theta=r) (heq2 : alpha theta (X^2) r*X^2=Phi)
    (hy : ∀ t, a ≤ t → HasDerivAt y (slowField r Phi (y t).1 (y t).2) t)
    (hR : ∀ t, a ≤ t → 0 < (y t).2) :
    Tendsto y atTop (𝓝 (theta,X^2)) := by
  let D := fun t => slowSqrtDistance (y t) theta X
  have hc : 0 < 2*Real.exp (-r^2/2) := by positivity
  have ht : Tendsto (fun t : ℝ => (2*Real.exp (-r^2/2))*(t-a)) atTop atTop :=
    (show Tendsto (fun t : ℝ => t-a) atTop atTop from by
      simpa only [sub_eq_add_neg,id_eq] using
        (tendsto_id.atTop_add (show Tendsto (fun _ : ℝ => -a) atTop (𝓝 (-a)) from tendsto_const_nhds))).const_mul_atTop hc
  have he : Tendsto (fun t : ℝ => Real.exp (-2*Real.exp (-r^2/2)*(t-a))*D a) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_mul,zero_mul,mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).mul_const (D a)
  have hD : Tendsto D atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun t => slowSqrtDistance_nonneg (y t) theta X) _ he
    filter_upwards [eventually_ge_atTop a] with t ht
    exact slow_positive_contraction r Phi theta X a t y hPhi hX ht heq1 heq2
      (fun s hs => hy s hs.1) (fun s hs => hR s hs.1)
  have hroot : Tendsto (fun t => Real.sqrt (D t)) atTop (𝓝 0) := by simpa using hD.sqrt
  have htheta : Tendsto (fun t => (y t).1) atTop (𝓝 theta) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hroot
    intro t
    rw [Real.norm_eq_abs]
    apply Real.le_sqrt_of_sq_le
    dsimp [D,slowSqrtDistance]
    rw [sq_abs]
    nlinarith [sq_nonneg (Real.sqrt (y t).2-X)]
  have hbulk : Tendsto (fun t => Real.sqrt (y t).2) atTop (𝓝 X) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hroot
    intro t
    rw [Real.norm_eq_abs]
    apply Real.le_sqrt_of_sq_le
    dsimp [D,slowSqrtDistance]
    rw [sq_abs]
    nlinarith [sq_nonneg ((y t).1-theta)]
  have hRlim : Tendsto (fun t => (y t).2) atTop (𝓝 (X^2)) := by
    apply (hbulk.pow 2).congr'
    filter_upwards [eventually_ge_atTop a] with t ht
    exact Real.sq_sqrt (hR t ht).le
  exact htheta.prodMk_nhds hRlim

end
end SparseSGD.Logistic
