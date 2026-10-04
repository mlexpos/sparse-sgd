import SparseSGD.Logistic.DynamicLinearBulk
import SparseSGD.Logistic.DynamicField
import Mathlib.Algebra.QuadraticDiscriminant
namespace SparseSGD.Logistic
noncomputable section
open Filter Topology
open scoped NNReal
set_option maxHeartbeats 1800000

def dynamicDualBackwardField (delta curvature : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (curvature*s.2,-delta*s.1-s.2)

theorem dynamicDualBackwardField_norm (delta curvature A : ℝ) (s : ℝ × ℝ)
    (hA : 0 ≤ A) (hcurv : |curvature| ≤ A) :
    ‖dynamicDualBackwardField delta curvature s‖ ≤ (|delta|+1+A)*‖s‖ := by
  have h1 : |s.1| ≤ ‖s‖ := norm_fst_le s
  have h2 : |s.2| ≤ ‖s‖ := norm_snd_le s
  apply norm_prod_le_iff.mpr
  constructor
  · change |curvature*s.2| ≤ _
    rw [abs_mul]
    have hb := mul_le_mul hcurv h2 (abs_nonneg s.2) hA
    nlinarith [mul_nonneg (abs_nonneg delta) (norm_nonneg s),norm_nonneg s]
  · change |-delta*s.1-s.2| ≤ _
    have ht : |-delta*s.1-s.2| ≤ |delta| * |s.1|+|s.2| := by
      simpa only [sub_eq_add_neg,abs_neg,abs_mul] using abs_add_le (-delta*s.1) (-s.2)
    have hb := mul_le_mul_of_nonneg_left h1 (abs_nonneg delta)
    nlinarith [mul_nonneg hA (norm_nonneg s)]

theorem dynamicDualBackwardField_sub (delta curvature : ℝ) (s u : ℝ × ℝ) :
    dynamicDualBackwardField delta curvature s-dynamicDualBackwardField delta curvature u=
      dynamicDualBackwardField delta curvature (s-u) := by ext <;> dsimp [dynamicDualBackwardField] <;> ring

/-- A continuous bounded curvature drives an actual linear bulk oscillator
on every prescribed finite interval. The proof solves a bounded extension,
then uses Gronwall to remove the extension. -/
theorem dynamic_dual_backward_exists (delta a b A : ℝ) (curvature : ℝ → ℝ)
    (s0 : ℝ × ℝ) (_hab : a ≤ b) (hA : 0 ≤ A)
    (hcurv : Continuous curvature) (hcurvA : ∀ t, |curvature t| ≤ A) :
    ∃ s : ℝ → ℝ × ℝ, s a=s0 ∧ ∀ t ∈ Set.Icc a b,
      HasDerivAt s (dynamicDualBackwardField delta (curvature t) (s t)) t := by
  let L := |delta|+1+A
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let K : ℝ≥0 := ⟨L,hL⟩
  let H := ‖s0‖*Real.exp (L*(b-a))+1
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let f := fun t s => dynamicDualBackwardField delta (curvature (t+a)) (dynamicBulkClamp H s)
  have hLip : ∀ t, LipschitzWith K (f t) := by
    intro t
    apply LipschitzWith.of_dist_le_mul
    intro x z
    have hb := dynamicDualBackwardField_norm delta (curvature (t+a)) A
      (dynamicBulkClamp H x-dynamicBulkClamp H z) hA (hcurvA _)
    rw [← dynamicDualBackwardField_sub] at hb
    have hc := (dynamicBulkClamp_lipschitz H).norm_sub_le x z
    simp only [NNReal.coe_one,one_mul] at hc
    have ht := mul_le_mul_of_nonneg_left hc hL
    convert hb.trans ht using 1 <;> simp [dist_eq_norm,K]
    exact Or.inl rfl
  have hf : ∀ t s, ‖f t s‖ ≤ L*H := by
    intro t s
    exact (dynamicDualBackwardField_norm delta (curvature (t+a)) A _ hA (hcurvA _)).trans
      (mul_le_mul_of_nonneg_left (dynamicBulkClamp_norm_bound H hH s) hL)
  have hcont : ∀ s, Continuous (fun t => f t s) := by
    intro s
    dsimp [f,dynamicDualBackwardField]
    fun_prop
  obtain ⟨z,hz0,hz⟩ := bounded_lipschitz_ode_global f s0 K (L*H) (mul_nonneg hL hH) hf hLip hcont
  have hznorm : ∀ t ∈ Set.Icc 0 (b-a), ‖z t‖ ≤ ‖s0‖*Real.exp (L*t) := by
    have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f:=z) (f':=fun t => f t (z t))
      (a:=0) (b:=b-a) (δ:=‖s0‖) (K:=L) (ε:=0)
      (fun t ht => (hz t).continuousAt.continuousWithinAt) (fun t ht => (hz t).hasDerivWithinAt)
      (by rw [hz0]) (by
        intro t ht
        have hb := dynamicDualBackwardField_norm delta (curvature (t+a)) A (dynamicBulkClamp H (z t)) hA (hcurvA _)
        have hc := mul_le_mul_of_nonneg_left (dynamicBulkClamp_norm_le H hH (z t)) hL
        simpa [f] using hb.trans hc)
    simpa only [gronwallBound_ε0,sub_zero] using hg
  have hzH : ∀ t ∈ Set.Icc 0 (b-a), ‖z t‖ ≤ H := by
    intro t ht
    have hb := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ht.2 hL)) (norm_nonneg s0)
    dsimp [H]
    linarith [hznorm t ht]
  refine ⟨fun t => z (t-a),by simpa using hz0,?_⟩
  intro t ht
  have hi : t-a ∈ Set.Icc 0 (b-a) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hc := dynamicBulkClamp_eq H (z (t-a)) (hzH (t-a) hi)
  convert (hz (t-a)).scomp t ((hasDerivAt_id t).sub_const a) using 1 <;> simp [f,hc,Function.comp_def]


/-- The physical covariance cone in dynamic order `(theta,Y,R,V,C)`. -/
def dynamicPhysical (y : DynamicState) : Prop :=
  0 ≤ y 2 ∧ 0 ≤ y 3 ∧ y 4^2 ≤ y 2*y 3

theorem dynamicPhysical_iff_quadratic (y : DynamicState) :
    dynamicPhysical y ↔ ∀ a b : ℝ, 0 ≤ y 2*a^2+2*y 4*a*b+y 3*b^2 := by
  constructor
  · rintro ⟨hR,hV,hC⟩ a b
    by_cases hz : y 2=0
    · have hc : y 4=0 := by rw [hz] at hC; nlinarith [sq_nonneg (y 4)]
      simp only [hz,hc,zero_mul,mul_zero,zero_add]; exact mul_nonneg hV (sq_nonneg b)
    · have hRp : 0<y 2 := lt_of_le_of_ne hR (Ne.symm hz)
      have hd : 0≤(y 2*y 3-(y 4)^2)*b^2 := mul_nonneg (by linarith) (sq_nonneg b)
      have hs := sq_nonneg (y 2*a+y 4*b)
      have H : 0≤y 2*(y 2*a^2+2*y 4*a*b+y 3*b^2) := by nlinarith [hd,hs]
      exact nonneg_of_mul_nonneg_right H hRp
  · intro h
    have hR := h 1 0
    have hV := h 0 1
    have hd := discrim_le_zero (a:=y 2) (b:=2*y 4) (c:=y 3) (fun x => by convert h x 1 using 1 <;> ring)
    dsimp [discrim] at hd
    exact ⟨by nlinarith,by nlinarith,by nlinarith⟩

theorem dynamicPhysical_closed : IsClosed {y : DynamicState | dynamicPhysical y} := by
  unfold dynamicPhysical
  exact (isClosed_le continuous_const (continuous_apply 2)).inter
    ((isClosed_le continuous_const (continuous_apply 3)).inter
      (isClosed_le ((continuous_apply 4).pow 2) ((continuous_apply 2).mul (continuous_apply 3))))

theorem dynamicPhysical_convex : Convex ℝ {y : DynamicState | dynamicPhysical y} := by
  intro x hx y hy a b ha hb hab
  apply (dynamicPhysical_iff_quadratic _).mpr
  intro u v
  have H := add_nonneg (mul_nonneg ha ((dynamicPhysical_iff_quadratic x).mp hx u v))
    (mul_nonneg hb ((dynamicPhysical_iff_quadratic y).mp hy u v))
  convert H using 1 <;> simp <;> ring

/-- A terminal adjoint solution for the time-varying covariance equation. -/
theorem dynamic_terminal_adjoint_exists (delta a b A : ℝ) (curvature : ℝ→ℝ)
    (s1 : ℝ×ℝ) (hab : a≤b) (hA : 0≤A)
    (hcurv : Continuous curvature) (hcurvA : ∀ t, |curvature t|≤A) :
    ∃ z : ℝ→ℝ×ℝ, z b=s1 ∧ ∀ t∈Set.Icc a b,
      HasDerivAt z (-curvature t*(z t).2,delta*(z t).1+(z t).2) t := by
  have hc : Continuous (fun u=>curvature (b-u)) := hcurv.comp (by fun_prop)
  obtain ⟨w,hw0,hw⟩ := dynamic_dual_backward_exists delta 0 (b-a) A
    (fun u=>curvature (b-u)) s1 (by linarith) hA hc (fun u=>hcurvA _)
  refine ⟨fun t=>w (b-t),by simpa using hw0,?_⟩
  intro t ht
  have hi : b-t∈Set.Icc 0 (b-a) := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  convert (hw (b-t) hi).scomp t ((hasDerivAt_const t b).sub (hasDerivAt_id t)) using 1 <;>
    simp [dynamicDualBackwardField,Function.comp_def] <;> ring

/-- An actual dynamic-alpha trajectory preserves the physical Gram cone.
The proof transports every quadratic form by the terminal adjoint equation;
its derivative is the nonnegative noise covariance. -/
theorem dynamicPhysical_preserved (r delta Phi a b : ℝ) (y : ℝ→DynamicState)
    (hab : a≤b) (hd : 0<delta) (hPhi : 0≤Phi)
    (hy : ∀ t∈Set.Icc a b, HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hy0 : dynamicPhysical (y a)) :
    ∀ t∈Set.Icc a b, dynamicPhysical (y t) := by
  have cy : ContinuousOn y (Set.Icc a b) := fun t ht=>(hy t ht).continuousAt.continuousWithinAt
  have ca : Continuous (dynamicAlpha r) := by unfold dynamicAlpha; fun_prop
  let clamp := fun t : ℝ=>max a (min b t)
  have hclamp : Continuous clamp := by dsimp [clamp]; fun_prop
  have hmem : ∀ t, clamp t∈Set.Icc a b := fun t=>⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩
  have heq : ∀ t∈Set.Icc a b, clamp t=t := by
    intro t ht;simp [clamp,min_eq_right ht.2,max_eq_right ht.1]
  let curvature := fun t=>dynamicAlpha r (y (clamp t))
  have hcurv : Continuous curvature := ca.comp (cy.comp_continuous hclamp hmem)
  obtain ⟨A0,hA0⟩ := isCompact_Icc.exists_bound_of_continuousOn (ca.comp_continuousOn cy)
  let A := max A0 0
  have hA : 0≤A := le_max_right _ _
  have hcurvA : ∀ t, |curvature t|≤A := fun t=>(hA0 (clamp t) (hmem t)).trans (le_max_left _ _)
  have hcurveq : ∀ t∈Set.Icc a b, curvature t=dynamicAlpha r (y t) := by
    intro t ht;dsimp [curvature];rw [heq t ht]
  intro t ht
  apply (dynamicPhysical_iff_quadratic _).mpr
  intro u v
  obtain ⟨z,hzt,hz⟩ := dynamic_terminal_adjoint_exists delta a t A curvature (u,v) ht.1 hA hcurv hcurvA
  let q := fun s=>y s 2*(z s).1^2+2*y s 4*(z s).1*(z s).2+y s 3*(z s).2^2
  have hq : ∀ s∈Set.Icc a t, HasDerivAt q ((2*Phi/delta)*(z s).2^2) s := by
    intro s hs
    have hs' : s∈Set.Icc a b := ⟨hs.1,hs.2.trans ht.2⟩
    have hc := hasDerivAt_pi.mp (hy s hs')
    have hz1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt s (hz s hs)
    have hz2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt s (hz s hs)
    convert (((hc 2).mul (hz1.pow 2)).add ((((hc 4).const_mul 2).mul hz1).mul hz2)).add
      ((hc 3).mul (hz2.pow 2)) using 1
    · rfl
    · simp [dynamicField,hcurveq s hs']
      ring
  have hm : MonotoneOn q (Set.Icc a t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a t)
    · exact fun s hs=>(hq s hs).continuousAt.continuousWithinAt
    · exact fun s hs=>(hq s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hq s (interior_subset hs)).deriv]
      exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hPhi) hd.le) (sq_nonneg _)
  have hqa : 0≤q a := (dynamicPhysical_iff_quadratic _).mp hy0 (z a).1 (z a).2
  have H := hqa.trans (hm ⟨le_rfl,ht.1⟩ ⟨ht.1,le_rfl⟩ ht.1)
  simpa [q,hzt] using H
end
end SparseSGD.Logistic
