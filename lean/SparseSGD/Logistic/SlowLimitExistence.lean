import Mathlib.Analysis.ODE.ExistUnique
namespace SparseSGD.Logistic
noncomputable section
open Filter Topology Set Metric
open scoped NNReal
set_option maxHeartbeats 1600000

/-- A uniformly bounded, uniformly Lipschitz continuous time-dependent field
has solutions on every finite interval. This is an application of Mathlib's
Picard-Lindelof theorem on a sufficiently large ball. -/
theorem bounded_lipschitz_ode_finite {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E → E) (x0 : E)
    (K : ℝ≥0) (F : ℝ) (hF : 0 ≤ F)
    (hbound : ∀ t x, ‖f t x‖ ≤ F)
    (hLip : ∀ t, LipschitzWith K (f t)) (hcont : ∀ x, Continuous (fun t => f t x))
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ y : ℝ → E, y 0=x0 ∧ ∀ t ∈ Set.Icc (-T) T, HasDerivAt y (f t (y t)) t := by
  let L : ℝ≥0 := ⟨F,hF⟩
  let a : ℝ≥0 := ⟨F*(T+1),by positivity⟩
  let t0 : Set.Icc (-(T+1)) (T+1) := ⟨0,by constructor <;> linarith⟩
  have hpl : IsPicardLindelof f t0 x0 a 0 L K := {
    lipschitzOnWith := fun t ht => (hLip t).lipschitzOnWith
    continuousOn := fun x hx => (hcont x).continuousOn
    norm_le := fun t ht x hx => hbound t x
    mul_max_le := by simp [t0,L,a]; exact le_rfl }
  obtain ⟨y,hy0,hy⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨y,hy0,?_⟩
  intro t ht
  have hi : t ∈ Set.Ioo (-(T+1)) (T+1) := by constructor <;> linarith [ht.1,ht.2]
  exact (hy t (Set.Ioo_subset_Icc_self hi)).hasDerivAt (Icc_mem_nhds hi.1 hi.2)

/-- Global existence for a bounded Lipschitz field. Finite Picard solutions
are patched using actual uniqueness on common intervals. -/
theorem bounded_lipschitz_ode_global {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E → E) (x0 : E)
    (K : ℝ≥0) (F : ℝ) (hF : 0 ≤ F)
    (hbound : ∀ t x, ‖f t x‖ ≤ F)
    (hLip : ∀ t, LipschitzWith K (f t)) (hcont : ∀ x, Continuous (fun t => f t x)) :
    ∃ y : ℝ → E, y 0=x0 ∧ ∀ t, HasDerivAt y (f t (y t)) t := by
  classical
  have hex : ∀ R : ℝ, ∃ y : ℝ → E, y 0=x0 ∧
      ∀ t ∈ Set.Icc (-(|R|+1)) (|R|+1), HasDerivAt y (f t (y t)) t := by
    intro R
    exact bounded_lipschitz_ode_finite f x0 K F hF hbound hLip hcont (|R|+1) (by positivity)
  choose curve hzero hcurve using hex
  have heq (R S t : ℝ) (htR : |t| < |R|+1) (htS : |t| < |S|+1) : curve R t=curve S t := by
    let A := min (|R|+1) (|S|+1)
    have hA : 0 < A := lt_min (by positivity) (by positivity)
    have hdomain : ∀ u ∈ Set.Ioo (-A) A,
        u ∈ Set.Icc (-(|R|+1)) (|R|+1) ∧ u ∈ Set.Icc (-(|S|+1)) (|S|+1) := by
      intro u hu
      have hAR : A ≤ |R|+1 := min_le_left _ _
      have hAS : A ≤ |S|+1 := min_le_right _ _
      constructor <;> constructor <;> linarith [hu.1,hu.2]
    have hu := ODE_solution_unique_of_mem_Ioo (v:=f) (K:=K) (s:=fun _ => Set.univ)
      (fun u hu => (hLip u).lipschitzOnWith) (t₀:=0) (by constructor <;> linarith)
      (fun u hu => ⟨hcurve R u (hdomain u hu).1,Set.mem_univ _⟩)
      (fun u hu => ⟨hcurve S u (hdomain u hu).2,Set.mem_univ _⟩)
      (by rw [hzero R,hzero S])
    apply hu
    have htA : |t| < A := lt_min htR htS
    exact ⟨by linarith [neg_abs_le t],by linarith [le_abs_self t]⟩
  let y := fun t => curve (|t|+1) t
  refine ⟨y,by exact hzero _,?_⟩
  intro t
  let R := |t|+2
  have hevent : y =ᶠ[𝓝 t] curve R := by
    filter_upwards [Metric.ball_mem_nhds t (by norm_num : (0:ℝ)<1)] with s hs
    have hdist : |s-t| < 1 := by simpa [Real.dist_eq] using hs
    have hsR : |s| < |R|+1 := by
      have ht := abs_add_le (s-t) t
      rw [sub_add_cancel] at ht
      have hR : 0 ≤ R := by dsimp [R]; positivity
      rw [abs_of_nonneg hR]
      dsimp [R]
      linarith
    have hsS : |s| < |(|s|+1)|+1 := by rw [abs_of_nonneg (by positivity : 0 ≤ |s|+1)]; linarith
    exact heq (|s|+1) R s hsS hsR
  have htR : t ∈ Set.Icc (-(|R|+1)) (|R|+1) := by
    have hR : 0 ≤ R := by dsimp [R]; positivity
    rw [abs_of_nonneg hR]
    dsimp [R]
    constructor <;> linarith [neg_abs_le t,le_abs_self t]
  have hderiv := (hcurve R t htR).congr_of_eventuallyEq hevent
  rw [hevent.eq_of_nhds] at ⊢
  exact hderiv


/-- A scalar barrier for an actual differentiable trajectory. The derivative
need only point inward on and outside the barrier. -/
theorem scalar_upper_barrier_global (x g : ℝ → ℝ) (a A : ℝ)
    (hx0 : x a ≤ A) (hx : ∀ t, a ≤ t → HasDerivAt x (g t) t)
    (hg : ∀ t, a ≤ t → A ≤ x t → g t ≤ 0) :
    ∀ t, a ≤ t → x t ≤ A := by
  intro t ht
  by_contra hn
  have hpos : 0 < x t-A := by linarith
  have hden : 0 < t-a+1 := by linarith
  let eps := (x t-A)/(2*(t-a+1))
  have heps : 0 < eps := by dsimp [eps]; positivity
  let B := fun s : ℝ => A+eps*(s-a+1)
  have hB : ∀ s, HasDerivAt B eps s := by
    intro s
    convert ((((hasDerivAt_id s).sub_const a).add_const 1).const_mul eps).const_add A using 1 <;> simp [B]
  have hinit : x a ≤ B a := by dsimp [B]; linarith
  have H := image_le_of_deriv_right_lt_deriv_boundary
    (f':=g) (B':=fun _ => eps)
    (fun s hs => (hx s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hx s hs.1).hasDerivWithinAt) hinit hB (by
      intro s hs heq
      have hb : A ≤ x s := by rw [heq]; dsimp [B]; nlinarith only [heps.le,hs.1]
      exact (hg s hs.1 hb).trans_lt heps)
    (x:=t) ⟨ht,le_rfl⟩
  have hid : eps*(t-a+1)=(x t-A)/2 := by dsimp [eps]; field_simp
  dsimp [B] at H
  rw [hid] at H
  linarith

end
end SparseSGD.Logistic
