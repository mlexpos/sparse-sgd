import SparseSGD.Logistic.SlowTrackingActual
import Mathlib.Analysis.ODE.DiscreteGronwall
namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 1600000

def slowVectorField (r Phi : ℝ) (s : ℝ × ℝ) : ℝ × ℝ := slowField r Phi s.1 s.2

theorem contDiff_slowVectorField (r Phi : ℝ) : ContDiff ℝ ⊤ (slowVectorField r Phi) := by
  unfold slowVectorField slowField alpha
  fun_prop

/-- The actual smooth field has a Lipschitz constant and a speed bound on
any state ball. -/
theorem slowVectorField_compact_bounds (r Phi M : ℝ) :
    ∃ L : ℝ≥0, ∃ F : ℝ, 0 ≤ F ∧
      LipschitzOnWith L (slowVectorField r Phi) (Metric.closedBall 0 M) ∧
      ∀ y, ‖y‖ ≤ M → ‖slowVectorField r Phi y‖ ≤ F := by
  obtain ⟨L,hL⟩ := (contDiff_slowVectorField r Phi).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall 0 M) (isCompact_closedBall 0 M)
  obtain ⟨F,hF⟩ := (isCompact_closedBall (0:(ℝ × ℝ)) M).exists_bound_of_continuousOn
    (contDiff_slowVectorField r Phi).continuous.continuousOn
  refine ⟨L,max F 0,le_max_right _ _,hL,?_⟩
  intro y hy
  exact (hF y (by simpa using hy)).trans (le_max_left _ _)

/-- The Euler truncation error follows from the actual ODE equation and
bounded speed on the interval; it is not postulated. -/
theorem slow_ode_euler_error (r Phi M F t h : ℝ) (L : ℝ≥0)
    (y : ℝ → (ℝ × ℝ)) (hh : 0 ≤ h) (hF : 0 ≤ F)
    (hy : ∀ s ∈ Set.Icc t (t+h), HasDerivAt y (slowVectorField r Phi (y s)) s)
    (hyM : ∀ s ∈ Set.Icc t (t+h), ‖y s‖ ≤ M)
    (hb : ∀ z, ‖z‖ ≤ M → ‖slowVectorField r Phi z‖ ≤ F)
    (hL : LipschitzOnWith L (slowVectorField r Phi) (Metric.closedBall 0 M)) :
    ‖y (t+h)-(y t+h • slowVectorField r Phi (y t))‖ ≤ (L:ℝ)*F*h^2 := by
  have hspeed : ∀ s ∈ Set.Icc t (t+h), ‖y s-y t‖ ≤ F*(s-t) :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs => (hy s hs).hasDerivWithinAt)
      (fun s hs => hb (y s) (hyM s (Set.mem_Icc_of_Ico hs)))
  let z := fun s => y s-(s-t) • slowVectorField r Phi (y t)
  have hz : ∀ s ∈ Set.Icc t (t+h), HasDerivAt z
      (slowVectorField r Phi (y s)-slowVectorField r Phi (y t)) s := by
    intro s hs
    convert (hy s hs).sub (((hasDerivAt_id s).sub_const t).smul_const
      (slowVectorField r Phi (y t))) using 1
    · rfl
    · simp
  have herr := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s hs => (hz s hs).hasDerivWithinAt) (C:=(L:ℝ)*F*h) (by
      intro s hs
      have hs' := Set.mem_Icc_of_Ico hs
      calc
        _ ≤ (L:ℝ)*‖y s-y t‖ := hL.norm_sub_le
          (by simpa using hyM s hs') (by simpa using hyM t ⟨le_rfl,by linarith⟩)
        _ ≤ (L:ℝ)*(F*(s-t)) := mul_le_mul_of_nonneg_left (hspeed s hs') L.coe_nonneg
        _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (by linarith [hs.2]) (mul_nonneg L.coe_nonneg hF))
    (t+h) ⟨by linarith,le_rfl⟩
  simpa [z,sub_eq_add_neg,mul_pow,pow_two,mul_assoc,add_assoc] using herr

/-- A one-step stability inequality, used for the proved actual drift
residual and the proved ODE truncation residual. -/
theorem slow_one_step_error (f : (ℝ × ℝ) → (ℝ × ℝ)) (h E G : ℝ)
    (L : ℝ≥0) (x z xn zn : (ℝ × ℝ)) (hh : 0 ≤ h)
    (hf : ‖f x-f z‖ ≤ (L:ℝ)*‖x-z‖)
    (hx : ‖xn-(x+h • f x)‖ ≤ E) (hz : ‖zn-(z+h • f z)‖ ≤ G) :
    ‖xn-zn‖ ≤ (1+h*(L:ℝ))*‖x-z‖+E+G := by
  have hid : xn-zn = (xn-(x+h • f x))+((x-z)+h • (f x-f z))+
      ((z+h • f z)-zn) := by module
  rw [hid]
  calc
    _ ≤ ‖xn-(x+h • f x)‖+‖(x-z)+h • (f x-f z)‖+‖(z+h • f z)-zn‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ E+(‖x-z‖+h*((L:ℝ)*‖x-z‖))+G := by
      have hn := (norm_add_le (x-z) (h • (f x-f z))).trans
        (add_le_add le_rfl (by simpa [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh] using
          mul_le_mul_of_nonneg_left hf hh))
      have hz' : ‖(z+h • f z)-zn‖ ≤ G := by simpa [norm_sub_rev] using hz
      exact add_le_add (add_le_add hx hn) hz'
    _ = _ := by ring



/-- Gronwall with a geometric initial layer. Its accumulated contribution
is proportional to the learning/retention ratio, uniformly in the retention
step. -/
theorem slow_discrete_gronwall_initial_layer (u : ℕ → ℝ) (N : ℕ) (h z H J L T : ℝ)
    (hun : ∀ n ≤ N, 0 ≤ u n) (hh : 0 < h) (hh1 : h ≤ 1) (hz : 0 ≤ z)
    (hH : 0 ≤ H) (hJ : 0 ≤ J) (hL : 0 ≤ L)
    (hu : ∀ n < N, u (n+1) ≤ (1+z*L)*u n+z*(H*(1-h/4)^n+J))
    (hT : (N:ℝ)*z ≤ T) :
    ∀ n ≤ N, u n ≤ (u 0+4*z*H/h+T*J)*Real.exp (T*L) := by
  let q := 1-h/4
  have hq : 0 ≤ q := by dsimp [q]; linarith
  let v := fun n => u (min n N)
  have hv : ∀ n ≥ 0, v (n+1) ≤ (1+z*L)*v n+z*(H*q^n+J) := by
    intro n _
    by_cases hn : n < N
    · simpa [v,q,Nat.min_eq_left (Nat.le_of_lt hn),Nat.min_eq_left (Nat.succ_le_of_lt hn)] using hu n hn
    · have hn' : N ≤ n := Nat.le_of_not_gt hn
      simp only [v,Nat.min_eq_right hn',Nat.min_eq_right (hn'.trans (Nat.le_succ n))]
      have huN : 0 ≤ u N := hun N le_rfl
      have hb : 0 ≤ z*(H*q^n+J) := by positivity
      nlinarith only [hb,mul_nonneg (mul_nonneg hz hL) huN]
  have hb := discrete_gronwall (u:=v) (b:=fun n => z*(H*q^n+J)) (c:=fun _ => z*L)
    (by simpa [v] using hun 0 (Nat.zero_le N)) hv (fun _ _ => mul_nonneg hz hL)
    (fun n _ => by positivity)
  intro n hn
  have hb' := hb (n:=n) (Nat.zero_le n)
  simp only [v,Nat.min_eq_left hn,Nat.zero_min,Nat.Ico_zero_eq_range] at hb'
  have hnt : (n:ℝ)*z ≤ T := (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hz).trans hT
  have hi := slow_initial_layer_sum (h/2) z n (by linarith) (by linarith) hz
  rw [show 1-(h/2)/2=q by dsimp [q]; ring] at hi
  have hir : 2*z/(h/2)=4*z/h := by field_simp; ring
  rw [hir] at hi
  have hsum : (∑ k ∈ Finset.range n, z*(H*q^k+J)) ≤ 4*z*H/h+T*J := by
    have hhi := mul_le_mul_of_nonneg_right hi hH
    have hnj := mul_le_mul_of_nonneg_right hnt hJ
    rw [Finset.mul_sum,Finset.sum_mul] at hhi
    simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    have hid : (∑ k ∈ Finset.range n, z*(q^k)*H) = ∑ k ∈ Finset.range n, z*(H*q^k) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hid,show 4*z/h*H=4*z*H/h by ring] at hhi
    nlinarith only [hhi,hnj]
  apply hb'.trans
  have hu0 : 0 ≤ u 0 := hun 0 (Nat.zero_le N)
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range n, z*(H*q^k+J) := Finset.sum_nonneg (fun _ _ => by positivity)
  have hTL : (n:ℝ)*(z*L) ≤ T*L := by nlinarith only [mul_le_mul_of_nonneg_right hnt hL]
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,add_assoc] using mul_le_mul
    (add_le_add le_rfl hsum) (Real.exp_le_exp.mpr hTL) (Real.exp_pos _).le (add_nonneg hu0 (hsum0.trans hsum))

end
end SparseSGD.Logistic
