import SparseSGD.Logistic.SlowLimitExistence
import SparseSGD.Logistic.SlowLimitEuler
import SparseSGD.Logistic.SlowGlobal
namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 1800000

/-- A bounded Lipschitz clipping map used solely in the existence proof. -/
def slowBoxClamp (A B : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (max (-A) (min A s.1),max 0 (min B s.2))

theorem slowBoxClamp_lipschitz (A B : ℝ) : LipschitzWith 1 (slowBoxClamp A B) := by
  have h1 : LipschitzWith 1 (fun s : ℝ × ℝ => max (-A) (min A s.1)) :=
    (LipschitzWith.prod_fst.const_min A).const_max (-A)
  have h2 : LipschitzWith 1 (fun s : ℝ × ℝ => max 0 (min B s.2)) :=
    (LipschitzWith.prod_snd.const_min B).const_max 0
  change LipschitzWith 1 (fun s : ℝ × ℝ => (max (-A) (min A s.1),max 0 (min B s.2)))
  simpa only [max_self] using h1.prodMk h2

theorem slowBoxClamp_bounds (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (s : ℝ × ℝ) :
    -A ≤ (slowBoxClamp A B s).1 ∧ (slowBoxClamp A B s).1 ≤ A ∧
    0 ≤ (slowBoxClamp A B s).2 ∧ (slowBoxClamp A B s).2 ≤ B := by
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _),
    le_max_left _ _,max_le hB (min_le_left _ _)⟩

theorem slowBoxClamp_norm (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (s : ℝ × ℝ) :
    ‖slowBoxClamp A B s‖ ≤ max A B := by
  have h := slowBoxClamp_bounds A B hA hB s
  apply norm_prod_le_iff.mpr
  constructor
  · exact (abs_le.mpr ⟨h.1,h.2.1⟩).trans (le_max_left _ _)
  · rw [Real.norm_eq_abs,abs_of_nonneg h.2.2.1]
    exact h.2.2.2.trans (le_max_right _ _)

theorem slowBoxClamp_eq (A B : ℝ) (s : ℝ × ℝ)
    (h1 : -A ≤ s.1) (h2 : s.1 ≤ A) (h3 : 0 ≤ s.2) (h4 : s.2 ≤ B) :
    slowBoxClamp A B s=s := by
  ext <;> simp [slowBoxClamp,min_eq_right h2,max_eq_right h1,min_eq_right h4,max_eq_right h3]

/-- The actual slow vector field admits a global forward solution for every
physical bulk start. The bounded extension is proved to remain in a box on
which it equals the actual field, including the zero-load/zero-bulk cases. -/
theorem slow_global_solution_exists (r Phi : ℝ) (s0 : ℝ × ℝ)
    (hr : 0 ≤ r) (hPhi : 0 ≤ Phi) (hR0 : 0 ≤ s0.2) :
    ∃ y : ℝ → ℝ × ℝ, y 0=s0 ∧ ∀ t, 0 ≤ t →
      HasDerivAt y (slowField r Phi (y t).1 (y t).2) t := by
  let c := Real.exp (-r^2/2)
  have hc : 0 < c := Real.exp_pos _
  let A := max |s0.1| (r/c)+1
  let B := max s0.2 (Phi/c)+1
  have hA : 0 ≤ A := by dsimp [A]; linarith [abs_nonneg s0.1,le_max_left |s0.1| (r/c)]
  have hB : 0 ≤ B := by dsimp [B]; linarith [le_max_left s0.2 (Phi/c)]
  have hrA : r ≤ c*A := by
    have ha : r/c ≤ A := by dsimp [A]; linarith [le_max_right |s0.1| (r/c)]
    simpa only [mul_comm] using (div_le_iff₀ hc).mp ha
  have hPhiB : Phi ≤ c*B := by
    have hb : Phi/c ≤ B := by dsimp [B]; linarith [le_max_right s0.2 (Phi/c)]
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hb
  have hinit1 : |s0.1| ≤ A := by dsimp [A]; linarith [le_max_left |s0.1| (r/c)]
  have hinit2 : s0.2 ≤ B := by dsimp [B]; linarith [le_max_left s0.2 (Phi/c)]
  obtain ⟨L,F,hF,hL,hFb⟩ := slowVectorField_compact_bounds r Phi (max A B)
  let f := fun s : ℝ × ℝ => slowVectorField r Phi (slowBoxClamp A B s)
  have hfLip : LipschitzWith L f := by
    apply LipschitzWith.of_dist_le_mul
    intro x z
    have hm := hL.norm_sub_le (by simpa using slowBoxClamp_norm A B hA hB x)
      (by simpa using slowBoxClamp_norm A B hA hB z)
    have hc := (slowBoxClamp_lipschitz A B).norm_sub_le x z
    simp only [NNReal.coe_one,one_mul] at hc
    have hb := mul_le_mul_of_nonneg_left hc L.coe_nonneg
    simpa [f,dist_eq_norm] using hm.trans hb
  have hfbound : ∀ s, ‖f s‖ ≤ F := fun s => hFb _ (slowBoxClamp_norm A B hA hB s)
  obtain ⟨y,hy0,hy⟩ := bounded_lipschitz_ode_global (fun _ => f) s0 L F hF
    (fun _ => hfbound) (fun _ => hfLip) (fun _ => continuous_const)
  have hy1 (t : ℝ) : HasDerivAt (fun u => (y u).1) (f (y t)).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hy t)
  have hy2 (t : ℝ) : HasDerivAt (fun u => (y u).2) (f (y t)).2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hy t)
  have halpha (s : ℝ × ℝ) : c ≤ alpha (slowBoxClamp A B s).1 (slowBoxClamp A B s).2 r := by
    apply Real.exp_le_exp.mpr
    nlinarith [(slowBoxClamp_bounds A B hA hB s).2.2.1,sq_nonneg (slowBoxClamp A B s).1]
  have hupper : ∀ t, 0 ≤ t → (y t).1 ≤ A := by
    apply scalar_upper_barrier_global (fun t => (y t).1) (fun t => (f (y t)).1) 0 A
      (by rw [hy0]; exact (le_abs_self _).trans hinit1) (fun t _ => hy1 t)
    intro t ht htheta
    have hid : (slowBoxClamp A B (y t)).1=A := by
      simp [slowBoxClamp,min_eq_left htheta,max_eq_right (by linarith : -A ≤ A)]
    have ha := mul_le_mul_of_nonneg_right (halpha (y t)) hA
    change r-alpha (slowBoxClamp A B (y t)).1 (slowBoxClamp A B (y t)).2 r*(slowBoxClamp A B (y t)).1 ≤ 0
    rw [hid] at ha ⊢
    linarith
  have hlower : ∀ t, 0 ≤ t → -(y t).1 ≤ A := by
    apply scalar_upper_barrier_global (fun t => -(y t).1) (fun t => -(f (y t)).1) 0 A
      (by rw [hy0]; exact (neg_le_abs _).trans hinit1) (fun t _ => (hy1 t).neg)
    intro t ht htheta
    have hs : (y t).1 ≤ -A := by linarith
    have hsA : (y t).1 ≤ A := hs.trans (by linarith)
    have hid : (slowBoxClamp A B (y t)).1 = -A := by
      simp [slowBoxClamp,min_eq_right hsA,max_eq_left hs]
    change -(r-alpha (slowBoxClamp A B (y t)).1 (slowBoxClamp A B (y t)).2 r*(slowBoxClamp A B (y t)).1) ≤ 0
    rw [hid]
    have ha : 0 ≤ alpha (-A) (slowBoxClamp A B (y t)).2 r*A := mul_nonneg (Real.exp_pos _).le hA
    linarith
  have hRlower : ∀ t, 0 ≤ t → -(y t).2 ≤ 0 := by
    apply scalar_upper_barrier_global (fun t => -(y t).2) (fun t => -(f (y t)).2) 0 0
      (by rw [hy0]; linarith) (fun t _ => (hy2 t).neg)
    intro t ht hR
    have hs : (y t).2 ≤ 0 := by linarith
    have hsB : (y t).2 ≤ B := hs.trans hB
    have hid : (slowBoxClamp A B (y t)).2=0 := by simp [slowBoxClamp,min_eq_right hsB,max_eq_left hs]
    change -(2*(Phi-alpha (slowBoxClamp A B (y t)).1 (slowBoxClamp A B (y t)).2 r*(slowBoxClamp A B (y t)).2)) ≤ 0
    rw [hid]
    nlinarith
  have hRupper : ∀ t, 0 ≤ t → (y t).2 ≤ B := by
    apply scalar_upper_barrier_global (fun t => (y t).2) (fun t => (f (y t)).2) 0 B
      (by rw [hy0]; exact hinit2) (fun t _ => hy2 t)
    intro t ht hR
    have hid : (slowBoxClamp A B (y t)).2=B := by simp [slowBoxClamp,min_eq_left hR,max_eq_right hB]
    have ha := mul_le_mul_of_nonneg_right (halpha (y t)) hB
    change 2*(Phi-alpha (slowBoxClamp A B (y t)).1 (slowBoxClamp A B (y t)).2 r*(slowBoxClamp A B (y t)).2) ≤ 0
    rw [hid] at ha ⊢
    linarith
  refine ⟨y,hy0,?_⟩
  intro t ht
  have hid := slowBoxClamp_eq A B (y t) (by linarith [hlower t ht]) (hupper t ht)
    (by linarith [hRlower t ht]) (hRupper t ht)
  simpa only [f,hid,slowVectorField] using hy t


/-- Global forward existence at every initial time. -/
theorem slow_global_solution_exists_at (r Phi a : ℝ) (s0 : ℝ × ℝ)
    (hr : 0 ≤ r) (hPhi : 0 ≤ Phi) (hR0 : 0 ≤ s0.2) :
    ∃ y : ℝ → ℝ × ℝ, y a=s0 ∧ ∀ t, a ≤ t →
      HasDerivAt y (slowField r Phi (y t).1 (y t).2) t := by
  obtain ⟨z,hz0,hz⟩ := slow_global_solution_exists r Phi s0 hr hPhi hR0
  refine ⟨fun t => z (t-a),by simpa using hz0,?_⟩
  intro t ht
  convert (hz (t-a) (by linarith)).scomp t ((hasDerivAt_id t).sub_const a) using 1 <;> simp [Function.comp_def]

/-- Existence and convergence of the actual slow trajectory, including
zero forcing and a zero initial bulk coordinate. -/
theorem slow_global_solution_exists_and_converges (r Phi a : ℝ) (s0 : ℝ × ℝ)
    (hr : 0 < r) (hPhi : 0 ≤ Phi) (hR0 : 0 ≤ s0.2) :
    ∃ y : ℝ → ℝ × ℝ, y a=s0 ∧
      (∀ t, a ≤ t → HasDerivAt y (slowField r Phi (y t).1 (y t).2) t) ∧
      Filter.Tendsto y Filter.atTop (nhds (positiveRoot r Phi,equilibriumBulk r Phi)) := by
  obtain ⟨y,hy0,hy⟩ := slow_global_solution_exists_at r Phi a s0 hr.le hPhi hR0
  refine ⟨y,hy0,hy,?_⟩
  exact slow_global_convergence r Phi a y hr hPhi (by simpa [hy0] using hR0) hy

end
end SparseSGD.Logistic
