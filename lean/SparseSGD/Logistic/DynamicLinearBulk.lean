import SparseSGD.Logistic.SlowLimitGlobalExistence
namespace SparseSGD.Logistic
noncomputable section
open Filter Topology
open scoped NNReal
set_option maxHeartbeats 1600000

def dynamicBulkClamp (H : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (max (-H) (min H s.1),max (-H) (min H s.2))

theorem dynamicBulkClamp_lipschitz (H : ℝ) : LipschitzWith 1 (dynamicBulkClamp H) := by
  have h1 : LipschitzWith 1 (fun s : ℝ × ℝ => max (-H) (min H s.1)) :=
    (LipschitzWith.prod_fst.const_min H).const_max (-H)
  have h2 : LipschitzWith 1 (fun s : ℝ × ℝ => max (-H) (min H s.2)) :=
    (LipschitzWith.prod_snd.const_min H).const_max (-H)
  change LipschitzWith 1 (fun s : ℝ × ℝ => (max (-H) (min H s.1),max (-H) (min H s.2)))
  simpa only [max_self] using h1.prodMk h2

theorem dynamicBulkClamp_norm_le (H : ℝ) (hH : 0 ≤ H) (s : ℝ × ℝ) :
    ‖dynamicBulkClamp H s‖ ≤ ‖s‖ := by
  have hc : dynamicBulkClamp H 0=0 := by ext <;> simp [dynamicBulkClamp,min_eq_right hH,max_eq_right (by linarith : -H ≤ 0)]
  have hb := (dynamicBulkClamp_lipschitz H).norm_sub_le s 0
  simpa [hc] using hb

theorem dynamicBulkClamp_norm_bound (H : ℝ) (hH : 0 ≤ H) (s : ℝ × ℝ) :
    ‖dynamicBulkClamp H s‖ ≤ H := by
  apply norm_prod_le_iff.mpr
  constructor <;> apply abs_le.mpr <;> constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem dynamicBulkClamp_eq (H : ℝ) (s : ℝ × ℝ) (hs : ‖s‖ ≤ H) :
    dynamicBulkClamp H s=s := by
  have h1 : |s.1| ≤ H := (norm_fst_le s).trans hs
  have h2 : |s.2| ≤ H := (norm_snd_le s).trans hs
  ext <;> simp [dynamicBulkClamp,min_eq_right (abs_le.mp h1).2,max_eq_right (abs_le.mp h1).1,
    min_eq_right (abs_le.mp h2).2,max_eq_right (abs_le.mp h2).1]

def dynamicLinearBulkField (delta curvature : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (-delta*s.2,-s.2+curvature*s.1)

theorem dynamicLinearBulkField_norm (delta curvature A : ℝ) (s : ℝ × ℝ)
    (hA : 0 ≤ A) (hcurv : |curvature| ≤ A) :
    ‖dynamicLinearBulkField delta curvature s‖ ≤ (|delta|+1+A)*‖s‖ := by
  have h1 : |s.1| ≤ ‖s‖ := norm_fst_le s
  have h2 : |s.2| ≤ ‖s‖ := norm_snd_le s
  apply norm_prod_le_iff.mpr
  constructor
  · change |-delta*s.2| ≤ _
    rw [abs_mul,abs_neg]
    have hb := mul_le_mul_of_nonneg_left h2 (abs_nonneg delta)
    have hn := norm_nonneg s
    nlinarith
  · change |-s.2+curvature*s.1| ≤ _
    have ht := abs_add_le (-s.2) (curvature*s.1)
    rw [abs_neg,abs_mul] at ht
    have hb := mul_le_mul hcurv h1 (abs_nonneg s.1) hA
    nlinarith [mul_nonneg (abs_nonneg delta) (norm_nonneg s)]

theorem dynamicLinearBulkField_sub (delta curvature : ℝ) (s u : ℝ × ℝ) :
    dynamicLinearBulkField delta curvature s-dynamicLinearBulkField delta curvature u=
      dynamicLinearBulkField delta curvature (s-u) := by ext <;> dsimp [dynamicLinearBulkField] <;> ring

/-- A continuous bounded curvature drives an actual linear bulk oscillator
on every prescribed finite interval. The proof solves a bounded extension,
then uses Gronwall to remove the extension. -/
theorem dynamic_linear_bulk_exists (delta a b A : ℝ) (curvature : ℝ → ℝ)
    (s0 : ℝ × ℝ) (_hab : a ≤ b) (hA : 0 ≤ A)
    (hcurv : Continuous curvature) (hcurvA : ∀ t, |curvature t| ≤ A) :
    ∃ s : ℝ → ℝ × ℝ, s a=s0 ∧ ∀ t ∈ Set.Icc a b,
      HasDerivAt s (dynamicLinearBulkField delta (curvature t) (s t)) t := by
  let L := |delta|+1+A
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let K : ℝ≥0 := ⟨L,hL⟩
  let H := ‖s0‖*Real.exp (L*(b-a))+1
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let f := fun t s => dynamicLinearBulkField delta (curvature (t+a)) (dynamicBulkClamp H s)
  have hLip : ∀ t, LipschitzWith K (f t) := by
    intro t
    apply LipschitzWith.of_dist_le_mul
    intro x z
    have hb := dynamicLinearBulkField_norm delta (curvature (t+a)) A
      (dynamicBulkClamp H x-dynamicBulkClamp H z) hA (hcurvA _)
    rw [← dynamicLinearBulkField_sub] at hb
    have hc := (dynamicBulkClamp_lipschitz H).norm_sub_le x z
    simp only [NNReal.coe_one,one_mul] at hc
    have ht := mul_le_mul_of_nonneg_left hc hL
    convert hb.trans ht using 1 <;> simp [dist_eq_norm,K]
    exact Or.inl rfl
  have hf : ∀ t s, ‖f t s‖ ≤ L*H := by
    intro t s
    exact (dynamicLinearBulkField_norm delta (curvature (t+a)) A _ hA (hcurvA _)).trans
      (mul_le_mul_of_nonneg_left (dynamicBulkClamp_norm_bound H hH s) hL)
  have hcont : ∀ s, Continuous (fun t => f t s) := by
    intro s
    dsimp [f,dynamicLinearBulkField]
    fun_prop
  obtain ⟨z,hz0,hz⟩ := bounded_lipschitz_ode_global f s0 K (L*H) (mul_nonneg hL hH) hf hLip hcont
  have hznorm : ∀ t ∈ Set.Icc 0 (b-a), ‖z t‖ ≤ ‖s0‖*Real.exp (L*t) := by
    have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f:=z) (f':=fun t => f t (z t))
      (a:=0) (b:=b-a) (δ:=‖s0‖) (K:=L) (ε:=0)
      (fun t ht => (hz t).continuousAt.continuousWithinAt) (fun t ht => (hz t).hasDerivWithinAt)
      (by rw [hz0]) (by
        intro t ht
        have hb := dynamicLinearBulkField_norm delta (curvature (t+a)) A (dynamicBulkClamp H (z t)) hA (hcurvA _)
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

end
end SparseSGD.Logistic
