import SparseSGD.Logistic.DynamicSource
import Mathlib.Analysis.ODE.ExistUnique
namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 1600000

/-- The smooth dynamic field has unique solutions on every common closed
interval of existence. Boundedness and the Lipschitz constant are derived. -/
theorem dynamic_solution_unique (r delta Phi a b : ℝ) (y z : ℝ → DynamicState)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (dynamicField r delta Phi (y t)) t)
    (hz : ∀ t ∈ Set.Icc a b, HasDerivAt z (dynamicField r delta Phi (z t)) t)
    (hi : y a=z a) : ∀ t ∈ Set.Icc a b, y t=z t := by
  have cy : ContinuousOn y (Set.Icc a b) := fun t ht => (hy t ht).continuousAt.continuousWithinAt
  have cz : ContinuousOn z (Set.Icc a b) := fun t ht => (hz t ht).continuousAt.continuousWithinAt
  obtain ⟨My,hMy⟩ := isCompact_Icc.exists_bound_of_continuousOn cy
  obtain ⟨Mz,hMz⟩ := isCompact_Icc.exists_bound_of_continuousOn cz
  let M := max My Mz
  obtain ⟨L,F,hF,hL,hb⟩ := dynamicField_compact_bounds r delta Phi M
  have hdist := dist_le_of_trajectories_ODE_of_mem (v:=fun _ => dynamicField r delta Phi)
    (s:=fun _ => Metric.closedBall (0:DynamicState) M) (K:=L)
    (fun _ _ => hL) cy
    (fun t ht => (hy t (Set.mem_Icc_of_Ico ht)).hasDerivWithinAt)
    (fun t ht => by simpa [M] using (hMy t (Set.mem_Icc_of_Ico ht)).trans (le_max_left My Mz))
    cz (fun t ht => (hz t (Set.mem_Icc_of_Ico ht)).hasDerivWithinAt)
    (fun t ht => by simpa [M] using (hMz t (Set.mem_Icc_of_Ico ht)).trans (le_max_right My Mz))
    (δ:=0) (by simp [hi])
  intro t ht
  exact dist_eq_zero.mp (le_antisymm (by simpa using hdist t ht) dist_nonneg)

/-- Every positive semidefinite rank-at-most-one bulk start admits real
oscillator coordinates, including the degenerate zero position case. -/
theorem dynamic_rank_one_factorization (y : DynamicState)
    (hR : 0 ≤ y 2) (hV : 0 ≤ y 3) (hQ : dynamicDeterminant y=0) :
    ∃ z : DynamicOscillatorState, dynamicRankOneLift z=y := by
  have hq : y 2*y 3=y 4^2 := by simpa [dynamicDeterminant,sub_eq_zero] using hQ
  by_cases hpos : 0 < y 2
  · let X := Real.sqrt (y 2)
    have hX : 0 < X := Real.sqrt_pos.mpr hpos
    have hXsq : X^2=y 2 := Real.sq_sqrt hR
    refine ⟨![y 0,y 1,X,y 4/X],?_⟩
    ext i
    fin_cases i <;> simp [dynamicRankOneLift]
    · exact hXsq
    · rw [div_pow,hXsq]
      apply (div_eq_iff (ne_of_gt hpos)).mpr
      nlinarith only [hq]
    · exact mul_div_cancel₀ _ hX.ne'
  · have hR0 : y 2=0 := le_antisymm (le_of_not_gt hpos) hR
    have hC0 : y 4=0 := by rw [hR0,zero_mul] at hq; nlinarith only [hq,sq_nonneg (y 4)]
    refine ⟨![y 0,y 1,0,Real.sqrt (y 3)],?_⟩
    ext i
    fin_cases i <;> simp [dynamicRankOneLift,hR0,hC0,Real.sq_sqrt hV]

/-- Any oscillator solution with the factored initial state is exactly the
noise-free five-coordinate solution, by actual ODE uniqueness. -/
theorem dynamic_rank_one_solution_lift (r delta a b : ℝ)
    (y : ℝ → DynamicState) (z : ℝ → DynamicOscillatorState)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (dynamicField r delta 0 (y t)) t)
    (hz : ∀ t ∈ Set.Icc a b, HasDerivAt z (dynamicOscillatorField r delta (z t)) t)
    (hi : dynamicRankOneLift (z a)=y a) :
    ∀ t ∈ Set.Icc a b, y t=dynamicRankOneLift (z t) := by
  apply dynamic_solution_unique r delta 0 a b y (fun t => dynamicRankOneLift (z t)) hy
    (fun t ht => hasDerivAt_dynamicRankOneLift r delta z t (hz t ht)) hi.symm

/-- In oscillator coordinates the actual bulk position is a square and the
coordinate derivatives are the two equations claimed in cell 3. -/
theorem dynamic_rank_one_oscillator_coordinates (r delta a b : ℝ)
    (y : ℝ → DynamicState) (z : ℝ → DynamicOscillatorState)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (dynamicField r delta 0 (y t)) t)
    (hz : ∀ t ∈ Set.Icc a b, HasDerivAt z (dynamicOscillatorField r delta (z t)) t)
    (hi : dynamicRankOneLift (z a)=y a) :
    ∀ t ∈ Set.Icc a b, y t 2=z t 2^2 ∧
      HasDerivAt (fun s => z s 2) (-delta*z t 3) t ∧
      HasDerivAt (fun s => z s 3) (-z t 3+dynamicAlpha r (y t)*z t 2) t := by
  intro t ht
  have heq := dynamic_rank_one_solution_lift r delta a b y z hy hz hi t ht
  have hc := hasDerivAt_pi.mp (hz t ht)
  refine ⟨by simp [heq,dynamicRankOneLift],?_,?_⟩
  · simpa [dynamicOscillatorField] using hc 2
  · simpa [heq,dynamicOscillatorField] using hc 3

/-- The oscillator itself is an actual smooth vector field. -/
theorem contDiff_dynamicOscillatorField (r delta : ℝ) :
    ContDiff ℝ ⊤ (dynamicOscillatorField r delta) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [dynamicOscillatorField,dynamicAlpha,dynamicRankOneLift] <;> fun_prop

/-- Picard-Lindelof supplies an actual local oscillator from every factored
PSD rank-one start; oscillator existence is not an assumed paper claim. -/
theorem dynamic_rank_one_oscillator_exists (r delta t0 : ℝ) (y0 : DynamicState)
    (hR : 0 ≤ y0 2) (hV : 0 ≤ y0 3) (hQ : dynamicDeterminant y0=0) :
    ∃ z : ℝ → DynamicOscillatorState, dynamicRankOneLift (z t0)=y0 ∧
      ∃ epsilon > (0:ℝ), ∀ t ∈ Set.Ioo (t0-epsilon) (t0+epsilon),
        HasDerivAt z (dynamicOscillatorField r delta (z t)) t := by
  obtain ⟨z0,hz0⟩ := dynamic_rank_one_factorization y0 hR hV hQ
  have hc : ContDiffAt ℝ 1 (dynamicOscillatorField r delta) z0 :=
    ((contDiff_dynamicOscillatorField r delta).of_le (by simp)).contDiffAt
  obtain ⟨z,hz,epsilon,hepsilon,hsol⟩ :=
    hc.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t0
  exact ⟨z,by rw [hz]; exact hz0,epsilon,hepsilon,hsol⟩

/-- On a genuine initial interval, every PSD rank-one five-coordinate
solution has actual oscillator coordinates, with existence and uniqueness
both proved from smooth calculus. -/
theorem dynamic_rank_one_local_oscillator (r delta a b : ℝ)
    (y : ℝ → DynamicState) (hab : a < b)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (dynamicField r delta 0 (y t)) t)
    (hR : 0 ≤ y a 2) (hV : 0 ≤ y a 3) (hQ : dynamicDeterminant (y a)=0) :
    ∃ epsilon > (0:ℝ), ∃ z : ℝ → DynamicOscillatorState,
      a+epsilon ≤ b ∧ ∀ t ∈ Set.Icc a (a+epsilon),
        y t=dynamicRankOneLift (z t) ∧
        HasDerivAt z (dynamicOscillatorField r delta (z t)) t := by
  obtain ⟨z,hz,sigma,hsigma,hsol⟩ := dynamic_rank_one_oscillator_exists r delta a (y a) hR hV hQ
  let epsilon := min (sigma/2) ((b-a)/2)
  have heps : 0 < epsilon := by dsimp [epsilon]; positivity
  have hes : epsilon < sigma := by
    have h := min_le_left (sigma/2) ((b-a)/2)
    dsimp [epsilon]
    linarith
  have heb : a+epsilon ≤ b := by
    have h := min_le_right (sigma/2) ((b-a)/2)
    dsimp [epsilon]
    linarith
  have hz' : ∀ t ∈ Set.Icc a (a+epsilon), HasDerivAt z (dynamicOscillatorField r delta (z t)) t := by
    intro t ht
    apply hsol t
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have heq := dynamic_rank_one_solution_lift r delta a (a+epsilon) y z
    (fun t ht => hy t ⟨ht.1,ht.2.trans heb⟩) hz' hz
  exact ⟨epsilon,heps,z,heb,fun t ht => ⟨heq t ht,hz' t ht⟩⟩

end
end SparseSGD.Logistic
