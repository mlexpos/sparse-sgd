import SparseSGD.Logistic.DynamicConvergence
namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 2400000

private theorem parameter_bound (r delta Phi delta0 Phi0 M a : ℝ) (y : DynamicState)
    (hM : 0 ≤ M) (hy : ‖y‖ ≤ M) (ha : 0 < a) (hd : a ≤ delta) (hd0 : a ≤ delta0) :
    ‖dynamicField r delta Phi y-dynamicField r delta0 Phi0 y‖ ≤
      ((2*M+1)*(1+2/a+2*|Phi0|/a^2))*(|delta-delta0|+|Phi-Phi0|) := by
  apply (dynamicField_parameter_error r delta Phi delta0 Phi0 M y hM hy).trans
  have hk := dynamicNoiseRate_parameter_error delta Phi delta0 Phi0 a ha hd hd0
  have hdif := abs_nonneg (delta-delta0)
  have hPhi := abs_nonneg (Phi-Phi0)
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2*M+1)
  have h1 : 0 ≤ 2/a := by positivity
  have h2 : 0 ≤ 2*|Phi0|/a^2 := by positivity
  nlinarith

/-- Proposition LR34 with a fixed compact reference tube. The recursion uses
actual Gaussian logistic coefficients. Its compact containment follows from
the numerical smallness hypothesis. Initial normalized states agree. -/
theorem dynamic_LR34_on_compact (r0 delta0 Phi0 M T : ℝ)
    (hd0 : 0 < delta0) (hM : 1 ≤ M) (hT : 0 ≤ T)
    (y : ℝ → DynamicState)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (dynamicField r0 delta0 Phi0 (y t)) t)
    (hyM : ∀ t ∈ Set.Icc 0 T, ‖y t‖ ≤ M-1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
      (mu : Vec d) (theta : ℕ → Vec d) (x : ℕ → DynamicState) (N : ℕ) (e : ℝ),
      r mu=r0 → 0 < (p:ℝ) → 0 < B → 2 ≤ d → 0 < eta →
      0 < 1-beta → 1-beta ≤ 1 → 0 ≤ e → e ≤ 1/2 →
      |eta*(p:ℝ)/(1-beta)-delta0| ≤ delta0/2 →
      |dynamicSourceLoad d B eta-Phi0| ≤ 1 →
      (N:ℝ)*(1-beta) ≤ T → x 0=y 0 →
      (∀ k < N, ‖theta k‖^2=x k 0^2+x k 2) →
      (∀ k < N, tameError p mu (theta k) ≤ e) →
      (∀ k < N, x (k+1)=dynamicDriftMap (B:=B) eta beta p mu (theta k) (x k)) →
      C*((1-beta)+|eta*(p:ℝ)/(1-beta)-delta0|+|dynamicSourceLoad d B eta-Phi0|+e) ≤ 1 →
      ∀ n ≤ N, ‖x n-y ((n:ℝ)*(1-beta))‖ ≤
        C*((1-beta)+|eta*(p:ℝ)/(1-beta)-delta0|+|dynamicSourceLoad d B eta-Phi0|+e) := by
  let a := delta0/2
  let D := 2*delta0
  let Q := 2*(|Phi0|+1)/a
  have ha : 0 < a := by dsimp [a]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  obtain ⟨Cs,hCs,hcons⟩ := dynamicDriftMap_uniform_consistency r0 M D Q
    (by linarith) (by dsimp [D]; positivity) hQ
  obtain ⟨L,F,hF,hL,hb⟩ := dynamicField_compact_bounds r0 delta0 Phi0 M
  let P := (2*M+1)*(1+2/a+2*|Phi0|/a^2)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  let K := Cs+P+(L:ℝ)*F+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let C := 1+T*K*Real.exp (T*(L:ℝ))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro d B eta beta p mu theta x N e hr hp hB hd heta hh hh1 he he1 hdelta hPhi htime hi hgeom htame hrec hsmall
  let delta := eta*(p:ℝ)/(1-beta)
  let Phi := dynamicSourceLoad d B eta
  let q := |delta-delta0|+|Phi-Phi0|
  let Z := (1-beta)+q+e
  let E := Cs*((1-beta)+e)+P*q
  have hE : 0 ≤ E := by dsimp [E,q]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z,q]; positivity
  have hda : a ≤ delta := by dsimp [delta,a] at *; linarith [(abs_le.mp hdelta).1]
  have hdpos : 0 < delta := ha.trans_le hda
  have hdd : |delta| ≤ D := by
    rw [abs_of_pos hdpos]
    dsimp [delta,D] at *
    linarith [(abs_le.mp hdelta).2]
  have hBr : (B:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hload := dynamicNoiseRate_eq_source d B eta (1-beta) (p:ℝ) heta.ne' hh.ne' hp.ne' hBr
  have hPhiabs : |Phi| ≤ |Phi0|+1 := by
    have h := abs_add_le (Phi-Phi0) Phi0
    rw [sub_add_cancel] at h
    exact h.trans (by dsimp [Phi]; linarith)
  have hk : dynamicNoiseRate d B (1-beta) (p:ℝ) ≤ Q := by
    rw [hload]
    change 2*Phi/delta ≤ 2*(|Phi0|+1)/a
    calc
      _ ≤ 2*|Phi|/delta := by gcongr; exact le_abs_self Phi
      _ ≤ _ := by gcongr
  have hlocal : ∀ k < N, ‖x k‖ ≤ M →
      ‖x (k+1)-(x k+(1-beta) • dynamicField r0 delta0 Phi0 (x k))‖ ≤ (1-beta)*E := by
    intro k hkN hx
    have hc := hcons eta beta p mu (theta k) (x k) hr hp hB hd heta.ne' hh hh1
      ((htame k hkN).trans he1) (hgeom k hkN) hx hdd hk
    have hc' : ‖dynamicDriftMap (B:=B) eta beta p mu (theta k) (x k)-
        (x k+(1-beta) • dynamicField r0 delta Phi (x k))‖ ≤ Cs*(1-beta)*((1-beta)+e) :=
      hc.trans (by gcongr; exact htame k hkN)
    have hpbound := parameter_bound r0 delta Phi delta0 Phi0 M a (x k) (by linarith) hx ha hda (by dsimp [a]; linarith)
    rw [hrec k hkN]
    have hid : dynamicDriftMap (B:=B) eta beta p mu (theta k) (x k)-
        (x k+(1-beta) • dynamicField r0 delta0 Phi0 (x k)) =
      (dynamicDriftMap (B:=B) eta beta p mu (theta k) (x k)-
        (x k+(1-beta) • dynamicField r0 delta Phi (x k)))+
        (1-beta) • (dynamicField r0 delta Phi (x k)-dynamicField r0 delta0 Phi0 (x k)) := by module
    rw [hid]
    calc
      _ ≤ ‖dynamicDriftMap (B:=B) eta beta p mu (theta k) (x k)-
          (x k+(1-beta) • dynamicField r0 delta Phi (x k))‖+
        ‖(1-beta) • (dynamicField r0 delta Phi (x k)-dynamicField r0 delta0 Phi0 (x k))‖ := norm_add_le _ _
      _ ≤ Cs*(1-beta)*((1-beta)+e)+(1-beta)*(P*q) := by
        apply add_le_add hc'
        simpa [norm_smul,Real.norm_eq_abs,abs_of_pos hh,P,q] using
          mul_le_mul_of_nonneg_left hpbound hh.le
      _ = _ := by dsimp [E]; ring
  have hbound : T*(E+(L:ℝ)*F*(1-beta))*Real.exp (T*(L:ℝ)) ≤ C*Z := by
    have hforce : E+(L:ℝ)*F*(1-beta) ≤ K*Z := by
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have hz1 : (1-beta)+e ≤ Z := by dsimp [Z]; linarith
      have hz2 : q ≤ Z := by dsimp [Z]; linarith
      have hz3 : 1-beta ≤ Z := by dsimp [Z]; linarith
      dsimp only [E]
      calc
        _ ≤ Cs*Z+P*Z+(L:ℝ)*F*Z := by gcongr
        _ ≤ K*Z := by dsimp [K]; nlinarith only [hZ]
    calc
      _ ≤ T*(K*Z)*Real.exp (T*(L:ℝ)) := by gcongr
      _ ≤ C*Z := by dsimp [C]; nlinarith
  have hsmall' : (‖x 0-y 0‖+T*(E+(L:ℝ)*F*(1-beta)))*Real.exp (T*(L:ℝ)) ≤ 1 := by
    rw [hi,sub_self,norm_zero,zero_add]
    exact hbound.trans (by simpa [Z,q,add_assoc] using hsmall)
  have hgrid := dynamic_grid_error_of_local_residual r0 delta0 Phi0 M F (1-beta) E T L N x y
    hh.le hE hF htime hy hyM hL hb hlocal hsmall'
  intro n hn
  have h := hgrid n hn
  rw [hi,sub_self,norm_zero,zero_add] at h
  exact h.trans (by simpa [Z,q,add_assoc] using hbound)

/-- Source Proposition LR34 on every closed interval of an actual solution.
The compact tube is supplied by continuity of the solution, and the actual
normalized drift recursion is proved to remain in it for small input error. -/
theorem prop_LR34 (r0 delta0 Phi0 T : ℝ) (hd0 : 0 < delta0) (hT : 0 ≤ T)
    (y : ℝ → DynamicState)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (dynamicField r0 delta0 Phi0 (y t)) t) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d B : ℕ} (eta beta : ℝ) (p : unitInterval)
      (mu : Vec d) (theta : ℕ → Vec d) (x : ℕ → DynamicState) (N : ℕ) (e : ℝ),
      r mu=r0 → 0 < (p:ℝ) → 0 < B → 2 ≤ d → 0 < eta →
      0 < 1-beta → 1-beta ≤ 1 → 0 ≤ e → e ≤ 1/2 →
      |eta*(p:ℝ)/(1-beta)-delta0| ≤ delta0/2 →
      |dynamicSourceLoad d B eta-Phi0| ≤ 1 →
      (N:ℝ)*(1-beta) ≤ T → x 0=y 0 →
      (∀ k < N, ‖theta k‖^2=x k 0^2+x k 2) →
      (∀ k < N, tameError p mu (theta k) ≤ e) →
      (∀ k < N, x (k+1)=dynamicDriftMap (B:=B) eta beta p mu (theta k) (x k)) →
      C*((1-beta)+|eta*(p:ℝ)/(1-beta)-delta0|+|dynamicSourceLoad d B eta-Phi0|+e) ≤ 1 →
      ∀ n ≤ N, ‖x n-y ((n:ℝ)*(1-beta))‖ ≤
        C*((1-beta)+|eta*(p:ℝ)/(1-beta)-delta0|+|dynamicSourceLoad d B eta-Phi0|+e) := by
  have hcont : ContinuousOn y (Set.Icc 0 T) :=
    fun t ht => (hy t ht).continuousAt.continuousWithinAt
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let M := max A 0+1
  have hM : 1 ≤ M := by dsimp [M]; linarith [le_max_right A 0]
  have hyM : ∀ t ∈ Set.Icc 0 T, ‖y t‖ ≤ M-1 := by
    intro t ht
    have hb := (hA t ht).trans (le_max_left A 0)
    dsimp [M]
    linarith
  exact dynamic_LR34_on_compact r0 delta0 Phi0 M T hd0 hM hT y hy hyM

end
end SparseSGD.Logistic
