import SparseSGD.Logistic.SlowLimitEuler
namespace SparseSGD.Logistic
noncomputable section
open scoped NNReal
set_option maxHeartbeats 2400000

/-- Coupled fast tracking and compact bootstrap for a slow Euler limit.
The geometric cold-start layer is summed before Gronwall. Compact containment
of every grid point is proved, rather than imposed on the numerical path. -/
theorem slow_grid_error_of_tracking (r Phi M T h z e J0 K Ctr Cres F : ℝ)
    (Lf : ℝ≥0) (N : ℕ) (x : ℕ → DynamicState) (y : ℝ → ℝ × ℝ)
    (_hM : 2 ≤ M) (hT0 : 0 ≤ T) (hh : 0 < h) (hh1 : h ≤ 1) (hz : 0 ≤ z)
    (he : 0 ≤ e) (hJ0 : 0 ≤ J0) (hK : 0 ≤ K) (hCtr : 0 ≤ Ctr)
    (hCres : 0 ≤ Cres) (hF : 0 ≤ F)
    (hLip : LipschitzOnWith Lf (slowVectorField r Phi) (Metric.closedBall 0 M))
    (hbound : ∀ s, ‖s‖ ≤ M → ‖slowVectorField r Phi s‖ ≤ F)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (slowVectorField r Phi (y t)) t)
    (hyM : ∀ t ∈ Set.Icc 0 T, ‖y t‖ ≤ M-2)
    (hinit : slowPosition (x 0)=y 0)
    (hfast0 : slowTrackingError r h Phi (x 0) ≤ J0)
    (horizon : (N:ℝ)*z ≤ T)
    (hlocal : ∀ n < N, ‖slowPosition (x n)‖ ≤ M →
      ‖slowPosition (x (n+1))-slowPosition (x n)‖ ≤ z*K*(1+slowTrackingError r h Phi (x n)) ∧
      ‖slowPosition (x (n+1))-(slowPosition (x n)+z • slowVectorField r Phi (slowPosition (x n)))‖ ≤
        z*Cres*(slowTrackingError r h Phi (x n)+z+e) ∧
      (‖slowPosition (x (n+1))‖ ≤ M →
        slowTrackingError r h Phi (x (n+1)) ≤
          (1-h/4)*slowTrackingError r h Phi (x n)+Ctr*(z+h*e)))
    (hmove : z*K*(1+J0+4*Ctr*(z/h+e)) ≤ 1)
    (hsmall : (4*z*(Cres*J0)/h+
      T*(Cres*(4*Ctr*(z/h+e)+z+e)+(Lf:ℝ)*F*z))*Real.exp (T*(Lf:ℝ)) ≤ 1) :
    ∀ n ≤ N,
      ‖slowPosition (x n)-y ((n:ℝ)*z)‖ ≤
        (4*z*(Cres*J0)/h+T*(Cres*(4*Ctr*(z/h+e)+z+e)+(Lf:ℝ)*F*z))*Real.exp (T*(Lf:ℝ)) ∧
      slowTrackingError r h Phi (x n) ≤ (1-h/4)^n*J0+4*Ctr*(z/h+e) := by
  let D := 4*Ctr*(z/h+e)
  let B := (4*z*(Cres*J0)/h+T*(Cres*(D+z+e)+(Lf:ℝ)*F*z))*Real.exp (T*(Lf:ℝ))
  let q := 1-h/4
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hfixed : q*D+Ctr*(z+h*e)=D := by dsimp [q,D]; field_simp; ring
  have htime : ∀ n ≤ N, (n:ℝ)*z ∈ Set.Icc 0 T := by
    intro n hn
    exact ⟨mul_nonneg (Nat.cast_nonneg n) hz,
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hz).trans horizon⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    change ‖slowPosition (x n)-y ((n:ℝ)*z)‖ ≤ B ∧ slowTrackingError r h Phi (x n) ≤ q^n*J0+D
    by_cases hn0 : n=0
    · subst n
      simp only [Nat.cast_zero,zero_mul,hinit,sub_self,norm_zero,pow_zero,one_mul]
      exact ⟨hB,hfast0.trans (le_add_of_nonneg_right hD)⟩
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      have hk : k < N := by omega
      have hik := ih k (Nat.lt_succ_self k) (Nat.le_of_lt hk)
      have hpos : ‖slowPosition (x k)‖ ≤ M-1 := by
        have ht := norm_add_le (slowPosition (x k)-y ((k:ℝ)*z)) (y ((k:ℝ)*z))
        rw [sub_add_cancel] at ht
        have hyr := hyM ((k:ℝ)*z) (htime k (Nat.le_of_lt hk))
        have hu : ‖slowPosition (x k)-y ((k:ℝ)*z)‖ ≤ 1 := hik.1.trans hsmall
        linarith
      have hloc := hlocal k hk (hpos.trans (by linarith))
      have hfast : slowTrackingError r h Phi (x k) ≤ J0+D := by
        have hp := mul_le_mul_of_nonneg_right (pow_le_one₀ (n:=k) hq hq1) hJ0
        apply hik.2.trans
        change q^k*J0+D ≤ J0+D
        exact add_le_add (by simpa using hp) le_rfl
      have hnext : ‖slowPosition (x (k+1))‖ ≤ M := by
        have ht := norm_add_le (slowPosition (x (k+1))-slowPosition (x k)) (slowPosition (x k))
        rw [sub_add_cancel] at ht
        have hm := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1:ℝ)) hfast) (mul_nonneg hz hK)
        have hstep : ‖slowPosition (x (k+1))-slowPosition (x k)‖ ≤ 1 :=
          hloc.1.trans (hm.trans (by simpa [D,add_assoc] using hmove))
        linarith
      have hfastnext : slowTrackingError r h Phi (x (k+1)) ≤ q^(k+1)*J0+D := by
        have hr := hloc.2.2 hnext
        have hb := mul_le_mul_of_nonneg_left hik.2 hq
        change slowTrackingError r h Phi (x (k+1)) ≤ q*slowTrackingError r h Phi (x k)+Ctr*(z+h*e) at hr
        change q*slowTrackingError r h Phi (x k) ≤ q*(q^k*J0+D) at hb
        rw [pow_succ]
        nlinarith only [hr,hb,hfixed]
      refine ⟨?_,hfastnext⟩
      let u := fun j => ‖slowPosition (x j)-y ((j:ℝ)*z)‖
      have hrec : ∀ j < k+1, u (j+1) ≤ (1+z*(Lf:ℝ))*u j+
          z*((Cres*J0)*q^j+(Cres*(D+z+e)+(Lf:ℝ)*F*z)) := by
        intro j hj
        have hjN : j < N := by omega
        have hij := ih j (by omega) (Nat.le_of_lt hjN)
        have hjM : ‖slowPosition (x j)‖ ≤ M := by
          have ht := norm_add_le (slowPosition (x j)-y ((j:ℝ)*z)) (y ((j:ℝ)*z))
          rw [sub_add_cancel] at ht
          have hyr := hyM ((j:ℝ)*z) (htime j (Nat.le_of_lt hjN))
          have hu : ‖slowPosition (x j)-y ((j:ℝ)*z)‖ ≤ 1 := hij.1.trans hsmall
          linarith
        have hjnext : (j:ℝ)*z+z ≤ T := by
          have ht := (htime (j+1) (by omega)).2
          simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using ht
        have hseg : ∀ t ∈ Set.Icc ((j:ℝ)*z) ((j:ℝ)*z+z), t ∈ Set.Icc 0 T := by
          intro t ht
          exact ⟨(mul_nonneg (Nat.cast_nonneg j) hz).trans ht.1,ht.2.trans hjnext⟩
        have heuler := slow_ode_euler_error r Phi M F ((j:ℝ)*z) z Lf y hz hF
          (fun t ht => hy t (hseg t ht)) (fun t ht => (hyM t (hseg t ht)).trans (by linarith))
          hbound hLip
        have hl := hLip.norm_sub_le (by simpa using hjM)
          (by simpa using (hyM ((j:ℝ)*z) (htime j (Nat.le_of_lt hjN))).trans (by linarith))
        have hr := (hlocal j hjN hjM).2.1
        have hs := slow_one_step_error (slowVectorField r Phi) z
          (z*Cres*(slowTrackingError r h Phi (x j)+z+e)) ((Lf:ℝ)*F*z^2)
          Lf (slowPosition (x j)) (y ((j:ℝ)*z)) (slowPosition (x (j+1)))
          (y ((j:ℝ)*z+z)) hz hl hr heuler
        have hf := mul_le_mul_of_nonneg_left hij.2 (mul_nonneg hz hCres)
        dsimp only [u]
        rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul]
        nlinarith only [hs,hf]
      have hg := slow_discrete_gronwall_initial_layer u (k+1) h z (Cres*J0)
        (Cres*(D+z+e)+(Lf:ℝ)*F*z) (Lf:ℝ) T
        (fun j _ => norm_nonneg _) hh hh1 hz (mul_nonneg hCres hJ0) (by positivity)
        Lf.coe_nonneg hrec ((htime (k+1) hn).2) (k+1) le_rfl
      simpa only [u,hinit,Nat.cast_zero,zero_mul,sub_self,norm_zero,zero_add] using hg

end
end SparseSGD.Logistic
