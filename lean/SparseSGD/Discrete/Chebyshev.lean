import SparseSGD.Discrete.Renewal
import Mathlib.RingTheory.Polynomial.Chebyshev

namespace SparseSGD
noncomputable section

/-- Chebyshev-polynomial form of the discrete mean impulse response. -/
def chebyResponse (p : Params) (n : ℕ) : ℝ :=
  -(Real.sqrt p.beta) ^ n *
    (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval
      ((1 + p.beta - p.w) / (2 * Real.sqrt p.beta))

theorem kickResponse_eq_chebyshev (p : Params) (hb : 0 < p.beta) (n : ℕ) :
    kickResponse p n = chebyResponse p n := by
  have hroot : 0 < Real.sqrt p.beta := Real.sqrt_pos.2 hb
  have hrootSq : (Real.sqrt p.beta) ^ 2 = p.beta := Real.sq_sqrt hb.le
  refine Nat.twoStepInduction
    (motive := fun k => kickResponse p k = chebyResponse p k) ?_ ?_ ?_ n
  · simp [chebyResponse, Polynomial.Chebyshev.U_zero]
  · simp [chebyResponse, kickResponse_one, Polynomial.Chebyshev.U_one]
    field_simp [ne_of_gt hroot]
    ring
  · intro k hk hk1
    rw [kickResponse_recurrence p k, hk1, hk]
    dsimp [chebyResponse]
    let x : ℝ := (1 + p.beta - p.w) / (2 * Real.sqrt p.beta)
    have hU := congrArg (fun q : Polynomial ℝ => q.eval x)
      (Polynomial.Chebyshev.U_add_two ℝ (k : ℤ))
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] at hU
    have hix :
        x = (1 + p.beta - p.w) / (2 * Real.sqrt p.beta) := rfl
    have htr' : 1 + p.beta - p.w = 2 * Real.sqrt p.beta * x := by
      rw [hix]
      field_simp [ne_of_gt hroot]
    rw [← hix]
    simp only [pow_succ]
    rw [htr', hU]
    ring_nf
    rw [hrootSq]
    ring

end

end SparseSGD
