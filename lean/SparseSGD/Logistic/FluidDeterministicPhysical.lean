import SparseSGD.Logistic.IncrementDriftMap
import Mathlib.Algebra.QuadraticDiscriminant
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1500000
/-- The physical bulk Gram cone in the matched order `(theta,Y,R,C,V)`. -/
def matchedPhysical (y : Fin 5 → ℝ) : Prop :=
  0 ≤ y 2 ∧ 0 ≤ y 4 ∧ (y 3)^2 ≤ y 2*y 4

theorem matchedPhysical_iff_quadratic (y : Fin 5 → ℝ) :
    matchedPhysical y ↔ ∀ a b : ℝ, 0 ≤ y 2*a^2+2*y 3*a*b+y 4*b^2 := by
  constructor
  · rintro ⟨hR,hV,hC⟩ a b
    by_cases hz : y 2=0
    · have hc : y 3=0 := by rw [hz] at hC; nlinarith [sq_nonneg (y 3)]
      simp only [hz,hc,zero_mul,mul_zero,zero_add]; exact mul_nonneg hV (sq_nonneg b)
    · have hRp : 0<y 2 := lt_of_le_of_ne hR (Ne.symm hz)
      have hd : 0≤(y 2*y 4-(y 3)^2)*b^2 := mul_nonneg (by linarith) (sq_nonneg b)
      have hs := sq_nonneg (y 2*a+y 3*b)
      have H : 0≤y 2*(y 2*a^2+2*y 3*a*b+y 4*b^2) := by nlinarith [hd,hs]
      exact nonneg_of_mul_nonneg_right H hRp
  · intro h
    have hR := h 1 0
    have hV := h 0 1
    have hd := discrim_le_zero (a:=y 2) (b:=2*y 3) (c:=y 4) (fun x => by convert h x 1 using 1 <;> ring)
    dsimp [discrim] at hd
    exact ⟨by nlinarith,by nlinarith,by nlinarith⟩

theorem matchedPhysical_convex : Convex ℝ {y : Fin 5 → ℝ | matchedPhysical y} := by
  intro x hx y hy a b ha hb hab
  apply (matchedPhysical_iff_quadratic _).mpr
  intro u v
  have H := add_nonneg (mul_nonneg ha ((matchedPhysical_iff_quadratic x).mp hx u v))
    (mul_nonneg hb ((matchedPhysical_iff_quadratic y).mp hy u v))
  convert H using 1 <;> simp <;> ring

theorem matchedPhysical_variance {y : Fin 5 → ℝ} (hy : matchedPhysical y) :
    0≤(y 0)^2+y 2 := add_nonneg (sq_nonneg _) hy.1

/-- Every sample summary is physical, including zero learning rate. -/
theorem matchedSummary_physical {d : ℕ} (eta beta : ℝ) (mu : Vec d) (s : State d) :
    matchedPhysical (matchedSummary eta beta mu s) := by
  have hc := real_inner_mul_inner_self_le (bulkPart mu s.1) (bulkPart mu s.2)
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hc
  unfold matchedPhysical
  dsimp [matchedSummary]
  refine ⟨sq_nonneg _,mul_nonneg (sq_nonneg _) (sq_nonneg _),?_⟩
  nlinarith [mul_nonneg (sq_nonneg (eta/(1-beta))) (sub_nonneg.mpr hc)]

/-- A coefficient step preserves the physical Gram cone whenever its actual
centered variance is nonnegative. This is the covariance pushforward identity. -/
theorem matchedCoefficientStep_physical (r eta beta A b z : ℝ) {y : Fin 5 → ℝ}
    (hy : matchedPhysical y) (hz : 0≤z) :
    matchedPhysical (matchedCoefficientStep r eta beta A b z y) := by
  apply (matchedPhysical_iff_quadratic _).mpr
  intro u v
  have H := (matchedPhysical_iff_quadratic y).mp hy
    ((1-eta*(1-beta)*A)*u+eta*A*v) (beta*(v-(1-beta)*u))
  have hz' : 0≤eta^2*z*(v-(1-beta)*u)^2 := by positivity
  convert add_nonneg H hz' using 1 <;> simp [matchedCoefficientStep] <;> ring
end
end SparseSGD.Logistic
