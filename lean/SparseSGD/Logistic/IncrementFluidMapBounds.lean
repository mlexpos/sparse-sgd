import SparseSGD.Logistic.IncrementFluidRates
import SparseSGD.Logistic.FluidDeterministicStateTaylor
import SparseSGD.Logistic.FluidDeterministicFree
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 2200000

abbrev MatchedCoordinate := Fin 5 → ℝ

/-- Uniform actual scalar value, first jet, and quadratic Taylor control
on a bounded physical domain. This carries no concentration premise. -/
structure ScalarExpansionControl (S : Set MatchedCoordinate) (f : MatchedCoordinate → ℝ)
    (df : MatchedCoordinate → MatchedCoordinate →L[ℝ] ℝ) (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  value : ∀ x ∈ S, |f x| ≤ C
  first : ∀ x ∈ S, ‖df x‖ ≤ C
  remainder : ∀ x ∈ S, ∀ y ∈ S,
    |f x-f y-df y (x-y)| ≤ C*‖x-y‖^2

namespace ScalarExpansionControl
variable {S : Set MatchedCoordinate} {f g : MatchedCoordinate → ℝ}
    {df dg : MatchedCoordinate → MatchedCoordinate →L[ℝ] ℝ} {C D : ℝ}

theorem add (hf : ScalarExpansionControl S f df C) (hg : ScalarExpansionControl S g dg D) :
    ScalarExpansionControl S (fun x => f x+g x) (fun x => df x+dg x) (C+D) := by
  refine ⟨add_nonneg hf.nonneg hg.nonneg,?_,?_,?_⟩
  · intro x hx
    exact (abs_add_le _ _).trans (add_le_add (hf.value x hx) (hg.value x hx))
  · intro x hx
    exact (norm_add_le _ _).trans (add_le_add (hf.first x hx) (hg.first x hx))
  · intro x hx y hy
    have he : f x+g x-(f y+g y)-(df y+dg y) (x-y) =
        (f x-f y-df y (x-y))+(g x-g y-dg y (x-y)) := by simp only [ContinuousLinearMap.add_apply]; ring
    rw [he]
    exact (abs_add_le _ _).trans (by convert add_le_add (hf.remainder x hx y hy) (hg.remainder x hx y hy) using 1 <;> ring)

theorem const_mul (hf : ScalarExpansionControl S f df C) (a : ℝ) :
    ScalarExpansionControl S (fun x => a*f x) (fun x => a • df x) (|a| * C) := by
  refine ⟨mul_nonneg (abs_nonneg _) hf.nonneg,?_,?_,?_⟩
  · intro x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hf.value x hx) (abs_nonneg a)
  · intro x hx
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf.first x hx) (abs_nonneg a)
  · intro x hx y hy
    have he : a*f x-a*f y-(a • df y) (x-y) = a*(f x-f y-df y (x-y)) := by
      simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]; ring
    rw [he,abs_mul]
    convert mul_le_mul_of_nonneg_left (hf.remainder x hx y hy) (abs_nonneg a) using 1 <;> ring

theorem difference_bound (hf : ScalarExpansionControl S f df C) (T : ℝ) (hT : 0 ≤ T)
    (hS : ∀ x ∈ S, ‖x‖ ≤ T) (x : MatchedCoordinate) (hx : x ∈ S) (y : MatchedCoordinate) (hy : y ∈ S) :
    |f x-f y| ≤ C*(1+2*T)*‖x-y‖ := by
  have hdiff : ‖x-y‖ ≤ 2*T := (norm_sub_le x y).trans (by linarith [hS x hx,hS y hy])
  have hfirst := (df y).le_opNorm (x-y)
  have hf' : |df y (x-y)| ≤ C*‖x-y‖ := by
    have hfirst' : |df y (x-y)| ≤ ‖df y‖*‖x-y‖ := by simpa only [Real.norm_eq_abs] using hfirst
    exact hfirst'.trans (mul_le_mul_of_nonneg_right (hf.first y hy) (norm_nonneg _))
  have he : f x-f y = (f x-f y-df y (x-y))+df y (x-y) := by ring
  rw [he]
  have hsq := mul_le_mul_of_nonneg_left hdiff (mul_nonneg hf.nonneg (norm_nonneg (x-y)))
  have hh := (abs_add_le _ _).trans (add_le_add (hf.remainder x hx y hy) hf')
  nlinarith

theorem mul (hf : ScalarExpansionControl S f df C) (hg : ScalarExpansionControl S g dg D)
    (T : ℝ) (hT : 0 ≤ T) (hS : ∀ x ∈ S, ‖x‖ ≤ T) :
    ScalarExpansionControl S (fun x => f x*g x)
      (fun x => (f x) • dg x+(g x) • df x) (C*D*(2+(1+2*T)^2)) := by
  have hC := hf.nonneg
  have hD := hg.nonneg
  have hCd : 0 ≤ C*D := mul_nonneg hf.nonneg hg.nonneg
  have hm : 2 ≤ 2+(1+2*T)^2 := by nlinarith [sq_nonneg (1+2*T)]
  refine ⟨by positivity,?_,?_,?_⟩
  · intro x hx
    rw [abs_mul]
    have hh := mul_le_mul (hf.value x hx) (hg.value x hx) (abs_nonneg _) hf.nonneg
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hm hCd])
  · intro x hx
    have hh := norm_add_le ((f x) • dg x) ((g x) • df x)
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs] at hh
    have h1 := mul_le_mul (hf.value x hx) (hg.first x hx) (norm_nonneg _) hf.nonneg
    have h2 := mul_le_mul (hg.value x hx) (hf.first x hx) (norm_nonneg _) hg.nonneg
    nlinarith [mul_le_mul_of_nonneg_left hm hCd]
  · intro x hx y hy
    have he : f x*g x-f y*g y-((f y) • dg y+(g y) • df y) (x-y) =
        f y*(g x-g y-dg y (x-y))+g y*(f x-f y-df y (x-y))+(f x-f y)*(g x-g y) := by
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]; ring
    rw [he]
    have h1 : |f y*(g x-g y-dg y (x-y))| ≤ C*D*‖x-y‖^2 := by
      rw [abs_mul]
      convert mul_le_mul (hf.value y hy) (hg.remainder x hx y hy) (abs_nonneg _) hf.nonneg using 1 <;> ring
    have h2 : |g y*(f x-f y-df y (x-y))| ≤ C*D*‖x-y‖^2 := by
      rw [abs_mul]
      convert mul_le_mul (hg.value y hy) (hf.remainder x hx y hy) (abs_nonneg _) hg.nonneg using 1 <;> ring
    have h3 : |(f x-f y)*(g x-g y)| ≤ C*D*(1+2*T)^2*‖x-y‖^2 := by
      rw [abs_mul]
      convert mul_le_mul (hf.difference_bound T hT hS x hx y hy) (hg.difference_bound T hT hS x hx y hy)
        (abs_nonneg _) (by positivity) using 1 <;> ring
    exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)).trans (by ring_nf; rfl)
theorem mono (hf : ScalarExpansionControl S f df C) (hCD : C ≤ D) : ScalarExpansionControl S f df D := by
  refine ⟨hf.nonneg.trans hCD,(fun x hx => (hf.value x hx).trans hCD),
    (fun x hx => (hf.first x hx).trans hCD),?_⟩
  intro x hx y hy
  exact (hf.remainder x hx y hy).trans (mul_le_mul_of_nonneg_right hCD (sq_nonneg _))

end ScalarExpansionControl

theorem scalarExpansion_const (S : Set MatchedCoordinate) (a : ℝ) :
    ScalarExpansionControl S (fun _ => a) (fun _ => 0) |a| := by
  refine ⟨abs_nonneg _,(fun _ _ => le_rfl),?_,?_⟩
  · intro x hx; simp <;> positivity
  · intro x hx y hy; simp <;> positivity

theorem scalarExpansion_proj (S : Set MatchedCoordinate) (T : ℝ) (hT : 0 ≤ T)
    (hS : ∀ x ∈ S, ‖x‖ ≤ T) (i : Fin 5) :
    ScalarExpansionControl S (fun x => x i) (fun _ => ContinuousLinearMap.proj i) (T+1) := by
  refine ⟨by positivity,?_,?_,?_⟩
  · intro x hx
    have hc : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    exact hc.trans ((hS x hx).trans (by linarith))
  · intro x hx
    have hp : ‖(ContinuousLinearMap.proj i : MatchedCoordinate →L[ℝ] ℝ)‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro y
      simpa using norm_le_pi_norm y i
    exact hp.trans (by linarith)
  · intro x hx y hy
    simp only [ContinuousLinearMap.proj_apply,Pi.sub_apply,sub_self,abs_zero]
    positivity

/-- A fixed polynomial in the state, normalized coefficient values, and
bounded dimensionless parameters. Its jet is assembled algebraically. -/
inductive MatchedPolynomial where
  | const : ℝ → MatchedPolynomial
  | var : Fin 16 → MatchedPolynomial
  | add : MatchedPolynomial → MatchedPolynomial → MatchedPolynomial
  | mul : MatchedPolynomial → MatchedPolynomial → MatchedPolynomial

namespace MatchedPolynomial
instance : Add MatchedPolynomial := ⟨MatchedPolynomial.add⟩
instance : Mul MatchedPolynomial := ⟨MatchedPolynomial.mul⟩
instance : Neg MatchedPolynomial := ⟨fun P => const (-1)*P⟩
instance : Sub MatchedPolynomial := ⟨fun P Q => P+(-Q)⟩
instance (n : ℕ) : OfNat MatchedPolynomial n := ⟨const n⟩

def eval : MatchedPolynomial → (Fin 16 → ℝ) → ℝ
  | const a,u => a
  | var i,u => u i
  | add P Q,u => P.eval u+Q.eval u
  | mul P Q,u => P.eval u*Q.eval u

@[simp] theorem eval_add (P Q : MatchedPolynomial) (u : Fin 16 → ℝ) :
    (P+Q).eval u = P.eval u+Q.eval u := rfl
@[simp] theorem eval_mul (P Q : MatchedPolynomial) (u : Fin 16 → ℝ) :
    (P*Q).eval u = P.eval u*Q.eval u := rfl
@[simp] theorem eval_neg (P : MatchedPolynomial) (u : Fin 16 → ℝ) :
    (-P).eval u = -P.eval u := by change (-1 : ℝ)*P.eval u = -(P.eval u); ring
@[simp] theorem eval_sub (P Q : MatchedPolynomial) (u : Fin 16 → ℝ) :
    (P-Q).eval u = P.eval u-Q.eval u := by change P.eval u+(-1 : ℝ)*Q.eval u = P.eval u-Q.eval u; ring

def jet : MatchedPolynomial → (Fin 16 → ℝ) → (Fin 16 → MatchedCoordinate →L[ℝ] ℝ) → MatchedCoordinate →L[ℝ] ℝ
  | const _,_,_ => 0
  | var i,_,du => du i
  | add P Q,u,du => P.jet u du+Q.jet u du
  | mul P Q,u,du => (P.eval u) • Q.jet u du+(Q.eval u) • P.jet u du

def bound : MatchedPolynomial → ℝ → ℝ → ℝ
  | const a,_,_ => |a|
  | var _,M,_ => M
  | add P Q,M,T => P.bound M T+Q.bound M T
  | mul P Q,M,T => P.bound M T*Q.bound M T*(2+(1+2*T)^2)

theorem bound_nonneg (P : MatchedPolynomial) (M T : ℝ) (hM : 0 ≤ M) : 0 ≤ P.bound M T := by
  induction P with
  | const a => exact abs_nonneg a
  | var i => exact hM
  | add P Q hP hQ => exact add_nonneg hP hQ
  | mul P Q hP hQ => dsimp [bound]; positivity

theorem control (P : MatchedPolynomial) (S : Set MatchedCoordinate) (M T : ℝ)
    (hT : 0 ≤ T) (hS : ∀ x ∈ S, ‖x‖ ≤ T)
    (u : MatchedCoordinate → Fin 16 → ℝ)
    (du : MatchedCoordinate → Fin 16 → MatchedCoordinate →L[ℝ] ℝ)
    (hu : ∀ i, ScalarExpansionControl S (fun x => u x i) (fun x => du x i) M) :
    ScalarExpansionControl S (fun x => P.eval (u x)) (fun x => P.jet (u x) (du x)) (P.bound M T) := by
  induction P with
  | const a => exact scalarExpansion_const S a
  | var i => exact hu i
  | add P Q hP hQ => exact hP.add hQ
  | mul P Q hP hQ => exact hP.mul hQ T hT hS
end MatchedPolynomial

/-- Dimensionless perturbation after factoring the exact fast map and `eta*p`.
Inputs are theta,Y,R,C,V,A/p,B/p,D0/p,Dtheta/p,beta,eps,z,Phi,eta/B,z/B,r. -/
def matchedPerturbationPolynomial (i : Fin 5) : MatchedPolynomial :=
  let v := MatchedPolynomial.var
  let n := 2*v 12*v 7+v 13*v 2*v 8-v 14*v 2*v 5*v 5
  ![-v 10*(v 5*v 0+v 6*v 15),
    v 5*v 0+v 6*v 15,
    (-2*v 10*v 5+v 11*v 10*v 10*v 5*v 5)*v 2+2*v 9*v 10*v 10*v 5*v 3+v 10*v 10*n,
    v 5*v 2-2*v 9*v 10*v 5*v 3-v 11*v 10*v 5*v 5*v 2-v 10*n,
    v 11*v 5*v 5*v 2+2*v 9*v 5*v 3+n] i

def matchedPerturbationBound (M T : ℝ) : ℝ := ∑ i : Fin 5, (matchedPerturbationPolynomial i).bound M T

def matchedPerturbationJet (u : MatchedCoordinate → Fin 16 → ℝ)
    (du : MatchedCoordinate → Fin 16 → MatchedCoordinate →L[ℝ] ℝ)
    (y : MatchedCoordinate) : MatchedCoordinate →L[ℝ] MatchedCoordinate :=
  ContinuousLinearMap.pi (fun i => (matchedPerturbationPolynomial i).jet (u y) (du y))

theorem matchedPerturbation_controls (S : Set MatchedCoordinate) (M T : ℝ) (hM : 0 ≤ M)
    (hT : 0 ≤ T) (hS : ∀ x ∈ S, ‖x‖ ≤ T)
    (u : MatchedCoordinate → Fin 16 → ℝ)
    (du : MatchedCoordinate → Fin 16 → MatchedCoordinate →L[ℝ] ℝ)
    (hu : ∀ i, ScalarExpansionControl S (fun x => u x i) (fun x => du x i) M) :
    (∀ y ∈ S, ‖matchedPerturbationJet u du y‖ ≤ matchedPerturbationBound M T) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      ‖(fun i => (matchedPerturbationPolynomial i).eval (u x))-
        (fun i => (matchedPerturbationPolynomial i).eval (u y))-matchedPerturbationJet u du y (x-y)‖ ≤
        matchedPerturbationBound M T*‖x-y‖^2) := by
  have hb (i : Fin 5) : 0 ≤ (matchedPerturbationPolynomial i).bound M T :=
    MatchedPolynomial.bound_nonneg _ M T hM
  have htotal : 0 ≤ matchedPerturbationBound M T := Finset.sum_nonneg (fun i _ => hb i)
  have hi (i : Fin 5) : (matchedPerturbationPolynomial i).bound M T ≤ matchedPerturbationBound M T :=
    Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i)
  have hc (i : Fin 5) := MatchedPolynomial.control (matchedPerturbationPolynomial i) S M T hT hS u du hu
  constructor
  · intro y hy
    apply ContinuousLinearMap.opNorm_le_bound _ htotal
    intro x
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg htotal (norm_nonneg x))).mpr
    intro i
    exact ((matchedPerturbationPolynomial i).jet (u y) (du y)).le_opNorm x |>.trans
      (mul_le_mul_of_nonneg_right ((hc i).first y hy |>.trans (hi i)) (norm_nonneg x))
  · intro x hx y hy
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg htotal (sq_nonneg ‖x-y‖))).mpr
    intro i
    have hrem : ‖((fun i => (matchedPerturbationPolynomial i).eval (u x))-
        (fun i => (matchedPerturbationPolynomial i).eval (u y))-matchedPerturbationJet u du y (x-y)) i‖ ≤
        (matchedPerturbationPolynomial i).bound M T*‖x-y‖^2 := by
      simpa [matchedPerturbationJet,Real.norm_eq_abs] using (hc i).remainder x hx y hy
    exact hrem.trans (mul_le_mul_of_nonneg_right (hi i) (sq_nonneg _))
def matchedPerturbationInput {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (y : MatchedCoordinate) : Fin 16 → ℝ :=
  ![y 0,y 1,y 2,y 3,y 4,
    matchedNormalizedScalarState 0 p (r mu) y,matchedNormalizedScalarState 1 p (r mu) y,
    matchedNormalizedScalarState 2 p (r mu) y,matchedNormalizedScalarState 3 p (r mu) y,
    beta,1-beta,eta*(p : ℝ),logisticPhi d B eta,eta/(B : ℝ),eta*(p : ℝ)/(B : ℝ),r mu]

def matchedPerturbationInputJet {d : ℕ} (p : unitInterval) (mu : Vec d)
    (y : MatchedCoordinate) : Fin 16 → MatchedCoordinate →L[ℝ] ℝ :=
  ![ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 1,ContinuousLinearMap.proj 2,
    ContinuousLinearMap.proj 3,ContinuousLinearMap.proj 4,
    matchedNormalizedScalarDerivative 0 p (r mu) y,matchedNormalizedScalarDerivative 1 p (r mu) y,
    matchedNormalizedScalarDerivative 2 p (r mu) y,matchedNormalizedScalarDerivative 3 p (r mu) y,
    0,0,0,0,0,0,0]

def matchedPopulationPerturbation {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (y : MatchedCoordinate) : MatchedCoordinate :=
  fun i => (matchedPerturbationPolynomial i).eval (matchedPerturbationInput (B := B) eta beta p mu y)

def matchedPopulationJacobian {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (y : MatchedCoordinate) : MatchedCoordinate →L[ℝ] MatchedCoordinate :=
  matchedFreeOperator beta+(eta*(p : ℝ)) •
    matchedPerturbationJet (matchedPerturbationInput (B := B) eta beta p mu) (matchedPerturbationInputJet p mu) y

/-- Exact learning-step factorization of the actual matched drift. -/
theorem matchedDriftMap_factorization {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (hp : (p : ℝ) ≠ 0) (y : MatchedCoordinate) :
    matchedDriftMap (B := B) eta beta p mu y = matchedFreeOperator beta y+
      (eta*(p : ℝ)) • matchedPopulationPerturbation (B := B) eta beta p mu y := by
  ext i
  fin_cases i <;>
    simp [matchedDriftMap,matchedCoefficientStep,matchedFreeOperator_apply,matchedPopulationPerturbation,
      matchedPerturbationInput,matchedPerturbationPolynomial,MatchedPolynomial.eval,
      matchedNormalizedScalarState,matchedScalarState,matchedScalarJet,logisticPhi]
    <;> field_simp [hp]
    <;> ring

/-- Polynomial jet control discharges the actual state-map first and second
Taylor estimates. Only actual scalar coefficient controls are used. -/
theorem matchedPopulationJacobian_control_from_inputs {d B : ℕ}
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (T M : ℝ)
    (heta : 0 ≤ eta) (hp : 0 ≤ (p : ℝ)) (hpne : (p : ℝ) ≠ 0)
    (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hu : ∀ i, ScalarExpansionControl {y : MatchedCoordinate | matchedPhysical y ∧ ‖y‖ ≤ T}
      (fun y => matchedPerturbationInput (B := B) eta beta p mu y i)
      (fun y => matchedPerturbationInputJet p mu y i) M) :
    (∀ y : MatchedCoordinate, matchedPhysical y → ‖y‖ ≤ T →
      ‖matchedPopulationJacobian (B := B) eta beta p mu y-matchedFreeOperator beta‖ ≤
        matchedPerturbationBound M T*(eta*(p : ℝ))) ∧
    (∀ x y : MatchedCoordinate, matchedPhysical x → matchedPhysical y → ‖x‖ ≤ T → ‖y‖ ≤ T →
      ‖matchedDriftMap (B := B) eta beta p mu x-matchedDriftMap (B := B) eta beta p mu y-
        matchedPopulationJacobian (B := B) eta beta p mu y (x-y)‖ ≤
        matchedPerturbationBound M T*(eta*(p : ℝ))*‖x-y‖^2) := by
  have hh := matchedPerturbation_controls {y : MatchedCoordinate | matchedPhysical y ∧ ‖y‖ ≤ T}
    M T hM hT (fun y hy => hy.2) (matchedPerturbationInput (B := B) eta beta p mu) (matchedPerturbationInputJet p mu) hu
  have hz : 0 ≤ eta*(p : ℝ) := mul_nonneg heta hp
  constructor
  · intro y hy hyn
    dsimp [matchedPopulationJacobian]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hz]
    convert mul_le_mul_of_nonneg_left (hh.1 y ⟨hy,hyn⟩) hz using 1 <;> ring
  · intro x y hx hy hxn hyn
    rw [matchedDriftMap_factorization eta beta p mu hpne x,matchedDriftMap_factorization eta beta p mu hpne y]
    have he : matchedFreeOperator beta x+(eta*(p : ℝ)) • matchedPopulationPerturbation (B := B) eta beta p mu x-
        (matchedFreeOperator beta y+(eta*(p : ℝ)) • matchedPopulationPerturbation (B := B) eta beta p mu y)-
        matchedPopulationJacobian (B := B) eta beta p mu y (x-y) =
        (eta*(p : ℝ)) • (matchedPopulationPerturbation (B := B) eta beta p mu x-
          matchedPopulationPerturbation (B := B) eta beta p mu y-
          matchedPerturbationJet (matchedPerturbationInput (B := B) eta beta p mu) (matchedPerturbationInputJet p mu) y (x-y)) := by
      simp only [matchedPopulationJacobian,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,map_sub]
      module
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hz]
    have hrem := hh.2 x ⟨hx,hxn⟩ y ⟨hy,hyn⟩
    change ‖matchedPopulationPerturbation (B := B) eta beta p mu x-
      matchedPopulationPerturbation (B := B) eta beta p mu y-
      matchedPerturbationJet (matchedPerturbationInput (B := B) eta beta p mu) (matchedPerturbationInputJet p mu) y (x-y)‖ ≤
      matchedPerturbationBound M T*‖x-y‖^2 at hrem
    calc
      _ ≤ (eta*(p : ℝ))*(matchedPerturbationBound M T*‖x-y‖^2) := mul_le_mul_of_nonneg_left hrem hz
      _ = _ := by ring
def matchedDimensionlessParameters {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d) : Fin 7 → ℝ :=
  ![beta,1-beta,eta*(p : ℝ),logisticPhi d B eta,eta/(B : ℝ),eta*(p : ℝ)/(B : ℝ),r mu]

private theorem matchedPerturbationInput_controls {d B : ℕ}
    (eta beta : ℝ) (p : unitInterval) (mu : Vec d) (T P C : ℝ)
    (hT : 0 ≤ T) (hP : 0 ≤ P) (hC : 0 ≤ C) (hp : 0 < (p : ℝ)) (hpHalf : (p : ℝ) ≤ 1/2)
    (hpar : ‖matchedDimensionlessParameters (B := B) eta beta p mu‖ ≤ P)
    (hcoef : ∀ i : Fin 4, ScalarExpansionControl {y : MatchedCoordinate | matchedPhysical y ∧ ‖y‖ ≤ T}
      (matchedNormalizedScalarState i p (r mu)) (matchedNormalizedScalarDerivative i p (r mu)) C) :
    ∀ i, ScalarExpansionControl {y : MatchedCoordinate | matchedPhysical y ∧ ‖y‖ ≤ T}
      (fun y => matchedPerturbationInput (B := B) eta beta p mu y i)
      (fun y => matchedPerturbationInputJet p mu y i) (T+C+P+1) := by
  let U : Set MatchedCoordinate := {y | matchedPhysical y ∧ ‖y‖ ≤ T}
  have hcoord (i : Fin 5) := (scalarExpansion_proj U T hT (fun y hy => hy.2) i).mono
    (show T+1 ≤ T+C+P+1 by linarith)
  have hcoeff (i : Fin 4) := (hcoef i).mono (show C ≤ T+C+P+1 by linarith)
  have hconstant (i : Fin 7) : ScalarExpansionControl U (fun _ => matchedDimensionlessParameters (B := B) eta beta p mu i)
      (fun _ => 0) (T+C+P+1) := by
    have hi : |matchedDimensionlessParameters (B := B) eta beta p mu i| ≤ P := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm _ i).trans hpar
    exact (scalarExpansion_const U _).mono (hi.trans (by linarith))
  intro i
  fin_cases i
  all_goals first
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,U] using hcoord 0
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,U] using hcoord 1
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,U] using hcoord 2
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,U] using hcoord 3
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,U] using hcoord 4
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,U] using hcoeff 0
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,U] using hcoeff 1
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,U] using hcoeff 2
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,U] using hcoeff 3
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,matchedDimensionlessParameters,U] using hconstant 0
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,matchedDimensionlessParameters,U] using hconstant 1
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,matchedDimensionlessParameters,U] using hconstant 2
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,matchedDimensionlessParameters,U] using hconstant 3
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,matchedDimensionlessParameters,U] using hconstant 4
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,matchedDimensionlessParameters,U] using hconstant 5
    | simpa [matchedPerturbationInput,matchedPerturbationInputJet,matchedDimensionlessParameters,U] using hconstant 6

/-- Dimension-uniform actual matched-map first-jet and quadratic-remainder
bounds on bounded physical states and bounded dimensionless parameters.
The constant depends only on the fixed teacher norm and these bounds. -/
theorem matchedPopulationJacobian_uniform_controls
    (S : SparseSGD.External.GaussianSteinCertificate 1) (teacherNorm T P : ℝ) (hT : 0 ≤ T) (hP : 0 ≤ P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d),
      r mu=teacherNorm → 0 ≤ eta → 0 < (p : ℝ) → (p : ℝ) ≤ 1/2 →
      ‖matchedDimensionlessParameters (B := B) eta beta p mu‖ ≤ P →
      (∀ y : MatchedCoordinate, matchedPhysical y → ‖y‖ ≤ T →
        ‖matchedPopulationJacobian (B := B) eta beta p mu y-matchedFreeOperator beta‖ ≤ C*(eta*(p : ℝ))) ∧
      (∀ x y : MatchedCoordinate, matchedPhysical x → matchedPhysical y → ‖x‖ ≤ T → ‖y‖ ≤ T →
        ‖matchedDriftMap (B := B) eta beta p mu x-matchedDriftMap (B := B) eta beta p mu y-
          matchedPopulationJacobian (B := B) eta beta p mu y (x-y)‖ ≤ C*(eta*(p : ℝ))*‖x-y‖^2) := by
  obtain ⟨Cc,hCc,hc⟩ := matchedNormalizedScalar_controls S teacherNorm T hT
  let M := T+Cc+P+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbound : 0 ≤ matchedPerturbationBound M T :=
    Finset.sum_nonneg (fun i _ => MatchedPolynomial.bound_nonneg _ M T hM)
  refine ⟨matchedPerturbationBound M T,hbound,?_⟩
  intro d B eta beta p mu hr heta hp hpHalf hpar
  have hcoef (i : Fin 4) : ScalarExpansionControl {y : MatchedCoordinate | matchedPhysical y ∧ ‖y‖ ≤ T}
      (matchedNormalizedScalarState i p (r mu)) (matchedNormalizedScalarDerivative i p (r mu)) Cc := by
    rw [hr]
    refine ⟨hCc,?_,?_,?_⟩
    · intro x hx
      exact (hc i p x x hp hpHalf hx.1 hx.1 hx.2 hx.2).1
    · intro x hx
      exact (hc i p x x hp hpHalf hx.1 hx.1 hx.2 hx.2).2.1
    · intro x hx y hy
      exact (hc i p y x hp hpHalf hy.1 hx.1 hy.2 hx.2).2.2
  exact matchedPopulationJacobian_control_from_inputs eta beta p mu T M heta hp.le (ne_of_gt hp) hT hM
    (matchedPerturbationInput_controls eta beta p mu T P Cc hT hP hCc hp hpHalf hpar hcoef)
/-- Actual finite-batch parameters are uniformly bounded under a bounded
load and effective learning step. This uses the actual Phi identity. -/
theorem matchedDimensionlessParameters_norm_le {d B : ℕ} (eta beta : ℝ) (p : unitInterval) (mu : Vec d)
    (Load : ℝ) (hd : 2 ≤ d) (hB : 0 < B) (heta : 0 ≤ eta)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) (hz : eta*(p : ℝ) ≤ 1)
    (hLoad : logisticPhi d B eta ≤ Load) :
    ‖matchedDimensionlessParameters (B := B) eta beta p mu‖ ≤ r mu+2*Load+2 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hdminus : 0 ≤ (d : ℝ)-1 := by linarith
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hbOne : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hp : 0 ≤ (p : ℝ) := p.property.1
  have hphi : 0 ≤ logisticPhi d B eta := by dsimp [logisticPhi]; positivity
  have hLoad0 : 0 ≤ Load := hphi.trans hLoad
  have hr : 0 ≤ r mu := norm_nonneg mu
  have hw : eta/(B : ℝ) ≤ 2*Load := by
    apply (eta_div_batch_le_phi eta hd hB heta).trans
    apply le_trans _ (mul_le_mul_of_nonneg_left hLoad (by norm_num : (0 : ℝ) ≤ 2))
    apply (div_le_iff₀ hdpos).2
    nlinarith [mul_nonneg hphi (show 0 ≤ (d : ℝ)-2 by linarith)]
  have hnu : eta*(p : ℝ)/(B : ℝ) ≤ 1 := (div_le_one hb).2 (hz.trans hbOne)
  have hP : 0 ≤ r mu+2*Load+2 := by positivity
  apply (pi_norm_le_iff_of_nonneg hP).mpr
  intro i
  fin_cases i <;> simp [matchedDimensionlessParameters,Real.norm_eq_abs]
  · rw [abs_of_nonneg hb0]; linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hb1)]; linarith
  · rw [abs_of_nonneg heta,abs_of_nonneg hp]; linarith
  · rw [abs_of_nonneg hphi]; linarith
  · rw [abs_of_nonneg heta]; linarith
  · rw [abs_of_nonneg heta,abs_of_nonneg hp]; linarith
  · rw [abs_of_nonneg hr]; linarith
end
end SparseSGD.Logistic




