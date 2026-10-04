import SparseSGD.Scaling.SmallDeltaExponential
import SparseSGD.Discrete.RenewalBounds

namespace SparseSGD.Scaling
noncomputable section
set_option maxHeartbeats 1000000

def learningProfile (u phi R t : ℝ) : ℝ :=
  phi/(1-u)+(R-phi/(1-u))*Real.exp (-2*(1-u)*t)

def geometricResponse (q u phi R : ℝ) (k : ℕ) : ℝ :=
  phi/(1-u)+(R-phi/(1-u))*(q+(1-q)*u)^k

theorem geometricResponse_zero (q u phi R : ℝ) : geometricResponse q u phi R 0=R := by
  simp [geometricResponse]

theorem geometricResponse_step (q u phi R : ℝ) (hu : u ≠ 1) (k : ℕ) :
    geometricResponse q u phi R (k+1)=q*geometricResponse q u phi R k+
      (1-q)*(u*geometricResponse q u phi R k+phi) := by
  dsimp [geometricResponse]
  rw [pow_succ]
  have h : 1-u ≠ 0 := by exact sub_ne_zero.mpr (Ne.symm hu)
  field_simp
  <;> ring

theorem geometricResponse_renewal (q u phi R : ℝ) (hu : u ≠ 1) (k : ℕ) :
    geometricResponse q u phi R k=R*q^k+
      ∑ j ∈ Finset.range k, geomLag q (k-j)*(u*geometricResponse q u phi R j+phi) := by
  induction k with
  | zero => simp [geometricResponse_zero]
  | succ k ih =>
    have H : (∑ j ∈ Finset.range k, geomLag q (k+1-j)*(u*geometricResponse q u phi R j+phi))=
        q*(∑ j ∈ Finset.range k, geomLag q (k-j)*(u*geometricResponse q u phi R j+phi)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk := Finset.mem_range.mp hj
      have hstep : geomLag q (k+1-j)=q*geomLag q (k-j) := by
        have hjpos : 0 < k-j := by omega
        obtain ⟨l,hl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
        rw [show k+1-j=(k-j)+1 by omega,hl]
        simp only [geomLag,pow_succ]
        ring
      rw [hstep]
      ring
    rw [geometricResponse_step q u phi R hu k,Finset.sum_range_succ,H]
    simp only [Nat.add_sub_cancel_left,show geomLag q 1=1-q by simp [geomLag],pow_succ]
    rw [ih]
    ring

theorem geometricResponse_bounds (q u phi R : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hp : 0 ≤ phi) (hR : 0 ≤ R) (k : ℕ) :
    0 ≤ geometricResponse q u phi R k ∧ geometricResponse q u phi R k ≤ R+phi/(1-u) := by
  have hs : 0 ≤ q+(1-q)*u := by positivity
  have hs1 : q+(1-q)*u ≤ 1 := by nlinarith [mul_nonneg (by linarith : 0≤1-q) (by linarith : 0≤1-u)]
  have hpow0 := pow_nonneg hs k
  have hpow1 := pow_le_one₀ hs hs1 (n:=k)
  have hL : 0 ≤ phi/(1-u) := by positivity
  have hid : geometricResponse q u phi R k=R*(q+(1-q)*u)^k+
      (phi/(1-u))*(1-(q+(1-q)*u)^k) := by dsimp [geometricResponse]; ring
  rw [hid]
  constructor
  · positivity
  · nlinarith [mul_nonneg hR (sub_nonneg.mpr hpow1),mul_nonneg hL hpow0]

theorem geometric_learning_power_bound (u z : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hz0 : 0 < z) (hz1 : z ≤ 1/8) (k : ℕ) :
    |(Real.exp (-2*z)+(1-Real.exp (-2*z))*u)^k-(Real.exp (-2*(1-u)*z))^k| ≤ 8*z := by
  let s := 1-u
  let rho := Real.exp (-2*z)
  let q := rho+(1-rho)*u
  let e := Real.exp (-2*s*z)
  have hs : 0 < s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hr0 : 0 < rho := Real.exp_pos _
  have hr1 : rho < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q]; nlinarith
  have hrErr := exp_neg_linear_remainder (2*z) (by positivity)
  have heErr := exp_neg_linear_remainder (2*s*z) (by positivity)
  have hrrem : 0 ≤ rho-(1-2*z) ∧ rho-(1-2*z) ≤ 4*z^2 := by
    have H := Real.add_one_le_exp (-2*z)
    change -2*z+1 ≤ rho at H
    have H2 := (abs_le.mp hrErr).2
    have H2' : rho-(1-2*z) ≤ (2*z)^2 := by simpa only [rho,neg_mul] using H2
    constructor <;> nlinarith
  have herem : 0 ≤ e-(1-2*s*z) ∧ e-(1-2*s*z) ≤ 4*s*z^2 := by
    have H := Real.add_one_le_exp (-2*s*z)
    change -2*s*z+1 ≤ e at H
    have H2 := (abs_le.mp heErr).2
    have H2' : e-(1-2*s*z) ≤ (2*s*z)^2 := by simpa only [e,neg_mul] using H2
    have H3 : s^2*z^2 ≤ s*z^2 := by nlinarith [mul_nonneg (sq_nonneg z) (show (0 : ℝ) ≤ s-s^2 from by nlinarith)]
    constructor <;> nlinarith
  have hqrem : 0 ≤ q-(1-2*s*z) ∧ q-(1-2*s*z) ≤ 4*s*z^2 := by
    have hid : q-(1-2*s*z)=s*(rho-(1-2*z)) := by dsimp [q,s]; ring
    rw [hid]
    constructor
    · exact mul_nonneg hs.le hrrem.1
    · nlinarith [mul_le_mul_of_nonneg_left hrrem.2 hs.le]
  have herr : |q-e| ≤ 8*s*z^2 := by rw [abs_le]; constructor <;> linarith [herem.1,herem.2,hqrem.1,hqrem.2]
  have hzsq : z^2 ≤ z/8 := by nlinarith
  have hgq : s*z ≤ 1-q := by
    have H := mul_le_mul_of_nonneg_left hzsq hs.le
    nlinarith [hqrem.2]
  have hge : s*z ≤ 1-e := by
    have H := mul_le_mul_of_nonneg_left hzsq hs.le
    nlinarith [herem.2]
  have hg : s*z ≤ 1-max q e := by
    have H : max q e ≤ 1-s*z := max_le (by linarith) (by linarith)
    linarith
  have hden : 0 < 1-max q e := by nlinarith
  have H := pow_sub_le_of_unit_interval q e hq0 he0.le hq1 he1 k
  refine H.trans ?_
  rw [div_le_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_left hg (show 0≤8*z by positivity)]

theorem learningProfile_initial (u phi R : ℝ) : learningProfile u phi R 0=R := by simp [learningProfile]

theorem learningProfile_hasDerivAt (u phi R t : ℝ) (hu : u ≠ 1) :
    HasDerivAt (learningProfile u phi R) (-2*(1-u)*learningProfile u phi R t+2*phi) t := by
  have H := ((((hasDerivAt_id t).const_mul (-2*(1-u))).exp).const_mul
    (R-phi/(1-u))).const_add (phi/(1-u))
  convert H using 1
  · rfl
  · dsimp [learningProfile]
    have h : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    field_simp
    <;> ring

theorem geometricResponse_learningProfile_error (u phi R z : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hp : 0 ≤ phi) (hR : 0 ≤ R)
    (hz0 : 0 < z) (hz1 : z ≤ 1/8) (k : ℕ) :
    |geometricResponse (Real.exp (-2*z)) u phi R k-learningProfile u phi R ((k : ℝ)*z)| ≤
      8*z*(R+phi/(1-u)) := by
  have H := geometric_learning_power_bound u z hu0 hu1 hz0 hz1 k
  have hpow : (Real.exp (-2*(1-u)*z))^k=Real.exp (-2*(1-u)*((k : ℝ)*z)) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  have hid : geometricResponse (Real.exp (-2*z)) u phi R k-learningProfile u phi R ((k : ℝ)*z)=
      (R-phi/(1-u))*((Real.exp (-2*z)+(1-Real.exp (-2*z))*u)^k-(Real.exp (-2*(1-u)*z))^k) := by
    rw [hpow]
    dsimp [geometricResponse,learningProfile]
    ring
  have hL : 0 ≤ phi/(1-u) := by positivity
  have hRL : |R-phi/(1-u)| ≤ R+phi/(1-u) := abs_le.mpr ⟨by linarith,by linarith⟩
  rw [hid,abs_mul]
  have Hb := mul_le_mul hRL H (abs_nonneg _) (by positivity : 0≤R+phi/(1-u))
  nlinarith only [Hb]

end
end SparseSGD.Scaling
