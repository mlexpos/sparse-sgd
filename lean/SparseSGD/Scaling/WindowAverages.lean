import SparseSGD.Scaling.WindowChain
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric

namespace SparseSGD
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1500000

/-- Radial damping cannot reduce a unit-circle chord by more than a factor two. -/
theorem window_geometric_denominator (r theta : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ Real.pi/2) :
    theta/2 ≤ ‖1-(r : ℂ)*Complex.exp (Complex.I*(2*theta : ℝ))‖ := by
  let z := Complex.exp (Complex.I*(2*theta : ℝ))
  have hz : ‖z‖ = 1 := by simp [z,Complex.norm_exp]
  have hq : ‖(r : ℂ)*z‖ = r := by rw [norm_mul,hz,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0,mul_one]
  have hr : 1-r ≤ ‖1-(r : ℂ)*z‖ := by
    simpa only [norm_one,hq] using norm_sub_norm_le (1 : ℂ) ((r : ℂ)*z)
  have hdiff : ‖(r : ℂ)*z-z‖ = 1-r := by
    rw [show (r : ℂ)*z-z = ((r : ℂ)-1)*z by ring,norm_mul,hz,mul_one,← Complex.ofReal_one,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
    ring
  have htri := norm_sub_le_norm_sub_add_norm_sub (1 : ℂ) ((r : ℂ)*z) z
  rw [hdiff] at htri
  have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos])
  have hchord : ‖1-z‖ = 2*Real.sin theta := by
    rw [norm_sub_rev]
    dsimp only [z]
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    simp [Real.norm_eq_abs,abs_of_nonneg hsin0]
  rw [hchord] at htri
  have hsin := Real.mul_le_sin ht0 ht1
  have hpi : theta/2 ≤ 2/Real.pi*theta := by
    have h4 : Real.pi ≤ 4 := Real.pi_lt_four.le
    have hh : (1 : ℝ)/2 ≤ 2/Real.pi := by
      apply (le_div_iff₀ Real.pi_pos).2
      linarith
    nlinarith
  change theta/2 ≤ ‖1-(r : ℂ)*z‖
  linarith

/-- Finite local geometric sums, uniformly in the starting index. -/
theorem window_geometric_sum_bound (q : ℂ) (theta : ℝ)
    (hq : ‖q‖ ≤ 1) (ht : 0 < theta) (hgap : theta/2 ≤ ‖1-q‖) (k N : ℕ) :
    ‖∑ j ∈ Finset.range N, q^(k+j)‖ ≤ 4/theta := by
  have hg : 0 < ‖1-q‖ := by linarith
  have hsum := congrArg norm (geom_sum_mul_neg q N)
  rw [norm_mul] at hsum
  have hnum : ‖1-q^N‖ ≤ 2 := (norm_sub_le _ _).trans (by
    rw [norm_one,norm_pow]
    have H := pow_le_one₀ (n := N) (norm_nonneg q) hq
    linarith)
  have HB : ‖∑ j ∈ Finset.range N, q^j‖ ≤ 4/theta := by
    apply (le_div_iff₀ ht).2
    have H := mul_le_mul_of_nonneg_left hgap (norm_nonneg (∑ j ∈ Finset.range N, q^j))
    nlinarith
  rw [show (∑ j ∈ Finset.range N, q^(k+j)) = q^k*(∑ j ∈ Finset.range N, q^j) by
    simp only [pow_add,Finset.mul_sum]]
  rw [norm_mul,norm_pow]
  calc
    _ ≤ 1*(4/theta) := mul_le_mul (pow_le_one₀ (n := k) (norm_nonneg q) hq) HB (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- Lipschitz control for the actual clean slow profile. -/
theorem windowSlowProfile_increment (delta u phi : ℝ) (s : Moments)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (A : ℝ)
    (hA : |slowEnergy delta s-2*phi/(1-u)| ≤ A)
    (t v : ℝ) (ht : 0 ≤ t) (hv : 0 ≤ v) :
    |windowSlowProfile delta u phi s (t+v)-windowSlowProfile delta u phi s t| ≤ A*v := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  have he : 0 ≤ Real.exp ((u-1)*t) := (Real.exp_pos _).le
  have he1 : Real.exp ((u-1)*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hev : Real.exp ((u-1)*v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hediff : |Real.exp ((u-1)*v)-1| ≤ v := by
    rw [abs_of_nonpos (by linarith)]
    have H := Real.add_one_le_exp ((u-1)*v)
    nlinarith [mul_nonneg hu0 hv]
  have hid : windowSlowProfile delta u phi s (t+v)-windowSlowProfile delta u phi s t =
      (slowEnergy delta s-2*phi/(1-u))*Real.exp ((u-1)*t)*(Real.exp ((u-1)*v)-1) := by
    simp only [windowSlowProfile,mul_add,Real.exp_add]
    ring
  rw [hid,abs_mul,abs_mul,abs_of_nonneg he]
  calc
    _ ≤ A*1*v := by gcongr
    _ = _ := by ring

/-- Summing a two-scale approximation gives the actual finite local average. -/
theorem window_average_transfer (R S : ℕ → ℝ) (Z q : ℂ) (E A h theta : ℝ)
    (hE : ∀ k, |R k-(S k/2+(Z*q^k).re/2)| ≤ E)
    (hslow : ∀ k j, |S (k+j)-S k| ≤ A*((j : ℝ)*h))
    (hA : 0 ≤ A) (hh : 0 ≤ h) (hq : ‖q‖ ≤ 1)
    (ht : 0 < theta) (hgap : theta/2 ≤ ‖1-q‖) (k N : ℕ) (hN : 0 < N) :
    |(∑ j ∈ Finset.range N, R (k+j))/(N : ℝ)-S k/2| ≤
      E+A*(N : ℝ)*h/2+2*‖Z‖/((N : ℝ)*theta) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let e := fun j => R (k+j)-(S (k+j)/2+(Z*q^(k+j)).re/2)
  let d := fun j => S (k+j)-S k
  have he : |∑ j ∈ Finset.range N, e j| ≤ (N : ℝ)*E := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, |e j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range N, E := Finset.sum_le_sum (fun j _ => hE (k+j))
      _ = _ := by simp
  have hd : |∑ j ∈ Finset.range N, d j| ≤ (N : ℝ)*(A*((N : ℝ)*h)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, |d j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range N, A*((N : ℝ)*h) := by
        apply Finset.sum_le_sum
        intro j hj
        apply (hslow k j).trans
        have hle : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Finset.mem_range.mp hj).le
        gcongr
      _ = _ := by simp
  have hz : |(∑ j ∈ Finset.range N, (Z*q^(k+j)).re)| ≤ 4*‖Z‖/theta := by
    rw [← Complex.re_sum,← Finset.mul_sum]
    calc
      _ ≤ ‖Z*(∑ j ∈ Finset.range N, q^(k+j))‖ := Complex.abs_re_le_norm _
      _ ≤ ‖Z‖*(4/theta) := by rw [norm_mul]; gcongr; exact window_geometric_sum_bound q theta hq ht hgap k N
      _ = _ := by ring
  have hid : (∑ j ∈ Finset.range N, R (k+j))/(N : ℝ)-S k/2 =
      (∑ j ∈ Finset.range N, e j)/(N : ℝ)+
      (∑ j ∈ Finset.range N, d j)/(2*(N : ℝ))+
      (∑ j ∈ Finset.range N, (Z*q^(k+j)).re)/(2*(N : ℝ)) := by
    simp only [e,d,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_div]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    field_simp [hNr.ne']
    <;> ring
  rw [hid]
  calc
    _ ≤ |(∑ j ∈ Finset.range N, e j)/(N : ℝ)+(∑ j ∈ Finset.range N, d j)/(2*(N : ℝ))|+
        |(∑ j ∈ Finset.range N, (Z*q^(k+j)).re)/(2*(N : ℝ))| := abs_add_le _ _
    _ ≤ (|(∑ j ∈ Finset.range N, e j)/(N : ℝ)|+|(∑ j ∈ Finset.range N, d j)/(2*(N : ℝ))|)+
        |(∑ j ∈ Finset.range N, (Z*q^(k+j)).re)/(2*(N : ℝ))| := by gcongr; exact abs_add_le _ _
    _ ≤ ((N : ℝ)*E)/(N : ℝ)+((N : ℝ)*(A*((N : ℝ)*h)))/(2*(N : ℝ))+(4*‖Z‖/theta)/(2*(N : ℝ)) := by
      simp only [abs_div,abs_of_nonneg hNr.le,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      gcongr
    _ = _ := by field_simp; ring


theorem windowOscillatoryProfile_power (delta u omega h : ℝ) (s : Moments) (k : ℕ) :
    windowOscillatoryProfile delta u omega s ((k : ℝ)*h) =
      oscillatoryEnergy delta (oscillatoryRoot omega) s*
        (Complex.exp (windowOscillatoryRate u omega*(h : ℂ)))^k := by
  unfold windowOscillatoryProfile
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem window_multiplier_bounds (u omega h theta : ℝ) (hu : 0 ≤ u) (hh : 0 ≤ h)
    (ht : 0 ≤ theta) (ht1 : theta ≤ Real.pi/2) (hangle : omega*h = theta) :
    ‖Complex.exp (windowOscillatoryRate u omega*(h : ℂ))‖ ≤ 1 ∧
    theta/2 ≤ ‖1-Complex.exp (windowOscillatoryRate u omega*(h : ℂ))‖ := by
  have hid : windowOscillatoryRate u omega*(h : ℂ) =
      ((-(1+u/2)*h : ℝ) : ℂ)+Complex.I*(2*theta : ℝ) := by
    have H : (omega : ℂ)*(h : ℂ) = (theta : ℂ) := by exact_mod_cast hangle
    unfold windowOscillatoryRate
    push_cast
    rw [← H]
    ring
  rw [hid,Complex.exp_add,← Complex.ofReal_exp]
  have hr0 : 0 ≤ Real.exp (-(1+u/2)*h) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(1+u/2)*h) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  constructor
  · simpa [norm_mul,Complex.norm_exp,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0] using hr1
  · exact window_geometric_denominator _ _ hr0 hr1 ht ht1

theorem windowSlowProfile_initial (delta u phi : ℝ) (s : Moments) :
    windowSlowProfile delta u phi s 0 = slowEnergy delta s := by simp [windowSlowProfile]

theorem windowSlowProfile_derivative (delta u phi : ℝ) (s : Moments) (hu : u ≠ 1) (t : ℝ) :
    HasDerivAt (windowSlowProfile delta u phi s)
      (-(1-u)*windowSlowProfile delta u phi s t+2*phi) t := by
  have H := ((((hasDerivAt_id t).const_mul (u-1)).exp).const_mul
    (slowEnergy delta s-2*phi/(1-u))).const_add (2*phi/(1-u))
  convert H using 1
  · rfl
  · dsimp [windowSlowProfile]
    field_simp
    <;> ring

end
end SparseSGD
