import Mathlib

namespace SparseSGD

noncomputable section

/-- The correction factor for sampling an exponential mode. -/
def m (y : ℂ) : ℂ := if y = 0 then 1 else y / (Complex.exp y - 1)

@[simp] theorem m_zero : m 0 = 1 := by simp [m]

/-- Finite geometric identity, including the resonant case `q = 1`. -/
theorem one_sub_mul_sum_geometric (q : ℂ) (k : ℕ) :
    (1 - q) * (∑ n ∈ Finset.range k, q ^ (n + 1)) = q * (1 - q ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        (1 - q) * (∑ n ∈ Finset.range k, q ^ (n + 1) + q ^ (k + 1))
            = (1 - q) * (∑ n ∈ Finset.range k, q ^ (n + 1)) +
                (1 - q) * q ^ (k + 1) := by ring
        _ = q * (1 - q ^ k) + (1 - q) * q ^ (k + 1) := by rw [ih]
        _ = q * (1 - q ^ (k + 1)) := by rw [pow_succ]; ring

def sampledPairSum (mu lambda ebar : ℂ) (k : ℕ) : ℂ :=
  ∑ n ∈ Finset.range k,
    ebar * Complex.exp (mu * ((n + 1 : ℕ) : ℂ) * ebar) *
      Complex.exp (lambda * ((k - n - 1 : ℕ) : ℂ) * ebar)

/-- Exact finite exponential-pair sampling identity in geometric form. -/
theorem sampled_pair_sum_geometric (mu lambda ebar : ℂ) (k : ℕ) :
    sampledPairSum mu lambda ebar k =
      ebar * Complex.exp (lambda * (k : ℂ) * ebar) *
        (∑ n ∈ Finset.range k,
          Complex.exp ((mu - lambda) * ebar) ^ (n + 1)) := by
  unfold sampledPairSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnlt : n < k := Finset.mem_range.mp hn
  have hnat : (n + 1) + (k - n - 1) = k := by omega
  rw [← Complex.exp_nat_mul]
  simp only [Nat.cast_add, Nat.cast_one]
  have hcast : (n : ℂ) + 1 + ((k - n - 1 : ℕ) : ℂ) = (k : ℂ) := by
    exact_mod_cast hnat
  simp only [mul_assoc]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  linear_combination lambda * ebar * hcast

/-- The resonant (`q = 1`) specialization of the sampled identity. -/
theorem sampled_pair_sum_q_one (mu lambda ebar : ℂ) (k : ℕ)
    (hq : Complex.exp ((mu - lambda) * ebar) = 1) :
    sampledPairSum mu lambda ebar k =
      ebar * Complex.exp (lambda * (k : ℂ) * ebar) * (k : ℂ) := by
  rw [sampled_pair_sum_geometric]
  simp only [hq, one_pow]
  simp

/-- A denominator-free identity, valid even at sampling resonances. -/
theorem sampled_pair_sum_mul_denominator (mu lambda ebar : ℂ) (k : ℕ) :
    (Complex.exp ((lambda - mu) * ebar) - 1) * sampledPairSum mu lambda ebar k =
      ebar * (Complex.exp (lambda * (k : ℂ) * ebar) -
        Complex.exp (mu * (k : ℂ) * ebar)) := by
  let E := Complex.exp ((lambda - mu) * ebar)
  let q := Complex.exp ((mu - lambda) * ebar)
  let L := Complex.exp (lambda * (k : ℂ) * ebar)
  have hEq : E * q = 1 := by
    dsimp [E, q]
    rw [← Complex.exp_add]
    have hzero : (lambda - mu) * ebar + (mu - lambda) * ebar = 0 := by ring
    rw [hzero, Complex.exp_zero]
  have hden : E - 1 = E * (1 - q) := by rw [mul_sub, hEq, mul_one]
  have hlast : L * q ^ k = Complex.exp (mu * (k : ℂ) * ebar) := by
    dsimp [L, q]
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    ring
  rw [sampled_pair_sum_geometric]
  change (E - 1) * (ebar * L * ∑ n ∈ Finset.range k, q ^ (n + 1)) = _
  rw [hden]
  calc
    E * (1 - q) * (ebar * L * ∑ n ∈ Finset.range k, q ^ (n + 1)) =
        ebar * L * E * ((1 - q) * ∑ n ∈ Finset.range k, q ^ (n + 1)) := by ring
    _ = ebar * L * E * (q * (1 - q ^ k)) := by
      rw [one_sub_mul_sum_geometric]
    _ = ebar * (L - L * q ^ k) := by
      calc
        _ = ebar * (L - L * q ^ k) * (E * q) := by ring
        _ = _ := by rw [hEq, mul_one]
    _ = _ := by rw [hlast]

/-- Closed form away from the nonzero aliasing poles. -/
theorem sampled_pair_sum_closed (mu lambda ebar : ℂ) (k : ℕ)
    (hpole : Complex.exp ((lambda - mu) * ebar) ≠ 1) :
    sampledPairSum mu lambda ebar k =
      ebar * (Complex.exp (lambda * (k : ℂ) * ebar) -
        Complex.exp (mu * (k : ℂ) * ebar)) /
          (Complex.exp ((lambda - mu) * ebar) - 1) := by
  apply (eq_div_iff (sub_ne_zero.mpr hpole)).mpr
  simpa [mul_comm] using sampled_pair_sum_mul_denominator mu lambda ebar k

/-- The continuous convolution of two exponential modes. -/
def pairIntegral (mu lambda : ℂ) (T : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..T, Complex.exp (mu * (t : ℂ)) *
    Complex.exp (lambda * ((T - t : ℝ) : ℂ))

theorem pair_integral_closed (mu lambda : ℂ) (T : ℝ) (hne : mu ≠ lambda) :
    pairIntegral mu lambda T =
      (Complex.exp (lambda * (T : ℂ)) - Complex.exp (mu * (T : ℂ))) /
        (lambda - mu) := by
  have hf : (fun t : ℝ => Complex.exp (mu * (t : ℂ)) *
      Complex.exp (lambda * ((T - t : ℝ) : ℂ))) =
      (fun t : ℝ => Complex.exp (lambda * (T : ℂ)) *
        Complex.exp ((mu - lambda) * (t : ℂ))) := by
    funext t
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold pairIntegral
  rw [hf, intervalIntegral.integral_const_mul,
    integral_exp_mul_complex (sub_ne_zero.mpr hne)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hprod : Complex.exp (lambda * (T : ℂ)) *
      Complex.exp ((mu - lambda) * (T : ℂ)) = Complex.exp (mu * (T : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hdiff : lambda - mu ≠ 0 := sub_ne_zero.mpr hne.symm
  have hdiff' : mu - lambda ≠ 0 := sub_ne_zero.mpr hne
  field_simp
  simp only [mul_comm (T : ℂ)] at hprod ⊢
  linear_combination (lambda - mu) * hprod

theorem pair_integral_equal (mu : ℂ) (T : ℝ) :
    pairIntegral mu mu T = (T : ℂ) * Complex.exp (mu * (T : ℂ)) := by
  have hf : (fun t : ℝ => Complex.exp (mu * (t : ℂ)) *
      Complex.exp (mu * ((T - t : ℝ) : ℂ))) =
      (fun _ : ℝ => Complex.exp (mu * (T : ℂ))) := by
    funext t
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold pairIntegral
  rw [hf, intervalIntegral.integral_const]
  simp

/-- Exact exponential-pair quadrature, including coincident exponents.
The hypothesis excludes nonzero aliasing poles; a zero step size is also allowed. -/
theorem sampled_pair_sum_quadrature (mu lambda : ℂ) (ebar : ℝ) (k : ℕ)
    (hpole : (lambda - mu) * (ebar : ℂ) = 0 ∨
      Complex.exp ((lambda - mu) * (ebar : ℂ)) ≠ 1) :
    sampledPairSum mu lambda (ebar : ℂ) k =
      m ((lambda - mu) * (ebar : ℂ)) * pairIntegral mu lambda ((k : ℝ) * ebar) := by
  by_cases heq : mu = lambda
  · subst lambda
    rw [sampled_pair_sum_q_one mu mu (ebar : ℂ) k (by simp), pair_integral_equal]
    simp only [sub_self, zero_mul, m_zero, one_mul, Complex.ofReal_mul,
      Complex.ofReal_natCast]
    simp only [mul_assoc]
    ring
  by_cases he : ebar = 0
  · subst ebar
    simp [sampledPairSum, pairIntegral]
  have hy : (lambda - mu) * (ebar : ℂ) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm heq)) (Complex.ofReal_ne_zero.mpr he)
  have hnonpole : Complex.exp ((lambda - mu) * (ebar : ℂ)) ≠ 1 :=
    hpole.resolve_left hy
  rw [sampled_pair_sum_closed mu lambda (ebar : ℂ) k hnonpole,
    pair_integral_closed mu lambda ((k : ℝ) * ebar) heq]
  simp only [m, hy, ite_false, Complex.ofReal_mul, Complex.ofReal_natCast]
  have hdiff : lambda - mu ≠ 0 := sub_ne_zero.mpr (Ne.symm heq)
  have hden : Complex.exp ((lambda - mu) * (ebar : ℂ)) - 1 ≠ 0 :=
    sub_ne_zero.mpr hnonpole
  field_simp

/-- The convergent infinite right-endpoint exponential sum. -/
theorem hasSum_sampled_exp (mu : ℂ) (ebar : ℝ)
    (hmu : mu.re < 0) (hebar : 0 < ebar) :
    HasSum (fun n : ℕ => (ebar : ℂ) *
      Complex.exp (mu * ((n + 1 : ℕ) : ℂ) * (ebar : ℂ)))
      (m (-mu * (ebar : ℂ)) / (-mu)) := by
  let q := Complex.exp (mu * (ebar : ℂ))
  have hnorm : ‖q‖ < 1 := by
    dsimp [q]
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    simpa using mul_neg_of_neg_of_pos hmu hebar
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hq1 : q ≠ 1 := by
    intro h
    rw [h, norm_one] at hnorm
    exact (lt_irrefl 1) hnorm
  have hmu0 : mu ≠ 0 := by
    intro h
    simp [h] at hmu
  have he0 : (ebar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hebar.ne'
  have hy : -mu * (ebar : ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hmu0) he0
  have hE : Complex.exp (-mu * (ebar : ℂ)) = q⁻¹ := by
    dsimp [q]
    rw [← Complex.exp_neg]
    congr 1
    ring
  have hfun : (fun n : ℕ => (ebar : ℂ) *
      Complex.exp (mu * ((n + 1 : ℕ) : ℂ) * (ebar : ℂ))) =
      (fun n : ℕ => ((ebar : ℂ) * q) * q ^ n) := by
    funext n
    dsimp [q]
    rw [← Complex.exp_nat_mul]
    simp only [Nat.cast_add, Nat.cast_one, mul_assoc]
    rw [← Complex.exp_add]
    congr 1
    congr 1
    ring
  rw [hfun]
  have hsum := (hasSum_geometric_of_norm_lt_one hnorm).mul_left ((ebar : ℂ) * q)
  convert hsum using 1
  simp only [m, hy, ite_false, hE]
  have hden : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  field_simp

theorem tsum_sampled_exp (mu : ℂ) (ebar : ℝ)
    (hmu : mu.re < 0) (hebar : 0 < ebar) :
    (∑' n : ℕ, (ebar : ℂ) *
      Complex.exp (mu * ((n + 1 : ℕ) : ℂ) * (ebar : ℂ))) =
      m (-mu * (ebar : ℂ)) / (-mu) :=
  (hasSum_sampled_exp mu ebar hmu hebar).tsum_eq

end
end SparseSGD
