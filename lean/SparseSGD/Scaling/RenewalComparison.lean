import SparseSGD.Discrete.RenewalBounds

namespace SparseSGD
noncomputable section

/-- Reversed finite lag sums are bounded by the total absolute sum. -/
theorem reversed_lag_sum_le_tsum (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hf : Summable f) (k : ℕ) : (∑ j ∈ Finset.range k, f (k-j)) ≤ ∑' n, f n := by
  have H : (∑ j ∈ Finset.range k, f (k-j))=∑ j ∈ Finset.range k, f (j+1) := by
    calc
      _ = ∑ j ∈ Finset.range k, f ((k-1-j)+1) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        have hjk := Finset.mem_range.mp hj
        omega
      _ = _ := Finset.sum_range_reflect (fun j => f (j+1)) k
  rw [H]
  have Hsum := hf.sum_le_tsum (Finset.range (k+1)) (fun n _ => hf0 n)
  rw [Finset.sum_range_succ'] at Hsum
  linarith [hf0 0]

/-- Uniform comparison of two renewal equations with a summable kernel defect. -/
theorem renewal_comparison (h g a b R x : ℕ → ℝ) (u phi A K F : ℝ)
    (hh : ∀ n, 0 ≤ h n) (hmass : ∀ k, (∑ j ∈ Finset.range k, h (k-j)) ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hA : 0 ≤ A) (hK : 0 ≤ K) (hF : 0 ≤ F)
    (hkernel : Summable (fun n => |h n-g n|)) (hkernelBound : ∑' n, |h n-g n| ≤ K)
    (hforcing : ∀ k, |a k-b k| ≤ A) (hx : ∀ k, |u*x k+phi| ≤ F)
    (hR : ∀ k, R k=a k+∑ j ∈ Finset.range k, h (k-j)*(u*R j+phi))
    (hX : ∀ k, x k=b k+∑ j ∈ Finset.range k, g (k-j)*(u*x j+phi)) :
    ∀ k, |R k-x k| ≤ (A+K*F)/(1-u) := by
  apply absolute_renewal_bound h (fun k => R k-x k) u (A+K*F) hh hmass hu0 hu1 (by positivity)
  intro k
  have hid : R k-x k=(a k-b k)+
      (∑ j ∈ Finset.range k, h (k-j)*(u*(R j-x j)))+
      (∑ j ∈ Finset.range k, (h (k-j)-g (k-j))*(u*x j+phi)) := by
    rw [hR k,hX k]
    rw [add_assoc,←Finset.sum_add_distrib]
    have H : (∑ j ∈ Finset.range k, (h (k-j)*(u*(R j-x j))+(h (k-j)-g (k-j))*(u*x j+phi)))=
        (∑ j ∈ Finset.range k, h (k-j)*(u*R j+phi))-(∑ j ∈ Finset.range k, g (k-j)*(u*x j+phi)) := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [H]
    ring
  have hfirst : |∑ j ∈ Finset.range k, h (k-j)*(u*(R j-x j))| ≤
      u*(∑ j ∈ Finset.range k, h (k-j)*|R j-x j|) := by
    calc
      _ ≤ ∑ j ∈ Finset.range k, |h (k-j)*(u*(R j-x j))| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul,abs_mul,abs_of_nonneg (hh _),abs_of_nonneg hu0]
        ring
  have hsecond : |∑ j ∈ Finset.range k, (h (k-j)-g (k-j))*(u*x j+phi)| ≤ K*F := by
    calc
      _ ≤ ∑ j ∈ Finset.range k, |(h (k-j)-g (k-j))*(u*x j+phi)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range k, |h (k-j)-g (k-j)| * F := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
      _ = (∑ j ∈ Finset.range k, |h (k-j)-g (k-j)|)*F := (Finset.sum_mul ..).symm
      _ ≤ K*F := mul_le_mul_of_nonneg_right
        ((reversed_lag_sum_le_tsum _ (fun _ => abs_nonneg _) hkernel k).trans hkernelBound) hF
  rw [hid]
  have H1 := abs_add_le ((a k-b k)+(∑ j ∈ Finset.range k,h (k-j)*(u*(R j-x j))))
    (∑ j ∈ Finset.range k,(h (k-j)-g (k-j))*(u*x j+phi))
  have H2 := abs_add_le (a k-b k) (∑ j ∈ Finset.range k,h (k-j)*(u*(R j-x j)))
  linarith [hforcing k]

end
end SparseSGD
