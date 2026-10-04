import SparseSGD.Scaling.WindowScalars
import SparseSGD.Continuum.PerronRate

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1500000

/-- In the large-Delta range the real root is exactly the spectral abscissa. -/
theorem continuumPerronRate_largeMode (delta u a : ℝ) (hd : 1 ≤ delta)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (ha : a^3+(4*delta-1)*a-4*delta*u = 0) :
    continuumPerronRate delta u = 1-a := by
  have hroot : ((a-1 : ℝ) : ℂ) ∈ continuumCharacteristicRoots delta u := by
    change _ = 0
    rw [largeMode_cubic_factor delta u a hd ha]
    simp
  have hmax (z : ℂ) (hz : z ∈ continuumCharacteristicRoots delta u) : z.re ≤ a-1 := by
    change _ = 0 at hz
    rw [largeMode_cubic_factor delta u a hd ha] at hz
    rcases mul_eq_zero.mp hz with hz | hz
    · have H := congrArg Complex.re (sub_eq_zero.mp hz)
      simpa only [Complex.ofReal_re] using H.le
    · have hr := congrArg Complex.re hz
      have hi := congrArg Complex.im hz
      simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.zero_re,Complex.zero_im,mul_zero,zero_mul,
        add_zero,sub_zero] at hr hi
      have hfreq := largeModeFrequency_pos delta a hd
      have him : z.im ≠ 0 := by
        intro H
        rw [H] at hr
        nlinarith only [hr, sq_nonneg (z.re+(1+a/2)),sq_pos_of_pos hfreq]
      have hre : z.re+(1+a/2) = 0 := by
        have H : 2*(z.re+(1+a/2))*z.im = 0 := by nlinarith only [hi]
        rcases mul_eq_zero.mp H with H | H
        · linarith
        · exact False.elim (him H)
      linarith
  have hmem : a-1 ∈ Complex.re '' continuumCharacteristicRoots delta u :=
    ⟨((a-1 : ℝ) : ℂ),hroot,rfl⟩
  have hsup : sSup (Complex.re '' continuumCharacteristicRoots delta u) = a-1 := by
    apply le_antisymm
    · apply csSup_le ⟨a-1,hmem⟩
      rintro _ ⟨z,hz,rfl⟩
      exact hmax z hz
    · exact le_csSup ((continuumCharacteristicRoots_finite delta u).image Complex.re).bddAbove hmem
  simp [continuumPerronRate,hsup]

/-- The actual continuum convergence rate reaches the cap with an explicit
O(Delta^{-1}) error, stronger than the window's O(Delta^{-1/2}) precision. -/
theorem window_continuum_rate_bound (delta u : ℝ) (hd : 1 ≤ delta)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    0 ≤ (1-u)-continuumPerronRate delta u ∧
      (1-u)-continuumPerronRate delta u ≤ 1/(4*delta) := by
  obtain ⟨a,ha0,ha1,ha⟩ := exists_largeMode_parameter delta u (by linarith) hu0 hu1
  rw [continuumPerronRate_largeMode delta u a hd ha0 ha1 ha]
  convert largeMode_parameter_shift delta u a hd ha0 ha1.le ha using 1 <;> ring_nf

end
end SparseSGD
