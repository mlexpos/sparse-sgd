import SparseSGD.Continuum.Hurwitz
import SparseSGD.Continuum.ModalInversion
import SparseSGD.Continuum.Uniqueness
import SparseSGD.Comparison.UniformBounds

namespace SparseSGD
noncomputable section

def largeModeFrequency (delta a : ℝ) : ℝ := Real.sqrt (4*delta-1+3*a^2/4)

def largeModeRootPlus (delta a : ℝ) : ℂ := -(1+a/2) + Complex.I*largeModeFrequency delta a

/-- Shifting the continuum cubic by one leaves a monotone depressed cubic;
its real root lies between zero and one for every subcritical feedback. -/
theorem exists_largeMode_parameter (delta u : ℝ) (hd : 0 < delta)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ a : ℝ, 0 ≤ a ∧ a < 1 ∧ a^3+(4*delta-1)*a-4*delta*u = 0 := by
  by_cases hu : u = 0
  · exact ⟨0, le_rfl, by norm_num, by simp [hu]⟩
  have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
  obtain ⟨x, hx0, hx1, hx⟩ := exists_spectrum_root_between delta u hd hup hu1
  refine ⟨x+1, by linarith, by linarith, ?_⟩
  unfold spectrumPolynomial at hx
  nlinarith

theorem largeModeFrequency_pos (delta a : ℝ) (hd : 1 ≤ delta) :
    0 < largeModeFrequency delta a := by
  unfold largeModeFrequency
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg a]

theorem largeModeFrequency_sq (delta a : ℝ) (hd : 1 ≤ delta) :
    largeModeFrequency delta a^2 = 4*delta-1+3*a^2/4 := by
  apply Real.sq_sqrt
  nlinarith [sq_nonneg a]

/-- Exact factorization supplies all three modes without a spectral oracle. -/
theorem largeMode_cubic_factor (delta u a : ℝ) (hd : 1 ≤ delta)
    (ha : a^3+(4*delta-1)*a-4*delta*u = 0) (z : ℂ) :
    z^3+3*z^2+(2+4*(delta : ℂ))*z+4*(delta : ℂ)*(1-(u : ℂ)) =
      (z-((a-1 : ℝ) : ℂ))*
        ((z+((1+a/2 : ℝ) : ℂ))^2+(largeModeFrequency delta a : ℂ)^2) := by
  have hsq : (largeModeFrequency delta a : ℂ)^2 =
      4*(delta : ℂ)-1+3*(a : ℂ)^2/4 := by
    exact_mod_cast largeModeFrequency_sq delta a hd
  have haC : (a : ℂ)^3+(4*(delta : ℂ)-1)*(a : ℂ)-4*(delta : ℂ)*(u : ℂ) = 0 := by
    exact_mod_cast ha
  rw [hsq]
  push_cast
  linear_combination haC

theorem largeModeRootPlus_is_root (delta u a : ℝ) (hd : 1 ≤ delta)
    (ha : a^3+(4*delta-1)*a-4*delta*u = 0) :
    (largeModeRootPlus delta a)^3+3*(largeModeRootPlus delta a)^2+
      (2+4*(delta : ℂ))*largeModeRootPlus delta a+4*(delta : ℂ)*(1-(u : ℂ)) = 0 := by
  rw [largeMode_cubic_factor delta u a hd ha]
  have hq : (largeModeRootPlus delta a+((1+a/2 : ℝ) : ℂ))^2+
      (largeModeFrequency delta a : ℂ)^2 = 0 := by
    apply Complex.ext <;> simp [largeModeRootPlus, pow_two, Complex.mul_re, Complex.mul_im] <;> ring
  rw [hq, mul_zero]

/-- The oscillatory frequency differs from the free frequency by O(1/omega),
with an explicit uniform constant. -/
theorem largeModeFrequency_deviation (delta a omega : ℝ)
    (hd : 1 ≤ delta) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ho : 0 < omega) (hosq : omega^2 = delta-1/4) :
    0 ≤ largeModeFrequency delta a-2*omega ∧
      largeModeFrequency delta a-2*omega ≤ 3/(16*omega) := by
  have hb := largeModeFrequency_pos delta a hd
  have hbsq := largeModeFrequency_sq delta a hd
  have hlower : 2*omega ≤ largeModeFrequency delta a := by nlinarith [sq_nonneg a]
  have hdiff : (largeModeFrequency delta a-2*omega)*
      (largeModeFrequency delta a+2*omega) = 3*a^2/4 := by nlinarith
  have hprod : (largeModeFrequency delta a-2*omega)*(4*omega) ≤ 3/4 := by
    have H := mul_le_mul_of_nonneg_left (show 4*omega ≤ largeModeFrequency delta a+2*omega by linarith)
      (show 0 ≤ largeModeFrequency delta a-2*omega by linarith)
    rw [hdiff] at H
    nlinarith
  refine ⟨by linarith, ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < 16*omega)).2
  nlinarith

def modeVelocityFactor (delta : ℝ) (z : ℂ) : ℂ :=
  (z^2+z+2*(delta : ℂ))/(2*(delta : ℂ)^2)

def modeCrossFactor (delta : ℝ) (z : ℂ) : ℂ := -z/(2*(delta : ℂ))

def exponentialModeMoments (delta : ℝ) (z c : ℂ) (t : ℝ) : Moments :=
  let q := c*Complex.exp (z*(t : ℂ))
  ⟨q.re, (modeVelocityFactor delta z*q).re, (modeCrossFactor delta z*q).re⟩

theorem mode_factors_eigenrelations (delta u : ℝ) (z : ℂ) (hd : delta ≠ 0)
    (hz : z^3+3*z^2+(2+4*(delta : ℂ))*z+4*(delta : ℂ)*(1-(u : ℂ)) = 0) :
    z = -2*(delta : ℂ)*modeCrossFactor delta z ∧
    z*modeVelocityFactor delta z = 2*modeCrossFactor delta z-
      2*modeVelocityFactor delta z+2/(delta : ℂ)*(u : ℂ) ∧
    z*modeCrossFactor delta z = 1-modeCrossFactor delta z-
      (delta : ℂ)*modeVelocityFactor delta z := by
  have hdc : (delta : ℂ) ≠ 0 := by exact_mod_cast hd
  unfold modeVelocityFactor modeCrossFactor
  constructor
  · field_simp
  constructor
  · field_simp
    linear_combination hz
  · field_simp
    ring

/-- Every root of the actual continuum cubic gives an actual exponential
solution of the moment ODE; the coefficients are complex and the moments real. -/
theorem exponentialModeMoments_isMomentSolution (delta u : ℝ) (z c : ℂ)
    (hd : delta ≠ 0)
    (hz : z^3+3*z^2+(2+4*(delta : ℂ))*z+4*(delta : ℂ)*(1-(u : ℂ)) = 0) :
    IsMomentSolution delta u 0 (exponentialModeMoments delta z c) := by
  obtain ⟨hR, hV, hC⟩ := mode_factors_eigenrelations delta u z hd hz
  intro t _
  have hq (b : ℂ) : HasDerivAt
      (fun t : ℝ => (b*c*Complex.exp (z*(t : ℂ))).re)
      (b*z*(c*Complex.exp (z*(t : ℂ)))).re t := by
    have H : HasDerivAt (fun x : ℂ => b*c*Complex.exp (z*x))
        (b*c*(Complex.exp (z*(t : ℂ))*z)) (t : ℂ) :=
      by simpa only [id_eq, mul_one] using
        (((hasDerivAt_id (t : ℂ)).const_mul z).cexp).const_mul (b*c)
    convert H.real_of_complex using 1 <;> congr 1 <;> ring
  have hqr := hq 1
  have hqv := hq (modeVelocityFactor delta z)
  have hqc := hq (modeCrossFactor delta z)
  let q := c*Complex.exp (z*(t : ℂ))
  have HR := congrArg (fun w : ℂ => (w*q).re) hR
  have HV := congrArg (fun w : ℂ => (w*q).re) hV
  have HC := congrArg (fun w : ℂ => (w*q).re) hC
  constructor
  · convert hqr using 1
    · simp only [exponentialModeMoments, one_mul]
    · dsimp [continuumField, exponentialModeMoments]
      simpa [q, Complex.mul_re, mul_assoc] using HR.symm
  constructor
  · convert hqv using 1
    · simp only [exponentialModeMoments, mul_assoc]
    · dsimp [continuumField, exponentialModeMoments]
      simp [q, Complex.mul_re, Complex.div_re, Complex.div_im] at HV ⊢
      field_simp at HV ⊢
      linear_combination -HV

  · convert hqc using 1
    · simp only [exponentialModeMoments, mul_assoc]
    · dsimp [continuumField, exponentialModeMoments]
      simp [q, Complex.mul_re] at HC ⊢
      linear_combination -HC


def largeModeSlowCoefficient (delta a : ℝ) (s : Moments) : ℝ :=
  (2*delta^2*s.V-2*delta*(1+a)*s.C+(2*delta+a+a^2)*s.R)/(4*delta-1+3*a^2)

def largeModeCosCoefficient (delta a : ℝ) (s : Moments) : ℝ :=
  s.R-largeModeSlowCoefficient delta a s

def largeModeSinCoefficient (delta a : ℝ) (s : Moments) : ℝ :=
  (-2*delta*s.C-(a-1)*largeModeSlowCoefficient delta a s+
    (1+a/2)*largeModeCosCoefficient delta a s)/largeModeFrequency delta a

def largeModeOscCoefficient (delta a : ℝ) (s : Moments) : ℂ :=
  largeModeCosCoefficient delta a s-Complex.I*largeModeSinCoefficient delta a s

def largeModeHomogeneousFlow (delta a : ℝ) (s : Moments) (t : ℝ) : Moments :=
  let f := exponentialModeMoments delta ((a-1 : ℝ) : ℂ)
    (largeModeSlowCoefficient delta a s) t
  let g := exponentialModeMoments delta (largeModeRootPlus delta a)
    (largeModeOscCoefficient delta a s) t
  ⟨f.R+g.R, f.V+g.V, f.C+g.C⟩

/-- Explicit inversion of the three distinct roots at the initial time. -/
theorem largeModeHomogeneousFlow_initial (delta a : ℝ) (s : Moments) (hd : 1 ≤ delta) :
    largeModeHomogeneousFlow delta a s 0 = s := by
  have hdne : delta ≠ 0 := by linarith
  have hb := largeModeFrequency_pos delta a hd
  have hbsq := largeModeFrequency_sq delta a hd
  have hden : 4*delta-1+3*a^2 ≠ 0 := by nlinarith [sq_nonneg a]
  apply Moments.ext
  · simp [largeModeHomogeneousFlow, exponentialModeMoments, largeModeOscCoefficient,
      largeModeCosCoefficient]
  · simp [largeModeHomogeneousFlow, exponentialModeMoments, modeVelocityFactor,
      largeModeRootPlus, largeModeOscCoefficient, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply, pow_two]
    rw [← pow_two (largeModeFrequency delta a), hbsq]
    unfold largeModeSinCoefficient largeModeCosCoefficient largeModeSlowCoefficient
    field_simp [hdne, hb.ne', hden]
    ring_nf
    have hinv : (-1+a^2*3+delta*4)*(-1+a^2*3+delta*4)⁻¹ = 1 :=
      mul_inv_cancel₀ (by nlinarith [sq_nonneg a])
    linear_combination -(32*a*delta*s.C-16*a*s.R-16*a^2*s.R+32*delta*s.C-32*delta*s.R-32*delta^2*s.V)*hinv
  · simp [largeModeHomogeneousFlow, exponentialModeMoments, modeCrossFactor,
      largeModeRootPlus, largeModeOscCoefficient, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply, pow_two]
    unfold largeModeSinCoefficient largeModeCosCoefficient largeModeSlowCoefficient
    field_simp
    ring

/-- The explicit initial-data expansion solves the actual homogeneous system. -/
theorem largeModeHomogeneousFlow_isMomentSolution (delta u a : ℝ) (s : Moments)
    (hd : 1 ≤ delta) (ha : a^3+(4*delta-1)*a-4*delta*u = 0) :
    IsMomentSolution delta u 0 (largeModeHomogeneousFlow delta a s) := by
  have hdne : delta ≠ 0 := by linarith
  have hz0 : ((a-1 : ℝ) : ℂ)^3+3*((a-1 : ℝ) : ℂ)^2+
      (2+4*(delta : ℂ))*((a-1 : ℝ) : ℂ)+4*(delta : ℂ)*(1-(u : ℂ)) = 0 := by
    rw [largeMode_cubic_factor delta u a hd ha]
    simp
  have hf := exponentialModeMoments_isMomentSolution delta u _
    (largeModeSlowCoefficient delta a s) hdne hz0
  have hg := exponentialModeMoments_isMomentSolution delta u _
    (largeModeOscCoefficient delta a s) hdne (largeModeRootPlus_is_root delta u a hd ha)
  intro t ht
  obtain ⟨hfR,hfV,hfC⟩ := hf t ht
  obtain ⟨hgR,hgV,hgC⟩ := hg t ht
  refine ⟨?_,?_,?_⟩
  · convert hfR.add hgR using 1 <;> dsimp [largeModeHomogeneousFlow,continuumField] <;> first | rfl | ring
  · convert hfV.add hgV using 1 <;> dsimp [largeModeHomogeneousFlow,continuumField] <;> first | rfl | ring
  · convert hfC.add hgC using 1 <;> dsimp [largeModeHomogeneousFlow,continuumField] <;> first | rfl | ring


def largeModeCenteredInitial (delta u phi : ℝ) (s : Moments) : Moments :=
  ⟨s.R-phi/(1-u),s.V-phi/(delta*(1-u)),s.C⟩

def largeModeFlow (delta u phi a : ℝ) (s : Moments) (t : ℝ) : Moments :=
  let f := largeModeHomogeneousFlow delta a (largeModeCenteredInitial delta u phi s) t
  ⟨f.R+phi/(1-u),f.V+phi/(delta*(1-u)),f.C⟩

theorem largeModeFlow_initial (delta u phi a : ℝ) (s : Moments) (hd : 1 ≤ delta) :
    largeModeFlow delta u phi a s 0 = s := by
  unfold largeModeFlow
  rw [largeModeHomogeneousFlow_initial delta a _ hd]
  apply Moments.ext <;> simp [largeModeCenteredInitial]

theorem largeModeFlow_isMomentSolution (delta u phi a : ℝ) (s : Moments)
    (hd : 1 ≤ delta) (hu : u ≠ 1) (ha : a^3+(4*delta-1)*a-4*delta*u = 0) :
    IsMomentSolution delta u phi (largeModeFlow delta u phi a s) := by
  have hf := largeModeHomogeneousFlow_isMomentSolution delta u a
    (largeModeCenteredInitial delta u phi s) hd ha
  have hdne : delta ≠ 0 := by linarith
  have hune : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  intro t ht
  obtain ⟨hfR,hfV,hfC⟩ := hf t ht
  refine ⟨?_,?_,?_⟩
  · convert hfR.add_const (phi/(1-u)) using 1
    · rfl
    · dsimp [largeModeFlow,continuumField] <;> ring
  · convert hfV.add_const (phi/(delta*(1-u))) using 1
    · rfl
    · dsimp [largeModeFlow,continuumField] <;> field_simp <;> ring
  · convert hfC using 1
    · rfl
    · dsimp [largeModeFlow,continuumField] <;> field_simp <;> ring

/-- Actual continuum risk expansion, with explicit coefficients determined by
initial data. No modal representation is assumed. -/
theorem continuumFlow_largeMode_expansion (delta u phi a : ℝ) (s : Moments)
    (hd : 1 ≤ delta) (hu : u ≠ 1) (ha : a^3+(4*delta-1)*a-4*delta*u = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    (continuumFlow delta u phi s t).R = phi/(1-u) +
      largeModeSlowCoefficient delta a (largeModeCenteredInitial delta u phi s)*
        Real.exp ((a-1)*t) +
      (largeModeOscCoefficient delta a (largeModeCenteredInitial delta u phi s)*
        Complex.exp (largeModeRootPlus delta a*(t : ℂ))).re := by
  have H := continuum_solution_unique delta u phi s (largeModeFlow delta u phi a s)
    (largeModeFlow_initial delta u phi a s hd)
    (largeModeFlow_isMomentSolution delta u phi a s hd hu ha) t ht
  rw [← H]
  simp [largeModeFlow, largeModeHomogeneousFlow, exponentialModeMoments,
    Complex.exp_re, Complex.mul_re, Complex.mul_im]
  ring


private theorem abs_sub_le_sum (x y : ℝ) : |x-y| ≤ |x|+|y| := by
  simpa using abs_sub_le x 0 y

theorem largeModeSlowCoefficient_bound (delta a N : ℝ) (s : Moments)
    (hd : 4 ≤ delta) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hN : 0 ≤ N)
    (hR : |s.R| ≤ N) (hV : delta*|s.V| ≤ N) (hC : |s.C| ≤ N) :
    |largeModeSlowCoefficient delta a s| ≤ 4*N := by
  have hden : 0 < 4*delta-1+3*a^2 := by nlinarith [sq_nonneg a]
  have ha2 : a^2 ≤ 1 := by nlinarith
  have hnum : |2*delta^2*s.V-2*delta*(1+a)*s.C+(2*delta+a+a^2)*s.R| ≤
      2*delta^2*|s.V|+2*delta*(1+a)*|s.C|+(2*delta+a+a^2)*|s.R| := by
    calc
      _ ≤ |2*delta^2*s.V-2*delta*(1+a)*s.C|+|(2*delta+a+a^2)*s.R| := abs_add_le _ _
      _ ≤ |2*delta^2*s.V|+|2*delta*(1+a)*s.C|+|(2*delta+a+a^2)*s.R| := by
        exact add_le_add (abs_sub_le_sum _ _) le_rfl
      _ = _ := by
        rw [abs_mul (2*delta^2),abs_mul (2*delta*(1+a)),abs_mul (2*delta+a+a^2)]
        rw [abs_of_nonneg (by positivity : 0 ≤ 2*delta^2),
          abs_of_nonneg (by positivity : 0 ≤ 2*delta*(1+a)),
          abs_of_nonneg (by positivity : 0 ≤ 2*delta+a+a^2)]
  have hv := mul_le_mul_of_nonneg_left hV (show 0 ≤ 2*delta by linarith)
  have hc := mul_le_mul_of_nonneg_left hC (show 0 ≤ 2*delta*(1+a) by positivity)
  have hr := mul_le_mul_of_nonneg_left hR (show 0 ≤ 2*delta+a+a^2 by positivity)
  have hn1 := mul_nonneg (show 0 ≤ 1-a by linarith) hN
  have hn2 := mul_nonneg (show 0 ≤ 1-a^2 by linarith) hN
  have hn3 := mul_nonneg (show 0 ≤ delta-4 by linarith) hN
  unfold largeModeSlowCoefficient
  rw [abs_div,abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  nlinarith [mul_nonneg (sq_nonneg a) hN]


theorem largeMode_coefficients_bound (delta a N : ℝ) (s : Moments)
    (hd : 4 ≤ delta) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hN : 0 ≤ N)
    (hR : |s.R| ≤ N) (hV : delta*|s.V| ≤ N) (hC : |s.C| ≤ N)
    (hCb : 2*delta*|s.C| ≤ largeModeFrequency delta a*N) :
    |largeModeSlowCoefficient delta a s|+‖largeModeOscCoefficient delta a s‖ ≤ 22*N := by
  have hslow := largeModeSlowCoefficient_bound delta a N s hd ha0 ha1 hN hR hV hC
  have hcos : |largeModeCosCoefficient delta a s| ≤ 5*N := by
    unfold largeModeCosCoefficient
    exact (abs_sub_le_sum _ _).trans (by linarith)
  have hb := largeModeFrequency_pos delta a (by linarith)
  have hbsq := largeModeFrequency_sq delta a (by linarith)
  have hb1 : 1 ≤ largeModeFrequency delta a := by nlinarith [sq_nonneg a]
  have hsin : |largeModeSinCoefficient delta a s| ≤ 13*N := by
    have hnum : |-2*delta*s.C-(a-1)*largeModeSlowCoefficient delta a s+
        (1+a/2)*largeModeCosCoefficient delta a s| ≤
        2*delta*|s.C|+(1-a)*|largeModeSlowCoefficient delta a s|+
          (1+a/2)*|largeModeCosCoefficient delta a s| := by
      calc
        _ ≤ |-2*delta*s.C-(a-1)*largeModeSlowCoefficient delta a s|+
          |(1+a/2)*largeModeCosCoefficient delta a s| := abs_add_le _ _
        _ ≤ |-2*delta*s.C|+|(a-1)*largeModeSlowCoefficient delta a s|+
          |(1+a/2)*largeModeCosCoefficient delta a s| := add_le_add (abs_sub_le_sum _ _) le_rfl
        _ = _ := by
          rw [abs_mul (-2*delta),abs_mul (a-1),abs_mul (1+a/2)]
          rw [abs_of_nonpos (by linarith : -2*delta ≤ 0),
            abs_of_nonpos (by linarith : a-1 ≤ 0),
            abs_of_nonneg (by positivity : 0 ≤ 1+a/2)]
          ring
    have hslow' := mul_le_mul_of_nonneg_left hslow (show 0 ≤ 1-a by linarith)
    have hcos' := mul_le_mul_of_nonneg_left hcos (show 0 ≤ 1+a/2 by positivity)
    have hn := mul_le_mul_of_nonneg_right hb1 hN
    unfold largeModeSinCoefficient
    rw [abs_div,abs_of_pos hb]
    apply (div_le_iff₀ hb).2
    nlinarith [mul_nonneg ha0 hN,mul_nonneg (show 0 ≤ 1-a by linarith) hN]
  have hosc : ‖largeModeOscCoefficient delta a s‖ ≤
      |largeModeCosCoefficient delta a s|+|largeModeSinCoefficient delta a s| := by
    unfold largeModeOscCoefficient
    calc
      _ ≤ ‖(largeModeCosCoefficient delta a s : ℂ)‖+
        ‖Complex.I*(largeModeSinCoefficient delta a s : ℂ)‖ := norm_sub_le _ _
      _ = _ := by simp [norm_mul]
  linarith


/-- Uniform coefficient estimate for the actual centered positive-semidefinite
initial data, with one absolute constant over the whole large-parameter regime. -/
theorem continuumFlow_largeMode_coefficients_bound (delta u phi a : ℝ) (s : Moments)
    (hd : 4 ≤ delta) (hu : u < 1) (hp : 0 ≤ phi) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hs : s.psd) :
    |largeModeSlowCoefficient delta a (largeModeCenteredInitial delta u phi s)|+
      ‖largeModeOscCoefficient delta a (largeModeCenteredInitial delta u phi s)‖ ≤
      22*(s.R+delta*s.V+phi/(1-u)) := by
  have hdp : 0 < delta := by linarith
  have hR := Moments.psd_R_nonneg hs
  have hV := Moments.psd_V_nonneg hs
  have hL : 0 ≤ phi/(1-u) := by positivity
  have hE : 0 ≤ s.R+delta*s.V := by positivity
  have hx := Moments.psd_cross_energy_bound delta hdp s hs
  have hdsq : Real.sqrt delta^2 = delta := Real.sq_sqrt hdp.le
  have hd1 : 1 ≤ Real.sqrt delta := by nlinarith [Real.sqrt_nonneg delta]
  have hb := largeModeFrequency_pos delta a (by linarith)
  have hbsq := largeModeFrequency_sq delta a (by linarith)
  have hdb : Real.sqrt delta ≤ largeModeFrequency delta a := by
    nlinarith [Real.sqrt_nonneg delta,sq_nonneg a]
  have hcross : |s.C| ≤ s.R+delta*s.V := by
    have H := mul_le_mul_of_nonneg_right hd1 (abs_nonneg s.C)
    nlinarith
  apply largeMode_coefficients_bound delta a _ _ hd ha0 ha1 (by positivity)
  · dsimp [largeModeCenteredInitial]
    exact (abs_sub_le_sum _ _).trans (by rw [abs_of_nonneg hR,abs_of_nonneg hL]; nlinarith)
  · dsimp [largeModeCenteredInitial]
    have H := mul_le_mul_of_nonneg_left (abs_sub_le_sum s.V (phi/(delta*(1-u)))) hdp.le
    have hvL : 0 ≤ phi/(delta*(1-u)) := by positivity
    rw [abs_of_nonneg hV,abs_of_nonneg hvL] at H
    have heq : delta*(phi/(delta*(1-u))) = phi/(1-u) := by field_simp
    rw [mul_add,heq] at H
    nlinarith
  · dsimp [largeModeCenteredInitial]
    linarith
  · dsimp [largeModeCenteredInitial]
    have H := mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg delta)
    have H' := mul_le_mul_of_nonneg_right hdb (show 0 ≤ s.R+delta*s.V+phi/(1-u) by positivity)
    nlinarith [mul_nonneg (Real.sqrt_nonneg delta) hL]


def largeModeRates (delta a : ℝ) : Fin 3 → ℂ :=
  ![((a-1 : ℝ) : ℂ),largeModeRootPlus delta a,star (largeModeRootPlus delta a)]

def largeModeCoefficients (delta u phi a : ℝ) (s : Moments) : Fin 3 → ℂ :=
  let v := largeModeCenteredInitial delta u phi s
  ![(largeModeSlowCoefficient delta a v : ℂ),largeModeOscCoefficient delta a v/2,
    star (largeModeOscCoefficient delta a v)/2]

private theorem complex_re_decomposition (z : ℂ) :
    (z.re : ℂ) = (z+star z)/2 := by
  apply Complex.ext <;> simp <;> ring

/-- The full three-mode form of the actual risk expansion. -/
theorem continuumFlow_largeMode_sum (delta u phi a : ℝ) (s : Moments)
    (hd : 1 ≤ delta) (hu : u ≠ 1) (ha : a^3+(4*delta-1)*a-4*delta*u = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    ((continuumFlow delta u phi s t).R : ℂ) = (phi/(1-u) : ℝ) +
      ∑ i : Fin 3, largeModeCoefficients delta u phi a s i*
        Complex.exp (largeModeRates delta a i*(t : ℂ)) := by
  rw [continuumFlow_largeMode_expansion delta u phi a s hd hu ha t ht]
  push_cast
  rw [complex_re_decomposition]
  have he (z : ℂ) : star (Complex.exp (z*(t : ℂ))) = Complex.exp (star z*(t : ℂ)) := by
    change (starRingEnd ℂ) (Complex.exp (z*(t : ℂ))) =
      Complex.exp ((starRingEnd ℂ) z*(t : ℂ))
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  simp only [largeModeCoefficients,largeModeRates,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  rw [star_mul,he]
  push_cast
  ring

theorem continuumFlow_largeMode_sum_coefficients_bound (delta u phi a : ℝ) (s : Moments)
    (hd : 4 ≤ delta) (hu : u < 1) (hp : 0 ≤ phi) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hs : s.psd) :
    (∑ i : Fin 3, ‖largeModeCoefficients delta u phi a s i‖) ≤
      22*(s.R+delta*s.V+phi/(1-u)) := by
  have H := continuumFlow_largeMode_coefficients_bound delta u phi a s hd hu hp ha0 ha1 hs
  simpa [largeModeCoefficients,Fin.sum_univ_succ,norm_div] using H


theorem largeModeRates_real_parts (delta a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ∀ i : Fin 3, -3/2 ≤ (largeModeRates delta a i).re ∧ (largeModeRates delta a i).re < 0 := by
  intro i
  fin_cases i <;> simp [largeModeRates,largeModeRootPlus] <;> constructor <;> linarith

theorem largeModeRootPlus_deviation (delta a omega : ℝ)
    (hd : 4 ≤ delta) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ho : 0 < omega) (hosq : omega^2 = delta-1/4) :
    ‖largeModeRootPlus delta a-oscillatoryRoot omega‖ ≤ 3 ∧
    |(largeModeRootPlus delta a).im-2*omega| ≤ 22/omega := by
  have H := largeModeFrequency_deviation delta a omega (by linarith) ha0 ha1 ho hosq
  have ho1 : 1 ≤ omega := by nlinarith
  have hfreq : largeModeFrequency delta a-2*omega ≤ 3/16 := by
    have h := (le_div_iff₀ (by positivity : 0 < 16*omega)).1 H.2
    nlinarith
  constructor
  · apply (Complex.norm_le_abs_re_add_abs_im _).trans
    simp [largeModeRootPlus,oscillatoryRoot,Complex.mul_im,Complex.mul_re]
    rw [abs_of_nonneg (by positivity : 0 ≤ a/2),abs_of_nonneg H.1]
    linarith
  · simp [largeModeRootPlus]
    rw [abs_of_nonneg H.1]
    apply H.2.trans
    apply (div_le_div_iff₀ (by positivity : 0 < 16*omega) ho).2
    nlinarith


theorem largeModeRates_imag_bound (delta a omega : ℝ)
    (hd : 4 ≤ delta) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ho : 0 < omega) (hosq : omega^2 = delta-1/4) (i : Fin 3) :
    |(largeModeRates delta a i).im| ≤ 2*omega+22/omega := by
  have H := largeModeFrequency_deviation delta a omega (by linarith) ha0 ha1 ho hosq
  have H' : largeModeFrequency delta a ≤ 2*omega+22/omega := by
    have hc : 3/(16*omega) ≤ 22/omega := by
      apply (div_le_div_iff₀ (by positivity : 0 < 16*omega) ho).2
      nlinarith
    linarith
  fin_cases i <;> simp [largeModeRates,largeModeRootPlus,
    abs_of_pos (largeModeFrequency_pos delta a (by linarith))] <;> first | exact H' | positivity

end
end SparseSGD
