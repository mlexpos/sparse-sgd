import Mathlib

namespace SparseSGD.Logistic.V2

open Matrix

/-- Hurwitz stability of a real matrix: every complex root of the characteristic
polynomial has negative real part. Same form as in `Continuum/Hurwitz.lean`. -/
def IsHurwitz {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ z : ℂ, Matrix.det (z • (1 : Matrix (Fin n) (Fin n) ℂ) - A.map Complex.ofReal) = 0 →
    z.re < 0

lemma det_step_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : ℝ) (hh : h ≠ 0) (mu : ℂ) :
    Matrix.det (mu • (1 : Matrix (Fin n) (Fin n) ℂ) - (1 + h • A).map Complex.ofReal) =
      (h : ℂ) ^ n * Matrix.det (((mu - 1) / h) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        A.map Complex.ofReal) := by
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have : mu • (1 : Matrix (Fin n) (Fin n) ℂ) - (1 + h • A).map Complex.ofReal =
      (h : ℂ) • (((mu - 1) / h) • (1 : Matrix (Fin n) (Fin n) ℂ) - A.map Complex.ofReal) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.sub_apply, Matrix.smul_apply]
      field_simp
      ring
    · simp [Matrix.sub_apply, Matrix.smul_apply, hij]
  rw [this, Matrix.det_smul]
  simp

lemma exists_small_step (S : Finset ℂ) (hS : ∀ z ∈ S, z.re < 0) :
    ∃ h : ℝ, 0 < h ∧ ∀ z ∈ S, h * ‖z‖ ^ 2 < -2 * z.re := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert z0 S hz0 ih =>
    obtain ⟨h, hpos, hh⟩ := ih (fun z hz => hS z (Finset.mem_insert_of_mem hz))
    have hre : z0.re < 0 := hS z0 (Finset.mem_insert_self _ _)
    have hn : 0 < ‖z0‖ ^ 2 + 1 := by positivity
    refine ⟨min h (-z0.re / (‖z0‖ ^ 2 + 1)), lt_min hpos (div_pos (by linarith) hn), ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · calc min h (-z.re / (‖z‖ ^ 2 + 1)) * ‖z‖ ^ 2
          ≤ (-z.re / (‖z‖ ^ 2 + 1)) * ‖z‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ < -2 * z.re := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ hn]
            nlinarith [sq_nonneg ‖z‖]
    · calc min h (-z0.re / (‖z0‖ ^ 2 + 1)) * ‖z‖ ^ 2 ≤ h * ‖z‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ < -2 * z.re := hh z hz

/-- v2 prop:S (ii) / cor:recursion: for a Hurwitz matrix there is a step `h > 0` such that
every eigenvalue of the Euler step matrix `1 + h A` lies in the open unit disc. -/
theorem exists_step_spectral_contraction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsHurwitz A) :
    ∃ h : ℝ, 0 < h ∧ ∀ mu : ℂ,
      Matrix.det (mu • (1 : Matrix (Fin n) (Fin n) ℂ) - (1 + h • A).map Complex.ofReal) = 0 →
        ‖mu‖ < 1 := by
  classical
  set p := (A.map Complex.ofReal).charpoly with hp
  have hpm : p ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hmem : ∀ z : ℂ, z ∈ p.roots.toFinset ↔
      Matrix.det (z • (1 : Matrix (Fin n) (Fin n) ℂ) - A.map Complex.ofReal) = 0 := by
    intro z
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hpm, Polynomial.IsRoot, hp,
      Matrix.eval_charpoly]
    simp [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  obtain ⟨h, hpos, hh⟩ := exists_small_step p.roots.toFinset
    (fun z hz => hA z ((hmem z).mp hz))
  refine ⟨h, hpos, fun mu hmu => ?_⟩
  rw [det_step_eq A h hpos.ne'] at hmu
  have hw : Matrix.det (((mu - 1) / h) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      A.map Complex.ofReal) = 0 := by
    rcases mul_eq_zero.mp hmu with h0 | h0
    · exact absurd (pow_eq_zero_iff'.mp h0).1 (by exact_mod_cast hpos.ne')
    · exact h0
  set w : ℂ := (mu - 1) / h with hwdef
  have hmu_eq : mu = 1 + h * w := by
    rw [hwdef]; have : (h : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp; ring
  have hlt := hh w ((hmem w).mpr hw)
  have hsq : ‖mu‖ ^ 2 < 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hmu_eq]
    have hn : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    rw [hn] at hlt
    nlinarith [mul_lt_mul_of_pos_left hlt hpos]
  by_contra hcon
  push Not at hcon
  nlinarith [norm_nonneg mu]


open Filter Topology in
open scoped ENNReal NNReal in
lemma exists_pow_norm_le_half {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [Nontrivial A] (a : A) (hspec : ∀ z ∈ spectrum ℂ a, ‖z‖ < 1) :
    ∃ m : ℕ, 1 ≤ m ∧ ‖a ^ m‖ ≤ 1 / 2 := by
  obtain ⟨z, hz, hzeq⟩ := spectrum.exists_nnnorm_eq_spectralRadius a
  have hρ : spectralRadius ℂ a < 1 := by
    rw [← hzeq]
    have := hspec z hz
    have h' : ‖z‖₊ < 1 := by exact_mod_cast this
    exact_mod_cast h'
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hT := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a
  have h1 : ∀ᶠ k : ℕ in atTop, (‖a ^ k‖₊ : ℝ≥0∞) ^ (1 / k : ℝ) < r :=
    hT.eventually (gt_mem_nhds hr1)
  have h2 : ∀ᶠ k : ℕ in atTop, r ^ k < 1 / 2 :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr2).eventually
      (gt_mem_nhds (by norm_num))
  obtain ⟨m, hm1, hm2, hm3⟩ := (h1.and (h2.and (eventually_ge_atTop 1))).exists
  refine ⟨m, hm3, ?_⟩
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have : (‖a ^ m‖₊ : ℝ≥0∞) < r ^ m := by
    have := ENNReal.rpow_lt_rpow hm1 (show (0 : ℝ) < m by positivity)
    rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hm0, ENNReal.rpow_one,
      ENNReal.rpow_natCast] at this
  have h3 : (‖a ^ m‖₊ : ℝ≥0∞) < ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
    refine this.trans ?_
    simpa using hm2
  have h4 : ‖a ^ m‖₊ < (1 / 2 : ℝ≥0) := by exact_mod_cast h3
  have h5 : ‖a ^ m‖ < 1 / 2 := by exact_mod_cast h4
  exact h5.le

open scoped Matrix.Norms.L2Operator in
lemma real_quad_le_of_opNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ‖M.map Complex.ofReal‖ ≤ 1 / 2) (x : Fin n → ℝ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ x) ≤ (1 / 4) * (x ⬝ᵥ x) := by
  set xc : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun i => (x i : ℂ)) with hxc
  have key := Matrix.l2_opNorm_mulVec (M.map Complex.ofReal) xc
  have hn1 : ‖xc‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [hxc, dotProduct, sq]
  have hn2 : ‖(EuclideanSpace.equiv (Fin n) ℂ).symm ((M.map Complex.ofReal) *ᵥ xc)‖ ^ 2 =
      (M *ᵥ x) ⬝ᵥ (M *ᵥ x) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [dotProduct, sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := RingHom.map_mulVec Complex.ofRealHom M x i
    simp [hxc] at this ⊢
    have h2 : (M.map Complex.ofReal *ᵥ fun i => (x i : ℂ)) i = (((M *ᵥ x) i : ℝ) : ℂ) :=
      this.symm
    rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_mul_abs_self]
  have h0 : 0 ≤ ‖xc‖ := norm_nonneg _
  have h3 : ‖(EuclideanSpace.equiv (Fin n) ℂ).symm ((M.map Complex.ofReal) *ᵥ xc)‖ ≤
      1 / 2 * ‖xc‖ := key.trans (mul_le_mul_of_nonneg_right hM h0)
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  rw [hn2, mul_pow, hn1] at h4
  linarith

lemma dot_self_nonneg' {n : ℕ} (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

lemma qf_sym {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (u v : Fin n → ℝ) :
    u ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (P *ᵥ u) := by
  rw [dotProduct_mulVec, ← hP, vecMul_transpose, hP, dotProduct_comm]

lemma qf_gram {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((Cᵀ * C) *ᵥ x) = (C *ᵥ x) ⬝ᵥ (C *ᵥ x) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- Gram sum. -/
def gramSum {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ k ∈ Finset.range m, (B ^ k)ᵀ * B ^ k

lemma gramSum_symm {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) : (gramSum B m)ᵀ = gramSum B m := by
  simp [gramSum, Matrix.transpose_sum, Matrix.transpose_mul]

lemma qf_gramSum {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (x : Fin n → ℝ) :
    x ⬝ᵥ (gramSum B m *ᵥ x) = ∑ k ∈ Finset.range m, (B ^ k *ᵥ x) ⬝ᵥ (B ^ k *ᵥ x) := by
  simp only [gramSum, Matrix.sum_mulVec, dotProduct_sum, qf_gram]

lemma qf_gramSum_step {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (x : Fin n → ℝ) :
    (B *ᵥ x) ⬝ᵥ (gramSum B m *ᵥ (B *ᵥ x)) =
      x ⬝ᵥ (gramSum B m *ᵥ x) - x ⬝ᵥ x + (B ^ m *ᵥ x) ⬝ᵥ (B ^ m *ᵥ x) := by
  rw [qf_gramSum, qf_gramSum]
  have h : ∀ k, (B ^ k *ᵥ (B *ᵥ x)) ⬝ᵥ (B ^ k *ᵥ (B *ᵥ x)) =
      (B ^ (k + 1) *ᵥ x) ⬝ᵥ (B ^ (k + 1) *ᵥ x) := by
    intro k
    rw [mulVec_mulVec, ← pow_succ]
  simp only [h]
  have := Finset.sum_range_succ' (fun k => (B ^ k *ᵥ x) ⬝ᵥ (B ^ k *ᵥ x)) m
  rw [Finset.sum_range_succ] at this
  simp at this
  linarith

lemma quad_le_of_entries {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ)
    (hM : ∀ i j, |M i j| ≤ μ) (x : Fin n → ℝ) :
    x ⬝ᵥ (M *ᵥ x) ≤ n * μ * (x ⬝ᵥ x) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [dotProduct]
  have hμ : 0 ≤ μ := (abs_nonneg _).trans (hM ⟨0, hn⟩ ⟨0, hn⟩)
  have hterm : ∀ i j, x i * (M i j * x j) ≤ μ * ((x i ^ 2 + x j ^ 2) / 2) := by
    intro i j
    have h1 : x i * (M i j * x j) ≤ |M i j| * |x i * x j| := by
      calc x i * (M i j * x j) = M i j * (x i * x j) := by ring
        _ ≤ |M i j * (x i * x j)| := le_abs_self _
        _ = |M i j| * |x i * x j| := abs_mul _ _
    have h2 : |x i * x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x i + x j), sq_nonneg (x i - x j)]
    calc x i * (M i j * x j) ≤ |M i j| * |x i * x j| := h1
      _ ≤ μ * ((x i ^ 2 + x j ^ 2) / 2) :=
        mul_le_mul (hM i j) h2 (abs_nonneg _) hμ
  calc x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, x i * (M i j * x j) := by
        simp [dotProduct, mulVec, Finset.mul_sum]
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, μ * ((x i ^ 2 + x j ^ 2) / 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = n * μ * (x ⬝ᵥ x) := by
        simp only [dotProduct, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, sq]
        rw [show ∑ i, x i * ((n : ℝ) * x i) = (n : ℝ) * ∑ i, x i * x i from by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
        ring

open scoped Matrix.Norms.L2Operator in
/-- Squared form of the power contraction, with the step `h` of
`exists_step_spectral_contraction`. Route: Gelfand's formula in the complex Banach algebra
of `n × n` complex matrices with the L2 operator norm. -/
lemma exists_sq_contraction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsHurwitz A) :
    ∃ h : ℝ, 0 < h ∧ ∃ m : ℕ, 1 ≤ m ∧ ∀ x : Fin n → ℝ,
      (((1 + h • A) ^ m) *ᵥ x) ⬝ᵥ (((1 + h • A) ^ m) *ᵥ x) ≤ (1 / 4) * (x ⬝ᵥ x) := by
  obtain ⟨h, hpos, hh⟩ := exists_step_spectral_contraction A hA
  refine ⟨h, hpos, ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨1, le_rfl, fun x => by simp [dotProduct]⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set B : Matrix (Fin n) (Fin n) ℝ := 1 + h • A with hB
  set Bc : Matrix (Fin n) (Fin n) ℂ := B.map Complex.ofReal with hBc
  have hspec : ∀ z ∈ spectrum ℂ Bc, ‖z‖ < 1 := by
    intro z hz
    apply hh
    by_contra hne
    apply hz
    rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one]
    have hdet : IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) - Bc).det :=
      isUnit_iff_ne_zero.mpr hne
    exact (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  obtain ⟨m, hm1, hm2⟩ := exists_pow_norm_le_half Bc hspec
  refine ⟨m, hm1, fun x => ?_⟩
  apply real_quad_le_of_opNorm
  have : Bc ^ m = (B ^ m).map Complex.ofReal :=
    ((Complex.ofRealHom.mapMatrix).map_pow B m).symm
  rw [← this]
  exact hm2

/-- v2 prop:S (ii) / cor:recursion: for a Hurwitz matrix some power of the Euler step matrix
`1 + h A` is a Euclidean `1/2`-contraction. -/
theorem exists_power_contraction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsHurwitz A) :
    ∃ h : ℝ, 0 < h ∧ ∃ m : ℕ, 1 ≤ m ∧ ∀ x : Fin n → ℝ,
      Real.sqrt ((((1 + h • A) ^ m) *ᵥ x) ⬝ᵥ (((1 + h • A) ^ m) *ᵥ x)) ≤
        (1 / 2) * Real.sqrt (x ⬝ᵥ x) := by
  obtain ⟨h, hpos, m, hm, hx⟩ := exists_sq_contraction A hA
  refine ⟨h, hpos, m, hm, fun x => ?_⟩
  have h1 : Real.sqrt ((1 / 4) * (x ⬝ᵥ x)) = (1 / 2) * Real.sqrt (x ⬝ᵥ x) := by
    rw [Real.sqrt_mul (by norm_num)]
    congr 1
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← h1]
  exact Real.sqrt_le_sqrt (hx x)

/-- v2 prop:S (ii) / cor:recursion (Lyapunov certificate): a Hurwitz matrix admits a symmetric
`P ≽ 1` with `Aᵀ P + P A ≼ -c`. Route: Gelfand's formula (not Schur triangulation) gives a
contractive power of `1 + h A`, and `P = ∑_{k<m} (Bᵏ)ᵀ Bᵏ` with `B = 1 + h A`; `c = 3/(4h)`. -/
theorem exists_lyapunov_certificate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsHurwitz A) :
    ∃ (P : Matrix (Fin n) (Fin n) ℝ) (c : ℝ), 0 < c ∧ Pᵀ = P ∧
      (∀ x : Fin n → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ (P *ᵥ x)) ∧
      (∀ x : Fin n → ℝ, x ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x) ≤ -c * (x ⬝ᵥ x)) := by
  obtain ⟨h, hpos, m, hm, hx⟩ := exists_sq_contraction A hA
  set B : Matrix (Fin n) (Fin n) ℝ := 1 + h • A with hB
  set P := gramSum B m with hP
  have hsym : Pᵀ = P := gramSum_symm B m
  have hge : ∀ x : Fin n → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ (P *ᵥ x) := by
    intro x
    rw [hP, qf_gramSum]
    have h0 : (0 : ℕ) ∈ Finset.range m := Finset.mem_range.mpr hm
    have := Finset.single_le_sum (f := fun k => (B ^ k *ᵥ x) ⬝ᵥ (B ^ k *ᵥ x))
      (fun k _ => dot_self_nonneg' _) h0
    simpa using this
  refine ⟨P, 3 / (4 * h), by positivity, hsym, hge, fun x => ?_⟩
  have hstep := qf_gramSum_step B m x
  have hxm := hx x
  have hBx : B *ᵥ x = x + h • (A *ᵥ x) := by
    rw [hB, add_mulVec, one_mulVec, smul_mulVec]
  set u := A *ᵥ x with hu
  have hexp : (B *ᵥ x) ⬝ᵥ (P *ᵥ (B *ᵥ x)) =
      x ⬝ᵥ (P *ᵥ x) + h * (x ⬝ᵥ (P *ᵥ u)) + h * (u ⬝ᵥ (P *ᵥ x)) +
        h ^ 2 * (u ⬝ᵥ (P *ᵥ u)) := by
    rw [hBx]
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    ring
  have hsw : u ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ (P *ᵥ u) := qf_sym P hsym u x
  have hM : x ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x) = 2 * (x ⬝ᵥ (P *ᵥ u)) := by
    rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
      vecMul_transpose, ← hu, hsw]
    ring
  have hPu : 0 ≤ u ⬝ᵥ (P *ᵥ u) := (dot_self_nonneg' u).trans (by simpa using hge u)
  have hxx : 0 ≤ x ⬝ᵥ x := dot_self_nonneg' x
  have hkey : h * (x ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x)) ≤ -(3 / 4) * (x ⬝ᵥ x) := by
    rw [hM]
    nlinarith [mul_nonneg (sq_nonneg h) hPu]
  have : x ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x) ≤ -(3 / (4 * h)) * (x ⬝ᵥ x) := by
    have hh0 : h ≠ 0 := hpos.ne'
    have e : -(3 / (4 * h)) * (x ⬝ᵥ x) = (-(3 / 4) * (x ⬝ᵥ x)) / h := by
      field_simp
    rw [e, le_div_iff₀ hpos]
    linarith
  exact this

/-- v2 prop:S (ii) / cor:recursion (robustness): a certificate for `A` remains a certificate
(with `c/2`) for every entrywise `η`-perturbation of `A`. -/
theorem certificate_robust {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 < c)
    (hdec : ∀ x : Fin n → ℝ, x ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x) ≤ -c * (x ⬝ᵥ x)) :
    ∃ η : ℝ, 0 < η ∧ ∀ A' : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |A' i j - A i j| ≤ η) →
        ∀ x : Fin n → ℝ, x ⬝ᵥ ((A'ᵀ * P + P * A') *ᵥ x) ≤ -(c / 2) * (x ⬝ᵥ x) := by
  set ρ : ℝ := ∑ i, ∑ j, |P i j| with hρ
  have hρ0 : 0 ≤ ρ := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hcol : ∀ j, ∑ k, |P k j| ≤ ρ := fun j =>
    Finset.sum_le_sum fun k _ =>
      Finset.single_le_sum (f := fun j => |P k j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hrow : ∀ i, ∑ k, |P i k| ≤ ρ := fun i =>
    Finset.single_le_sum (f := fun i => ∑ k, |P i k|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hnρ : 0 ≤ (n : ℝ) * ρ := by positivity
  refine ⟨c / (4 * ((n : ℝ) * ρ + 1)), by positivity, fun A' hA' x => ?_⟩
  set η := c / (4 * ((n : ℝ) * ρ + 1)) with hη
  have hη0 : 0 ≤ η := by positivity
  set E := A' - A with hE
  have hEij : ∀ i j, |E i j| ≤ η := fun i j => hA' i j
  have hsplit : A'ᵀ * P + P * A' = (Aᵀ * P + P * A) + (Eᵀ * P + P * E) := by
    have : A' = A + E := by rw [hE]; abel
    rw [this]
    simp only [Matrix.transpose_add, add_mul, mul_add]
    abel
  have hent : ∀ i j, |(Eᵀ * P + P * E) i j| ≤ 2 * η * ρ := by
    intro i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
    have h1 : |∑ k, E k i * P k j| ≤ η * ρ := by
      calc |∑ k, E k i * P k j| ≤ ∑ k, |E k i * P k j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k, η * |P k j| := Finset.sum_le_sum fun k _ => by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hEij k i) (abs_nonneg _)
        _ = η * ∑ k, |P k j| := by rw [Finset.mul_sum]
        _ ≤ η * ρ := mul_le_mul_of_nonneg_left (hcol j) hη0
    have h2 : |∑ k, P i k * E k j| ≤ η * ρ := by
      calc |∑ k, P i k * E k j| ≤ ∑ k, |P i k * E k j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k, η * |P i k| := Finset.sum_le_sum fun k _ => by
            rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hEij k j) (abs_nonneg _)
        _ = η * ∑ k, |P i k| := by rw [Finset.mul_sum]
        _ ≤ η * ρ := mul_le_mul_of_nonneg_left (hrow i) hη0
    calc _ ≤ |∑ k, E k i * P k j| + |∑ k, P i k * E k j| := abs_add_le _ _
      _ ≤ 2 * η * ρ := by linarith
  have hq := quad_le_of_entries _ _ hent x
  have hxx : 0 ≤ x ⬝ᵥ x := dot_self_nonneg' x
  have hη' : (n : ℝ) * (2 * η * ρ) ≤ c / 2 := by
    have : (n : ℝ) * (2 * η * ρ) = c * (n * ρ) / (2 * (n * ρ + 1)) := by
      rw [hη]; field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  rw [hsplit, add_mulVec, dotProduct_add]
  have h3 := hdec x
  have h4 : (n : ℝ) * (2 * η * ρ) * (x ⬝ᵥ x) ≤ c / 2 * (x ⬝ᵥ x) :=
    mul_le_mul_of_nonneg_right hη' hxx
  nlinarith

end SparseSGD.Logistic.V2
