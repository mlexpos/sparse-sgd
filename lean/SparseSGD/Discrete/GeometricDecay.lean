import SparseSGD.Discrete.Algebra
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

open scoped Matrix.Norms.Operator

open Filter
open scoped Topology

namespace SparseSGD

/-- A contracting block of powers gives geometric decay along its multiples. -/
theorem power_block_decay {R : Type*} [NormedRing R] [NormOneClass R]
    (A : R) (m : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hblock : ‖A ^ m‖ ≤ c) (k : ℕ) :
    ‖A ^ (m * k)‖ ≤ c ^ k := by
  induction k with
  | zero =>
      rw [Nat.mul_zero, pow_zero, pow_zero, norm_one]
  | succ k ih =>
      rw [Nat.mul_succ, pow_add]
      calc
        ‖A ^ (m * k) * A ^ m‖ ≤ ‖A ^ (m * k)‖ * ‖A ^ m‖ := norm_mul_le _ _
        _ ≤ c ^ k * c := mul_le_mul ih hblock (norm_nonneg _) (pow_nonneg hc0 _)
        _ = c ^ (k + 1) := by rw [pow_succ]

/-- Convergence of powers supplies a strict contraction at some positive block length. -/
theorem power_has_contracting_block {R : Type*} [NormedRing R] [NormOneClass R]
    (A : R) (hA : Tendsto (fun n : ℕ => A ^ n) atTop (𝓝 0)) :
    ∃ m : ℕ, 0 < m ∧ ‖A ^ m‖ ≤ (1/2 : ℝ) := by
  have hn : Tendsto (fun n : ℕ => ‖A ^ n‖) atTop (𝓝 0) :=
    by
      simpa [Function.comp_def] using (continuous_norm.tendsto 0).comp hA
  have hevent := (Metric.tendsto_atTop.1 hn) (1/2) (by norm_num)
  obtain ⟨N, hN⟩ := hevent
  refine ⟨N + 1, by omega, ?_⟩
  have h := hN (N + 1) (by omega)
  have habs : |‖A ^ (N + 1)‖ - 0| < 1/2 := by simpa using h
  rw [sub_zero, abs_of_nonneg (norm_nonneg _)] at habs
  linarith

/-- A block contraction and bounds on the finitely many remainders give a bound
at every exponent, with the geometric factor indexed by the quotient. -/
theorem power_all_exponents_geometric {R : Type*} [NormedRing R] [NormOneClass R]
    (A : R) (m : ℕ) (hm : 0 < m) (C : ℝ) (hC : 0 ≤ C)
    (hrem : ∀ r < m, ‖A ^ r‖ ≤ C) (k : ℕ)
    (hblock : ‖A ^ m‖ ≤ (1/2 : ℝ)) :
    ‖A ^ k‖ ≤ C * (1/2 : ℝ) ^ (k / m) := by
  let q := k / m
  let r := k % m
  have hk : k = m * q + r := by simp [q, r, Nat.div_add_mod]
  have hr : r < m := Nat.mod_lt _ hm
  have hq : (m * q + r) / m = q := by rw [← hk]
  rw [hk, pow_add]
  have hp : A ^ (m * q) = (A ^ m) ^ q := by rw [pow_mul]
  rw [hp, hq]
  calc
    ‖(A ^ m) ^ q * A ^ r‖ ≤ ‖(A ^ m) ^ q‖ * ‖A ^ r‖ := norm_mul_le _ _
    _ ≤ (1/2 : ℝ) ^ q * C := by
      apply mul_le_mul
      · have h := power_block_decay A m (1/2) (by norm_num) hblock q
        simpa [pow_mul] using h
      · exact hrem r hr
      · exact norm_nonneg _
      · positivity
    _ = C * (1/2 : ℝ) ^ q := by ring

/-- Powers converging to zero admit a geometrically decaying subsequence of block powers. -/
theorem power_tendsto_zero_block_geometric {R : Type*} [NormedRing R] [NormOneClass R]
    (A : R) (hA : Tendsto (fun n : ℕ => A ^ n) atTop (𝓝 0)) :
    ∃ m : ℕ, 0 < m ∧ ∀ k : ℕ, ‖A ^ (m * k)‖ ≤ (1/2 : ℝ) ^ k := by
  obtain ⟨m, hm, hblock⟩ := power_has_contracting_block A hA
  refine ⟨m, hm, ?_⟩
  intro k
  exact power_block_decay A m (1/2) (by norm_num) hblock k

/-- Every exponent has a geometric norm bound once matrix powers tend to zero. -/
theorem matrix_power_geometric_bound (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : Tendsto (fun n : ℕ => A ^ n) atTop (𝓝 0)) :
    ∃ m : ℕ, 0 < m ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, ‖A ^ k‖ ≤ C * (1/2 : ℝ) ^ (k / m) := by
  obtain ⟨m, hm, hblock⟩ := power_has_contracting_block A hA
  let C : ℝ := ∑ r ∈ Finset.range m, ‖A ^ r‖
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun r _ => norm_nonneg _
  refine ⟨m, hm, C, hC, ?_⟩
  intro k
  apply power_all_exponents_geometric A m hm C hC ?_ k hblock
  intro r hr
  dsimp [C]
  exact Finset.single_le_sum (fun x _ => norm_nonneg (A ^ x)) (Finset.mem_range.mpr hr)

end SparseSGD
