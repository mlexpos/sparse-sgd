import SparseSGD.Scaling.Helps.ExactRate
import SparseSGD.Probability.LeastSquares.Model

/-!
# A decaying learning rate (momentum-helps appendix, `rem:schedule`)

Paper label: `rem:schedule`.

* (Q1) `chung_tendsto`: a Chung-type sequence lemma. If `a (k+1) = (1 - c/k + r k) a k + D/k^2`
  with `c > 1` and `|r k| <= M/k^2` for `k >= k0`, then `k a k -> D/(c-1)`.
  The proof is the standard absorbing-set argument on `y_k = k a_k - D/(c-1)`
  (`chung_abstract`), using only the divergence of the harmonic series.
* (Q2) `schedule_step_R`: at `beta = 0` and `eta_k = 1/(p k)` the `R`-coordinate of the step map
  is `(1 - 2/k + K/k^2) R + varsigma^2 d/(B p k^2)`, `K = (d+2-p)/(B p) + 1`.
* (Q3) `schedule_risk_asymptotic`: along the scheduled moment recursion,
  `k R_k -> varsigma^2 d/(B p)`, i.e. `R_k N_k -> varsigma^2 d` for `N_k = B p k`.

Not formalized: the numerical check `R_k N_k/(varsigma^2 d) = 1.0028` quoted in the remark, and
the closing sentence about the Cramer-Rao bound and minimax risk.
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD Filter Topology

noncomputable section

/-! ### Q1: the Chung-type lemma -/

/-- Harmonic-type divergence used in `chung_abstract`: `sum_{i<n} 1/(i+1) -> infinity`. -/
private theorem harmonic_unbounded (T : ℝ) : ∃ n : ℕ, T ≤ ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) :=
  (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_ge_atTop T).exists

/-- Abstract Chung step (`rem:schedule`): if `|y (k+1)| <= (1 - gamma/k)|y k| + F/k^2`
eventually, with `gamma > 0`, then `y -> 0`. -/
theorem chung_abstract {γ F : ℝ} (hγ : 0 < γ) (k1 : ℕ) (y : ℕ → ℝ)
    (hy : ∀ k : ℕ, k1 ≤ k → |y (k + 1)| ≤ (1 - γ / k) * |y k| + F / (k : ℝ) ^ 2) :
    Tendsto y atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e : ℝ := ε / 2 with he
  have he0 : 0 < e := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (γ + 2 * |F| / (γ * e) + 1)
  set K0 : ℕ := N + k1 + 1 with hK0
  have hK0N : (N : ℝ) ≤ K0 := by
    rw [hK0]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) k1]
  have hK0pos : (1 : ℝ) ≤ K0 := by
    rw [hK0]; push_cast
    linarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) k1]
  have hK0gt : γ + 2 * |F| / (γ * e) < K0 := by linarith
  -- uniform facts for k >= K0
  have hfact : ∀ k : ℕ, K0 ≤ k →
      (1 : ℝ) ≤ k ∧ γ ≤ k ∧ k1 ≤ k ∧ F / (k : ℝ) ^ 2 ≤ γ * e / (2 * k) := by
    intro k hk
    have hkR : (K0 : ℝ) ≤ k := by exact_mod_cast hk
    have hk1 : (1 : ℝ) ≤ k := le_trans hK0pos hkR
    have hkpos : (0 : ℝ) < k := by linarith
    have hkγ : γ ≤ k := by
      have : 0 ≤ 2 * |F| / (γ * e) := by positivity
      linarith
    have hk1' : k1 ≤ k := by
      have : k1 ≤ K0 := by omega
      omega
    refine ⟨hk1, hkγ, hk1', ?_⟩
    have h2 : 2 * |F| / (γ * e) ≤ k := by
      have : 0 ≤ γ := hγ.le
      linarith
    have h3 : 2 * |F| ≤ k * (γ * e) := by
      rw [div_le_iff₀ (by positivity)] at h2; exact h2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : F ≤ |F| := le_abs_self F
    nlinarith [mul_pos hγ he0, hkpos, mul_pos (mul_pos hγ he0) hkpos]
  -- absorbing and decreasing steps
  have hstep_abs : ∀ k : ℕ, K0 ≤ k → |y k| ≤ e → |y (k + 1)| ≤ e := by
    intro k hk hyk
    obtain ⟨hk1, hkγ, hk1', hFk⟩ := hfact k hk
    have hkpos : (0 : ℝ) < k := by linarith
    have h := hy k hk1'
    have h0 : 0 ≤ 1 - γ / k := by
      rw [sub_nonneg, div_le_one hkpos]; exact hkγ
    have h4 : (1 - γ / k) * |y k| ≤ (1 - γ / k) * e := mul_le_mul_of_nonneg_left hyk h0
    have h5 : γ * e / (2 * k) = γ * e / k / 2 := by field_simp
    have h6 : (1 - γ / k) * e = e - γ * e / k := by ring
    have h7 : 0 ≤ γ * e / k := by positivity
    linarith
  have hstep_dec : ∀ k : ℕ, K0 ≤ k → e < |y k| →
      |y (k + 1)| ≤ |y k| - γ * e / (2 * k) := by
    intro k hk hyk
    obtain ⟨hk1, hkγ, hk1', hFk⟩ := hfact k hk
    have hkpos : (0 : ℝ) < k := by linarith
    have h := hy k hk1'
    have h4 : γ * e / k ≤ γ / k * |y k| := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hkpos]
      exact mul_le_mul_of_nonneg_left hyk.le hγ.le
    have h5 : γ * e / (2 * k) = γ * e / k / 2 := by field_simp
    have h6 : (1 - γ / k) * |y k| = |y k| - γ / k * |y k| := by ring
    linarith
  -- some index above K0 is inside the ball
  have hexists : ∃ m : ℕ, K0 ≤ m ∧ |y m| ≤ e := by
    by_contra hcon
    push Not at hcon
    have hdec : ∀ n : ℕ, |y (K0 + n)| ≤ |y K0| -
        (γ * e / (2 * K0)) * ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hlt : e < |y (K0 + n)| := hcon _ (by omega)
        have h := hstep_dec (K0 + n) (by omega) hlt
        have hcast : ((K0 + n : ℕ) : ℝ) = K0 + n := by push_cast; ring
        rw [hcast] at h
        have hpos1 : (0 : ℝ) < K0 + n := by
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith
        have hle : (γ * e / (2 * K0)) * (1 / ((n : ℝ) + 1)) ≤ γ * e / (2 * (K0 + n)) := by
          rw [mul_one_div, div_div, div_le_div_iff_of_pos_left (by positivity) (by positivity)
            (by positivity)]
          have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith
        rw [show K0 + (n + 1) = K0 + n + 1 by ring, Finset.sum_range_succ, mul_add]
        have : K0 + n + 1 = K0 + (n + 1) := by ring
        linarith
    obtain ⟨n, hn⟩ := harmonic_unbounded (2 * K0 * (|y K0| + 1) / (γ * e))
    have h1 := hdec n
    have h2 : (γ * e / (2 * K0)) * (2 * K0 * (|y K0| + 1) / (γ * e)) = |y K0| + 1 := by
      field_simp
    have h3 : (γ * e / (2 * K0)) * (2 * K0 * (|y K0| + 1) / (γ * e)) ≤
        (γ * e / (2 * K0)) * ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    have h4 : 0 ≤ |y (K0 + n)| := abs_nonneg _
    linarith
  obtain ⟨m, hm, hym⟩ := hexists
  have habs : ∀ n : ℕ, |y (m + n)| ≤ e := by
    intro n
    induction n with
    | zero => simpa using hym
    | succ n ih => exact hstep_abs (m + n) (by omega) ih
  refine ⟨m, fun j hj => ?_⟩
  have := habs (j - m)
  rw [show m + (j - m) = j by omega] at this
  rw [Real.dist_eq, sub_zero]
  linarith

/-- (Q1) `rem:schedule`: a sequence with `a (k+1) = (1 - c/k + r k) a k + D/k^2` for `k >= k0`,
`c > 1` and `|r k| <= M/k^2`, satisfies `k a k -> D/(c-1)`. -/
theorem chung_tendsto {c D M : ℝ} (hc : 1 < c) (hM : 0 ≤ M) {k0 : ℕ} (hk0 : 1 ≤ k0)
    (a r : ℕ → ℝ) (hr : ∀ k : ℕ, k0 ≤ k → |r k| ≤ M / (k : ℝ) ^ 2)
    (ha : ∀ k : ℕ, k0 ≤ k → a (k + 1) = (1 - c / k + r k) * a k + D / (k : ℝ) ^ 2) :
    Tendsto (fun k : ℕ => (k : ℝ) * a k) atTop (𝓝 (D / (c - 1))) := by
  have hc1 : c - 1 ≠ 0 := by linarith
  obtain ⟨L, rfl⟩ : ∃ L, D = L * (c - 1) := ⟨D / (c - 1), by field_simp⟩
  rw [mul_div_cancel_right₀ _ hc1]
  set E : ℝ := c + 2 * M with hE
  set F : ℝ := |L| * E + |L * (c - 1)| with hF
  obtain ⟨K1, hK1⟩ := exists_nat_gt (max (k0 : ℝ) (max c (2 * E / (c - 1))))
  have hK1a : (k0 : ℝ) < K1 := lt_of_le_of_lt (le_max_left _ _) hK1
  have hK1b : c < K1 :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hK1
  have hK1c : 2 * E / (c - 1) < K1 :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hK1
  have hlim : Tendsto (fun k : ℕ => (k : ℝ) * a k - L) atTop (𝓝 0) := by
    refine chung_abstract (γ := (c - 1) / 2) (F := F) (by linarith) K1 _ ?_
    intro k hk
    have hkR : (K1 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0R : (k0 : ℝ) ≤ k := by linarith
    have hk0' : k0 ≤ k := by exact_mod_cast hk0R
    have hkpos : (0 : ℝ) < k := by
      have : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
      linarith
    have hk1 : (1 : ℝ) ≤ k := by
      have : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
      linarith
    have hkc : c < k := by linarith
    have hkE : 2 * E / (c - 1) < k := by linarith
    -- the error terms
    set e : ℝ := -c / (k : ℝ) ^ 2 + r k * ((k + 1) / k) with hed
    have hrk := hr k hk0'
    have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    have hratio : (k + 1) / (k : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hkpos]; linarith
    have hratio0 : 0 ≤ ((k : ℝ) + 1) / k := by positivity
    have he : |e| ≤ E / (k : ℝ) ^ 2 := by
      have h1 : |r k * ((k + 1) / k)| ≤ 2 * M / (k : ℝ) ^ 2 := by
        rw [abs_mul, abs_of_nonneg hratio0]
        calc |r k| * ((k + 1) / k) ≤ (M / (k : ℝ) ^ 2) * 2 :=
              mul_le_mul hrk hratio (by exact hratio0) (by positivity)
          _ = 2 * M / (k : ℝ) ^ 2 := by ring
      have h2 : |-c / (k : ℝ) ^ 2| = c / (k : ℝ) ^ 2 := by
        rw [abs_div, abs_neg, abs_of_pos (by linarith), abs_of_pos hk2]
      calc |e| ≤ |-c / (k : ℝ) ^ 2| + |r k * ((k + 1) / k)| := abs_add_le _ _
        _ ≤ c / (k : ℝ) ^ 2 + 2 * M / (k : ℝ) ^ 2 := by rw [h2]; linarith
        _ = E / (k : ℝ) ^ 2 := by rw [hE]; ring
    -- the exact recursion for y
    have hrec : ((k + 1 : ℕ) : ℝ) * a (k + 1) - L =
        (1 - (c - 1) / k + e) * ((k : ℝ) * a k - L) + (L * e + L * (c - 1) / (k : ℝ) ^ 2) := by
      rw [ha k hk0']
      push_cast
      rw [hed]
      field_simp
      ring
    have hf : |L * e + L * (c - 1) / (k : ℝ) ^ 2| ≤ F / (k : ℝ) ^ 2 := by
      calc |L * e + L * (c - 1) / (k : ℝ) ^ 2|
          ≤ |L * e| + |L * (c - 1) / (k : ℝ) ^ 2| := abs_add_le _ _
        _ ≤ |L| * (E / (k : ℝ) ^ 2) + |L * (c - 1)| / (k : ℝ) ^ 2 := by
            rw [abs_mul, abs_div, abs_of_pos hk2]
            exact add_le_add (mul_le_mul_of_nonneg_left he (abs_nonneg _)) le_rfl
        _ = F / (k : ℝ) ^ 2 := by rw [hF]; ring
    have hg : 0 ≤ 1 - (c - 1) / (k : ℝ) := by
      rw [sub_nonneg, div_le_one hkpos]; linarith
    have hE0 : 0 < E := by rw [hE]; linarith
    have hcoef : |1 - (c - 1) / (k : ℝ) + e| ≤ 1 - ((c - 1) / 2) / k := by
      have h1 : |1 - (c - 1) / (k : ℝ) + e| ≤ (1 - (c - 1) / k) + E / (k : ℝ) ^ 2 :=
        (abs_add_le _ _).trans (by rw [abs_of_nonneg hg]; exact add_le_add le_rfl he)
      have h2 : E / (k : ℝ) ^ 2 ≤ ((c - 1) / 2) / k := by
        have h3 : 2 * E ≤ (c - 1) * k := by
          rw [div_lt_iff₀ (by linarith)] at hkE; linarith
        rw [div_le_div_iff₀ hk2 hkpos]
        nlinarith
      have h4 : (c - 1) / (k : ℝ) = 2 * (((c - 1) / 2) / k) := by ring
      linarith
    rw [hrec]
    calc |(1 - (c - 1) / k + e) * ((k : ℝ) * a k - L) + (L * e + L * (c - 1) / (k : ℝ) ^ 2)|
        ≤ |(1 - (c - 1) / k + e) * ((k : ℝ) * a k - L)| +
          |L * e + L * (c - 1) / (k : ℝ) ^ 2| := abs_add_le _ _
      _ ≤ (1 - ((c - 1) / 2) / k) * |(k : ℝ) * a k - L| + F / (k : ℝ) ^ 2 := by
          rw [abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)) hf
  have := hlim.add_const L
  simpa using this

/-! ### Q2: the scheduled step at `beta = 0` -/

open SparseSGD.Probability.LeastSquares in
/-- (Q2) `rem:schedule`: at `beta = 0`, `eta_k = 1/(p k)`,
`R_{k+1} = (1 - 2/k + K/k^2) R_k + varsigma^2 d/(B p k^2)` with `K = (d+2-p)/(B p) + 1`.
Equivalently `w_k = 1/k`, `u_{n,k} = (d+2-p)/(2 B p k)`, `varphi_k = varsigma^2 d/(2 B p k)`. -/
theorem schedule_step_R (d B : ℕ) (p : unitInterval) (ν : MeasureTheory.Measure ℝ)
    (hp : (p : ℝ) ≠ 0) (hB : 0 < B) (k : ℕ) (hk : 1 ≤ k) (s : Moments) :
    ((params d B p ν 0 (1 / ((p : ℝ) * k))).step s).R =
      (1 - 2 / (k : ℝ) + (((d : ℝ) + 2 - p) / (B * p) + 1) / (k : ℝ) ^ 2) * s.R +
        labelVariance ν * d / (B * p * (k : ℝ) ^ 2) := by
  have hk' : (k : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  rw [params_explicit p hp]
  simp only [Params.step, Params.eps]
  field_simp
  ring

open SparseSGD.Probability.LeastSquares in
/-- (Q2, coordinates) `rem:schedule`: the parameters at `eta_k = 1/(p k)`, `beta = 0`. -/
theorem schedule_params (d B : ℕ) (p : unitInterval) (ν : MeasureTheory.Measure ℝ)
    (hp : (p : ℝ) ≠ 0) (hB : 0 < B) (k : ℕ) (hk : 1 ≤ k) :
    (params d B p ν 0 (1 / ((p : ℝ) * k))).w = 1 / k ∧
    (params d B p ν 0 (1 / ((p : ℝ) * k))).noise = ((d : ℝ) + 2 - p) / (2 * B * p * k) ∧
    (params d B p ν 0 (1 / ((p : ℝ) * k))).additive =
      labelVariance ν * d / (2 * B * p * k) := by
  have hk' : (k : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  rw [params_explicit p hp]
  refine ⟨?_, ?_, ?_⟩ <;> simp only <;> field_simp <;> first | done | norm_num

/-! ### Q3: the asymptotic risk -/

open SparseSGD.Probability.LeastSquares in
/-- (Q3) `rem:schedule`: along the scheduled recursion `s (k+1) = step_k (s k)` for `k >= k0 >= 1`
at `beta = 0`, `eta_k = 1/(p k)`, one has `k R_k -> varsigma^2 d/(B p)`, i.e.
`R_k N_k -> varsigma^2 d` for `N_k = B p k`.  The numerical check and the Cramer-Rao/minimax
sentence of the remark are not formalized. -/
theorem schedule_risk_asymptotic (d B : ℕ) (p : unitInterval) (ν : MeasureTheory.Measure ℝ)
    (hp : (p : ℝ) ≠ 0) (hB : 0 < B) {k0 : ℕ} (hk0 : 1 ≤ k0) (s : ℕ → Moments)
    (hs : ∀ k : ℕ, k0 ≤ k → s (k + 1) = (params d B p ν 0 (1 / ((p : ℝ) * k))).step (s k)) :
    Tendsto (fun k : ℕ => (k : ℝ) * (s k).R) atTop
      (𝓝 (labelVariance ν * d / (B * p))) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hppos : (0 : ℝ) < p := lt_of_le_of_ne p.2.1 (Ne.symm hp)
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  set K : ℝ := ((d : ℝ) + 2 - p) / (B * p) + 1 with hK
  have hK0 : 0 ≤ K := by
    have : (0 : ℝ) ≤ (d : ℝ) + 2 - p := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    rw [hK]; positivity
  have h := chung_tendsto (c := 2) (D := labelVariance ν * d / (B * p)) (M := K)
    (by norm_num) hK0 hk0 (fun k => (s k).R) (fun k => K / (k : ℝ) ^ 2)
    (fun k hk => by
      have : 0 ≤ K / (k : ℝ) ^ 2 := by positivity
      rw [abs_of_nonneg this])
    (fun k hk => by
      have hk1 : 1 ≤ k := le_trans hk0 hk
      have := schedule_step_R d B p ν hp hB k hk1 (s k)
      rw [hs k hk, this]
      ring)
  have e2 : labelVariance ν * d / (B * p) / (2 - 1) = labelVariance ν * d / (B * p) := by
    norm_num
  rw [e2] at h
  exact h

end

end SparseSGD.Scaling.Helps
