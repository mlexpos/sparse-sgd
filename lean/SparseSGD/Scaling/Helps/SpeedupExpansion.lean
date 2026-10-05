import SparseSGD.Scaling.Helps.CubicRoots

/-!
# Small-`Δ` expansion of `r_c` and the speedup ratio (momentum-helps appendix)

Formalizes the analytic parts of `v2 lem:speedup`:

* (iii) the expansion `Γ(Δ,u) = 1 + (1-3u)Δ + O(Δ²)`, via an elementary real-root bracket
  `χ(-q + (c₃ ∓ 1)Δ³) ≶ 0` (no implicit function theorem), where
  `q(Δ) = 2(1-u)Δ + 2(1-u)(1-3u)Δ²` and `c₃(u) = 32u³-60u²+32u-4`;
* (iv) the dichotomy `u ≥ 1/3` (supremum `1`, not attained) versus `u < 1/3` (`Γ > 1` for small
  `Δ`);
* (ii), limit clause: `sup_Δ Γ(Δ,u) → 2` as `u → 0`.

Dependencies from `CubicRoots`: `speedupRatio_lt_two` (i), `speedupRatio_quarter` (ii),
`speedupRatio_lt_one` (iv, first sentence), `continuumPerronRate_eq_of_rightmost`.
-/

namespace SparseSGD.Scaling.Helps

open SparseSGD Filter Topology Set

noncomputable section

/-- `v2 lem:speedup (iii)`: the quadratic approximant `q(Δ) = 2(1-u)Δ + 2(1-u)(1-3u)Δ²` of
`r_c(Δ,u)`. -/
def expansionQ (Delta u : ℝ) : ℝ := 2*(1-u)*Delta + 2*(1-u)*(1-3*u)*Delta^2

/-- `v2 lem:speedup (iii)`: the cubic coefficient `c₃(u) = 32u³-60u²+32u-4`. -/
def expansionC3 (u : ℝ) : ℝ := 32*u^3 - 60*u^2 + 32*u - 4

/-- The polynomial `P(t,Δ,u) = χ(-q(Δ) + tΔ³; Δ, u)/Δ³`, written out in powers of `Δ`. -/
def bracketPoly (t D u : ℝ) : ℝ :=
  D^6*t^3 + D^5*(-18*t^2*u^2 + 24*t^2*u - 6*t^2)
  + D^4*(6*t^2*u - 6*t^2 + 108*t*u^4 - 288*t*u^3 + 264*t*u^2 - 96*t*u + 12*t)
  + D^3*(3*t^2 - 72*t*u^3 + 168*t*u^2 - 120*t*u + 24*t - 216*u^6 + 864*u^5 - 1368*u^4
      + 1088*u^3 - 456*u^2 + 96*u - 8)
  + D^2*(-24*t*u^2 + 24*t*u + 216*u^5 - 792*u^4 + 1104*u^3 - 720*u^2 + 216*u - 24)
  + D*(12*t*u - 8*t + 36*u^4 - 48*u^3 - 24*u^2 + 48*u - 12)
  + (2*t - 64*u^3 + 120*u^2 - 64*u + 8)

/-- `v2 lem:speedup (iii)`: the algebraic identity `χ(-q+tΔ³) = Δ³ P(t,Δ,u)`. -/
theorem spectrumPolynomial_bracket (t D u : ℝ) :
    spectrumPolynomial D u (-(expansionQ D u) + t*D^3) = D^3 * bracketPoly t D u := by
  unfold spectrumPolynomial expansionQ bracketPoly
  ring

/-- `v2 lem:speedup (iii)`: `P(t,0,u) = 2(t - c₃(u))`. -/
theorem bracketPoly_zero (t u : ℝ) : bracketPoly t 0 u = 2*(t - expansionC3 u) := by
  unfold bracketPoly expansionC3
  ring

theorem continuous_bracketPoly_D (t u : ℝ) : Continuous (fun D => bracketPoly t D u) := by
  unfold bracketPoly
  fun_prop

/-- **(X1)** `v2 lem:speedup (iii)`, real root bracket: for small `Δ>0`,
`χ(-q + (c₃-1)Δ³) < 0 < χ(-q + (c₃+1)Δ³)`. -/
theorem spectrumPolynomial_bracket_signs (u : ℝ) :
    ∃ δ > 0, ∀ D : ℝ, 0 < D → D < δ →
      spectrumPolynomial D u (-(expansionQ D u) + (expansionC3 u - 1)*D^3) < 0 ∧
      0 < spectrumPolynomial D u (-(expansionQ D u) + (expansionC3 u + 1)*D^3) := by
  have hlo : ∀ᶠ D in 𝓝 (0:ℝ), bracketPoly (expansionC3 u - 1) D u < 0 := by
    have hc := (continuous_bracketPoly_D (expansionC3 u - 1) u).continuousAt (x := 0)
    have h0 : bracketPoly (expansionC3 u - 1) 0 u = -2 := by
      rw [bracketPoly_zero]; ring
    exact hc.eventually (gt_mem_nhds (by show bracketPoly (expansionC3 u - 1) 0 u < 0; rw [h0]; norm_num))
  have hhi : ∀ᶠ D in 𝓝 (0:ℝ), 0 < bracketPoly (expansionC3 u + 1) D u := by
    have hc := (continuous_bracketPoly_D (expansionC3 u + 1) u).continuousAt (x := 0)
    have h0 : bracketPoly (expansionC3 u + 1) 0 u = 2 := by
      rw [bracketPoly_zero]; ring
    exact hc.eventually (lt_mem_nhds (by show 0 < bracketPoly (expansionC3 u + 1) 0 u; rw [h0]; norm_num))
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 (hlo.and hhi)
  refine ⟨ε, hε, fun D hD hDε => ?_⟩
  have hdist : dist D 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hD]; exact hDε
  obtain ⟨h1, h2⟩ := hεP hdist
  have hD3 : 0 < D^3 := by positivity
  rw [spectrumPolynomial_bracket, spectrumPolynomial_bracket]
  exact ⟨mul_neg_of_pos_of_neg hD3 h1, mul_pos hD3 h2⟩

/-- `v2 lem:speedup (iii)`: a real root of `χ` in the bracket, for small `Δ`, with `δ ≤ 1/20`. -/
theorem exists_bracket_root (u : ℝ) :
    ∃ δ > 0, δ ≤ 1/20 ∧ ∀ D : ℝ, 0 < D → D < δ →
      ∃ x : ℝ, -(expansionQ D u) + (expansionC3 u - 1)*D^3 < x ∧
        x < -(expansionQ D u) + (expansionC3 u + 1)*D^3 ∧ spectrumPolynomial D u x = 0 := by
  obtain ⟨δ, hδ, hsign⟩ := spectrumPolynomial_bracket_signs u
  refine ⟨min δ (1/20), lt_min hδ (by norm_num), min_le_right _ _, fun D hD hDδ => ?_⟩
  obtain ⟨hl, hh⟩ := hsign D hD (lt_of_lt_of_le hDδ (min_le_left _ _))
  have hD3 : 0 < D^3 := by positivity
  have hab : -(expansionQ D u) + (expansionC3 u - 1)*D^3 ≤
      -(expansionQ D u) + (expansionC3 u + 1)*D^3 := by nlinarith
  have hcont : ContinuousOn (spectrumPolynomial D u)
      (Icc (-(expansionQ D u) + (expansionC3 u - 1)*D^3)
        (-(expansionQ D u) + (expansionC3 u + 1)*D^3)) := by
    unfold spectrumPolynomial; fun_prop
  have := intermediate_value_Ioo hab hcont ⟨hl, hh⟩
  obtain ⟨x, hx, hx0⟩ := this
  exact ⟨x, hx.1, hx.2, hx0⟩

/-- `|c₃(u)| ≤ 128` on `[0,1]`. -/
theorem abs_expansionC3_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : |expansionC3 u| ≤ 128 := by
  unfold expansionC3
  have h2 : u^2 ≤ 1 := by nlinarith
  have h3 : u^3 ≤ 1 := by nlinarith [sq_nonneg u]
  have h2' : 0 ≤ u^2 := sq_nonneg u
  have h3' : 0 ≤ u^3 := by positivity
  rw [abs_le]; constructor <;> nlinarith

/-- **(X2, first half)** `v2 lem:speedup (iii)`: `|r_c(Δ,u) - q(Δ)| ≤ (|c₃(u)|+1)Δ³` for small
`Δ>0`, `u ∈ [0,1)`. -/
theorem continuumPerronRate_sub_expansionQ_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ δ > 0, ∀ D : ℝ, 0 < D → D < δ →
      |continuumPerronRate D u - expansionQ D u| ≤ (|expansionC3 u| + 1) * D^3 := by
  obtain ⟨δ, hδ, hδ20, hbr⟩ := exists_bracket_root u
  refine ⟨δ, hδ, fun D hD hDδ => ?_⟩
  obtain ⟨x, hxl, hxh, hxr⟩ := hbr D hD hDδ
  have hD20 : D ≤ 1/20 := by linarith
  have hD3 : 0 < D^3 := by positivity
  have hD2 : D^2 ≤ D/20 := by nlinarith
  have hDD3 : D^3 ≤ D/400 := by nlinarith [sq_nonneg D]
  have hc3 := abs_expansionC3_le hu0 hu1.le
  have hc3a := neg_abs_le (expansionC3 u)
  have hc3b := le_abs_self (expansionC3 u)
  have hK0 := abs_nonneg (expansionC3 u)
  have hxq1 : -((|expansionC3 u| + 1) * D^3) ≤ x + expansionQ D u := by
    have : (-(|expansionC3 u|) - 1) * D^3 ≤ (expansionC3 u - 1) * D^3 :=
      mul_le_mul_of_nonneg_right (by linarith) hD3.le
    nlinarith
  have hxq2 : x + expansionQ D u ≤ (|expansionC3 u| + 1) * D^3 := by
    have : (expansionC3 u + 1) * D^3 ≤ (|expansionC3 u| + 1) * D^3 :=
      mul_le_mul_of_nonneg_right (by linarith) hD3.le
    nlinarith
  -- `q ≤ 2Δ + 4Δ²`
  have hq : expansionQ D u ≤ 2*D + 4*D^2 := by
    unfold expansionQ
    have h1 : 2*(1-u)*D ≤ 2*D := by nlinarith
    have h2 : 2*(1-u)*(1-3*u)*D^2 ≤ 4*D^2 := by
      have : (1-u)*(1-3*u) ≤ 2 := by nlinarith
      nlinarith [sq_nonneg D]
    linarith
  have hxgt : -1/3 < x := by
    have h129 : (|expansionC3 u| + 1) * D^3 ≤ 129 * D^3 := by nlinarith
    nlinarith
  have hq3 : 0 < 3*x^2+6*x+2+4*D := by nlinarith [sq_nonneg x]
  have hrate := continuumPerronRate_eq_of_rightmost hxr (by linarith) hq3
  rw [hrate, abs_le]
  constructor <;> linarith

/-- `Γ - 1 - (1-3u)Δ = (r_c - q)/(2Δ(1-u))`. -/
theorem speedupRatio_sub_eq {D u : ℝ} (hD : D ≠ 0) (hu : u ≠ 1) :
    speedupRatio D u - 1 - (1-3*u)*D = (continuumPerronRate D u - expansionQ D u) /
      (2*D*(1-u)) := by
  have h1u : 1 - u ≠ 0 := sub_ne_zero.2 (Ne.symm hu)
  unfold speedupRatio expansionQ
  field_simp
  ring

/-- **(X2)** `v2 lem:speedup (iii)`: `|r_c - q| ≤ CΔ³` and `|Γ - 1 - (1-3u)Δ| ≤ CΔ²` for small
`Δ>0` (here for every `u ∈ [0,1)`, in particular for `u ∈ (0,1)`). -/
theorem speedup_expansion {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ D : ℝ, 0 < D → D < δ →
      |continuumPerronRate D u - expansionQ D u| ≤ C * D^3 ∧
      |speedupRatio D u - 1 - (1-3*u)*D| ≤ C * D^2 := by
  obtain ⟨δ, hδ, hb⟩ := continuumPerronRate_sub_expansionQ_le hu0 hu1
  have h1u : 0 < 1 - u := by linarith
  set K : ℝ := |expansionC3 u| + 1 with hK
  have hK1 : 1 ≤ K := by rw [hK]; linarith [abs_nonneg (expansionC3 u)]
  have hm : 0 < 1/(1-u) := by positivity
  refine ⟨K * (1 + 1/(1-u)), δ, by positivity, hδ, fun D hD hDδ => ⟨?_, ?_⟩⟩
  · refine (hb D hD hDδ).trans ?_
    have hD3 : 0 < D^3 := by positivity
    have : K * D^3 ≤ K * (1 + 1/(1-u)) * D^3 := by
      have : K * 1 ≤ K * (1 + 1/(1-u)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    exact this
  · rw [speedupRatio_sub_eq hD.ne' hu1.ne, abs_div]
    have hden : 0 < 2*D*(1-u) := by positivity
    rw [abs_of_pos hden, div_le_iff₀ hden]
    refine (hb D hD hDδ).trans ?_
    have hD2 : 0 < D^2 := by positivity
    have : 1/(1-u) * (1-u) = 1 := by field_simp
    have hkey : K * D^3 ≤ K * (1 + 1/(1-u)) * D^2 * (2*D*(1-u)) := by
      have e : K * (1 + 1/(1-u)) * D^2 * (2*D*(1-u)) =
          2*K*D^3*((1-u) + 1) := by
        field_simp
      rw [e]
      have : 0 < K * D^3 := by positivity
      nlinarith
    exact hkey

/-- **(X2, Asymptotics form)** `v2 lem:speedup (iii)`:
`Γ(Δ,u) = 1 + (1-3u)Δ + O(Δ²)` as `Δ → 0+`. -/
theorem speedupRatio_isBigO {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (fun D => speedupRatio D u - 1 - (1-3*u)*D) =O[𝓝[>] (0:ℝ)] (fun D => D^2) := by
  obtain ⟨C, δ, _, hδ, hb⟩ := speedup_expansion hu0 hu1
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with D hD
  have := (hb D hD.1 hD.2).2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg D)]
  exact this

/-- **(X3)** `v2 lem:speedup (iii)`: `Γ(Δ,u) → 1` as `Δ → 0+`. -/
theorem speedupRatio_tendsto_one {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Tendsto (fun D => speedupRatio D u) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hE := (speedupRatio_isBigO hu0 hu1).trans_tendsto
    (show Tendsto (fun D : ℝ => D^2) (𝓝[>] (0:ℝ)) (𝓝 0) by
      have : Tendsto (fun D : ℝ => D^2) (𝓝 (0:ℝ)) (𝓝 (0^2)) :=
        (continuous_pow 2).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds)
  have hL : Tendsto (fun D : ℝ => 1 + (1-3*u)*D) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have : Tendsto (fun D : ℝ => 1 + (1-3*u)*D) (𝓝 (0:ℝ)) (𝓝 (1 + (1-3*u)*0)) :=
      (by fun_prop : Continuous fun D : ℝ => 1 + (1-3*u)*D).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have := hL.add hE
  simp only [add_zero] at this
  refine this.congr (fun D => ?_)
  ring

/-- **(X4, first half)** `v2 lem:speedup (iv)`: for `1/3 ≤ u < 1`,
`sup_{Δ>0} Γ(Δ,u) = 1` (not attained, by `speedupRatio_lt_one`). -/
theorem sSup_speedupRatio_eq_one {u : ℝ} (hu0 : 1/3 ≤ u) (hu1 : u < 1) :
    sSup ((fun D => speedupRatio D u) '' Ioi (0:ℝ)) = 1 := by
  have hne : ((fun D => speedupRatio D u) '' Ioi (0:ℝ)).Nonempty := ⟨_, 1, by simp, rfl⟩
  apply le_antisymm
  · refine csSup_le hne ?_
    rintro _ ⟨D, hD, rfl⟩
    exact (speedupRatio_lt_one hD hu0 hu1).le
  · have hbdd : BddAbove ((fun D => speedupRatio D u) '' Ioi (0:ℝ)) := ⟨1, by
      rintro _ ⟨D, hD, rfl⟩
      exact (speedupRatio_lt_one hD hu0 hu1).le⟩
    refine le_of_tendsto (speedupRatio_tendsto_one (show (0:ℝ) ≤ u by linarith) hu1) ?_
    filter_upwards [self_mem_nhdsWithin] with D hD
    exact le_csSup hbdd ⟨D, hD, rfl⟩

/-- **(X4, second half)** `v2 lem:speedup (iv)`: for `0 < u < 1/3`, `Γ(Δ,u) > 1` for all
sufficiently small `Δ>0`. -/
theorem speedupRatio_gt_one_eventually {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1/3) :
    ∀ᶠ D in 𝓝[>] (0:ℝ), 1 < speedupRatio D u := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := speedup_expansion hu0.le (by linarith)
  have hs : 0 < 1 - 3*u := by linarith
  have hδ' : 0 < min δ ((1-3*u)/(2*C)) := lt_min hδ (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ'] with D hD
  have hD0 : 0 < D := hD.1
  have hDδ : D < δ := lt_of_lt_of_le hD.2 (min_le_left _ _)
  have hDc : D < (1-3*u)/(2*C) := lt_of_lt_of_le hD.2 (min_le_right _ _)
  have hCD : C * D < (1-3*u)/2 := by
    have := (lt_div_iff₀ (by positivity : 0 < 2*C)).1 hDc
    nlinarith
  have h := (abs_le.1 (hb D hD0 hDδ).2).1
  have : C * D^2 < (1-3*u)/2 * D := by nlinarith
  nlinarith

/-- **(X5)** `v2 lem:speedup (ii)`, limit clause: `sup_{Δ>0} Γ(Δ,u) → 2` as `u → 0+`.
The squeeze uses `Γ(1/4,u) = 2/(1+a+a²)` with `a = u^{1/3}` (lower bound) and `Γ < 2`
(upper bound). -/
theorem tendsto_sSup_speedupRatio_zero :
    Tendsto (fun u : ℝ => sSup ((fun D => speedupRatio D u) '' Ioi (0:ℝ)))
      (𝓝[Ioo 0 1] (0:ℝ)) (𝓝 2) := by
  have hlow : Tendsto (fun u : ℝ => 2 / (1 + u^((1/3 : ℝ)) + (u^((1/3 : ℝ)))^2))
      (𝓝[Ioo 0 1] (0:ℝ)) (𝓝 2) := by
    have hc : ContinuousAt (fun u : ℝ => u^((1/3 : ℝ))) 0 :=
      Real.continuousAt_rpow_const 0 (1/3) (Or.inr (by norm_num))
    have h0 : Tendsto (fun u : ℝ => u^((1/3 : ℝ))) (𝓝 0) (𝓝 0) := by
      have := hc.tendsto
      simpa [Real.zero_rpow (by norm_num : (1/3 : ℝ) ≠ 0)] using this
    have hden : Tendsto (fun u : ℝ => 1 + u^((1/3 : ℝ)) + (u^((1/3 : ℝ)))^2) (𝓝 0) (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1:ℝ))).add h0 |>.add (h0.pow 2)
      simpa using this
    have h := (tendsto_const_nhds (x := (2:ℝ))).div hden (by norm_num)
    rw [show (2:ℝ) / 1 = 2 by norm_num] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with u hu
    rw [← speedupRatio_quarter hu.1 hu.2]
    have hbdd : BddAbove ((fun D => speedupRatio D u) '' Ioi (0:ℝ)) := ⟨2, by
      rintro _ ⟨D, hD, rfl⟩
      exact (speedupRatio_lt_two hD hu.1 hu.2).le⟩
    exact le_csSup hbdd ⟨1/4, by norm_num, rfl⟩
  · filter_upwards [self_mem_nhdsWithin] with u hu
    refine csSup_le ⟨_, 1, by simp, rfl⟩ ?_
    rintro _ ⟨D, hD, rfl⟩
    exact (speedupRatio_lt_two hD hu.1 hu.2).le

end
end SparseSGD.Scaling.Helps
