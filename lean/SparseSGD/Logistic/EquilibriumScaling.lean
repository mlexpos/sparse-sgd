import SparseSGD.Logistic.EquilibriumAnalysis
import SparseSGD.Logistic.FixedPointAsymptotics
import SparseSGD.Scaling.IntegerFamilies

open Filter Topology
namespace SparseSGD.Logistic
noncomputable section

/-- An actual natural batch family and a real power-law learning rate. -/
def familyPhi (eta alpha : ℝ) (B : ℕ → ℕ) (d : ℕ) : ℝ :=
  logisticPhi d (B d) (eta*(d : ℝ)^(-alpha))

theorem familyPhi_ratio_tendsto (eta alpha sigma scale : ℝ) (B : ℕ → ℕ)
    (hs : 0 < scale) (hB : ∀ d, 0 < B d)
    (hbatch : Tendsto (fun d : ℕ => (B d : ℝ)/(d : ℝ)^sigma) atTop (𝓝 scale)) :
    Tendsto (fun d : ℕ => familyPhi eta alpha B d/(d : ℝ)^(1-sigma-alpha))
      atTop (𝓝 (eta/(2*scale))) := by
  have hnum : Tendsto (fun d : ℕ => 1-1/(d : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hh := (hnum.div hbatch hs.ne').const_mul (eta/2)
  have hh' : Tendsto (fun d : ℕ => eta/2*((1-1/(d : ℝ))/((B d : ℝ)/(d : ℝ)^sigma)))
      atTop (𝓝 (eta/(2*scale))) := by convert hh using 1 <;> ring
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hBd : (B d : ℝ) ≠ 0 := by exact_mod_cast (hB d).ne'
  have he : (d : ℝ)^(1-sigma-alpha)*(d : ℝ)^sigma = (d : ℝ)^(-alpha)*(d : ℝ) := by
    rw [← Real.rpow_add hdR, show 1-sigma-alpha+sigma=(-alpha)+1 by ring,Real.rpow_add hdR,Real.rpow_one]
  unfold familyPhi logisticPhi
  field_simp
  linear_combination eta*((d : ℝ)-1)*he

theorem integerBatch_power_ratio (scale sigma : ℝ) (hs : 0 < scale) (hsigma : 0 < sigma) :
    Tendsto (fun d : ℕ => (SparseSGD.Scaling.integerBatch scale sigma d : ℝ)/(d : ℝ)^sigma)
      atTop (𝓝 scale) := by
  have h := (SparseSGD.Scaling.integerBatch_ratio_tendsto scale sigma hs hsigma).const_mul scale
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  field_simp

theorem familyPhi_integerBatch_ratio (eta alpha sigma scale : ℝ)
    (hs : 0 < scale) (hsigma : 0 < sigma) :
    Tendsto (fun d : ℕ => familyPhi eta alpha (SparseSGD.Scaling.integerBatch scale sigma) d/
      (d : ℝ)^(1-sigma-alpha)) atTop (𝓝 (eta/(2*scale))) :=
  familyPhi_ratio_tendsto eta alpha sigma scale _ hs
    (SparseSGD.Scaling.integerBatch_pos scale sigma) (integerBatch_power_ratio scale sigma hs hsigma)

/-- Corrected source D(v): bounded loads supply a uniform positive comparison
constant, even when the signal norm itself varies with dimension. -/
theorem equilibriumBulk_family_comparable (eta alpha sigma scale P : ℝ)
    (B : ℕ → ℕ) (r : ℕ → ℝ) (heta : 0 < eta) (hs : 0 < scale)
    (hB : ∀ d, 0 < B d) (hr : ∀ d, 0 < r d)
    (hbatch : Tendsto (fun d : ℕ => (B d : ℝ)/(d : ℝ)^sigma) atTop (𝓝 scale))
    (hcap : ∀ᶠ d : ℕ in atTop, familyPhi eta alpha B d ≤ P) :
    ∃ c > 0, ∃ C > 0, ∀ᶠ d : ℕ in atTop,
      c*(d : ℝ)^(1-sigma-alpha) ≤ equilibriumBulk (r d) (familyPhi eta alpha B d) ∧
      equilibriumBulk (r d) (familyPhi eta alpha B d) ≤ C*(d : ℝ)^(1-sigma-alpha) := by
  let L := eta/(2*scale)
  have hL : 0 < L := by dsimp [L]; positivity
  have hlim := familyPhi_ratio_tendsto eta alpha sigma scale B hs hB hbatch
  have hevent : ∀ᶠ d : ℕ in atTop,
      familyPhi eta alpha B d/(d : ℝ)^(1-sigma-alpha) ∈ Set.Icc (L/2) (2*L) :=
    hlim.eventually (Icc_mem_nhds (by change L/2<L; linarith) (by change L<2*L; linarith))
  refine ⟨L/2/Real.exp (P/2),by positivity,2*L,by positivity,?_⟩
  filter_upwards [hevent,hcap,eventually_ge_atTop (1 : ℕ)] with d hd hcap hd1
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
  have hpow := Real.rpow_pos_of_pos hdR (1-sigma-alpha)
  have hPhi : 0 ≤ familyPhi eta alpha B d := logisticPhi_nonneg _ _ _ hd1 (by positivity)
  obtain ⟨hrootpos,hroot⟩ := positiveRoot_spec (r d) (familyPhi eta alpha B d) (hr d) hPhi
  have hb := bulk_bounds_of_phi_le (r d) (familyPhi eta alpha B d)
    (positiveRoot (r d) (familyPhi eta alpha B d)) P (hr d) hPhi hrootpos hroot hcap
  have hlo := (le_div_iff₀ hpow).mp hd.1
  have hup := (div_le_iff₀ hpow).mp hd.2
  constructor
  · apply le_trans _ hb.1
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    field_simp
    nlinarith [hlo]
  · exact hb.2.trans hup

theorem equilibriumBulk_integerBatch_comparable (eta alpha sigma scale P : ℝ)
    (r : ℕ → ℝ) (heta : 0 < eta) (hs : 0 < scale) (hsigma : 0 < sigma)
    (hr : ∀ d, 0 < r d)
    (hcap : ∀ᶠ d : ℕ in atTop,
      familyPhi eta alpha (SparseSGD.Scaling.integerBatch scale sigma) d ≤ P) :
    ∃ c > 0, ∃ C > 0, ∀ᶠ d : ℕ in atTop,
      c*(d : ℝ)^(1-sigma-alpha) ≤
        equilibriumBulk (r d) (familyPhi eta alpha (SparseSGD.Scaling.integerBatch scale sigma) d) ∧
      equilibriumBulk (r d) (familyPhi eta alpha (SparseSGD.Scaling.integerBatch scale sigma) d) ≤
        C*(d : ℝ)^(1-sigma-alpha) :=
  equilibriumBulk_family_comparable eta alpha sigma scale P _ r heta hs
    (SparseSGD.Scaling.integerBatch_pos scale sigma) hr
    (integerBatch_power_ratio scale sigma hs hsigma) hcap

theorem equilibriumBulk_fixedBatch_comparable (eta alpha P : ℝ) (B : ℕ)
    (r : ℕ → ℝ) (heta : 0 < eta) (hB : 0 < B) (hr : ∀ d, 0 < r d)
    (hcap : ∀ᶠ d : ℕ in atTop, familyPhi eta alpha (fun _ => B) d ≤ P) :
    ∃ c > 0, ∃ C > 0, ∀ᶠ d : ℕ in atTop,
      c*(d : ℝ)^(1-alpha) ≤ equilibriumBulk (r d) (familyPhi eta alpha (fun _ => B) d) ∧
      equilibriumBulk (r d) (familyPhi eta alpha (fun _ => B) d) ≤ C*(d : ℝ)^(1-alpha) := by
  have h := equilibriumBulk_family_comparable eta alpha 0 (B : ℝ) P (fun _ => B) r
    heta (by exact_mod_cast hB) (fun _ => hB) hr (by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (B : ℝ)) atTop (𝓝 (B : ℝ)))) hcap
  simpa using h

end
end SparseSGD.Logistic
