import SparseSGD.Logistic.FluidCells
import SparseSGD.Logistic.SlowLimitGlobalExistence
import SparseSGD.Logistic.DynamicGlobal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 2800000

/-- Actual cold-start fluid limit in cells 3 and 4 on every fixed finite min-clock horizon. Both ODE existence and actual stochastic containment are proved. -/
theorem cor_fluid_cells_three_four
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : ∀ n, SparseSGD.External.GaussianSteinCertificate n)
    (B : ℕ → ℕ)
    (F : ∀ d, SparseSGD.External.MartingaleBernsteinCertificate (World d (B d)))
    (eta beta : ℕ → ℝ) (p : ℕ → unitInterval) (mu : ∀ d, Vec d) (N : ℕ → ℕ)
    (teacherNorm delta Phi T q : ℝ)
    (hr : 0 < teacherNorm) (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) (hT : 0 ≤ T) (hq : 0 ≤ q+14)
    (hparams : ∀ᶠ d : ℕ in atTop, 0 < B d ∧ 0 < r (mu d) ∧ r (mu d)=teacherNorm ∧ 0 < (p d : ℝ) ∧
      0 < eta d ∧ 0 < 1-beta d ∧ 1-beta d ≤ 1)
    (hclock : ∀ᶠ d : ℕ in atTop, (N d : ℝ)*min (eta d*(p d : ℝ)) (1-beta d) ≤ T)
    (hdlim : Tendsto (fun d => eta d*(p d : ℝ)/(1-beta d)) atTop (𝓝 delta))
    (hPlim : Tendsto (fun d => dynamicSourceLoad d (B d) (eta d)) atTop (𝓝 Phi))
    (hepslim : Tendsto (fun d => 1-beta d) atTop (𝓝 0))
    (hplim : Tendsto (fun d => (p d : ℝ)) atTop (𝓝 0))
    (hetaSize : Tendsto (fun d => eta d*Real.sqrt (Real.log d/(d : ℝ))) atTop (𝓝 0))
    (hN : ∀ᶠ d : ℕ in atTop, 0 < N d)
    (hpoly : ∀ᶠ d : ℕ in atTop, (N d : ℝ) ≤ (d : ℝ)^q) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ENNReal.ofReal (1-((d : ℝ)^10)⁻¹) ≤
        (worldLaw (B := B d) (p d) (Measure.dirac (coldState d))) {ω | ∀ k ≤ N d,
          ‖matchedProcess (eta d) (beta d) (p d) (mu d) k ω-
            matchedOrbit (B := B d) (eta d) (beta d) (p d) (mu d) (coldState d) k‖ ≤
              C*Real.sqrt (Real.log d/(d : ℝ))} := by
  obtain ⟨v,hv0,hv,hphysical⟩ := dynamic_solution_exists_on_finite_horizon teacherNorm delta Phi
    (T*max 1 (1/(delta/2))) (0 : DynamicState) hdelta hPhi (by positivity)
    (by simp [dynamicPhysical])
  exact actual_fluid_cells_three_four H Ho G S B F eta beta p mu N teacherNorm delta Phi T q
    hr hdelta hPhi hT hq v hv0 hv hparams hclock hdlim hPlim hepslim hplim hetaSize hN hpoly

/-- Actual cold-start fluid limit in cell 2 on every fixed finite min-clock horizon. The limiting slow reference is obtained from global ODE existence. -/
theorem cor_fluid_cell_two
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : ∀ n, SparseSGD.External.GaussianSteinCertificate n)
    (B : ℕ → ℕ)
    (F : ∀ d, SparseSGD.External.MartingaleBernsteinCertificate (World d (B d)))
    (eta beta : ℕ → ℝ) (p : ℕ → unitInterval) (mu : ∀ d, Vec d) (N : ℕ → ℕ)
    (teacherNorm Phi T q : ℝ)
    (hr : 0 < teacherNorm) (hPhi : 0 ≤ Phi) (hT : 0 ≤ T) (hq : 0 ≤ q+14)
    (hparams : ∀ᶠ d : ℕ in atTop, 0 < B d ∧ 0 < r (mu d) ∧ r (mu d)=teacherNorm ∧ 0 < (p d : ℝ) ∧
      0 < eta d ∧ 0 < 1-beta d ∧ 1-beta d ≤ 1)
    (hclock : ∀ᶠ d : ℕ in atTop, (N d : ℝ)*min (eta d*(p d : ℝ)) (1-beta d) ≤ T)
    (hdlim : Tendsto (fun d => eta d*(p d : ℝ)/(1-beta d)) atTop (𝓝 0))
    (hzlim : Tendsto (fun d => eta d*(p d : ℝ)) atTop (𝓝 0))
    (hPlim : Tendsto (fun d => dynamicSourceLoad d (B d) (eta d)) atTop (𝓝 Phi))
    (hplim : Tendsto (fun d => (p d : ℝ)) atTop (𝓝 0))
    (hetaSize : Tendsto (fun d => eta d*Real.sqrt (Real.log d/(d : ℝ))) atTop (𝓝 0))
    (hN : ∀ᶠ d : ℕ in atTop, 0 < N d)
    (hpoly : ∀ᶠ d : ℕ in atTop, (N d : ℝ) ≤ (d : ℝ)^q) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ENNReal.ofReal (1-((d : ℝ)^10)⁻¹) ≤
        (worldLaw (B := B d) (p d) (Measure.dirac (coldState d))) {ω | ∀ k ≤ N d,
          ‖matchedProcess (eta d) (beta d) (p d) (mu d) k ω-
            matchedOrbit (B := B d) (eta d) (beta d) (p d) (mu d) (coldState d) k‖ ≤
              C*Real.sqrt (Real.log d/(d : ℝ))} := by
  obtain ⟨v,hv0,hv⟩ := slow_global_solution_exists teacherNorm Phi (0,0) hr.le hPhi (by norm_num)
  exact actual_fluid_cell_two H Ho G S B F eta beta p mu N teacherNorm Phi T q
    hr hPhi hT hq v hv0 (fun t ht => hv t ht.1) hparams hclock hdlim hzlim hPlim hplim hetaSize hN hpoly

end
end SparseSGD.Logistic
