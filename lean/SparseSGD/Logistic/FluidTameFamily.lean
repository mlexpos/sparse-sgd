import SparseSGD.Logistic.IncrementFluidAutomatic
import SparseSGD.Logistic.FluidAsymptotics

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 2200000

/-- Uniform concentration for actual dimension-indexed logistic SGD families.
The positive rare-class threshold is chosen before the actual family;
vanishing rare-class probabilities are not required. All stochastic, derivative,
product and nonlinear bootstrap conditions are proved; the remaining dynamical
input is eventual deterministic containment. -/
theorem actual_matched_fluid_tame_family
    (H : ∀ n, SparseSGD.External.BernsteinMomentsCertificate (Sample n))
    (Ho : ∀ n, SparseSGD.External.HoeffdingCertificate (Sample n))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : ∀ n, SparseSGD.External.GaussianSteinCertificate n)
    (teacherNorm RefBound Load LearningT q : ℝ)
    (hr : 0 < teacherNorm) (hRef : 0 ≤ RefBound) (hLoad : 0 ≤ Load)
    (hT : 0 ≤ LearningT) (hq : 0 ≤ q+14) :
    ∃ pCap : ℝ, 0 < pCap ∧ ∀
    (B : ℕ → ℕ)
    (F : ∀ d, SparseSGD.External.MartingaleBernsteinCertificate (World d (B d)))
    (eta beta : ℕ → ℝ) (p : (d : ℕ) → unitInterval) (mu : (d : ℕ) → Vec d)
    (s0 : (d : ℕ) → State d) (N : ℕ → ℕ),
    ∀ (hB : ∀ᶠ d : ℕ in atTop, 0 < B d)
    (heta : ∀ᶠ d : ℕ in atTop, 0 ≤ eta d)
    (hbeta : ∀ᶠ d : ℕ in atTop, 0 ≤ beta d ∧ beta d < 1)
    (hp : ∀ᶠ d : ℕ in atTop, 0 < (p d : ℝ))
    (hmu : ∀ᶠ d : ℕ in atTop, r (mu d)=teacherNorm)
    (hPhi : ∀ᶠ d : ℕ in atTop, logisticPhi d (B d) (eta d) ≤ Load)
    (hpSmall : ∀ᶠ d : ℕ in atTop, (p d : ℝ) ≤ pCap)
    (hz0 : Tendsto (fun d => eta d*(p d : ℝ)) atTop (𝓝 0))
    (hetaSize : Tendsto (fun d => eta d*Real.sqrt (Real.log d/(d : ℝ))) atTop (𝓝 0))
    (hN : ∀ᶠ d : ℕ in atTop, 0 < N d)
    (hpoly : ∀ᶠ d : ℕ in atTop, (N d : ℝ) ≤ (d : ℝ)^q)
    (hclock : ∀ᶠ d : ℕ in atTop, (N d : ℝ)*(eta d*(p d : ℝ)) ≤ LearningT)
    (href : ∀ᶠ d : ℕ in atTop, ∀ k ≤ N d,
      ‖matchedOrbit (B := B d) (eta d) (beta d) (p d) (mu d) (s0 d) k‖ ≤ RefBound),
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ENNReal.ofReal (1-((d : ℝ)^10)⁻¹) ≤
        (worldLaw (B := B d) (p d) (Measure.dirac (s0 d))) {ω | ∀ k ≤ N d,
          ‖matchedProcess (eta d) (beta d) (p d) (mu d) k ω-
            matchedOrbit (B := B d) (eta d) (beta d) (p d) (mu d) (s0 d) k‖ ≤
              C*Real.sqrt (Real.log d/(d : ℝ))} := by
  obtain ⟨Cjet,hCjet,hactual⟩ := actual_matched_fluid_on_bounded_orbit (S 1)
    teacherNorm RefBound 1 Load hr.le hRef (by norm_num) hLoad
  let C := boundedFluidRateConstant teacherNorm (matchedTubeParameterBound RefBound 1)
    (matchedTubeMomentumBound RefBound 1) 1 LearningT Load (matchedOrbitGamma Cjet LearningT) q 1
  let Q := matchedTubeParameterBound RefBound 1
  let tameC := Real.exp (2*Q^2)+Real.exp (3*Q^2/2)+(1+Real.exp (Q^2/2))*Real.exp (Q*teacherNorm)
  have htamePos : 0 < tameC := by dsimp [tameC]; positivity
  let pCap : ℝ := min (1/2) ((1/2)/tameC)
  have hcap : 0 < pCap := lt_min (by norm_num) (div_pos (by norm_num) htamePos)
  refine ⟨pCap,hcap,?_⟩
  intro B F eta beta p mu s0 N hB heta hbeta hp hmu hPhi hpSmall hz0 hetaSize hN hpoly hclock href
  have hboot := fluid_sqrt_rate_eventual_bootstrap C (2*Cjet*LearningT*matchedOrbitGamma Cjet LearningT) 1 (by norm_num)
  refine ⟨|C|+1,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ),hB,heta,hbeta,hp,hmu,hPhi,hN,hpoly,hclock,href,hboot,
    hpSmall,
    hz0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    hetaSize.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))]
    with d hd hb he hbta hp' hm hphi hn hpo hcl hrf hbs hps hz heSize
  have hph : (p d : ℝ) ≤ 1/2 := hps.trans (min_le_left _ _)
  have htame : (p d : ℝ)*tameC ≤ 1/2 :=
    (le_div_iff₀ htamePos).mp (hps.trans (min_le_right _ _))
  have htm : (p d : ℝ)*stoppedTameConstant (mu d) (matchedTubeParameterBound RefBound 1) ≤ 1/2 := by
    simpa only [stoppedTameConstant,hm,tameC,Q] using htame
  have hh := hactual H Ho G (S d) (S 2) (F d) (eta d) (beta d) (p d) (mu d) (s0 d) (N d)
    LearningT q 1 hd hb hp' hph hm (by rw [hm]; exact hr) he hbta.1 hbta.2 hz.le hphi hn hT hcl
    hq hpo heSize.le hrf htm hbs.1 hbs.2
  apply hh.trans
  apply measure_mono
  intro ω hω k hk
  apply (hω k hk).trans
  change C*Real.sqrt (Real.log d/(d : ℝ)) ≤ (|C|+1)*Real.sqrt (Real.log d/(d : ℝ))
  exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (Real.sqrt_nonneg _)

end
end SparseSGD.Logistic
