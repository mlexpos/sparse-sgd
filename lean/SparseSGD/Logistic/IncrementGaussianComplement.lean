import SparseSGD.Logistic.GaussianFrameSplit
import SparseSGD.Logistic.IncrementSquareMGF
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

/-- The exact law of an iid weighted Gaussian vector sum. This includes
zero weights and zero variance; no conditional Gaussian assertion is assumed. -/
theorem gaussian_weighted_sum_law (m B : ℕ) (w : Fin B → ℝ) :
    (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)).map
      (fun a => ∑ i, w i • (WithLp.toLp 2 (a i) : Vec m)) =
    (stdGaussian (Vec m)).map (fun z => Real.sqrt (∑ i, (w i)^2) • z) := by
  let κ := Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)
  have hm (i : Fin B) : Measurable (fun z : NoiseVec m => w i • (WithLp.toLp 2 z : Vec m)) := by
    fun_prop
  have hi := iIndepFun_pi (μ := fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)
    (X := fun i z => w i • (WithLp.toLp 2 z : Vec m)) (fun i => (hm i).aemeasurable)
  have hsingle (i : Fin B) : κ.map (fun a => w i • (WithLp.toLp 2 (a i) : Vec m)) =
      (stdGaussian (Vec m)).map (fun z => w i • z) := by
    rw [show (fun a : Fin B → NoiseVec m => w i • (WithLp.toLp 2 (a i) : Vec m)) =
      (fun z : NoiseVec m => w i • (WithLp.toLp 2 z : Vec m)) ∘ (fun a => a i) from rfl,
      ← Measure.map_map (hm i) (measurable_pi_apply i),
      (measurePreserving_eval (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m) i).map_eq]
    rw [show (fun z : NoiseVec m => w i • (WithLp.toLp 2 z : Vec m)) =
      (fun z : Vec m => w i • z) ∘ WithLp.toLp 2 from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop)]
    rw [SparseSGD.Probability.standardGaussianProduct, map_pi_eq_stdGaussian]
  apply Measure.ext_of_charFun
  ext t
  have hchar := congrFun (hi.charFun_map_fun_sum_eq_prod
    (fun i => ((hm i).comp (measurable_pi_apply i)).aemeasurable)) t
  dsimp [κ] at hsingle
  simp only [Finset.prod_apply, Function.comp_def] at hchar
  simp_rw [hsingle, charFun_map_smul, charFun_stdGaussian] at hchar
  rw [hchar, charFun_map_smul, charFun_stdGaussian]
  simp only [norm_smul, Real.norm_eq_abs, ← Complex.ofReal_pow, mul_pow, sq_abs]
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (w i)))]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [← Finset.sum_div, Finset.sum_neg_distrib, ← Finset.sum_mul]

/-- Conditional-on-weights chi-square MGF for the actual Gaussian batch
sum, obtained from its proved law. -/
theorem gaussian_weighted_sum_norm_mgf
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (m B : ℕ) (w : Fin B → ℝ) (t : ℝ)
    (ht : 2*|t| * (∑ i, (w i)^2) < 1) :
    Integrable (fun a : Fin B → NoiseVec m => Real.exp
      (t*(‖∑ i, w i • (WithLp.toLp 2 (a i) : Vec m)‖^2-(m : ℝ)*(∑ i, (w i)^2))))
        (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)) ∧
    (∫ a : Fin B → NoiseVec m, Real.exp
      (t*(‖∑ i, w i • (WithLp.toLp 2 (a i) : Vec m)‖^2-(m : ℝ)*(∑ i, (w i)^2)))
      ∂Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)) ≤
      Real.exp ((m : ℝ)*t^2*(∑ i, (w i)^2)^2/(1-2*|t| * (∑ i, (w i)^2))) := by
  let q := ∑ i, (w i)^2
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _ => sq_nonneg (w i))
  let g : Vec m → ℝ := fun z => Real.exp (t*(‖z‖^2-(m : ℝ)*q))
  let S : (Fin B → NoiseVec m) → Vec m := fun a => ∑ i, w i • WithLp.toLp 2 (a i)
  let T : NoiseVec m → Vec m := fun z => Real.sqrt q • WithLp.toLp 2 z
  have hg : Measurable g := by fun_prop
  have hS : Measurable S := by fun_prop
  have hT : Measurable T := by fun_prop
  have hlaw : (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)).map S =
      (SparseSGD.Probability.standardGaussianProduct m).map T := by
    rw [gaussian_weighted_sum_law, ← map_pi_eq_stdGaussian,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have he (z : NoiseVec m) : g (T z) = Real.exp
      ((t*q)*(‖(WithLp.toLp 2 z : Vec m)‖^2-(m : ℝ))) := by
    dsimp [g, T]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt hq]
    congr 1
    ring
  have hcert := G.norm_mgf m (t*q) (by
    rw [abs_mul, abs_of_nonneg hq]
    simpa [q, mul_assoc] using ht)
  have htg : Integrable (g ∘ T) (SparseSGD.Probability.standardGaussianProduct m) := by
    change Integrable (fun z => g (T z)) _
    simp_rw [he]
    exact hcert.1
  have hgmap : Integrable g ((SparseSGD.Probability.standardGaussianProduct m).map T) :=
    (integrable_map_measure hg.aestronglyMeasurable hT.aemeasurable).mpr htg
  have hp : MeasurePreserving S
      (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m))
      ((SparseSGD.Probability.standardGaussianProduct m).map T) := ⟨hS, hlaw⟩
  refine ⟨hp.integrable_comp_of_integrable hgmap, ?_⟩
  change (∫ a, g (S a) ∂Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)) ≤ _
  rw [← integral_map hS.aemeasurable hg.aestronglyMeasurable, hlaw,
    integral_map hT.aemeasurable hg.aestronglyMeasurable]
  simp_rw [he]
  refine hcert.2.trans_eq ?_
  congr 1
  rw [abs_mul, abs_of_nonneg hq]
  ring

end
end SparseSGD.Logistic
