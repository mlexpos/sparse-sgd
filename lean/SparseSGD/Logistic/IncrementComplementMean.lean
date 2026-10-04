import SparseSGD.Logistic.IncrementComplementBounds
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

theorem gaussian_weighted_sum_norm_second (m B : ℕ) (w : Fin B → ℝ) :
    Integrable (fun a : Fin B → NoiseVec m => ‖∑ i, w i • (WithLp.toLp 2 (a i) : Vec m)‖^2)
      (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)) ∧
    (∫ a : Fin B → NoiseVec m, ‖∑ i, w i • (WithLp.toLp 2 (a i) : Vec m)‖^2
      ∂Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)) =
      (m : ℝ)*(∑ i, (w i)^2) := by
  let q := ∑ i, (w i)^2
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  let g : Vec m → ℝ := fun x => ‖x‖^2
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
  have he (z : NoiseVec m) : g (T z) = q*‖(WithLp.toLp 2 z : Vec m)‖^2 := by
    dsimp [g, T]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt hq]
  have hi : Integrable (g ∘ T) (SparseSGD.Probability.standardGaussianProduct m) := by
    change Integrable (fun z => g (T z)) _
    simp_rw [he]
    exact ((SparseSGD.Probability.LeastSquares.gaussian_norm_sq_memLp_two m).integrable (by norm_num)).const_mul q
  have hgmap : Integrable g ((SparseSGD.Probability.standardGaussianProduct m).map T) :=
    (integrable_map_measure hg.aestronglyMeasurable hT.aemeasurable).mpr hi
  have hp : MeasurePreserving S
      (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m))
      ((SparseSGD.Probability.standardGaussianProduct m).map T) := ⟨hS, hlaw⟩
  refine ⟨hp.integrable_comp_of_integrable hgmap, ?_⟩
  change (∫ a, g (S a) ∂Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)) = _
  rw [← integral_map hS.aemeasurable hg.aestronglyMeasurable, hlaw,
    integral_map hT.aemeasurable hg.aestronglyMeasurable]
  simp_rw [he]
  rw [integral_const_mul, SparseSGD.Probability.LeastSquares.gaussian_norm_sq_integral]
  ring

/-- The actual complement square is integrable and has the exact rare
mean used in the centered compound-Gaussian MGF. -/
theorem residualGaussianComplement_norm_second {k m B : ℕ} (p : unitInterval)
    (mu theta : Vec k) (hB : 0 < B) :
    Integrable (fun z : Batch k B × (Fin B → NoiseVec m) =>
      ‖residualGaussianComplement p mu theta z.1 z.2‖^2)
      ((batchLaw k B p).prod (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m))) ∧
    (∫ z : Batch k B × (Fin B → NoiseVec m), ‖residualGaussianComplement p mu theta z.1 z.2‖^2
      ∂((batchLaw k B p).prod (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)))) =
      (m : ℝ)*coefD0 p mu theta/(B : ℝ) := by
  let F := fun z : Batch k B × (Fin B → NoiseVec m) => ‖residualGaussianComplement p mu theta z.1 z.2‖^2
  have hFm : Measurable F := (measurable_residualGaussianComplement p mu theta).norm.pow_const 2
  have hs (a : Batch k B) : Integrable (fun z => F (a,z))
      (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)) ∧
      (∫ z, F (a,z) ∂Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)) =
        (m : ℝ)*batchResidualEnergy p mu theta a := by
    simpa only [F, residualGaussianComplement, complementWeight_variance] using
      gaussian_weighted_sum_norm_second m B (complementWeight p mu theta a)
  have hMI : Integrable (fun a : Batch k B => (m : ℝ)*batchResidualEnergy p mu theta a) (batchLaw k B p) :=
    ((batchResidualEnergy_memLp_two p mu theta).integrable (by norm_num)).const_mul _
  have hi : Integrable F ((batchLaw k B p).prod
      (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m))) := by
    apply (integrable_prod_iff hFm.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun a => (hs a).1), ?_⟩
    have he (a : Batch k B) : (∫ z, ‖F (a,z)‖
        ∂Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)) =
        (m : ℝ)*batchResidualEnergy p mu theta a := by
      have hn (z : Fin B → NoiseVec m) : ‖F (a,z)‖ = F (a,z) := by
        dsimp [F]
        exact abs_of_nonneg (sq_nonneg _)
      simp_rw [hn]
      exact (hs a).2
    simpa only [he] using hMI
  refine ⟨hi, ?_⟩
  change (∫ z, F z ∂_) = _
  rw [integral_prod _ hi]
  simp_rw [fun a => (hs a).2]
  rw [integral_const_mul, batchResidualEnergy_integral p mu theta hB]
  ring
end
end SparseSGD.Logistic
