import SparseSGD.Comparison.General.Embedding
import SparseSGD.Comparison.SquareRootLift

/-!
# Square-root lift for the momentum range `β ∈ (0,1)` (v2)

This is the v2 form of the square-root lift statements of `Comparison/SquareRootLift.lean`
that carry the hypothesis `1/2 ≤ β`.  They are restated under `0 < β` as new declarations with
suffix `_v2`; the v1 signatures are frozen.  The uniform defect bound
`Params.squareRootLift_defect` is not repeated here: it is covered by
`trajectory_risk_defect_sup_bound_v2`.
-/

open scoped Matrix.Norms.Operator Matrix

namespace SparseSGD
noncomputable section

/-- v2 (β ∈ (0,1)) form of `Params.noiseFree_rankOne_square_root_lift`. -/
theorem Params.noiseFree_rankOne_square_root_lift_v2 (p : Params) (s : Moments)
    (x : Fin 2 → ℝ) (hx : s.cov = Matrix.vecMulVec x x)
    (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (k : ℕ) :
    (p.trajectory s k).R = ((p.meanMatrix ^ k).mulVec x 0)^2 ∧
      (p.trajectory s k).R = p.matchedFreeRisk s ((k : ℝ)*p.matchedStep) := by
  exact ⟨p.trajectory_R_rankOne_noiseFree s hnoise hadd x hx k,
    p.noiseFree_risk_eq_matched_grid_v2 hb0 hb1 hw0 hw1 s hnoise hadd k⟩

/-- v2 (β ∈ (0,1)) form of `Params.noiseFree_risk_squareRootLift_grid`. -/
theorem Params.noiseFree_risk_squareRootLift_grid_v2 (p : Params) (s : Moments)
    (x : Fin 2 → ℝ)
    (hx : s.cov = Matrix.vecMulVec x x)
    (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (k : ℕ) :
    (p.trajectory s k).R = (p.squareRootLiftX x ((k : ℝ)*p.matchedStep))^2 := by
  rw [p.noiseFree_risk_eq_matched_grid_v2 hb0 hb1 hw0 hw1 s hnoise hadd,
    p.matchedFreeRisk_squareRootLift s x hx]

/-- v2 (β ∈ (0,1)) form of `Params.squareRootLiftVector_ne_zero`. -/
theorem Params.squareRootLiftVector_ne_zero_v2 (p : Params) (x : Fin 2 → ℝ) (hx : x ≠ 0)
    (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta)) (t : ℝ) :
    p.squareRootLiftVector x t ≠ 0 := by
  have hP : IsUnit p.matchingMatrix.det :=
    isUnit_iff_ne_zero.mpr (p.matchingMatrix_det_ne_zero_v2 hb0 hb1 hw0 hw1)
  have hPi := Matrix.mulVec_injective_of_det_ne_zero
    ((p.matchingMatrix.isUnit_nonsing_inv_det hP).ne_zero)
  have hE : IsUnit (continuumMeanFlow p.matchedDelta t) :=
    NormedSpace.isUnit_exp (t • continuumMeanGenerator p.matchedDelta)
  have hEi := Matrix.mulVec_injective_of_isUnit hE
  have hinj : Function.Injective (fun z => p.squareRootLiftVector z t) := hEi.comp hPi
  intro hz
  apply hx
  apply hinj
  simpa [Params.squareRootLiftVector] using hz

/-- v2 (β ∈ (0,1)) form of `Params.comparisonFlow_squareRootLift_rank`. -/
theorem Params.comparisonFlow_squareRootLift_rank_v2 (p : Params) (s : Moments)
    (x : Fin 2 → ℝ)
    (hx : s.cov = Matrix.vecMulVec x x) (hne : x ≠ 0)
    (hb0 : 0 < p.beta) (hb1 : p.beta < 1)
    (hw0 : 0 < p.w) (hw1 : p.w < 2*(1+p.beta))
    (hnoise : p.noise = 0) (hadd : p.additive = 0) (t : ℝ) :
    (p.comparisonFlow s t).cov.rank = 1 := by
  have hv := p.squareRootLiftVector_ne_zero_v2 x hne hb0 hb1 hw0 hw1 t
  rw [p.comparisonFlow_squareRootLift_cov s x hx hnoise hadd]
  generalize p.squareRootLiftVector x t = y at hv ⊢
  have hupper := Matrix.rank_vecMulVec_le y y
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hv
    funext i
    exact hn i
  let B : Matrix (Fin 1) (Fin 1) ℝ := (Matrix.vecMulVec y y).submatrix (fun _ => i) (fun _ => i)
  have hdet : B.det ≠ 0 := by
    simpa [B, Matrix.det_fin_one, Matrix.vecMulVec] using mul_ne_zero hi hi
  have hlower := Matrix.rank_submatrix_le (Matrix.vecMulVec y y)
    (fun _ : Fin 1 => i) (fun _ : Fin 1 => i)
  have hrank : B.rank = 1 := by simpa using Matrix.rank_of_det_ne_zero hdet
  change B.rank ≤ _ at hlower
  rw [hrank] at hlower
  omega

end
end SparseSGD
