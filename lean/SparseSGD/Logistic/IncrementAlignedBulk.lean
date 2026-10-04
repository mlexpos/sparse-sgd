import SparseSGD.Logistic.IncrementBernsteinAssembly
import SparseSGD.Logistic.FrameAlignmentEnergy
open MeasureTheory ProbabilityTheory
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false

theorem aligned_bulk_square_mgf {k m B : ℕ}
    (H : SparseSGD.External.BernsteinMomentsCertificate (Sample (k+1)))
    (J : SparseSGD.External.HoeffdingCertificate (Sample (k+1)))
    (G : SparseSGD.External.GaussianQuadraticCertificate)
    (S : SparseSGD.External.GaussianSteinCertificate ((k+1)+m))
    (O : Vec ((k+1)+m) ≃ₗᵢ[ℝ] Vec ((k+1)+m))
    (p : unitInterval) (mu theta : Vec ((k+1)+m)) (Q t : ℝ)
    (hB : 0 < B) (hp : 0 < (p : ℝ)) (hr : 0 < r mu)
    (hmu : O mu=EuclideanSpace.single ⟨0,by omega⟩ (r mu))
    (htheta : frameComplement (O theta)=0)
    (htame : tameError p mu theta ≤ 1/2) (hθ : ‖theta‖ ≤ Q)
    (hactive : |(k : ℝ)*(2*t)| ≤ projectionSquareRadius Q B)
    (hrest : |2*t| * complementQuadraticScale m B ≤ 1) :
    Integrable (fun a : Batch ((k+1)+m) B => Real.exp (t*centeredBulkSquare p mu theta a))
      (batchLaw ((k+1)+m) B p) ∧
    (∫ a : Batch ((k+1)+m) B, Real.exp (t*centeredBulkSquare p mu theta a)
      ∂batchLaw ((k+1)+m) B p) ≤ Real.exp
        (Real.exp (8*Real.exp (2*Q^2+4))*projectionSquareVariance Q p B*((k : ℝ)*(2*t))^2+
          256*Real.exp (1/2)*complementQuadraticVariance p m B*(2*t)^2) := by
  let u := fun i : Fin k => O.symm (EuclideanSpace.single (Fin.castAdd m i.succ) 1)
  let A := batchProjectionEnergy p mu theta u (B := B)
  let P := fun a : Batch ((k+1)+m) B => splitGaussianBatch (rotateBatch O a)
  let mu' := framePrefix (O mu)
  let theta' := framePrefix (O theta)
  let ν := (batchLaw (k+1) B p).prod
    (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m))
  let C := fun z : Batch (k+1) B × (Fin B → NoiseVec m) => ‖residualGaussianComplement p mu' theta' z.1 z.2‖^2
  have hPm : Measurable P := by
    have hs : Measurable (splitGaussianBatch (k := k+1) (m := m) (B := B)) := by
      unfold splitGaussianBatch splitGaussianSample splitGaussianNoise
      fun_prop
    exact hs.comp (measurable_rotateBatch O)
  have hMP : MeasurePreserving P (batchLaw ((k+1)+m) B p) ν :=
    ⟨hPm, frame_rotated_batchLaw_split O p⟩
  have hCm : Measurable C := (measurable_residualGaussianComplement p mu' theta').norm.pow_const 2
  have hCmoment := residualGaussianComplement_norm_second (m := m) p mu' theta' hB
  have hCI : Integrable C ν := hCmoment.1
  have hPCint : Integrable (fun a => C (P a)) (batchLaw ((k+1)+m) B p) := hMP.integrable_comp_of_integrable hCI
  have hPCmean : (∫ a : Batch ((k+1)+m) B, C (P a) ∂batchLaw ((k+1)+m) B p) =
      (m : ℝ)*coefD0 p mu' theta'/(B : ℝ) := by
    rw [← integral_map hPm.aemeasurable hCm.aestronglyMeasurable, hMP.map_eq]
    exact hCmoment.2
  have hAm : Measurable A := by
    exact Finset.measurable_sum _ (fun i _ => (measurable_const.inner
      ((measurable_centeredBatchGradient p mu).comp
        (f := fun a : Batch ((k+1)+m) B => (theta,a)) (measurable_const.prodMk measurable_id))).pow_const 2)
  have hAI : Integrable A (batchLaw ((k+1)+m) B p) := by
    apply integrable_finsetSum
    intro i hi
    have hLp := ((innerSL ℝ) (u i)).comp_memLp' (centeredBatchGradient_memLp_two (B := B) p mu theta)
    simpa only [Function.comp_def, innerSL_apply_apply] using hLp.integrable_sq
  have henergy (a : Batch ((k+1)+m) B) :
      ‖bulkPart mu (centeredBatchGradient p mu theta a)‖^2 = A a+C (P a) :=
    frame_centered_bulk_energy O S hB p mu theta hr hmu htheta a
  have hcenter (a : Batch ((k+1)+m) B) : centeredBulkSquare p mu theta a =
      (A a-(∫ b, A b ∂batchLaw ((k+1)+m) B p))+
      (C (P a)-(m : ℝ)*coefD0 p mu' theta'/B) := by
    dsimp [centeredBulkSquare]
    simp_rw [henergy]
    rw [integral_add hAI hPCint, hPCmean]
    ring
  have hmuC : frameComplement (O mu)=0 := by
    ext j
    rw [frameComplement_apply,hmu]
    simp
    intro he
    have hv := congrArg Fin.val he
    simp at hv
  have htame' : tameError p mu' theta' ≤ 1/2 := by
    rw [← frame_tameError_prefix p (O mu) (O theta) hmuC htheta, frame_tameError_rotation]
    exact htame
  have hu (i : Fin k) : ‖u i‖ ≤ 1 := (frame_active_axis_unit O _).le
  have horth (i : Fin k) : |inner ℝ (u i) mu| ≤ 1 := by
    have hh := frame_active_axis_orthogonal O mu (⟨0,by omega⟩) (Fin.castAdd m i.succ) hmu
      (by apply Fin.ne_of_val_ne; simp)
    simp only [u, hh, abs_zero]
    norm_num
  have ha := tame_batch_projection_energy_mgf G p mu theta u Q (2*t) hB hp htame hθ hu horth hactive
  have hc := tame_residualGaussianComplement_simple_mgf H J G p mu' theta' (2*t) hB hp htame' hrest
  let c0 := (m : ℝ)*coefD0 p mu' theta'/B
  let f := fun a : Batch ((k+1)+m) B => t*(A a-(∫ b, A b ∂batchLaw ((k+1)+m) B p))
  let g := fun a : Batch ((k+1)+m) B => t*(C (P a)-c0)
  have hgEI : Integrable (fun a => Real.exp ((2*t)*(C (P a)-c0))) (batchLaw ((k+1)+m) B p) :=
    hMP.integrable_comp_of_integrable hc.1
  have hgEB : (∫ a : Batch ((k+1)+m) B, Real.exp ((2*t)*(C (P a)-c0))
      ∂batchLaw ((k+1)+m) B p) ≤ Real.exp (256*Real.exp (1/2)*complementQuadraticVariance p m B*(2*t)^2) := by
    have hmE : Measurable (fun z => Real.exp ((2*t)*(C z-c0))) :=
      ((hCm.sub measurable_const).const_mul (2*t)).exp
    rw [← integral_map hPm.aemeasurable hmE.aestronglyMeasurable, hMP.map_eq]
    exact hc.2
  have hf2 (a : Batch ((k+1)+m) B) : 2*f a = (2*t)*(A a-(∫ b, A b ∂batchLaw ((k+1)+m) B p)) := by dsimp [f]; ring
  have hg2 (a : Batch ((k+1)+m) B) : 2*g a = (2*t)*(C (P a)-c0) := by dsimp [g]; ring
  have hh := exp_add_integrable_bound (batchLaw ((k+1)+m) B p) f g
    ((hAm.sub measurable_const).const_mul t) (((hCm.comp hPm).sub measurable_const).const_mul t)
    (Real.exp (8*Real.exp (2*Q^2+4))*projectionSquareVariance Q p B*((k : ℝ)*(2*t))^2)
    (256*Real.exp (1/2)*complementQuadraticVariance p m B*(2*t)^2)
    (by dsimp [projectionSquareVariance, symmetricProjectionConstant]; positivity)
    (by dsimp [complementQuadraticVariance]; positivity)
    (by simp_rw [hf2]; exact ha.1) (by simp_rw [hg2]; exact hgEI)
    (by simp_rw [hf2]; exact ha.2) (by simp_rw [hg2]; exact hgEB)
  have he (a : Batch ((k+1)+m) B) : t*centeredBulkSquare p mu theta a = f a+g a := by
    rw [hcenter]
    dsimp [f,g,c0]
    ring
  simp_rw [he]
  exact hh
end
end SparseSGD.Logistic
