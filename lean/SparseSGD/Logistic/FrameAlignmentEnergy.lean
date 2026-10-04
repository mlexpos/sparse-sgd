import SparseSGD.Logistic.FrameAlignmentBasis
import SparseSGD.Logistic.FrameAlignmentCoordinates
namespace SparseSGD.Logistic
noncomputable section
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false

theorem frame_meanBatchGradient_rotation {d B : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d)
    (p : unitInterval) (mu theta : Vec d) :
    meanBatchGradient (B:=B) p (O mu) (O theta)=O (meanBatchGradient (B:=B) p mu theta) := by
  unfold meanBatchGradient
  have hmap : (∫ a : Batch d B, batchGradient p (O mu) (O theta) a ∂batchLaw d B p)=
      ∫ a : Batch d B, batchGradient p (O mu) (O theta) (rotateBatch O a) ∂batchLaw d B p := by
    conv_lhs => rw [← batch_rotation_invariant O p]
    exact integral_map_of_stronglyMeasurable (measurable_rotateBatch O)
      ((measurable_batchGradient d B p (O mu)).comp (measurable_const.prodMk measurable_id)).stronglyMeasurable
  rw [hmap]
  simp_rw [frame_batchGradient_rotation]
  exact (O.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    ((batchGradient_memLp_two d B p mu theta).integrable (by norm_num)))

theorem frame_centeredBatchGradient_rotation {d B : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d)
    (p : unitInterval) (mu theta : Vec d) (a : Batch d B) :
    centeredBatchGradient p (O mu) (O theta) (rotateBatch O a)=
      O (centeredBatchGradient p mu theta a) := by
  simp only [centeredBatchGradient,frame_batchGradient_rotation,frame_meanBatchGradient_rotation,map_sub]

theorem frame_bulk_zero_coordinate {d : ℕ} (mu x : Vec d) (i0 : Fin d)
    (hr : 0 < r mu) (hmu : mu=EuclideanSpace.single i0 (r mu)) :
    (bulkPart mu x) i0=0 := by
  have hi : inner ℝ x mu=r mu*x i0 := by
    conv_lhs => rw [hmu]
    simp [EuclideanSpace.inner_single_right]
  have hv : mu i0=r mu := by conv_lhs => rw [hmu]; simp
  simp only [bulkPart,signalCoord,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,hv]
  rw [hi]
  field_simp
  ring

theorem frame_bulk_other_coordinate {d : ℕ} (mu x : Vec d) (i0 j : Fin d)
    (hmu : mu=EuclideanSpace.single i0 (r mu)) (hj : j≠i0) :
    (bulkPart mu x) j=x j := by
  have hv : mu j=0 := by conv_lhs => rw [hmu]; simp [hj]
  simp [bulkPart,PiLp.sub_apply,PiLp.smul_apply,hv]

theorem frame_bulk_norm_square {k m : ℕ} (mu x : Vec ((k+1)+m))
    (hr : 0 < r mu) (hmu : mu=EuclideanSpace.single ⟨0,by omega⟩ (r mu)) :
    ‖bulkPart mu x‖^2=(∑ i : Fin k, x (Fin.castAdd m i.succ)^2)+‖frameComplement x‖^2 := by
  rw [frame_norm_square_split]
  have hc : frameComplement (bulkPart mu x)=frameComplement x := by
    ext j
    exact frame_bulk_other_coordinate mu x _ _ hmu (by apply Fin.ne_of_val_ne; simp)
  rw [hc,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
  have hzero := frame_bulk_zero_coordinate mu x ⟨0,by omega⟩ hr hmu
  have heq : (Fin.castAdd m (0 : Fin (k+1)))=(⟨0,by omega⟩ : Fin ((k+1)+m)) := Fin.ext rfl
  have hhead : (framePrefix (bulkPart mu x)) 0=0 := by simpa only [framePrefix_apply,heq] using hzero
  rw [hhead,zero_pow (by norm_num : 2≠0),zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [framePrefix_apply]
  rw [frame_bulk_other_coordinate mu x _ _ hmu (by apply Fin.ne_of_val_ne; simp)]

theorem frame_active_axis_unit {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (j : Fin d) :
    ‖O.symm (EuclideanSpace.single j 1)‖=1 := by simp

theorem frame_active_axis_orthogonal {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d)
    (mu : Vec d) (i0 j : Fin d) (hmu : O mu=EuclideanSpace.single i0 (r mu)) (hj : j≠i0) :
    inner ℝ (O.symm (EuclideanSpace.single j 1)) mu=0 := by
  rw [← O.inner_map_map,O.apply_symm_apply,hmu]
  simp [EuclideanSpace.inner_single_left,hj]

theorem frame_active_axis_projection {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (x : Vec d) (j : Fin d) :
    inner ℝ (O.symm (EuclideanSpace.single j 1)) x=(O x) j := by
  rw [← O.inner_map_map,O.apply_symm_apply]
  simp [EuclideanSpace.inner_single_left]


/-- Exact actual bulk-energy decomposition. There are k active bulk axes and
an independent Gaussian complement after the actual rotation/product-law split. -/
theorem frame_centered_bulk_energy {k m B : ℕ}
    (O : Vec ((k+1)+m) ≃ₗᵢ[ℝ] Vec ((k+1)+m))
    (H : SparseSGD.External.GaussianSteinCertificate ((k+1)+m)) (hB : 0<B)
    (p : unitInterval) (mu theta : Vec ((k+1)+m)) (hr : 0<r mu)
    (hmu : O mu=EuclideanSpace.single ⟨0,by omega⟩ (r mu))
    (htheta : frameComplement (O theta)=0) (a : Batch ((k+1)+m) B) :
    ‖bulkPart mu (centeredBatchGradient p mu theta a)‖^2 =
      (∑ i : Fin k, (inner ℝ (O.symm (EuclideanSpace.single (Fin.castAdd m i.succ) 1))
        (centeredBatchGradient p mu theta a))^2)+
      ‖residualGaussianComplement p (framePrefix (O mu)) (framePrefix (O theta))
        (splitGaussianBatch (rotateBatch O a)).1 (splitGaussianBatch (rotateBatch O a)).2‖^2 := by
  have hmu' : O mu=EuclideanSpace.single ⟨0,by omega⟩ (r (O mu)) := by simpa [r] using hmu
  have hr' : 0<r (O mu) := by simpa [r] using hr
  have hmuC : frameComplement (O mu)=0 := by
    ext j
    rw [frameComplement_apply,hmu]
    simp
    intro he
    have hv := congrArg Fin.val he
    simp at hv
  have hnorm : ‖bulkPart mu (centeredBatchGradient p mu theta a)‖=
      ‖bulkPart (O mu) (centeredBatchGradient p (O mu) (O theta) (rotateBatch O a))‖ := by
    rw [frame_centeredBatchGradient_rotation,frame_bulk_rotation,O.norm_map]
  rw [hnorm,frame_bulk_norm_square (O mu) _ hr' hmu',
    frameComplement_centeredBatchGradient H hB p (O mu) (O theta) htheta hmuC]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [frame_centeredBatchGradient_rotation,frame_active_axis_projection]

end
end SparseSGD.Logistic
