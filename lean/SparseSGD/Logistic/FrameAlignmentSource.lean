import SparseSGD.Logistic.FrameAlignmentEnergy
namespace SparseSGD.Logistic
noncomputable section
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

/-- Actual full-state Gaussian frame and bulk-energy split. The active bulk
axes are constructed from the state, rather than supplied as a hypothesis. -/
theorem logistic_full_state_frame {d B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate d) (hB : 0<B)
    (p : unitInterval) (mu theta momentum : Vec d) (hr : 0<r mu) :
    ∃ k rest : ℕ, k≤2 ∧ d=(k+1)+rest ∧
      ∃ muPrefix thetaPrefix : Vec (k+1), ∃ axes : Fin k → Vec d,
      ∃ split : Batch d B → Batch (k+1) B × (Fin B → NoiseVec rest),
        Measurable split ∧
        (batchLaw d B p).map split=(batchLaw (k+1) B p).prod
          (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct rest)) ∧
        (∀ i, ‖axes i‖=1 ∧ inner ℝ (axes i) mu=0) ∧
        ‖muPrefix‖=‖mu‖ ∧ ‖thetaPrefix‖=‖theta‖ ∧
        tameError p muPrefix thetaPrefix=tameError p mu theta ∧
        coefD0 p muPrefix thetaPrefix=coefD0 p mu theta ∧
        (∀ a : Batch d B,
          ‖bulkPart mu (centeredBatchGradient p mu theta a)‖^2 =
            (∑ i : Fin k, (inner ℝ (axes i) (centeredBatchGradient p mu theta a))^2)+
              ‖residualGaussianComplement p muPrefix thetaPrefix (split a).1 (split a).2‖^2) := by
  obtain ⟨k,rest,hk,hd,O,i0,hi0,hmu,htheta,hmomentum⟩ := exists_two_bulk_logistic_frame mu theta momentum hr
  subst d
  have hi : i0=(⟨0,by omega⟩ : Fin ((k+1)+rest)) := Fin.ext hi0
  rw [hi] at hmu
  have hmuC : frameComplement (O mu)=0 := by
    ext j
    rw [frameComplement_apply,hmu]
    simp
    intro he
    have hv := congrArg Fin.val he
    simp at hv
  have hthetaC : frameComplement (O theta)=0 := frameComplement_of_support _ htheta
  let axes : Fin k → Vec ((k+1)+rest) := fun i => O.symm (EuclideanSpace.single (Fin.castAdd rest i.succ) 1)
  let split := fun a : Batch ((k+1)+rest) B => splitGaussianBatch (k:=k+1) (m:=rest) (rotateBatch O a)
  have hs : Measurable split := by
    change Measurable ((splitGaussianBatch (k:=k+1) (m:=rest)) ∘ rotateBatch O)
    have hf : Measurable (splitGaussianBatch (k:=k+1) (m:=rest) (B:=B)) := by
      unfold splitGaussianBatch splitGaussianSample splitGaussianNoise
      fun_prop
    exact hf.comp (measurable_rotateBatch O)
  refine ⟨k,rest,hk,rfl,framePrefix (O mu),framePrefix (O theta),axes,split,hs,
    frame_rotated_batchLaw_split O p,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact ⟨frame_active_axis_unit O _,frame_active_axis_orthogonal O mu _ _ hmu
      (by apply Fin.ne_of_val_ne; simp)⟩
  · rw [← frame_norm_prefix (O mu) hmuC,O.norm_map]
  · rw [← frame_norm_prefix (O theta) hthetaC,O.norm_map]
  · rw [← frame_tameError_prefix p (O mu) (O theta) hmuC hthetaC,frame_tameError_rotation]
  · rw [← frame_coefD0_prefix p (O mu) (O theta) (by simpa [r] using hr) hmuC hthetaC,
      frame_coefD0_rotation O p mu theta hr]
  · exact frame_centered_bulk_energy O H hB p mu theta hr hmu hthetaC

end
end SparseSGD.Logistic
