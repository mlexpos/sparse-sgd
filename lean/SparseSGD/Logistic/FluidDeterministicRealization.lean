import SparseSGD.Logistic.FluidDeterministicVariance
import SparseSGD.Logistic.FrameAlignmentBasis
import SparseSGD.Logistic.IncrementStoppedDomain
namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1800000

/-- Every nonnegative scalar bulk variance has an actual parameter realization
in the given Gaussian model, preserving its signal vector. -/
theorem exists_parameter_of_scalar_geometry {d : ℕ} (mu : Vec d)
    (hd : 2≤d) (hr : 0<r mu) (t R : ℝ) (hR : 0≤R) :
    ∃ theta : Vec d, signalCoord mu theta=t ∧ ‖theta‖^2=t^2+R := by
  classical
  obtain ⟨q,hq,hq3,hqd,O,i0,hi0,hmu,_,_⟩ := exists_active_logistic_frame mu 0 0 hr
  let i1 : Fin d := ⟨1,by omega⟩
  have hneq : i0≠i1 := by intro h; have h':=congrArg Fin.val h; dsimp [i1] at h'; omega
  let w : Vec d := EuclideanSpace.single i0 t+EuclideanSpace.single i1 (Real.sqrt R)
  refine ⟨O.symm w,?_,?_⟩
  · unfold signalCoord
    have hi : inner ℝ (O.symm w) mu=t*r mu := by
      rw [← O.inner_map_map, O.apply_symm_apply,hmu]
      dsimp [w]
      rw [inner_add_left,EuclideanSpace.inner_single_left,EuclideanSpace.inner_single_left]
      simp [PiLp.single_apply,hneq,hneq.symm]
    rw [hi,mul_div_cancel_right₀ t hr.ne']
  · rw [O.symm.norm_map]
    dsimp [w]
    rw [norm_add_sq_real,EuclideanSpace.inner_single_left]
    simp [PiLp.norm_single,PiLp.single_apply,hneq,hneq.symm,Real.sq_sqrt hR]

/-- A scalar physical state admits actual parameters satisfying the same
compact tame bound. This supplies coefficients in compact bootstraps. -/
theorem exists_parameter_of_physical_state {d : ℕ} (mu : Vec d)
    (hd : 2≤d) (hr : 0<r mu) (y : Fin 5→ℝ) (hy : matchedPhysical y) :
    ∃ theta : Vec d, signalCoord mu theta=y 0 ∧ ‖theta‖^2=(y 0)^2+y 2 :=
  exists_parameter_of_scalar_geometry mu hd hr (y 0) (y 2) hy.1
end
end SparseSGD.Logistic
