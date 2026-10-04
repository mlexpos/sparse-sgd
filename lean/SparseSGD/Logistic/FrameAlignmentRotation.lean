import SparseSGD.Logistic.MarkovReduction
import SparseSGD.Logistic.GaussianFrameSplit
import SparseSGD.Logistic.ScalarCoefficients
import SparseSGD.Logistic.TameCoefficients
namespace SparseSGD.Logistic
noncomputable section
open MeasureTheory ProbabilityTheory
set_option maxHeartbeats 1600000

/-- Feature covariance under an arbitrary orthogonal frame change, with the
mean vector transformed together with the noise. -/
theorem frame_feature_rotation {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d)
    (mu : Vec d) (a : Sample d) :
    feature (O mu) (rotateSample O a)=O (feature mu a) := by
  rcases a with ⟨label,z⟩
  cases label <;> simp [feature,rotateSample,rotateNoise,map_add]

theorem frame_bias_rotation {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d)
    (p : unitInterval) (mu : Vec d) : bias p (O mu)=bias p mu := by simp [bias]

theorem frame_gradient_rotation {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d)
    (p : unitInterval) (mu theta : Vec d) (a : Sample d) :
    gradient p (O mu) (O theta) (rotateSample O a)=O (gradient p mu theta a) := by
  simp only [gradient,frame_feature_rotation,frame_bias_rotation,O.inner_map_map,map_smul]
  rfl

theorem frame_batchGradient_rotation {d B : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d)
    (p : unitInterval) (mu theta : Vec d) (a : Batch d B) :
    batchGradient p (O mu) (O theta) (rotateBatch O a)=O (batchGradient p mu theta a) := by
  simp only [batchGradient,rotateBatch,frame_gradient_rotation,map_smul,map_sum]

theorem frame_signal_rotation {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (mu theta : Vec d) :
    signalCoord (O mu) (O theta)=signalCoord mu theta := by simp [signalCoord,r]

theorem frame_bulk_rotation {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (mu theta : Vec d) :
    bulkPart (O mu) (O theta)=O (bulkPart mu theta) := by
  simp [bulkPart,frame_signal_rotation,r]

theorem frame_tameError_rotation {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d)
    (p : unitInterval) (mu theta : Vec d) :
    tameError p (O mu) (O theta)=tameError p mu theta := by simp [tameError,gaussianAlpha]

theorem frame_coefD0_rotation {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d)
    (p : unitInterval) (mu theta : Vec d) (hr : 0 < r mu) :
    coefD0 p (O mu) (O theta)=coefD0 p mu theta := by
  rw [coefD0_eq_scalar p (O mu) (O theta) (by simpa [r] using hr),coefD0_eq_scalar p mu theta hr]
  simp [r,frame_signal_rotation]

/-- The actual aligned batch law is the independent prefix/complement law.
Orthogonal invariance is the proved standard-Gaussian invariance theorem,
followed by the existing coordinate product split. -/
theorem frame_rotated_batchLaw_split {k m B : ℕ}
    (O : Vec (k+m) ≃ₗᵢ[ℝ] Vec (k+m)) (p : unitInterval) :
    (batchLaw (k+m) B p).map (fun a => splitGaussianBatch (k:=k) (m:=m) (rotateBatch O a)) =
      (batchLaw k B p).prod (Measure.pi (fun _ : Fin B => SparseSGD.Probability.standardGaussianProduct m)) := by
  change (batchLaw (k+m) B p).map (splitGaussianBatch (k:=k) (m:=m) ∘ rotateBatch O) = _
  have hm : Measurable (splitGaussianBatch (k:=k) (m:=m) (B:=B)) := by
    unfold splitGaussianBatch splitGaussianSample splitGaussianNoise
    fun_prop
  rw [← Measure.map_map hm (measurable_rotateBatch O),batch_rotation_invariant]
  exact batchLaw_split k m B p

end
end SparseSGD.Logistic
