import SparseSGD.Logistic.FrameAlignmentRotation
import SparseSGD.Logistic.IncrementComplementMGF
namespace SparseSGD.Logistic
noncomputable section
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

def framePrefix {k m : ℕ} (x : Vec (k+m)) : Vec k :=
  WithLp.toLp 2 (fun i => x (Fin.castAdd m i))
def frameComplement {k m : ℕ} (x : Vec (k+m)) : Vec m :=
  WithLp.toLp 2 (fun j => x (Fin.natAdd k j))
@[simp] theorem framePrefix_apply {k m : ℕ} (x : Vec (k+m)) (i : Fin k) :
    framePrefix x i=x (Fin.castAdd m i) := rfl
@[simp] theorem frameComplement_apply {k m : ℕ} (x : Vec (k+m)) (j : Fin m) :
    frameComplement x j=x (Fin.natAdd k j) := rfl

theorem frame_norm_square_split {k m : ℕ} (x : Vec (k+m)) :
    ‖x‖^2=‖framePrefix x‖^2+‖frameComplement x‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  exact Fin.sum_univ_add (fun i => x i ^ 2)

theorem frame_inner_split {k m : ℕ} (x y : Vec (k+m)) :
    inner ℝ x y=inner ℝ (framePrefix x) (framePrefix y)+
      inner ℝ (frameComplement x) (frameComplement y) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Fin.sum_univ_add (fun i => y i * x i)

theorem frame_inner_of_complement_zero {k m : ℕ} (x y : Vec (k+m))
    (hx : frameComplement x=0) :
    inner ℝ x y=inner ℝ (framePrefix x) (framePrefix y) := by
  rw [frame_inner_split,hx,inner_zero_left,add_zero]

theorem framePrefix_feature {k m : ℕ} (mu : Vec (k+m)) (a : Sample (k+m)) :
    framePrefix (feature mu a)=feature (framePrefix mu) (splitGaussianSample a).1 := by
  ext i
  cases h : a.1 <;> simp [feature,framePrefix,splitGaussianSample,splitGaussianNoise,h]

theorem frameComplement_feature {k m : ℕ} (mu : Vec (k+m)) (a : Sample (k+m))
    (hmu : frameComplement mu=0) :
    frameComplement (feature mu a)=WithLp.toLp 2 (splitGaussianSample a).2 := by
  have hm (j : Fin m) : mu (Fin.natAdd k j)=0 := by
    exact congrArg (fun x : Vec m => x j) hmu
  ext j
  cases h : a.1 <;> simp [feature,frameComplement,splitGaussianSample,splitGaussianNoise,h,hm]

theorem frame_bias_prefix {k m : ℕ} (p : unitInterval) (mu : Vec (k+m))
    (hmu : frameComplement mu=0) : bias p mu=bias p (framePrefix mu) := by
  unfold bias
  rw [frame_norm_square_split,hmu,norm_zero,zero_pow (by norm_num : 2≠0),add_zero]

theorem frame_logit_prefix {k m : ℕ} (p : unitInterval) (mu theta : Vec (k+m))
    (htheta : frameComplement theta=0) (hmu : frameComplement mu=0) (a : Sample (k+m)) :
    inner ℝ theta (feature mu a)+bias p mu =
      inner ℝ (framePrefix theta) (feature (framePrefix mu) (splitGaussianSample a).1)+
        bias p (framePrefix mu) := by
  rw [frame_inner_of_complement_zero theta _ htheta,framePrefix_feature,frame_bias_prefix p mu hmu]

theorem frameComplement_gradient {k m : ℕ} (p : unitInterval) (mu theta : Vec (k+m))
    (htheta : frameComplement theta=0) (hmu : frameComplement mu=0) (a : Sample (k+m)) :
    frameComplement (gradient p mu theta a)=
      (sigma (inner ℝ (framePrefix theta) (feature (framePrefix mu) (splitGaussianSample a).1)+
        bias p (framePrefix mu))-labelReal a.1) • WithLp.toLp 2 (splitGaussianSample a).2 := by
  ext j
  simp only [gradient,frameComplement_apply,PiLp.smul_apply]
  rw [frame_logit_prefix p mu theta htheta hmu]
  have hf := congrArg (fun x : Vec m => x j) (frameComplement_feature mu a hmu)
  simpa only [frameComplement_apply,smul_eq_mul] using congrArg (fun x : ℝ =>
    (sigma (inner ℝ (framePrefix theta) (feature (framePrefix mu) (splitGaussianSample a).1)+
        bias p (framePrefix mu))-labelReal a.1)*x) hf

theorem frameComplement_batchGradient {k m B : ℕ} (p : unitInterval) (mu theta : Vec (k+m))
    (htheta : frameComplement theta=0) (hmu : frameComplement mu=0) (a : Batch (k+m) B) :
    frameComplement (batchGradient p mu theta a)=
      residualGaussianComplement p (framePrefix mu) (framePrefix theta)
        (splitGaussianBatch a).1 (splitGaussianBatch a).2 := by
  ext j
  simp only [batchGradient,residualGaussianComplement,complementWeight,
    frameComplement_apply,PiLp.smul_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h := congrArg (fun x : Vec m => x j) (frameComplement_gradient p mu theta htheta hmu (a i))
  simpa [splitGaussianBatch,splitGaussianSample,mul_assoc] using congrArg (fun x : ℝ => (B:ℝ)⁻¹*x) h

theorem frameComplement_meanBatchGradient {k m B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate (k+m)) (hB : 0<B)
    (p : unitInterval) (mu theta : Vec (k+m))
    (htheta : frameComplement theta=0) (hmu : frameComplement mu=0) :
    frameComplement (meanBatchGradient (B:=B) p mu theta)=0 := by
  unfold meanBatchGradient
  rw [batchGradient_integral H hB]
  ext j
  have ht := congrArg (fun x : Vec m => x j) htheta
  have hm := congrArg (fun x : Vec m => x j) hmu
  simp only [frameComplement_apply,PiLp.add_apply,PiLp.smul_apply] at *
  simp [ht,hm]

theorem frameComplement_centeredBatchGradient {k m B : ℕ}
    (H : SparseSGD.External.GaussianSteinCertificate (k+m)) (hB : 0<B)
    (p : unitInterval) (mu theta : Vec (k+m))
    (htheta : frameComplement theta=0) (hmu : frameComplement mu=0) (a : Batch (k+m) B) :
    frameComplement (centeredBatchGradient p mu theta a)=
      residualGaussianComplement p (framePrefix mu) (framePrefix theta)
        (splitGaussianBatch a).1 (splitGaussianBatch a).2 := by
  have hm := frameComplement_meanBatchGradient H hB p mu theta htheta hmu
  have hg := frameComplement_batchGradient p mu theta htheta hmu a
  ext j
  have hmj : (meanBatchGradient (B:=B) p mu theta) (Fin.natAdd k j)=0 := by
    simpa using congrArg (fun x : Vec m => x j) hm
  change (batchGradient p mu theta a) (Fin.natAdd k j) -
    (meanBatchGradient (B:=B) p mu theta) (Fin.natAdd k j) = _
  rw [hmj,sub_zero]
  exact congrArg (fun x : Vec m => x j) hg


/-- Discarding a zero complement preserves the actual parameter norm. -/
theorem frame_norm_prefix {k m : ℕ} (x : Vec (k+m)) (hx : frameComplement x=0) :
    ‖x‖=‖framePrefix x‖ := by
  have hs := frame_norm_square_split x
  rw [hx,norm_zero,zero_pow (by norm_num : 2≠0),add_zero] at hs
  nlinarith [norm_nonneg x,norm_nonneg (framePrefix x)]

theorem frame_r_prefix {k m : ℕ} (mu : Vec (k+m)) (hmu : frameComplement mu=0) :
    r mu=r (framePrefix mu) := frame_norm_prefix mu hmu

theorem frame_signal_prefix {k m : ℕ} (mu theta : Vec (k+m)) (hmu : frameComplement mu=0) :
    signalCoord mu theta=signalCoord (framePrefix mu) (framePrefix theta) := by
  unfold signalCoord
  rw [frame_inner_split, hmu, inner_zero_right, add_zero, frame_r_prefix mu hmu]

theorem frame_gaussianAlpha_prefix {k m : ℕ} (mu theta : Vec (k+m))
    (hmu : frameComplement mu=0) (htheta : frameComplement theta=0) :
    gaussianAlpha mu theta=gaussianAlpha (framePrefix mu) (framePrefix theta) := by
  simp only [gaussianAlpha,frame_norm_prefix mu hmu,frame_norm_prefix theta htheta]

theorem frame_tameError_prefix {k m : ℕ} (p : unitInterval) (mu theta : Vec (k+m))
    (hmu : frameComplement mu=0) (htheta : frameComplement theta=0) :
    tameError p mu theta=tameError p (framePrefix mu) (framePrefix theta) := by
  simp only [tameError,frame_norm_prefix mu hmu,frame_norm_prefix theta htheta,
    frame_inner_of_complement_zero theta mu htheta,frame_gaussianAlpha_prefix mu theta hmu htheta]

theorem frame_coefD0_prefix {k m : ℕ} (p : unitInterval) (mu theta : Vec (k+m))
    (hr : 0<r mu) (hmu : frameComplement mu=0) (htheta : frameComplement theta=0) :
    coefD0 p mu theta=coefD0 p (framePrefix mu) (framePrefix theta) := by
  rw [coefD0_eq_scalar p mu theta hr,
    coefD0_eq_scalar p (framePrefix mu) (framePrefix theta) (by simpa [← frame_r_prefix mu hmu] using hr),
    frame_r_prefix mu hmu,frame_signal_prefix mu theta hmu,frame_norm_prefix theta htheta]


theorem frameComplement_of_support {k m : ℕ} (x : Vec (k+m))
    (hx : ∀ j : Fin (k+m), k≤j.val → x j=0) : frameComplement x=0 := by
  ext j
  exact hx (Fin.natAdd k j) (by simp)

end
end SparseSGD.Logistic
