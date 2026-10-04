import SparseSGD.Probability.GaussianProjection
import SparseSGD.External.GaussianStein
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Extend

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace SparseSGD.Probability
noncomputable section

private theorem gaussian_integrable_bounded (f : ℝ → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ x, |f x| ≤ C) (a c : ℝ) :
    Integrable (fun z : ℝ => f (a*z+c)) (gaussianReal 0 1) := by
  apply Integrable.of_bound (hf.comp (by fun_prop)).aestronglyMeasurable C
  exact Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hC (a*z+c))

theorem gaussianAverage_mean_hasDerivAt (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (F D : ℝ) (hF : ∀ x, |f x| ≤ F) (hD : ∀ x, |f' x| ≤ D)
    (c q : ℝ) :
    HasDerivAt (fun c => gaussianAverage f c q) (gaussianAverage f' c q) c := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (F := fun c z : ℝ => f (Real.sqrt q*z+c))
    (F' := fun c z : ℝ => f' (Real.sqrt q*z+c)) (bound := fun _ => D)
    (μ := gaussianReal 0 1) (by simp)
    (Eventually.of_forall (fun c => (hfc.comp (by fun_prop)).aestronglyMeasurable))
    (gaussian_integrable_bounded f hfc F hF (Real.sqrt q) c)
    (hf'.comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall (fun z c _ => by simpa only [Real.norm_eq_abs] using hD (Real.sqrt q*z+c)))
    (integrable_const D)
    (Eventually.of_forall (fun z c _ => by
      simpa only [Function.comp_def, mul_one] using (hf (Real.sqrt q*z+c)).comp c ((hasDerivAt_id c).const_add (Real.sqrt q*z))))).2

theorem gaussian_scale_hasDerivAt (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (F D : ℝ) (hF : ∀ x, |f x| ≤ F) (hD : ∀ x, |f' x| ≤ D)
    (a c : ℝ) :
    HasDerivAt (fun a => ∫ z : ℝ, f (a*z+c) ∂gaussianReal 0 1)
      (∫ z : ℝ, f' (a*z+c)*z ∂gaussianReal 0 1) a := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hid : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := (memLp_id_gaussianReal 1).integrable (by norm_num)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (F := fun a z : ℝ => f (a*z+c)) (F' := fun a z : ℝ => f' (a*z+c)*z)
    (bound := fun z : ℝ => D*|z|) (μ := gaussianReal 0 1) (by simp)
    (Eventually.of_forall (fun a => (hfc.comp (by fun_prop)).aestronglyMeasurable))
    (gaussian_integrable_bounded f hfc F hF a c)
    (((hf'.comp (by fun_prop)).mul continuous_id).aestronglyMeasurable)
    (Eventually.of_forall (fun z a _ => by
      simp only [Real.norm_eq_abs, Pi.mul_apply, Function.comp_apply, id_eq, abs_mul]
      exact mul_le_mul_of_nonneg_right (hD _) (abs_nonneg z)))
    (hid.abs.const_mul D)
    (Eventually.of_forall (fun z a _ => by
      simpa only [Function.comp_def, one_mul, id_eq] using (hf (a*z+c)).comp a (((hasDerivAt_id a).mul_const z).add_const c)))).2

/-- Scalar integration by parts is the dimension-one instance of the explicit
standard Gaussian Stein certificate. -/
theorem gaussian_scalar_stein (H : SparseSGD.External.GaussianSteinCertificate 1)
    (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (F D : ℝ) (hF : ∀ x, |f x| ≤ F) (hD : ∀ x, |f' x| ≤ D) (a c : ℝ) :
    (∫ z : ℝ, f (a*z+c)*z ∂gaussianReal 0 1) =
      a*(∫ z : ℝ, f' (a*z+c) ∂gaussianReal 0 1) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hid : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := (memLp_id_gaussianReal 1).integrable (by norm_num)
  have hfi : Integrable (fun z : ℝ => f (a*z+c)*z) (gaussianReal 0 1) := by
    apply (hid.abs.const_mul F).mono' ((hfc.comp (by fun_prop)).mul continuous_id).aestronglyMeasurable
    exact Eventually.of_forall (fun z => by
      simp only [Real.norm_eq_abs, Pi.mul_apply, Function.comp_apply, id_eq, abs_mul]
      exact mul_le_mul_of_nonneg_right (hF _) (abs_nonneg z))
  have hfpi := gaussian_integrable_bounded f' hf' D hD a c
  have mp := measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) (0 : Fin 1)
  have heval : (standardGaussianProduct 1).map (fun z : Fin 1 → ℝ => z 0) = gaussianReal 0 1 := mp.map_eq
  have HI := mp.integrable_comp_of_integrable hfi
  have HD := mp.integrable_comp_of_integrable hfpi
  have HH := H.first_order (fun _ => a) c f f' 0 hf hf'
    (by simpa [Function.comp_def, Function.eval, standardGaussianProduct] using HI) (by simpa [Function.comp_def, Function.eval, standardGaussianProduct] using HD)
  simp only [Fin.sum_univ_one] at HH
  have he (g : ℝ → ℝ) (hg : Continuous g) :
      (∫ z : Fin 1 → ℝ, g (z 0) ∂standardGaussianProduct 1) = ∫ z, g z ∂gaussianReal 0 1 := by
    rw [← heval, integral_map (measurable_pi_apply (0 : Fin 1)).aemeasurable hg.aestronglyMeasurable]
  rw [he (fun z => f (a*z+c)*z) (by fun_prop), he (fun z => f' (a*z+c)) (by fun_prop)] at HH
  exact HH

theorem gaussianAverage_variance_hasDerivAt (H : SparseSGD.External.GaussianSteinCertificate 1)
    (f f' f'' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hf'' : Continuous f'')
    (F D E : ℝ) (hF : ∀ x, |f x| ≤ F) (hD : ∀ x, |f' x| ≤ D)
    (hE : ∀ x, |f'' x| ≤ E) (c q : ℝ) (hq : 0 < q) :
    HasDerivAt (gaussianAverage f c) (gaussianAverage f'' c q/2) q := by
  have hfc' : Continuous f' := continuous_iff_continuousAt.mpr fun x => (hf' x).continuousAt
  have hd := (gaussian_scale_hasDerivAt f f' hf hfc' F D hF hD (Real.sqrt q) c).comp q
    (Real.hasDerivAt_sqrt hq.ne')
  have hs := gaussian_scalar_stein H f' f'' hf' hf'' D E hD hE (Real.sqrt q) c
  rw [hs] at hd
  convert hd using 1
  · rfl
  · dsimp [gaussianAverage]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hq)]

/-- Bounded continuous test functions give a continuous mean/variance average,
including variance zero. -/
theorem gaussianAverage_continuous (f : ℝ → ℝ) (hf : Continuous f)
    (F : ℝ) (hF : ∀ x, |f x| ≤ F) :
    Continuous (fun x : ℝ × ℝ => gaussianAverage f x.1 x.2) := by
  unfold gaussianAverage
  apply continuous_of_dominated (bound := fun _ => F)
  · intro x
    exact (hf.comp (by fun_prop)).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hF (Real.sqrt x.2*z+x.1))
  · exact integrable_const F
  · exact Eventually.of_forall (fun z => hf.comp (by fun_prop))

@[simp] theorem gaussianAverage_zero (f : ℝ → ℝ) (c : ℝ) :
    gaussianAverage f c 0 = f c := by simp [gaussianAverage]

/-- The heat identity extends to the boundary as a right derivative. -/
theorem gaussianAverage_variance_hasDerivWithinAt
    (H : SparseSGD.External.GaussianSteinCertificate 1)
    (f f' f'' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hf'' : Continuous f'')
    (F D E : ℝ) (hF : ∀ x, |f x| ≤ F) (hD : ∀ x, |f' x| ≤ D)
    (hE : ∀ x, |f'' x| ≤ E) (c q : ℝ) (hq : 0 ≤ q) :
    HasDerivWithinAt (gaussianAverage f c) (gaussianAverage f'' c q/2) (Ici 0) q := by
  rcases eq_or_lt_of_le hq with hq | hq
  · subst q
    have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
    have hc : Continuous (gaussianAverage f c) :=
      (gaussianAverage_continuous f hfc F hF).comp (continuous_const.prodMk continuous_id)
    have hc'' : Continuous (gaussianAverage f'' c) :=
      (gaussianAverage_continuous f'' hf'' E hE).comp (continuous_const.prodMk continuous_id)
    apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
      (fun x hx => (gaussianAverage_variance_hasDerivAt H f f' f'' hf hf' hf'' F D E hF hD hE c x hx).differentiableAt.differentiableWithinAt)
      hc.continuousAt.continuousWithinAt self_mem_nhdsWithin
    have hd : (fun x => deriv (gaussianAverage f c) x) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun x => gaussianAverage f'' c x/2) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (gaussianAverage_variance_hasDerivAt H f f' f'' hf hf' hf'' F D E hF hD hE c x hx).deriv
    exact ((hc''.div_const 2).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hd.symm
  · exact (gaussianAverage_variance_hasDerivAt H f f' f'' hf hf' hf'' F D E hF hD hE c q hq).hasDerivWithinAt

end
end SparseSGD.Probability
