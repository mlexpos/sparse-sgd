import SparseSGD.Logistic.IncrementGlobalEnvelope
import SparseSGD.Logistic.IncrementBoundedMGF

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

def pairedDifference {X : Type*} (f : X → ℝ) (z : X × X) : ℝ := f z.1-f z.2

theorem paired_weighted_moment {X : Type*} [MeasurableSpace X]
    (κ : Measure X) [IsProbabilityMeasure κ] (f : X → ℝ) (hfm : Measurable f)
    (n : ℕ) (hn : 0 < n) (s b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hI : Integrable (fun x => |f x|^n*Real.exp (|s| * |f x|)) κ)
    (heI : Integrable (fun x => Real.exp (|s| * |f x|)) κ)
    (hB : (∫ x, |f x|^n*Real.exp (|s| * |f x|) ∂κ) ≤ b)
    (heB : (∫ x, Real.exp (|s| * |f x|) ∂κ) ≤ c) :
    Integrable (fun z => |pairedDifference f z|^n*Real.exp (|s| * |pairedDifference f z|)) (κ.prod κ) ∧
    (∫ z, |pairedDifference f z|^n*Real.exp (|s| * |pairedDifference f z|) ∂κ.prod κ) ≤
      2^n*b*c := by
  let U := fun x => |f x|^n*Real.exp (|s| * |f x|)
  let V := fun x => Real.exp (|s| * |f x|)
  let M := fun z : X × X => (2 : ℝ)^(n-1)*(U z.1*V z.2+V z.1*U z.2)
  have hMI : Integrable M (κ.prod κ) := ((hI.mul_prod heI).add (heI.mul_prod hI)).const_mul _
  have hpoint (z : X × X) : |pairedDifference f z|^n*Real.exp (|s| * |pairedDifference f z|) ≤ M z := by
    have ha : |pairedDifference f z| ≤ |f z.1|+|f z.2| := by
      exact abs_sub (f z.1) (f z.2)
    have hp := (pow_le_pow_left₀ (abs_nonneg _) ha n).trans
      (add_pow_le (abs_nonneg (f z.1)) (abs_nonneg (f z.2)) n)
    have he : Real.exp (|s| * |pairedDifference f z|) ≤ Real.exp (|s| * |f z.1|)*Real.exp (|s| * |f z.2|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left ha (abs_nonneg s)]
    have hh := mul_le_mul hp he (Real.exp_pos _).le (by positivity : 0 ≤ (2 : ℝ)^(n-1)*(|f z.1|^n+|f z.2|^n))
    exact hh.trans_eq (by dsimp [M, U, V]; ring)
  have hm : Measurable (pairedDifference f) := (hfm.comp measurable_fst).sub (hfm.comp measurable_snd)
  have hi : Integrable (fun z => |pairedDifference f z|^n*Real.exp (|s| * |pairedDifference f z|)) (κ.prod κ) := by
    apply hMI.mono' ((hm.abs.pow_const n).mul
      (Real.measurable_exp.comp (measurable_const.mul hm.abs))).aestronglyMeasurable
    filter_upwards with z
    change ‖|pairedDifference f z|^n*Real.exp (|s| * |pairedDifference f z|)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpoint z
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi hMI hpoint
  have heM : (∫ z, M z ∂κ.prod κ) = (2 : ℝ)^(n-1)*
      ((∫ x, U x ∂κ)*(∫ x, V x ∂κ)+(∫ x, V x ∂κ)*(∫ x, U x ∂κ)) := by
    dsimp [M]
    rw [integral_const_mul, integral_add (hI.mul_prod heI) (heI.mul_prod hI),
      integral_prod_mul U V, integral_prod_mul V U]
  rw [heM] at hh
  have hUb : (∫ x, U x ∂κ)*(∫ x, V x ∂κ) ≤ b*c :=
    mul_le_mul hB heB (integral_nonneg (fun _ => by positivity)) hb
  have hcoef : (2 : ℝ)^(n-1)*2 ≤ 2^n := by
    have he : n-1+1 = n := by omega
    rw [← pow_succ, he]
  have hs := mul_le_mul_of_nonneg_left (show (∫ x, U x ∂κ)*(∫ x, V x ∂κ)+
      (∫ x, V x ∂κ)*(∫ x, U x ∂κ) ≤ 2*b*c by nlinarith)
      (show 0 ≤ (2 : ℝ)^(n-1) by positivity)
  have hc' := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hb hc)
  nlinarith

def symmetricProjectionConstant (Q : ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ)^n*(n.factorial : ℝ)*(4*Real.exp (2*Q^2+4))*(2*Real.exp (1/2))

theorem tame_paired_projection_weighted_moment {d : ℕ} (p : unitInterval)
    (mu theta u : Vec d) (Q s : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hp : 0 < (p : ℝ)) (htame : tameError p mu theta ≤ 1/2)
    (hθ : ‖theta‖ ≤ Q) (hu : ‖u‖ ≤ 1) (hmu : |inner ℝ u mu| ≤ 1) :
    Integrable (fun z : Sample d × Sample d =>
      |pairedDifference (fun a => inner ℝ u (gradient p mu theta a)) z|^n*
      Real.exp (|s| * |pairedDifference (fun a => inner ℝ u (gradient p mu theta a)) z|))
        ((sampleLaw d p).prod (sampleLaw d p)) ∧
    (∫ z : Sample d × Sample d,
      |pairedDifference (fun a => inner ℝ u (gradient p mu theta a)) z|^n*
      Real.exp (|s| * |pairedDifference (fun a => inner ℝ u (gradient p mu theta a)) z|)
      ∂((sampleLaw d p).prod (sampleLaw d p))) ≤
        symmetricProjectionConstant Q n*(p : ℝ)*Real.exp (3*s^2) := by
  have hw := tame_global_projection_weighted_moment p mu theta u Q s n hn hp htame hθ hu hmu
  have he := normalized_projection_exp_abs_bound p mu theta u s hu hmu
  have hm : Measurable (fun a : Sample d => inner ℝ u (gradient p mu theta a)) :=
    measurable_const.inner ((measurable_gradient d p mu).comp
      (f := fun a : Sample d => (theta,a)) (measurable_const.prodMk measurable_id))
  have hh := paired_weighted_moment (sampleLaw d p) _ hm n (by omega) s _ _
    (by positivity) (by positivity) hw.1 he.1 hw.2 he.2
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  have hex : Real.exp (2*s^2)*Real.exp (s^2) = Real.exp (3*s^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp [symmetricProjectionConstant]
  calc
    _ = (2 : ℝ)^n*(n.factorial : ℝ)*(4*Real.exp (2*Q^2+4))*(2*Real.exp (1/2))*(p : ℝ)*
      (Real.exp (2*s^2)*Real.exp (s^2)) := by ring
    _ = _ := by rw [hex]

end
end SparseSGD.Logistic
