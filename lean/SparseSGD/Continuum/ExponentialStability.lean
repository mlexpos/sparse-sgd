import SparseSGD.Continuum.PositiveFlow
import SparseSGD.Continuum.Hurwitz

open Set Filter
open scoped Topology

namespace SparseSGD
noncomputable section

/-- A covariance Lyapunov functional adapted to the subcritical feedback load. -/
def continuumStabilityEnergy (delta u : ℝ) (s : Moments) : ℝ :=
  (1 / (1 + u) + 1 / (2 * delta)) * s.R + delta / (1 + u) * s.V - s.C

def continuumStabilityGap (u : ℝ) : ℝ := (1 - u) / (1 + u)
def continuumStabilityComparison (delta u : ℝ) : ℝ := 1 / (1 + u) + 1 / delta + 1 / 2

def continuumStabilityRate (delta u : ℝ) : ℝ :=
  continuumStabilityGap u / continuumStabilityComparison delta u

private theorem stability_energy_bounds {delta u : ℝ} (hd : 0 < delta) (hu : 0 ≤ u)
    (s : Moments) (hs : s.psd) :
    continuumStabilityGap u / 2 * (s.R + delta * s.V) ≤ continuumStabilityEnergy delta u s ∧
    continuumStabilityEnergy delta u s ≤ continuumStabilityComparison delta u * (s.R + delta * s.V) := by
  have hR : 0 ≤ s.R := hs.diag_nonneg (i := 0)
  have hV : 0 ≤ s.V := hs.diag_nonneg (i := 1)
  have hminus := hs.dotProduct_mulVec_nonneg ![(1 : ℝ), -delta]
  have hplus := hs.dotProduct_mulVec_nonneg ![(1 : ℝ), delta]
  simp [Moments.cov, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hminus hplus
  have hm : 0 ≤ s.R - 2 * delta * s.C + delta ^ 2 * s.V := by nlinarith [hminus]
  have hp : 0 ≤ s.R + 2 * delta * s.C + delta ^ 2 * s.V := by nlinarith [hplus]
  have h1 : 1 + u ≠ 0 := by linarith
  have hlow : continuumStabilityEnergy delta u s -
      continuumStabilityGap u / 2 * (s.R + delta * s.V) =
      s.R / 2 + (s.R - 2 * delta * s.C + delta ^ 2 * s.V) / (2 * delta) := by
    dsimp [continuumStabilityEnergy, continuumStabilityGap]
    field_simp
    ring
  have hupp : continuumStabilityComparison delta u * (s.R + delta * s.V) -
      continuumStabilityEnergy delta u s =
      s.R / 2 + s.V + (s.R + 2 * delta * s.C + delta ^ 2 * s.V) / (2 * delta) := by
    dsimp [continuumStabilityEnergy, continuumStabilityComparison]
    field_simp
    ring
  constructor
  · have hnon : 0 ≤ s.R / 2 + (s.R - 2 * delta * s.C + delta ^ 2 * s.V) / (2 * delta) := by positivity
    linarith
  · have hnon : 0 ≤ s.R / 2 + s.V + (s.R + 2 * delta * s.C + delta ^ 2 * s.V) / (2 * delta) := by positivity
    linarith

theorem continuumStabilityRate_pos {delta u : ℝ} (hd : 0 < delta) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    0 < continuumStabilityRate delta u := by
  dsimp [continuumStabilityRate, continuumStabilityGap, continuumStabilityComparison]
  positivity

private theorem stability_energy_hasDerivAt {delta u : ℝ} (hd : 0 < delta) (hu : 0 ≤ u)
    (s : Moments) (t : ℝ) :
    HasDerivAt (fun t => continuumStabilityEnergy delta u (continuumFlow delta u 0 s t))
      (-continuumStabilityGap u * ((continuumFlow delta u 0 s t).R +
        delta * (continuumFlow delta u 0 s t).V)) t := by
  obtain ⟨hR, hV, hC⟩ := continuumFlow_hasDerivAt delta u 0 s t
  convert ((hR.const_mul (1 / (1 + u) + 1 / (2 * delta))).add
    (hV.const_mul (delta / (1 + u)))).sub hC using 1
  · rfl
  · dsimp [continuumField, continuumStabilityGap]
    have h1 : 1 + u ≠ 0 := by linarith
    field_simp
    ring

private theorem dissipative_exp_bound {W : ℝ → ℝ} {lambda : ℝ}
    (hW : ∀ t, 0 ≤ t → ∃ d, HasDerivAt W d t ∧ d ≤ -lambda * W t)
    {t : ℝ} (ht : 0 ≤ t) : W t ≤ W 0 * Real.exp (-lambda * t) := by
  have hd (x : ℝ) (hx : 0 ≤ x) :
      ∃ d, HasDerivAt (fun x => Real.exp (lambda * x) * W x) d x ∧ d ≤ 0 := by
    obtain ⟨d, hd, hb⟩ := hW x hx
    refine ⟨lambda * Real.exp (lambda * x) * W x + Real.exp (lambda * x) * d, ?_, ?_⟩
    · convert! (((hasDerivAt_id x).const_mul lambda).exp).mul hd using 1 <;>
        (simp only [id_eq]; ring)
    · have := mul_le_mul_of_nonneg_left hb (Real.exp_pos (lambda * x)).le
      nlinarith
  have hanti : AntitoneOn (fun x => Real.exp (lambda * x) * W x) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro x hx
      obtain ⟨d, hd, _⟩ := hd x hx
      exact hd.continuousAt.continuousWithinAt
    · intro x hx
      obtain ⟨d, hd, _⟩ := hd x (interior_subset hx)
      exact hd.differentiableAt.differentiableWithinAt
    · intro x hx
      obtain ⟨d, hd, hb⟩ := hd x (interior_subset hx)
      rwa [hd.deriv]
  have hb := hanti (by simp) ht ht
  simp only [mul_zero, Real.exp_zero, one_mul] at hb
  have he : Real.exp (lambda * t) * Real.exp (-lambda * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hh := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-lambda * t)).le
  calc
    W t = (Real.exp (lambda * t) * W t) * Real.exp (-lambda * t) := by
      calc
        W t = W t * (Real.exp (lambda * t) * Real.exp (-lambda * t)) := by rw [he, mul_one]
        _ = _ := by ring
    _ ≤ W 0 * Real.exp (-lambda * t) := hh

/-- The actual subcritical homogeneous continuum flow has exponential Lyapunov decay. -/
theorem continuumFlow_stabilityEnergy_exp_bound {delta u : ℝ}
    (hd : 0 < delta) (hu0 : 0 ≤ u) (hu1 : u < 1) (s : Moments) (hs : s.psd)
    {t : ℝ} (ht : 0 ≤ t) :
    continuumStabilityEnergy delta u (continuumFlow delta u 0 s t) ≤
      continuumStabilityEnergy delta u s * Real.exp (-continuumStabilityRate delta u * t) := by
  have hgap : 0 < continuumStabilityGap u := by dsimp [continuumStabilityGap]; positivity
  have hM : 0 < continuumStabilityComparison delta u := by dsimp [continuumStabilityComparison]; positivity
  have hrate : continuumStabilityRate delta u * continuumStabilityComparison delta u =
      continuumStabilityGap u := by
    dsimp [continuumStabilityRate]
    exact div_mul_cancel₀ _ hM.ne'
  have hb := dissipative_exp_bound (W := fun t => continuumStabilityEnergy delta u
    (continuumFlow delta u 0 s t)) (lambda := continuumStabilityRate delta u) ?_ ht
  · simpa only [continuumFlow_initial] using hb
  · intro x hx
    refine ⟨_, stability_energy_hasDerivAt hd hu0 s x, ?_⟩
    have hpsd := continuumFlow_psd hd hu0 (le_refl 0) s hs hx
    have hupp := (stability_energy_bounds hd hu0 (continuumFlow delta u 0 s x) hpsd).2
    have hsc := mul_le_mul_of_nonneg_left hupp (continuumStabilityRate_pos hd hu0 hu1).le
    rw [← mul_assoc, hrate] at hsc
    linarith

/-- Exponential decay of the second-moment energy of the actual subcritical continuum flow. -/
theorem continuumFlow_energy_exp_bound {delta u : ℝ}
    (hd : 0 < delta) (hu0 : 0 ≤ u) (hu1 : u < 1) (s : Moments) (hs : s.psd)
    {t : ℝ} (ht : 0 ≤ t) :
    (continuumFlow delta u 0 s t).R + delta * (continuumFlow delta u 0 s t).V ≤
      (2 * continuumStabilityComparison delta u / continuumStabilityGap u) *
        (s.R + delta * s.V) * Real.exp (-continuumStabilityRate delta u * t) := by
  have hgap : 0 < continuumStabilityGap u := by dsimp [continuumStabilityGap]; positivity
  have hpsd := continuumFlow_psd hd hu0 (le_refl 0) s hs ht
  have hlow := (stability_energy_bounds hd hu0 (continuumFlow delta u 0 s t) hpsd).1
  have hbound := continuumFlow_stabilityEnergy_exp_bound hd hu0 hu1 s hs ht
  have hinit := (stability_energy_bounds hd hu0 s hs).2
  have hinitexp := mul_le_mul_of_nonneg_right hinit (Real.exp_pos (-continuumStabilityRate delta u * t)).le
  have hh := hlow.trans (hbound.trans hinitexp)
  apply (mul_le_mul_iff_right₀ (show 0 < continuumStabilityGap u / 2 by positivity)).mp
  have hcancel : continuumStabilityGap u / 2 *
      ((2 * continuumStabilityComparison delta u / continuumStabilityGap u) *
        (s.R + delta * s.V) * Real.exp (-continuumStabilityRate delta u * t)) =
      continuumStabilityComparison delta u * (s.R + delta * s.V) *
        Real.exp (-continuumStabilityRate delta u * t) := by field_simp
  rw [hcancel]
  exact hh

/-- The sum of absolute moment coordinates. -/
def continuumMomentSize (s : Moments) : ℝ := |s.R| + |s.V| + |s.C|

/-- Coordinate difference of two moment states. -/
def continuumMomentDifference (s q : Moments) : Moments := ⟨s.R - q.R, s.V - q.V, s.C - q.C⟩
private def positivePart (s : Moments) : Moments :=
  ⟨s.R + continuumMomentSize s, s.V + continuumMomentSize s, s.C⟩
private def negativePart (s : Moments) : Moments :=
  ⟨continuumMomentSize s, continuumMomentSize s, 0⟩

private theorem absoluteCovariance_psd (c : ℝ) : (Moments.mk |c| |c| c).psd := by
  by_cases hc : 0 ≤ c
  · have h := (Matrix.posSemidef_vecMulVec_self_star ![(1 : ℝ), 1]).smul hc
    change (Moments.mk |c| |c| c).cov.PosSemidef
    have heq : (Moments.mk |c| |c| c).cov = c • Matrix.vecMulVec ![(1 : ℝ), 1] (star ![1, 1]) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Moments.cov, Matrix.vecMulVec, abs_of_nonneg hc]
    rw [heq]
    exact h
  · have hc' : 0 ≤ -c := by linarith
    have h := (Matrix.posSemidef_vecMulVec_self_star ![(1 : ℝ), -1]).smul hc'
    change (Moments.mk |c| |c| c).cov.PosSemidef
    have heq : (Moments.mk |c| |c| c).cov = (-c) • Matrix.vecMulVec ![(1 : ℝ), -1] (star ![1, -1]) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Moments.cov, Matrix.vecMulVec, abs_of_nonpos (le_of_not_ge hc)]
    rw [heq]
    exact h

private theorem positivePart_psd (s : Moments) : (positivePart s).psd := by
  have hr : 0 ≤ s.R + continuumMomentSize s - |s.C| := by
    dsimp [continuumMomentSize]
    linarith [neg_abs_le s.R, abs_nonneg s.V]
  have hv : 0 ≤ s.V + continuumMomentSize s - |s.C| := by
    dsimp [continuumMomentSize]
    linarith [neg_abs_le s.V, abs_nonneg s.R]
  have hdiag : (Matrix.diagonal ![s.R + continuumMomentSize s - |s.C|,
      s.V + continuumMomentSize s - |s.C|]).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i
    · exact hr
    · exact hv
  have h := hdiag.add (absoluteCovariance_psd s.C)
  change (positivePart s).cov.PosSemidef
  have heq : (positivePart s).cov = Matrix.diagonal ![s.R + continuumMomentSize s - |s.C|,
      s.V + continuumMomentSize s - |s.C|] + (Moments.mk |s.C| |s.C| s.C).cov := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [positivePart, Moments.cov, Matrix.diagonal] <;> ring
  rw [heq]
  exact h

private theorem negativePart_psd (s : Moments) : (negativePart s).psd := by
  have hsize : 0 ≤ continuumMomentSize s := by dsimp [continuumMomentSize]; positivity
  have hdiag : (Matrix.diagonal ![continuumMomentSize s, continuumMomentSize s]).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> exact hsize
  change (negativePart s).cov.PosSemidef
  have heq : (negativePart s).cov = Matrix.diagonal ![continuumMomentSize s, continuumMomentSize s] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [negativePart, Moments.cov, Matrix.diagonal]
  rw [heq]
  exact hdiag

private theorem continuumFlow_difference (delta u : ℝ) (s q : Moments) {t : ℝ} (ht : 0 ≤ t) :
    continuumFlow delta u 0 (continuumMomentDifference s q) t =
      continuumMomentDifference (continuumFlow delta u 0 s t) (continuumFlow delta u 0 q t) := by
  have hsol : IsMomentSolution delta u 0 (fun t =>
      continuumMomentDifference (continuumFlow delta u 0 s t) (continuumFlow delta u 0 q t)) := by
    intro x _
    obtain ⟨hsR, hsV, hsC⟩ := continuumFlow_hasDerivAt delta u 0 s x
    obtain ⟨hqR, hqV, hqC⟩ := continuumFlow_hasDerivAt delta u 0 q x
    refine ⟨?_, ?_, ?_⟩
    · convert hsR.sub hqR using 1 <;> (first | rfl | (simp [continuumMomentDifference, continuumField]; try ring))
    · convert hsV.sub hqV using 1 <;> (first | rfl | (simp [continuumMomentDifference, continuumField]; try ring))
    · convert hsC.sub hqC using 1 <;> (first | rfl | (simp [continuumMomentDifference, continuumField]; try ring))
  exact (continuum_solution_unique delta u 0 (continuumMomentDifference s q) _
    (by simp only [continuumFlow_initial]) hsol t ht).symm

private theorem psd_momentSize_bound {delta : ℝ} (hd : 0 < delta) (s : Moments) (hs : s.psd) :
    continuumMomentSize s ≤ 2 * (1 + 1 / delta) * (s.R + delta * s.V) := by
  have hr : 0 ≤ s.R := hs.diag_nonneg (i := 0)
  have hv : 0 ≤ s.V := hs.diag_nonneg (i := 1)
  have hm := hs.dotProduct_mulVec_nonneg ![(1 : ℝ), -1]
  have hp := hs.dotProduct_mulVec_nonneg ![(1 : ℝ), 1]
  simp [Moments.cov, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hm hp
  have hc : |s.C| ≤ s.R + s.V := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have henergy : s.R + s.V ≤ (1 + 1 / delta) * (s.R + delta * s.V) := by
    have heq : (1 + 1 / delta) * (s.R + delta * s.V) - (s.R + s.V) =
        s.R / delta + delta * s.V := by field_simp; ring
    have hn : 0 ≤ s.R / delta + delta * s.V := by positivity
    linarith
  dsimp [continuumMomentSize]
  rw [abs_of_nonneg hr, abs_of_nonneg hv]
  linarith

private theorem momentSize_difference_le (s q : Moments) :
    continuumMomentSize (continuumMomentDifference s q) ≤ continuumMomentSize s + continuumMomentSize q := by
  dsimp [continuumMomentSize, continuumMomentDifference]
  linarith [abs_sub s.R q.R, abs_sub s.V q.V, abs_sub s.C q.C]

/-- Actual exponential stability of the homogeneous continuum flow for arbitrary signed moments. -/
theorem continuumFlow_exponentially_stable {delta u : ℝ}
    (hd : 0 < delta) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ A lambda : ℝ, 0 < A ∧ 0 < lambda ∧ ∀ s : Moments, ∀ t : ℝ, 0 ≤ t →
      continuumMomentSize (continuumFlow delta u 0 s t) ≤
        A * continuumMomentSize s * Real.exp (-lambda * t) := by
  let D := 2 * (1 + 1 / delta)
  let F := 2 * continuumStabilityComparison delta u / continuumStabilityGap u
  let A := D * F * (3 * (1 + delta))
  have hgap : 0 < continuumStabilityGap u := by dsimp [continuumStabilityGap]; positivity
  have hM : 0 < continuumStabilityComparison delta u := by dsimp [continuumStabilityComparison]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨A, continuumStabilityRate delta u, by dsimp [A]; positivity,
    continuumStabilityRate_pos hd hu0 hu1, ?_⟩
  intro s t ht
  have hP := positivePart_psd s
  have hN := negativePart_psd s
  have hFP := continuumFlow_psd hd hu0 (le_refl 0) (positivePart s) hP ht
  have hFN := continuumFlow_psd hd hu0 (le_refl 0) (negativePart s) hN ht
  have hbp := psd_momentSize_bound hd _ hFP
  have hbn := psd_momentSize_bound hd _ hFN
  have hep := continuumFlow_energy_exp_bound hd hu0 hu1 (positivePart s) hP ht
  have hen := continuumFlow_energy_exp_bound hd hu0 hu1 (negativePart s) hN ht
  have hsp := mul_le_mul_of_nonneg_left hep hD.le
  have hsn := mul_le_mul_of_nonneg_left hen hD.le
  have hdiff : continuumMomentDifference (positivePart s) (negativePart s) = s := by
    apply Moments.ext <;> simp [continuumMomentDifference, positivePart, negativePart]
  have hflow := continuumFlow_difference delta u (positivePart s) (negativePart s) ht
  rw [hdiff] at hflow
  rw [hflow]
  have hsize := momentSize_difference_le
    (continuumFlow delta u 0 (positivePart s) t) (continuumFlow delta u 0 (negativePart s) t)
  have hsum : (positivePart s).R + delta * (positivePart s).V +
      ((negativePart s).R + delta * (negativePart s).V) ≤
      3 * (1 + delta) * continuumMomentSize s := by
    have hr : s.R ≤ continuumMomentSize s := by
      dsimp [continuumMomentSize]
      linarith [le_abs_self s.R, abs_nonneg s.V, abs_nonneg s.C]
    have hv : s.V ≤ continuumMomentSize s := by
      dsimp [continuumMomentSize]
      linarith [le_abs_self s.V, abs_nonneg s.R, abs_nonneg s.C]
    have hvdelta := mul_le_mul_of_nonneg_left hv hd.le
    dsimp [positivePart, negativePart]
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ D * F * Real.exp (-continuumStabilityRate delta u * t) by positivity)
  dsimp [D, F] at hsp hsn
  have hbtotal := hsize.trans (add_le_add (hbp.trans hsp) (hbn.trans hsn))
  dsimp [A, D, F] at hscaled ⊢
  nlinarith [hbtotal]


/-- An affine trajectory relative to an equilibrium is the homogeneous flow of its displacement. -/
theorem continuumFlow_equilibrium_shift (delta u phi : ℝ) (s q : Moments)
    (hq : continuumField delta u phi q = 0) {t : ℝ} (ht : 0 ≤ t) :
    continuumMomentDifference (continuumFlow delta u phi s t) q =
      continuumFlow delta u 0 (continuumMomentDifference s q) t := by
  have hqR := congrArg Moments.R hq
  have hqV := congrArg Moments.V hq
  have hqC := congrArg Moments.C hq
  change -2 * delta * q.C = 0 at hqR
  change 2 * q.C - 2 * q.V + 2 / delta * (u * q.R + phi) = 0 at hqV
  change q.R - q.C - delta * q.V = 0 at hqC
  have hsol : IsMomentSolution delta u 0 (fun t =>
      continuumMomentDifference (continuumFlow delta u phi s t) q) := by
    intro x _
    obtain ⟨hR, hV, hC⟩ := continuumFlow_hasDerivAt delta u phi s x
    refine ⟨?_, ?_, ?_⟩
    · convert hR.sub_const q.R using 1 <;>
        (first | rfl | (dsimp [continuumMomentDifference, continuumField]; linear_combination -hqR))
    · convert hV.sub_const q.V using 1 <;>
        (first | rfl | (dsimp [continuumMomentDifference, continuumField]; linear_combination -hqV))
    · convert hC.sub_const q.C using 1 <;>
        (first | rfl | (dsimp [continuumMomentDifference, continuumField]; linear_combination -hqC))
  exact continuum_solution_unique delta u 0 (continuumMomentDifference s q) _
    (by simp only [continuumFlow_initial]) hsol t ht

/-- Every affine equilibrium attracts all signed moments at a uniform exponential rate. -/
theorem continuumFlow_equilibrium_exponential_bound {delta u : ℝ}
    (hd : 0 < delta) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ A lambda : ℝ, 0 < A ∧ 0 < lambda ∧ ∀ (phi : ℝ) (s q : Moments),
      continuumField delta u phi q = 0 → ∀ t : ℝ, 0 ≤ t →
      continuumMomentSize (continuumMomentDifference (continuumFlow delta u phi s t) q) ≤
        A * continuumMomentSize (continuumMomentDifference s q) * Real.exp (-lambda * t) := by
  obtain ⟨A, lambda, hA, hl, hbound⟩ := continuumFlow_exponentially_stable hd hu0 hu1
  refine ⟨A, lambda, hA, hl, ?_⟩
  intro phi s q hq t ht
  rw [continuumFlow_equilibrium_shift delta u phi s q hq ht]
  exact hbound _ t ht

private def realEigenMoments (delta x : ℝ) : Moments :=
  ⟨1, (x ^ 2 + x + 2 * delta) / (2 * delta ^ 2), -x / (2 * delta)⟩

private def realEigenTrajectory (delta x t : ℝ) : Moments :=
  ⟨Real.exp (x * t), (realEigenMoments delta x).V * Real.exp (x * t),
    (realEigenMoments delta x).C * Real.exp (x * t)⟩

private theorem realEigenTrajectory_isMomentSolution {delta u x : ℝ} (hd : delta ≠ 0)
    (hx : spectrumPolynomial delta u x = 0) :
    IsMomentSolution delta u 0 (realEigenTrajectory delta x) := by
  have hR : x = -2 * delta * (realEigenMoments delta x).C := by
    dsimp [realEigenMoments]; field_simp
  have hV : (realEigenMoments delta x).V * x =
      2 * (realEigenMoments delta x).C - 2 * (realEigenMoments delta x).V + 2 / delta * u := by
    dsimp [realEigenMoments]
    dsimp [spectrumPolynomial] at hx
    field_simp
    linear_combination hx
  have hC : (realEigenMoments delta x).C * x =
      1 - (realEigenMoments delta x).C - delta * (realEigenMoments delta x).V := by
    dsimp [realEigenMoments]; field_simp; ring
  intro t _
  have he : HasDerivAt (fun t : ℝ => Real.exp (x * t)) (Real.exp (x * t) * x) t :=
    by simpa using ((hasDerivAt_id t).const_mul x).exp
  refine ⟨?_, ?_, ?_⟩
  · convert he using 1 <;> (first | rfl | (dsimp [realEigenTrajectory, continuumField]; nlinarith [congrArg (fun z : ℝ => z * Real.exp (x * t)) hR]))
  · convert he.const_mul (realEigenMoments delta x).V using 1 <;>
      (first | rfl | (dsimp [realEigenTrajectory, continuumField]; nlinarith [congrArg (fun z : ℝ => z * Real.exp (x * t)) hV]))
  · convert he.const_mul (realEigenMoments delta x).C using 1 <;>
      (first | rfl | (dsimp [realEigenTrajectory, continuumField]; nlinarith [congrArg (fun z : ℝ => z * Real.exp (x * t)) hC]))

/-- At and above the critical load there is an actual nondecaying trajectory. -/
theorem continuumFlow_not_exponentially_stable {delta u : ℝ}
    (hd : 0 < delta) (hu : 1 ≤ u) :
    ¬ ∃ A lambda : ℝ, 0 < A ∧ 0 < lambda ∧ ∀ s : Moments, ∀ t : ℝ, 0 ≤ t →
      continuumMomentSize (continuumFlow delta u 0 s t) ≤
        A * continuumMomentSize s * Real.exp (-lambda * t) := by
  rintro ⟨A, lambda, hA, hl, hbound⟩
  obtain ⟨x, hx0, hx⟩ := exists_nonneg_spectrum_root delta u hd hu
  have hflow {t : ℝ} (ht : 0 ≤ t) :
      continuumFlow delta u 0 (realEigenMoments delta x) t = realEigenTrajectory delta x t := by
    exact (continuum_solution_unique delta u 0 (realEigenMoments delta x) _
      (by simp [realEigenTrajectory, realEigenMoments])
      (realEigenTrajectory_isMomentSolution hd.ne' hx) t ht).symm
  have hge {t : ℝ} (ht : 0 ≤ t) :
      1 ≤ A * continuumMomentSize (realEigenMoments delta x) * Real.exp (-lambda * t) := by
    have hb := hbound (realEigenMoments delta x) t ht
    rw [hflow ht] at hb
    have he : 1 ≤ Real.exp (x * t) := by exact Real.one_le_exp (mul_nonneg hx0 ht)
    have hn := abs_nonneg ((realEigenTrajectory delta x t).V)
    have hc := abs_nonneg ((realEigenTrajectory delta x t).C)
    have hab : |(realEigenTrajectory delta x t).R| = Real.exp (x * t) :=
      abs_of_pos (Real.exp_pos _)
    dsimp [continuumMomentSize] at hb
    rw [hab] at hb
    dsimp [continuumMomentSize]
    linarith
  have he : Tendsto (fun t : ℝ => Real.exp (-lambda * t)) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hl) using 1 <;>
      simp [Function.comp_def, neg_mul]
  have hlim := he.const_mul (A * continuumMomentSize (realEigenMoments delta x))
  have hcontra : (1 : ℝ) ≤ 0 := by
    have hh : (1 : ℝ) ≤ A * continuumMomentSize (realEigenMoments delta x) * 0 := by
      apply ge_of_tendsto hlim
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hge ht
    simpa using hh
  linarith

/-- The exact subcritical threshold for uniform exponential stability of the actual flow. -/
theorem continuumFlow_exponentially_stable_iff {delta u : ℝ} (hd : 0 < delta) (hu : 0 ≤ u) :
    (∃ A lambda : ℝ, 0 < A ∧ 0 < lambda ∧ ∀ s : Moments, ∀ t : ℝ, 0 ≤ t →
      continuumMomentSize (continuumFlow delta u 0 s t) ≤
        A * continuumMomentSize s * Real.exp (-lambda * t)) ↔ u < 1 := by
  constructor
  · intro h
    by_contra hn
    exact continuumFlow_not_exponentially_stable hd (le_of_not_gt hn) h
  · exact continuumFlow_exponentially_stable hd hu

end
end SparseSGD
