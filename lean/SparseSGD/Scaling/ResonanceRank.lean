import SparseSGD.Scaling.ColdRegular
import SparseSGD.Continuum.PositiveFlow

open Filter Set Topology
namespace SparseSGD
noncomputable section

/-- Positive additive forcing prevents the risk trajectory from vanishing
identically, even from a zero cold start. -/
theorem continuumFlow_nonzeroRisk_of_positive_forcing {d u phi : ℝ}
    (hd : 0 < d) (hp : 0 < phi) (s : Moments) :
    ∃ t, 0 ≤ t ∧ (continuumFlow d u phi s t).R ≠ 0 := by
  by_contra H
  have hR (t : ℝ) (ht : 0 < t) : (continuumFlow d u phi s t).R=0 := by
    by_contra hne
    exact H ⟨t,ht.le,hne⟩
  have hC (t : ℝ) (ht : 0 < t) : (continuumFlow d u phi s t).C=0 := by
    have Hz : HasDerivAt (fun x => (continuumFlow d u phi s x).R) 0 t :=
      (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
        (eventually_of_mem (Ioi_mem_nhds ht) (fun x hx => hR x hx))
    have He := (continuumFlow_hasDerivAt d u phi s t).1.unique Hz
    change -2*d*(continuumFlow d u phi s t).C=0 at He
    nlinarith
  have hV (t : ℝ) (ht : 0 < t) : (continuumFlow d u phi s t).V=0 := by
    have Hz : HasDerivAt (fun x => (continuumFlow d u phi s x).C) 0 t :=
      (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
        (eventually_of_mem (Ioi_mem_nhds ht) (fun x hx => hC x hx))
    have He := (continuumFlow_hasDerivAt d u phi s t).2.2.unique Hz
    change (continuumFlow d u phi s t).R-(continuumFlow d u phi s t).C-
      d*(continuumFlow d u phi s t).V=0 at He
    rw [hR t ht,hC t ht] at He
    nlinarith
  have Hz : HasDerivAt (fun x => (continuumFlow d u phi s x).V) 0 1 :=
    (hasDerivAt_const 1 (0 : ℝ)).congr_of_eventuallyEq
      (eventually_of_mem (Ioi_mem_nhds (by norm_num : (0 : ℝ)<1)) (fun x hx => hV x hx))
  have He := (continuumFlow_hasDerivAt d u phi s 1).2.1.unique Hz
  change 2*(continuumFlow d u phi s 1).C-2*(continuumFlow d u phi s 1).V+
    2/d*(u*(continuumFlow d u phi s 1).R+phi)=0 at He
  rw [hR 1 (by norm_num),hC 1 (by norm_num),hV 1 (by norm_num)] at He
  have Hpos : 0 < 2/d*phi := by positivity
  nlinarith

/-- The source resonance limit has strictly positive covariance determinant
at every positive time, including positive label noise from the zero state. -/
theorem cor_resonance_rank (D u variance R : ℝ) (hD : 0 < D) (hu : 0 < u)
    (hvar : 0 ≤ variance) (hR : 0 ≤ R) (hn : 0 < R ∨ 0 < variance)
    (t : ℝ) (ht : 0 < t) :
    0 < (continuumFlow D u (variance*u) ⟨R,0,0⟩ t).rankDefect ∧
    (continuumFlow D u (variance*u) ⟨R,0,0⟩ t).cov.PosDef := by
  have hphi : 0 ≤ variance*u := mul_nonneg hvar hu.le
  have hnonzero : ∃ y, 0 ≤ y ∧ (continuumFlow D u (variance*u) ⟨R,0,0⟩ y).R ≠ 0 := by
    rcases hn with hRp | hvp
    · refine ⟨0,le_rfl,?_⟩
      simpa [continuumFlow_initial] using hRp.ne'
    · exact continuumFlow_nonzeroRisk_of_positive_forcing hD (mul_pos hvp hu) _
  exact ⟨continuumFlow_rankDefect_pos hD hu.le hphi (by linarith) _
    (coldMoments_psd R hR) hnonzero ht,
    continuumFlow_cov_posDef hD hu.le hphi (by linarith) _
    (coldMoments_psd R hR) hnonzero ht⟩

end
end SparseSGD
