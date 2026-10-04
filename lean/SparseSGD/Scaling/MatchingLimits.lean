import SparseSGD.Scaling.MatchingApproximation

open Filter Topology

namespace SparseSGD.Scaling
noncomputable section

def rawDelta (p : SparseSGD.Params) : ℝ := p.w / p.eps^2

def retentionEps (p : SparseSGD.Params) : ℝ := p.eps

theorem small_step_matchedDelta_tendsto_finite
    (P : ℕ → SparseSGD.Params) (Delta : ℕ → ℝ) (D : ℝ)
    (hbeta : ∀ᶠ d : ℕ in atTop, 1/2 ≤ (P d).beta ∧ (P d).beta < 1)
    (hDpos : ∀ᶠ d : ℕ in atTop, 0 < Delta d)
    (hw : ∀ᶠ d : ℕ in atTop, (P d).w = Delta d * (P d).eps^2)
    (heps : Tendsto (fun d => (P d).eps) atTop (𝓝 0))
    (hDelta : Tendsto Delta atTop (𝓝 D)) :
    Tendsto (fun d => (P d).matchedDelta) atTop (𝓝 D) := by
  have hWprod : Tendsto (fun d => Delta d * (P d).eps^2) atTop (𝓝 0) := by
    have heps2 : Tendsto (fun d => (P d).eps^2) atTop (𝓝 (0 : ℝ)) := by simpa using heps.pow 2
    simpa using hDelta.mul heps2
  have hW : Tendsto (fun d => (P d).w) atTop (𝓝 0) := by
    apply hWprod.congr'
    filter_upwards [hw] with d hd
    rw [hd]
  have hwsmall : ∀ᶠ d : ℕ in atTop, (P d).w ≤ 1/16 := by
    filter_upwards [hW.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/16))] with d hd
    linarith
  have hK : Tendsto (fun d => (128*Delta d^2+10*Delta d+7)) atTop
      (𝓝 (128*D^2+10*D+7)) := by
    have h1 : Tendsto (fun d => 128*Delta d^2) atTop (𝓝 (128*D^2)) := by simpa using (tendsto_const_nhds.mul (hDelta.pow 2))
    have h2 : Tendsto (fun d => 10*Delta d) atTop (𝓝 (10*D)) := by simpa using (tendsto_const_nhds.mul hDelta)
    simpa using (h1.add h2).add tendsto_const_nhds
  have hbound : Tendsto (fun d => (128*Delta d^2+10*Delta d+7)*(P d).eps) atTop (𝓝 0) := by
    simpa using hK.mul heps
  have habs : Tendsto (fun d => |(P d).matchedDelta-Delta d|) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => 0)
      (h := fun d => (128*Delta d^2+10*Delta d+7)*(P d).eps)
    · exact tendsto_const_nhds
    · exact hbound
    · exact Filter.Eventually.of_forall (fun d => abs_nonneg _ )
    · filter_upwards [hbeta,hDpos,hw,hwsmall] with d hb hD hw' hw1
      rcases hb with ⟨hb0,hb1⟩
      have heps0 : 0 < (P d).eps := by dsimp [SparseSGD.Params.eps]; linarith
      have H := (P d).small_step_matchedDelta (Delta d) hb0 hb1 hD hw' hw1
      exact H
  have herr : Tendsto (fun d => (P d).matchedDelta-Delta d) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun d => -|(P d).matchedDelta-Delta d|)
      (h := fun d => |(P d).matchedDelta-Delta d|)
    · simpa using habs.neg
    · exact habs
    · exact Filter.Eventually.of_forall (fun _ => neg_abs_le _)
    · exact Filter.Eventually.of_forall (fun _ => le_abs_self _)
  have hsum := hDelta.add herr
  have heq : (fun d => Delta d + ((P d).matchedDelta-Delta d)) =ᶠ[atTop]
      (fun d => (P d).matchedDelta) := Filter.Eventually.of_forall (fun d => by ring)
  simpa using hsum.congr' heq

theorem small_step_matchedDelta_relative_tendsto_one
    (P : ℕ → SparseSGD.Params) (Delta : ℕ → ℝ)
    (hbeta : ∀ᶠ d : ℕ in atTop, 1/2 ≤ (P d).beta ∧ (P d).beta < 1)
    (hDone : ∀ᶠ d : ℕ in atTop, 1 ≤ Delta d)
    (hw : ∀ᶠ d : ℕ in atTop, (P d).w = Delta d * (P d).eps^2)
    (hw0 : Tendsto (fun d => (P d).w) atTop (𝓝 0))
    (heps : Tendsto (fun d => (P d).eps) atTop (𝓝 0)) :
    Tendsto (fun d => (P d).matchedDelta / Delta d) atTop (𝓝 1) := by
  have hbound : Tendsto (fun d => 130*(P d).w+15*(P d).eps) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hw0).add (tendsto_const_nhds.mul heps)
  have habs : Tendsto (fun d => |(P d).matchedDelta / Delta d - 1|) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => 0)
      (h := fun d => 130*(P d).w+15*(P d).eps)
    · exact tendsto_const_nhds
    · exact hbound
    · exact Filter.Eventually.of_forall (fun d => abs_nonneg _)
    · filter_upwards [hbeta,hDone,hw,hw0.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/16))] with d hb hD hw' hwsmall
      rcases hb with ⟨hb0,hb1⟩
      have hw1 : (P d).w ≤ 1/16 := by linarith
      exact (P d).small_step_matchedDelta_relative (Delta d) hb0 hb1 hD hw' hw1
  have hminus : Tendsto (fun d => (P d).matchedDelta / Delta d - 1) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun d => -|(P d).matchedDelta / Delta d - 1|)
      (h := fun d => |(P d).matchedDelta / Delta d - 1|)
    · simpa using habs.neg
    · exact habs
    · exact Filter.Eventually.of_forall (fun _ => neg_abs_le _)
    · exact Filter.Eventually.of_forall (fun _ => le_abs_self _)
  have hplus := hminus.add_const 1
  simpa [sub_add_cancel] using hplus

theorem small_step_matchedDelta_tendsto_atTop
    (P : ℕ → SparseSGD.Params) (Delta : ℕ → ℝ)
    (hbeta : ∀ᶠ d : ℕ in atTop, 1/2 ≤ (P d).beta ∧ (P d).beta < 1)
    (hDpos : ∀ᶠ d : ℕ in atTop, 0 < Delta d)
    (hDlarge : Tendsto Delta atTop atTop)
    (hw : ∀ᶠ d : ℕ in atTop, (P d).w = Delta d * (P d).eps^2)
    (hw0 : Tendsto (fun d => (P d).w) atTop (𝓝 0))
    (heps : Tendsto (fun d => (P d).eps) atTop (𝓝 0)) :
    Tendsto (fun d => (P d).matchedDelta) atTop atTop := by
  have hrel : Tendsto (fun d => (P d).matchedDelta / Delta d) atTop (𝓝 1) := by
    have hbound : Tendsto (fun d => 130*(P d).w+15*(P d).eps) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hw0).add (tendsto_const_nhds.mul heps)
    have habs : Tendsto (fun d => |(P d).matchedDelta / Delta d - 1|) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => 0)
        (h := fun d => 130*(P d).w+15*(P d).eps)
      · exact tendsto_const_nhds
      · exact hbound
      · exact Filter.Eventually.of_forall (fun d => abs_nonneg _)
      · filter_upwards [hbeta,hDpos,hDlarge.eventually (eventually_ge_atTop (1:ℝ)),hw,hw0.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/16))] with d hb hD hlarge hw' hwsmall
        rcases hb with ⟨hb0,hb1⟩
        have hw1 : (P d).w ≤ 1/16 := by linarith
        exact (P d).small_step_matchedDelta_relative (Delta d) hb0 hb1 hlarge hw' hw1
    have hminus : Tendsto (fun d => (P d).matchedDelta / Delta d - 1) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun d => -|(P d).matchedDelta / Delta d - 1|)
        (h := fun d => |(P d).matchedDelta / Delta d - 1|)
      · simpa using habs.neg
      · exact habs
      · exact Filter.Eventually.of_forall (fun _ => neg_abs_le _)
      · exact Filter.Eventually.of_forall (fun _ => le_abs_self _)
    have hplus := hminus.add_const 1
    simpa [sub_add_cancel] using hplus
  have hrelpos : ∀ᶠ d : ℕ in atTop, 0 < (P d).matchedDelta/Delta d := by
    filter_upwards [hrel.eventually (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))] with d hd
    linarith
  have hprod : Tendsto (fun d => Delta d * ((P d).matchedDelta/Delta d)) atTop atTop :=
    hDlarge.atTop_mul_pos (by norm_num) hrel
  have heq : (fun d => Delta d * ((P d).matchedDelta/Delta d)) =ᶠ[atTop]
      (fun d => (P d).matchedDelta) := by
    filter_upwards [hDpos] with d hD
    field_simp
  exact hprod.congr' heq

theorem small_step_matchedStep_tendsto_zero
    (P : ℕ → SparseSGD.Params)
    (hbeta : ∀ᶠ d : ℕ in atTop, 1/2 ≤ (P d).beta ∧ (P d).beta < 1)
    (heps : Tendsto (fun d => (P d).eps) atTop (𝓝 0)) :
    Tendsto (fun d => (P d).matchedStep) atTop (𝓝 0) := by
  have hupper : Tendsto (fun d => (P d).eps+2*(P d).eps^2) atTop (𝓝 (0:ℝ)) := by
    have h2 : Tendsto (fun d => (P d).eps^2) atTop (𝓝 (0:ℝ)) := by simpa using heps.pow 2
    simpa using heps.add (tendsto_const_nhds.mul h2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => 0)
    (h := fun d => (P d).eps+2*(P d).eps^2)
  · exact tendsto_const_nhds
  · exact hupper
  · filter_upwards [hbeta] with d hb
    rcases hb with ⟨hb0,hb1⟩
    have ⟨he,he1,hh0,hh1,_⟩ := (P d).small_step_bounds hb0 hb1
    have hepos : 0 < (P d).eps := by dsimp [SparseSGD.Params.eps]; linarith
    exact le_of_lt (hepos.trans_le hh0)
  · filter_upwards [hbeta] with d hb
    rcases hb with ⟨hb0,hb1⟩
    have ⟨he,he1,hh0,hh1,_⟩ := (P d).small_step_bounds hb0 hb1
    exact hh1

end
end SparseSGD.Scaling
