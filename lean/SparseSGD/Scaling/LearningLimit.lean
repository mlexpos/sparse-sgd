import SparseSGD.Scaling.Tikhonov
import SparseSGD.Scaling.LearningProfileLimits

open Filter Topology
namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1000000

/-- The scalar learning limit is uniform in every time index. Parameter
convergence and the small raw-curvature regime are enough; convergence of the
risk sequence itself is a conclusion. -/
theorem learning_chain_uniform_convergence
    (P : ℕ → Params) (Delta : ℕ → ℝ) (R u phi : ℝ)
    (jury : External.JuryStability) (hR : 0 ≤ R) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hphi : 0 ≤ phi)
    (hvalid : ∀ᶠ n in atTop, 1/2 ≤ (P n).beta ∧ (P n).beta < 1 ∧
      0 < Delta n ∧ (P n).w=Delta n*(P n).eps^2 ∧
      0 ≤ (P n).renormNoise ∧ 0 ≤ (P n).renormAdditive)
    (hDelta : Tendsto Delta atTop (𝓝 0))
    (hu : Tendsto (fun n => (P n).renormNoise) atTop (𝓝 u))
    (hp : Tendsto (fun n => (P n).renormAdditive) atTop (𝓝 phi)) :
    ∀ e > 0, ∀ᶠ n in atTop, ∀ k : ℕ,
      |((P n).trajectory ⟨R,0,0⟩ k).R-
        Scaling.learningProfile u phi R ((k : ℝ)*((P n).w/(P n).eps))| < e := by
  let margin := (1-u)/2
  have hm : 0 < margin := by dsimp [margin]; linarith
  have hm1 : margin ≤ 1 := by dsimp [margin]; linarith
  have huM : u ≤ 1-margin := by dsimp [margin]; linarith
  have hun : ∀ᶠ n in atTop, (P n).renormNoise ≤ 1-margin := by
    have H : u < 1-margin := by dsimp [margin]; linarith
    filter_upwards [hu.eventually (eventually_lt_nhds H)] with n hn
    exact hn.le
  have hdel : ∀ᶠ n in atTop, Delta n ≤ 1/8 := by
    filter_upwards [hDelta.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/8))] with n hn
    exact hn.le
  let E := fun n => (538/(1-(P n).renormNoise)+8)*Delta n*
      (R+(P n).renormAdditive/(1-(P n).renormNoise))+
      (4/margin^2)*((R+(P n).renormAdditive+phi)*|(P n).renormNoise-u|+
        |(P n).renormAdditive-phi|)
  have hden : Tendsto (fun n => 1-(P n).renormNoise) atTop (𝓝 (1-u)) := tendsto_const_nhds.sub hu
  have hnz : 1-u ≠ 0 := by linarith
  have hfirst : Tendsto (fun n => (538/(1-(P n).renormNoise)+8)*Delta n*
      (R+(P n).renormAdditive/(1-(P n).renormNoise))) atTop (𝓝 0) := by
    have H := ((((tendsto_const_nhds (x := (538 : ℝ))).div hden hnz).add_const 8).mul hDelta).mul
      ((hp.div hden hnz).const_add R)
    simpa using H
  have hsecond : Tendsto (fun n => (4/margin^2)*
      ((R+(P n).renormAdditive+phi)*|(P n).renormNoise-u|+|(P n).renormAdditive-phi|))
      atTop (𝓝 0) := by
    have H := ((((hp.const_add R).add_const phi).mul (hu.sub_const u).abs).add
      (hp.sub_const phi).abs).const_mul (4/margin^2)
    simpa using H
  have hE : Tendsto E atTop (𝓝 0) := by simpa [E] using hfirst.add hsecond
  intro e he
  filter_upwards [hvalid,hun,hdel,hE.eventually (eventually_lt_nhds he)] with n hv hnu hnd hsmall
  obtain ⟨hb0,hb1,hd0,hw,hun0,hpn0⟩ := hv
  have hun1 : (P n).renormNoise < 1 := by linarith
  intro k
  have H := smallDelta_trajectory_learningProfile (P n) (Delta n) R jury hb0 hb1 hd0 hnd hw
    hR hun0 hun1 hpn0 k
  have ht : 0 ≤ (k : ℝ)*((P n).w/(P n).eps) := by
    have heps : 0 < (P n).eps := by dsimp [Params.eps]; linarith
    rw [hw]
    positivity
  have Hp := Scaling.learningProfile_uniform_parameter_perturbation margin (P n).renormNoise u
    (P n).renormAdditive phi R ((k : ℝ)*((P n).w/(P n).eps)) hm hm1 hun0 hu0 hnu huM hpn0 hphi hR ht
  have Htri := abs_sub_le (((P n).trajectory ⟨R,0,0⟩ k).R)
    (Scaling.learningProfile (P n).renormNoise (P n).renormAdditive R ((k : ℝ)*((P n).w/(P n).eps)))
    (Scaling.learningProfile u phi R ((k : ℝ)*((P n).w/(P n).eps)))
  change E n < e at hsmall
  dsimp [E] at hsmall
  nlinarith only [H,Hp,Htri,hsmall]

end
end SparseSGD
