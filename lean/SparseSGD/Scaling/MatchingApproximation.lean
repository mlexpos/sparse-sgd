import SparseSGD.Scaling.SmallStepGeometry

namespace SparseSGD
noncomputable section
set_option maxHeartbeats 1000000

/-- The two scalar coefficients in the trace expansion have first-order
retention errors, uniformly up to critical damping. -/
theorem matching_trace_coefficients (e h s : ℝ)
    (he : 0 < e) (he1 : e ≤ 1/2) (hh0 : e ≤ h)
    (hh1 : h ≤ e+2*e^2) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1)
    (hs2 : s^2=1-e) :
    0 ≤ e^2/(s*h^2) ∧ e^2/(s*h^2) ≤ 2 ∧
    |e^2/(s*h^2)-1| ≤ 10*e ∧
    |1/(1+s)^2-1/4| ≤ e := by
  have hh : 0 < h := he.trans_le hh0
  have hs : 0 < s := by linarith
  have hh2 : e^2 ≤ h^2 := sq_le_sq₀ he.le hh.le |>.mpr hh0
  have hden : 0 < s*h^2 := by positivity
  have hr0 : 0 ≤ e^2/(s*h^2) := by positivity
  have hr2 : e^2/(s*h^2) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg (show 0 ≤ s-1/2 by linarith) (sq_nonneg h)]
  have hratio0 : 0 ≤ e/h := by positivity
  have hratio1 : e/h ≤ 1 := (div_le_one hh).mpr hh0
  have hratioNear : 1-e/h ≤ 2*e := by
    have H : 1-2*e ≤ e/h := by
      apply (le_div_iff₀ hh).mpr
      nlinarith [mul_le_mul_of_nonneg_left hh0 he.le]
    linarith
  have hsqNear : 1-(e/h)^2 ≤ 4*e := by
    nlinarith [sq_nonneg (1-e/h)]
  have hinv : 1-s ≤ e := by nlinarith [sq_nonneg (1-s)]
  have hrNear : |e^2/(s*h^2)-1| ≤ 10*e := by
    have hid : e^2/(s*h^2)=(e/h)^2/s := by ring
    rw [hid,abs_le]
    constructor
    · have H : 1-10*e ≤ (e/h)^2/s := by
        apply (le_div_iff₀ hs).mpr
        nlinarith [mul_nonneg he.le (show 0≤1-s by linarith)]
      linarith
    · have H : (e/h)^2/s ≤ 1+10*e := by
        apply (div_le_iff₀ hs).mpr
        nlinarith [mul_nonneg he.le (show 0 ≤ s-1/2 by linarith)]
      linarith
  have hplus : 0 < (1+s)^2 := by positivity
  have hlast : |1/(1+s)^2-1/4| ≤ e := by
    rw [abs_le]
    constructor
    · have H : 1/4 ≤ 1/(1+s)^2 := by
        apply (le_div_iff₀ hplus).mpr
        nlinarith
      linarith
    · have H : 1/(1+s)^2 ≤ 1/4+e := by
        apply (div_le_iff₀ hplus).mpr
        have hp : 1 ≤ (1+s)^2 := by nlinarith
        have He := mul_le_mul_of_nonneg_left hp he.le
        nlinarith
      linarith
  exact ⟨hr0,hr2,hrNear,hlast⟩

/-- Replacing the exact trace by its linear curvature approximation costs
only first order in retention. -/
theorem Params.small_step_linear_delta (p : Params) (Delta : ℝ)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hD : 0 ≤ Delta) (hw : p.w=Delta*p.eps^2) :
    |(1/4+2*(1-p.traceCosine)/p.matchedStep^2)-Delta| ≤
      (10*Delta+5)*p.eps := by
  obtain ⟨he,he1,hh0,hh1,_,hs0,hs1⟩ := p.small_step_bounds hb0 hb1
  have hb : 0 < p.beta := by linarith
  have hh : 0 < p.matchedStep := he.trans_le hh0
  have hs : 0 < Real.sqrt p.beta := Real.sqrt_pos.mpr hb
  have hs2 : (Real.sqrt p.beta)^2=1-p.eps := by
    simpa [Params.eps] using Real.sq_sqrt hb.le
  obtain ⟨hT0,hT2,hTerr,hAerr⟩ := matching_trace_coefficients
    p.eps p.matchedStep (Real.sqrt p.beta) he he1 hh0 hh1 hs0 hs1.le hs2
  let T := p.eps^2/(Real.sqrt p.beta*p.matchedStep^2)
  let A := 1/(1+Real.sqrt p.beta)^2
  have Hid : (1/4+2*(1-p.traceCosine)/p.matchedStep^2)-Delta =
      (T-1)*(Delta-1/4)+T*(1/4-A) := by
    have H := p.small_step_trace_identity Delta hb hw
    dsimp [T,A]
    linear_combination -2/p.matchedStep^2*H
  rw [Hid]
  have hDabs : |Delta-1/4| ≤ Delta+1/4 := by rw [abs_le]; constructor <;> linarith
  have hA : |1/4-A| ≤ p.eps := by simpa only [abs_sub_comm] using hAerr
  calc
    |(T-1)*(Delta-1/4)+T*(1/4-A)| ≤
        |T-1| * |Delta-1/4| + |T| * |1/4-A| := by simpa only [abs_mul] using abs_add_le ((T-1)*(Delta-1/4)) (T*(1/4-A))
    _ ≤ 10*p.eps*(Delta+1/4)+2*p.eps := by
      apply add_le_add
      · exact mul_le_mul hTerr hDabs (abs_nonneg _) (by positivity)
      · rw [abs_of_nonneg hT0]
        exact mul_le_mul hT2 hA (abs_nonneg _) (by norm_num)
    _ ≤ (10*Delta+5)*p.eps := by nlinarith

/-- Taylor comparison of the matched curvature with the trace approximation.
Both damping branches, including the repeated root, share this bound. -/
theorem Params.small_step_delta_remainder (p : Params) (Delta : ℝ)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hD : 0 < Delta) (hw : p.w=Delta*p.eps^2) (hw1 : p.w ≤ 1/16) :
    |p.matchedDelta-(1/4+2*(1-p.traceCosine)/p.matchedStep^2)| ≤
      (128*Delta^2+2)*p.eps^2 := by
  obtain ⟨he,he1,hh0,hh1,hh2,hs0,hs1⟩ := p.small_step_bounds hb0 hb1
  have hb : 0 < p.beta := by linarith
  have hh : 0 < p.matchedStep := he.trans_le hh0
  have hhsq : 0 < p.matchedStep^2 := by positivity
  have hw0 : 0 < p.w := by rw [hw]; positivity
  obtain ⟨hq,hqerr⟩ := p.small_step_trace hb0 hb1 hw0.le hw1
  have heh : p.eps^2 ≤ p.matchedStep^2 := (sq_le_sq₀ he.le hh.le).mpr hh0
  by_cases hc : |p.traceCosine| ≤ 1
  · obtain ⟨ha2,ha1⟩ := p.small_step_angle hb0 hb1 hw0.le hw1 hc
    have ha0 := p.foldedAngle_bounds.1
    have hcos : Real.cos p.foldedAngle=p.traceCosine := by
      unfold Params.foldedAngle
      rw [abs_of_pos hq,Real.cos_arccos (by linarith) (by simpa only [abs_of_pos hq] using hc)]
    have H := cos_quadratic_remainder p.foldedAngle (by rwa [abs_of_nonneg ha0])
    rw [hcos] at H
    have Hid : p.matchedDelta-(1/4+2*(1-p.traceCosine)/p.matchedStep^2) =
        2*(p.traceCosine-(1-p.foldedAngle^2/2))/p.matchedStep^2 := by
      simp only [Params.matchedDelta,hc,ite_true]
      ring
    rw [Hid,abs_div,abs_mul,abs_of_pos hhsq]
    norm_num only [abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have Hfour : p.foldedAngle^4 ≤ 64*Delta^2*p.eps^2*p.matchedStep^2 := by
      rw [hw] at ha2
      have Hsq := (sq_le_sq₀ (sq_nonneg p.foldedAngle) (by positivity : 0 ≤ 8*(Delta*p.eps^2))).mpr ha2
      have HH := mul_le_mul_of_nonneg_left heh (show 0 ≤ 64*Delta^2*p.eps^2 by positivity)
      nlinarith only [Hsq,HH]
    calc
      2*|p.traceCosine-(1-p.foldedAngle^2/2)|/p.matchedStep^2 ≤
          2*p.foldedAngle^4/p.matchedStep^2 := div_le_div_of_nonneg_right (by linarith) hhsq.le
      _ ≤ 128*Delta^2*p.eps^2 := (div_le_iff₀ hhsq).mpr (by nlinarith only [Hfour])
      _ ≤ (128*Delta^2+2)*p.eps^2 := by nlinarith [sq_nonneg p.eps]
  · have hc1 : 1 < |p.traceCosine| := lt_of_not_ge hc
    let a := Real.arcosh |p.traceCosine|
    have ha0 : 0 ≤ a := Real.arcosh_nonneg hc1.le
    have ha : a < p.matchedStep/2 := p.arcosh_traceCosine_lt_half_step hb hb1 hw0 (by linarith) hc1
    have hae : a ≤ p.eps := by linarith
    have hah : a ≤ p.matchedStep := by linarith
    have ha1 : |a| ≤ 1 := by rw [abs_of_nonneg ha0]; linarith
    have hcosh : Real.cosh a=p.traceCosine := by
      dsimp [a]
      rw [Real.cosh_arcosh hc1.le,abs_of_pos hq]
    have H := cosh_quadratic_remainder a ha1
    rw [hcosh] at H
    have Hid : p.matchedDelta-(1/4+2*(1-p.traceCosine)/p.matchedStep^2) =
        2*(p.traceCosine-(1+a^2/2))/p.matchedStep^2 := by
      simp only [Params.matchedDelta,hc,ite_false]
      dsimp [a]
      ring
    have Hfour : a^4 ≤ p.eps^2*p.matchedStep^2 := by
      have Hae := (sq_le_sq₀ ha0 he.le).mpr hae
      have Hah := (sq_le_sq₀ ha0 hh.le).mpr hah
      have Hmul := mul_le_mul Hae Hah (sq_nonneg a) (sq_nonneg p.eps)
      nlinarith only [Hmul]
    rw [Hid,abs_div,abs_mul,abs_of_pos hhsq]
    norm_num only [abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    calc
      2*|p.traceCosine-(1+a^2/2)|/p.matchedStep^2 ≤ 2*a^4/p.matchedStep^2 :=
        div_le_div_of_nonneg_right (by linarith) hhsq.le
      _ ≤ 2*p.eps^2 := (div_le_iff₀ hhsq).mpr (by nlinarith only [Hfour])
      _ ≤ (128*Delta^2+2)*p.eps^2 := by nlinarith [mul_nonneg (sq_nonneg Delta) (sq_nonneg p.eps)]

/-- The exact matching map is uniformly first-order accurate in retention on
bounded raw-curvature sets. The estimate crosses critical damping. -/
theorem Params.small_step_matchedDelta (p : Params) (Delta : ℝ)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hD : 0 < Delta) (hw : p.w=Delta*p.eps^2) (hw1 : p.w ≤ 1/16) :
    |p.matchedDelta-Delta| ≤ (128*Delta^2+10*Delta+7)*p.eps := by
  have H1 := p.small_step_delta_remainder Delta hb0 hb1 hD hw hw1
  have H2 := p.small_step_linear_delta Delta hb0 hb1 hD.le hw
  have H := abs_sub_le p.matchedDelta (1/4+2*(1-p.traceCosine)/p.matchedStep^2) Delta
  obtain ⟨he,he1,_⟩ := p.small_step_bounds hb0 hb1
  have He : p.eps^2 ≤ p.eps := by nlinarith
  have HH := mul_le_mul_of_nonneg_left He (show 0 ≤ 128*Delta^2+2 by positivity)
  nlinarith only [H,H1,H2,HH]

/-- The sharper error keeps the squared-retention term separate. This form
also applies when the raw curvature tends to infinity while `w` tends to zero. -/
theorem Params.small_step_matchedDelta_sharp (p : Params) (Delta : ℝ)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hD : 0 < Delta) (hw : p.w=Delta*p.eps^2) (hw1 : p.w ≤ 1/16) :
    |p.matchedDelta-Delta| ≤
      (128*Delta^2+2)*p.eps^2+(10*Delta+5)*p.eps := by
  exact (abs_sub_le p.matchedDelta (1/4+2*(1-p.traceCosine)/p.matchedStep^2) Delta).trans
    (add_le_add (p.small_step_delta_remainder Delta hb0 hb1 hD hw hw1)
      (p.small_step_linear_delta Delta hb0 hb1 hD.le hw))

/-- Relative matching accuracy in the intermediate oscillatory window. -/
theorem Params.small_step_matchedDelta_relative (p : Params) (Delta : ℝ)
    (hb0 : 1/2 ≤ p.beta) (hb1 : p.beta < 1)
    (hD : 1 ≤ Delta) (hw : p.w=Delta*p.eps^2) (hw1 : p.w ≤ 1/16) :
    |p.matchedDelta/Delta-1| ≤ 130*p.w+15*p.eps := by
  have hD0 : 0 < Delta := by linarith
  have H := p.small_step_matchedDelta_sharp Delta hb0 hb1 hD0 hw hw1
  have he := (p.small_step_bounds hb0 hb1).1.le
  have HD2 : 1 ≤ Delta^2 := by nlinarith
  have Hsq := mul_le_mul_of_nonneg_right HD2 (sq_nonneg p.eps)
  have Hlin := mul_le_mul_of_nonneg_right hD he
  rw [show p.matchedDelta/Delta-1=(p.matchedDelta-Delta)/Delta by field_simp,
    abs_div,abs_of_pos hD0]
  apply (div_le_iff₀ hD0).mpr
  rw [hw]
  nlinarith only [H,Hsq,Hlin]

end
end SparseSGD
