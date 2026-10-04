import SparseSGD.Scaling.GeometricRenewal
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Filter Topology

namespace SparseSGD.Scaling
noncomputable section

theorem expNeg_rate_difference_bound_ordered (m a b t : ℝ)
    (hm : 0 < m) (ham : m ≤ a) (hbm : m ≤ b) (ht : 0 ≤ t) (hab : a ≤ b) :
    |Real.exp (-a*t) - Real.exp (-b*t)| ≤ |a-b| / m := by
  have hrate : 0 ≤ b-a := sub_nonneg.mpr hab
  have hx : 0 ≤ (b-a)*t := mul_nonneg hrate ht
  have hsmall : 0 ≤ 1-Real.exp (-((b-a)*t)) := by
    have := Real.exp_le_one_iff.mpr (by nlinarith : -((b-a)*t) ≤ 0)
    linarith
  have hlinear : 1-Real.exp (-((b-a)*t)) ≤ (b-a)*t := by
    have := Real.add_one_le_exp (-((b-a)*t))
    linarith
  have hdiff : Real.exp (-a*t) - Real.exp (-b*t) =
      Real.exp (-a*t) * (1-Real.exp (-((b-a)*t))) := by
    rw [show -b*t = -a*t + -((b-a)*t) by ring, Real.exp_add]
    ring
  rw [hdiff, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hsmall)]
  calc
    Real.exp (-a*t) * (1-Real.exp (-((b-a)*t))) ≤
        Real.exp (-a*t) * ((b-a)*t) := mul_le_mul_of_nonneg_left hlinear (Real.exp_pos _).le
    _ = (b-a) * (t * Real.exp (-a*t)) := by ring
    _ ≤ (b-a) / a := by
      have htbound : t * Real.exp (-a*t) ≤ 1/a := by
        have H := Real.mul_exp_neg_le_exp_neg_one (a*t)
        have hle : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
        have H' : (a*t)*Real.exp (-(a*t)) ≤ 1 := H.trans hle
        have ha : 0 < a := hm.trans_le ham
        rw [show -(a*t) = -a*t by ring] at H'
        apply (le_div_iff₀ ha).2
        nlinarith [H']
      calc
        _ ≤ (b-a) * (1/a) := mul_le_mul_of_nonneg_left htbound hrate
        _ = (b-a) / a := by ring
    _ ≤ (b-a) / m := by
      exact div_le_div_of_nonneg_left hrate hm ham
    _ = |a-b| / m := by
      rw [show a-b = -(b-a) by ring, abs_neg, abs_of_nonneg hrate]
theorem expNeg_rate_difference_bound (m a b t : ℝ)
    (hm : 0 < m) (ham : m ≤ a) (hbm : m ≤ b) (ht : 0 ≤ t) :
    |Real.exp (-a*t) - Real.exp (-b*t)| ≤ |a-b| / m := by
  rcases le_total a b with hab | hba
  · exact expNeg_rate_difference_bound_ordered m a b t hm ham hbm ht hab
  · have h := expNeg_rate_difference_bound_ordered m b a t hm hbm ham ht hba
    simpa [abs_sub_comm] using h

theorem learningProfile_uniform_parameter_perturbation
    (margin u v phi psi R t : ℝ)
    (hm : 0 < margin) (hmle : margin ≤ 1)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (hu : u ≤ 1-margin) (hv : v ≤ 1-margin)
    (hphi : 0 ≤ phi) (hpsi : 0 ≤ psi) (hR : 0 ≤ R) (ht : 0 ≤ t) :
    |learningProfile u phi R t-learningProfile v psi R t| ≤
      (4/margin^2) * ((R+phi+psi)* |u-v|+|phi-psi|) := by
  have huDen : margin ≤ 1-u := by linarith
  have hvDen : margin ≤ 1-v := by linarith
  have huDenPos : 0 < 1-u := lt_of_lt_of_le hm huDen
  have hvDenPos : 0 < 1-v := lt_of_lt_of_le hm hvDen
  let L := phi/(1-u)
  let M := psi/(1-v)
  let a := 2*(1-u)
  let b := 2*(1-v)
  have hLnon : 0 ≤ L := by dsimp [L]; positivity
  have hMnon : 0 ≤ M := by dsimp [M]; positivity
  have hMbound : M ≤ psi/margin := by
    dsimp [M]
    exact div_le_div_of_nonneg_left hpsi hm hvDen
  have hLdiff : |L-M| ≤ |phi-psi|/margin + psi* |u-v|/margin^2 := by
    have hdecomp : L-M=(phi-psi)/(1-u)+psi*(u-v)/((1-u)*(1-v)) := by
      dsimp [L,M]
      field_simp [huDenPos.ne', hvDenPos.ne']
      <;> ring
    have hdenpos : 0 < (1-u)*(1-v) := mul_pos huDenPos hvDenPos
    have hden : margin^2 ≤ (1-u)*(1-v) := by nlinarith [mul_le_mul huDen hvDen (le_of_lt hm) (le_of_lt huDenPos)]
    rw [hdecomp]
    calc
      |(phi-psi)/(1-u)+psi*(u-v)/((1-u)*(1-v))| ≤
          |(phi-psi)/(1-u)|+|psi*(u-v)/((1-u)*(1-v))| := abs_add_le _ _
      _ ≤ |phi-psi|/margin + (psi* |u-v|)/margin^2 := by
        have hfirst : |(phi-psi)/(1-u)| ≤ |phi-psi|/margin := by
          rw [abs_div, abs_of_pos huDenPos]
          exact div_le_div_of_nonneg_left (abs_nonneg _) hm huDen
        have hsecond : |psi*(u-v)/((1-u)*(1-v))| ≤ (psi* |u-v|)/margin^2 := by
          rw [abs_div, abs_mul, abs_of_nonneg hpsi, abs_of_pos hdenpos]
          exact div_le_div_of_nonneg_left (mul_nonneg hpsi (abs_nonneg _)) (sq_pos_of_pos hm) hden
        linarith
      _ = |phi-psi|/margin + psi* |u-v|/margin^2 := by rfl
  have hE1 : 0 ≤ Real.exp (-a*t) := (Real.exp_pos _).le
  have hE2 : 0 ≤ Real.exp (-b*t) := (Real.exp_pos _).le
  have hE1le : Real.exp (-a*t) ≤ 1 := Real.exp_le_one_iff.mpr (by dsimp [a]; nlinarith)
  have ha : 2*margin ≤ a := by dsimp [a]; nlinarith
  have hb : 2*margin ≤ b := by dsimp [b]; nlinarith
  have hEdiff : |Real.exp (-a*t)-Real.exp (-b*t)| ≤ |u-v|/margin := by
    have h := expNeg_rate_difference_bound (2*margin) a b t (by positivity) ha hb ht
    have habs : |a-b| = 2* |u-v| := by
      calc
        |a-b| = |2*(v-u)| := by dsimp [a,b]; congr 1 <;> ring
        _ = 2* |u-v| := by rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)), abs_sub_comm v u]
    rw [habs] at h
    have hmpos : 0 < margin := hm
    calc
      |Real.exp (-a*t)-Real.exp (-b*t)| ≤ 2* |u-v|/(2*margin) := h
      _ = |u-v|/margin := by field_simp [hmpos.ne']
  have hdecomp : learningProfile u phi R t-learningProfile v psi R t =
      (L-M)*(1-Real.exp (-a*t))+(R-M)*(Real.exp (-a*t)-Real.exp (-b*t)) := by
    dsimp [learningProfile, L, M, a, b]
    ring
  have hmain : |learningProfile u phi R t-learningProfile v psi R t| ≤
      |L-M|+(R+M)* |u-v|/margin := by
    rw [hdecomp]
    have hOne : |1-Real.exp (-a*t)| ≤ 1 := by
      rw [abs_of_nonneg (by linarith : 0 ≤ 1-Real.exp (-a*t))]
      linarith
    have hRM : |R-M| ≤ R+M := by
      rw [abs_le]
      constructor <;> linarith
    calc
      |(L-M)*(1-Real.exp (-a*t)) + (R-M)*(Real.exp (-a*t)-Real.exp (-b*t))| ≤
          |(L-M)*(1-Real.exp (-a*t))| + |(R-M)*(Real.exp (-a*t)-Real.exp (-b*t))| := abs_add_le _ _
      _ = |L-M| * |1-Real.exp (-a*t)| + |R-M| * |Real.exp (-a*t)-Real.exp (-b*t)| := by rw [abs_mul, abs_mul]
      _ ≤ |L-M|+(R+M)* |u-v|/margin := by
        have hA : |L-M| * |1-Real.exp (-a*t)| ≤ |L-M| := by
          calc
            _ ≤ |L-M| * 1 := mul_le_mul_of_nonneg_left hOne (abs_nonneg _)
            _ = |L-M| := by ring
        have hB : |R-M| * |Real.exp (-a*t)-Real.exp (-b*t)| ≤ (R+M) * (|u-v|/margin) :=
          mul_le_mul hRM hEdiff (abs_nonneg _) (by linarith [hR, hMnon])
        calc
          _ ≤ |L-M| + (R+M) * (|u-v|/margin) := add_le_add hA hB
          _ = |L-M| + (R+M)*|u-v|/margin := by ring
      _ = |L-M|+(R+M)* |u-v|/margin := by ring
  have hprofile : |learningProfile u phi R t-learningProfile v psi R t| ≤
      |phi-psi|/margin + (R+2*psi/margin)* |u-v|/margin := by
    calc
      _ ≤ |L-M|+(R+M)* |u-v|/margin := hmain
      _ ≤ (|phi-psi|/margin+psi* |u-v|/margin^2)+(R+psi/margin)* |u-v|/margin := by
        have hprod : (R+M)*|u-v|/margin ≤ (R+psi/margin)*|u-v|/margin := by
          calc
            (R+M)*|u-v|/margin = (R+M)*(|u-v|/margin) := by ring
            _ ≤ (R+psi/margin)*(|u-v|/margin) :=
              mul_le_mul_of_nonneg_right (add_le_add_right hMbound R)
                (div_nonneg (abs_nonneg _) (le_of_lt hm))
            _ = (R+psi/margin)*|u-v|/margin := by ring
        exact add_le_add hLdiff hprod
      _ = |phi-psi|/margin + (R+2*psi/margin)* |u-v|/margin := by ring
  have hdu : 0 ≤ |u-v| := abs_nonneg _
  have hcoeff : 1/margin ≤ 4/margin^2 := by
    have hmpos : margin ≠ 0 := hm.ne'
    field_simp [hmpos]
    nlinarith [hmle]
  have hcoefR : 1/margin ≤ 4/margin^2 := hcoeff
  have hbound : |phi-psi|/margin + R* |u-v|/margin + 2*psi* |u-v|/margin^2 ≤
      (4/margin^2)*((R+phi+psi)* |u-v|+|phi-psi|) := by
    let C := 4/margin^2
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hRterm : R*|u-v|/margin ≤ C*(R*|u-v|) := by
      have hcoeffC : 1/margin ≤ C := by simpa [C] using hcoeff
      have h := mul_le_mul_of_nonneg_right hcoeffC hR
      calc
        R*|u-v|/margin = (R/margin)*|u-v| := by ring
        _ ≤ (C*R)*|u-v| := mul_le_mul_of_nonneg_right (by simpa [div_eq_mul_inv, mul_comm] using h) (abs_nonneg _)
        _ = C*(R*|u-v|) := by ring
    have hcoeff2 : 2/margin^2 ≤ C := by
      dsimp [C]
      have hm2 : 0 < margin^2 := sq_pos_of_pos hm
      exact (div_le_div_iff₀ hm2 hm2).2 (by nlinarith [hm2])
    have hPsiterm : 2*psi*|u-v|/margin^2 ≤ C*(psi*|u-v|) := by
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff2 hpsi) hdu
      calc
        2*psi*|u-v|/margin^2 = (2*psi/margin^2)*|u-v| := by ring
        _ ≤ (C*psi)*|u-v| := by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
        _ = C*(psi*|u-v|) := by ring
    have hDiffterm : |phi-psi|/margin ≤ C*|phi-psi| := by
      have hcoeffC : 1/margin ≤ C := by simpa [C] using hcoeff
      simpa [C, div_eq_mul_inv, mul_comm] using
        (mul_le_mul_of_nonneg_right hcoeffC (abs_nonneg (phi-psi)))
    calc
      _ ≤ C*(R*|u-v|)+C*(psi*|u-v|)+C*|phi-psi| := by linarith [hRterm, hPsiterm, hDiffterm]
      _ ≤ C*((R+phi+psi)*|u-v|+|phi-psi|) := by
        have hx : 0 ≤ C*(phi*|u-v|) := mul_nonneg hC (mul_nonneg hphi (abs_nonneg _))
        nlinarith [hx]

  calc
    |learningProfile u phi R t-learningProfile v psi R t| ≤
        |phi-psi|/margin + (R+2*psi/margin)* |u-v|/margin := hprofile
    _ = |phi-psi|/margin + R* |u-v|/margin +
        2*psi* |u-v|/margin^2 := by ring
    _ ≤ (4/margin^2)*((R+phi+psi)* |u-v|+|phi-psi|) := hbound

end
end SparseSGD.Scaling
