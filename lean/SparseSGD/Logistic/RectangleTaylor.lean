import SparseSGD.Foundations

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

/-- Taylor's bound on a closed rectangle from one-variable derivative jets.
The derivatives are within their intervals, so a zero variance endpoint needs
only the existing right derivatives. No extension to negative variance is used. -/
theorem rectangle_taylor_bound
    (F Fx Fy Fxx Fxy Fyy : ℝ → ℝ → ℝ) (x0 x1 y0 y1 L : ℝ) (hL : 0 ≤ L)
    (hFx : ∀ x ∈ Set.uIcc x0 x1, ∀ y ∈ Set.uIcc y0 y1,
      HasDerivWithinAt (fun z => F z y) (Fx x y) (Set.uIcc x0 x1) x)
    (hFy : ∀ y ∈ Set.uIcc y0 y1,
      HasDerivWithinAt (F x0) (Fy x0 y) (Set.uIcc y0 y1) y)
    (hFxx : ∀ x ∈ Set.uIcc x0 x1, ∀ y ∈ Set.uIcc y0 y1,
      HasDerivWithinAt (fun z => Fx z y) (Fxx x y) (Set.uIcc x0 x1) x)
    (hFxy : ∀ y ∈ Set.uIcc y0 y1,
      HasDerivWithinAt (Fx x0) (Fxy x0 y) (Set.uIcc y0 y1) y)
    (hFyy : ∀ y ∈ Set.uIcc y0 y1,
      HasDerivWithinAt (Fy x0) (Fyy x0 y) (Set.uIcc y0 y1) y)
    (hxx : ∀ x ∈ Set.uIcc x0 x1, ∀ y ∈ Set.uIcc y0 y1, |Fxx x y| ≤ L)
    (hxy : ∀ y ∈ Set.uIcc y0 y1, |Fxy x0 y| ≤ L)
    (hyy : ∀ y ∈ Set.uIcc y0 y1, |Fyy x0 y| ≤ L) :
    |F x1 y1-F x0 y0-Fx x0 y0*(x1-x0)-Fy x0 y0*(y1-y0)| ≤
      L*(|x1-x0|+|y1-y0|)^2 := by
  have hx0 : x0 ∈ Set.uIcc x0 x1 := Set.left_mem_uIcc
  have hx1 : x1 ∈ Set.uIcc x0 x1 := Set.right_mem_uIcc
  have hy0 : y0 ∈ Set.uIcc y0 y1 := Set.left_mem_uIcc
  have hy1 : y1 ∈ Set.uIcc y0 y1 := Set.right_mem_uIcc
  have Hxy : |Fx x0 y1-Fx x0 y0| ≤ L*|y1-y0| := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hFxy (fun y hy => by simpa only [Real.norm_eq_abs] using hxy y hy)
      (convex_uIcc y0 y1) hy0 hy1
  have Hx (x : ℝ) (hx : x ∈ Set.uIcc x0 x1) :
      |Fx x y1-Fx x0 y0| ≤ L*(|x1-x0|+|y1-y0|) := by
    have Hxx : |Fx x y1-Fx x0 y1| ≤ L*|x-x0| := by
      simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun z hz => hFxx z hz y1 hy1)
        (fun z hz => by simpa only [Real.norm_eq_abs] using hxx z hz y1 hy1)
        (convex_uIcc x0 x1) hx0 hx
    have hdist : |x-x0| ≤ |x1-x0| := by
      simpa only [Real.dist_eq,abs_sub_comm] using Real.dist_left_le_of_mem_uIcc hx
    calc
      _ ≤ |Fx x y1-Fx x0 y1|+|Fx x0 y1-Fx x0 y0| := abs_sub_le _ _ _
      _ ≤ L*|x-x0|+L*|y1-y0| := add_le_add Hxx Hxy
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hdist hL]
  have Hy (y : ℝ) (hy : y ∈ Set.uIcc y0 y1) : |Fy x0 y-Fy x0 y0| ≤ L*|y1-y0| := by
    have Hyy : |Fy x0 y-Fy x0 y0| ≤ L*|y-y0| := by
      simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        hFyy (fun z hz => by simpa only [Real.norm_eq_abs] using hyy z hz)
        (convex_uIcc y0 y1) hy0 hy
    have hdist : |y-y0| ≤ |y1-y0| := by
      simpa only [Real.dist_eq,abs_sub_comm] using Real.dist_left_le_of_mem_uIcc hy
    exact Hyy.trans (mul_le_mul_of_nonneg_left hdist hL)
  have hdx (x : ℝ) (hx : x ∈ Set.uIcc x0 x1) :=
    (hFx x hx y1 hy1).sub (((hasDerivAt_id x).const_mul (Fx x0 y0)).hasDerivWithinAt)
  have hdy (y : ℝ) (hy : y ∈ Set.uIcc y0 y1) :=
    (hFy y hy).sub (((hasDerivAt_id y).const_mul (Fy x0 y0)).hasDerivWithinAt)
  have RX : |(F x1 y1-Fx x0 y0*x1)-(F x0 y1-Fx x0 y0*x0)| ≤
      (L*(|x1-x0|+|y1-y0|))*|x1-x0| := by
    simpa only [mul_one,Real.norm_eq_abs,Pi.sub_apply,id_eq] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hdx (fun x hx => by simpa only [mul_one,Real.norm_eq_abs] using Hx x hx)
      (convex_uIcc x0 x1) hx0 hx1
  have RY : |(F x0 y1-Fy x0 y0*y1)-(F x0 y0-Fy x0 y0*y0)| ≤
      (L*|y1-y0|)*|y1-y0| := by
    simpa only [mul_one,Real.norm_eq_abs,Pi.sub_apply,id_eq] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hdy (fun y hy => by simpa only [mul_one,Real.norm_eq_abs] using Hy y hy)
      (convex_uIcc y0 y1) hy0 hy1
  calc
    _ = |((F x1 y1-Fx x0 y0*x1)-(F x0 y1-Fx x0 y0*x0))+
          ((F x0 y1-Fy x0 y0*y1)-(F x0 y0-Fy x0 y0*y0))| := by congr 1; ring
    _ ≤ |(F x1 y1-Fx x0 y0*x1)-(F x0 y1-Fx x0 y0*x0)|+
          |(F x0 y1-Fy x0 y0*y1)-(F x0 y0-Fy x0 y0*y0)| := abs_add_le _ _
    _ ≤ (L*(|x1-x0|+|y1-y0|))*|x1-x0|+(L*|y1-y0|)*|y1-y0| := add_le_add RX RY
    _ ≤ _ := by nlinarith only [mul_nonneg hL (mul_nonneg (abs_nonneg (x1-x0)) (abs_nonneg (y1-y0)))]

end
end SparseSGD.Logistic
