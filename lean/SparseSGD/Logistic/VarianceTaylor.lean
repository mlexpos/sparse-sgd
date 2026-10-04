import SparseSGD.Logistic.RectangleTaylor

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 1600000

/-- Composing a scalar signal/variance Taylor bound with q=theta^2+R.
This is the physical coordinate change used in the actual matched LR map. -/
theorem variance_lift_taylor_bound
    (F : ℝ → ℝ → ℝ) (Fx Fy x0 x1 R0 R1 Q L M E : ℝ)
    (hQ : 0 ≤ Q) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hx0 : |x0| ≤ Q) (hx1 : |x1| ≤ Q)
    (hx : |x1-x0| ≤ E) (hR : |R1-R0| ≤ E) (hFy : |Fy| ≤ M)
    (htaylor : |F x1 (x1^2+R1)-F x0 (x0^2+R0)-Fx*(x1-x0)-Fy*((x1^2+R1)-(x0^2+R0))| ≤
      L*(|x1-x0|+|(x1^2+R1)-(x0^2+R0)|)^2) :
    |F x1 (x1^2+R1)-F x0 (x0^2+R0)-(Fx+2*x0*Fy)*(x1-x0)-Fy*(R1-R0)| ≤
      (L*(2*Q+2)^2+M)*E^2 := by
  have hE : 0 ≤ E := (abs_nonneg _).trans hx
  have hq : |(x1^2+R1)-(x0^2+R0)| ≤ 2*Q*|x1-x0|+|R1-R0| := by
    have heq : (x1^2+R1)-(x0^2+R0)=(x1+x0)*(x1-x0)+(R1-R0) := by ring
    rw [heq]
    calc
      _ ≤ |(x1+x0)*(x1-x0)|+|R1-R0| := abs_add_le _ _
      _ = |x1+x0| *|x1-x0|+|R1-R0| := by rw [abs_mul]
      _ ≤ (|x1|+|x0|)*|x1-x0|+|R1-R0| := by gcongr; exact abs_add_le _ _
      _ ≤ _ := by gcongr; linarith
  have hsum : |x1-x0|+|(x1^2+R1)-(x0^2+R0)| ≤ (2*Q+2)*E := by
    have H := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2*Q by positivity)
    nlinarith only [hq,H,hx,hR]
  have Hsq : L*(|x1-x0|+|(x1^2+R1)-(x0^2+R0)|)^2 ≤ L*((2*Q+2)*E)^2 := by
    gcongr
  have Hfy : |Fy*(x1-x0)^2| ≤ M*E^2 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg (x1-x0)),← sq_abs]
    gcongr
  calc
    _ = |(F x1 (x1^2+R1)-F x0 (x0^2+R0)-Fx*(x1-x0)-Fy*((x1^2+R1)-(x0^2+R0)))+
        Fy*(x1-x0)^2| := by congr 1; ring
    _ ≤ |F x1 (x1^2+R1)-F x0 (x0^2+R0)-Fx*(x1-x0)-Fy*((x1^2+R1)-(x0^2+R0))|+
        |Fy*(x1-x0)^2| := abs_add_le _ _
    _ ≤ L*((2*Q+2)*E)^2+M*E^2 := add_le_add (htaylor.trans Hsq) Hfy
    _ = _ := by ring

end
end SparseSGD.Logistic
