import SparseSGD.Discrete.Loads

namespace SparseSGD
noncomputable section

def Params.equilibrium (p : Params) : Moments :=
  let r := p.additive / (1-p.totalLoad)
  ⟨r, 2*p.w*r/(1+p.beta), -p.w*r/(1+p.beta)⟩

theorem Params.steady_of_balance (p : Params) (r : ℝ) (hb : 1+p.beta ≠ 0)
    (hr : p.noise*r+p.additive = (1-p.curvature)*r) :
    p.step ⟨r, 2*p.w*r/(1+p.beta), -p.w*r/(1+p.beta)⟩ =
      ⟨r, 2*p.w*r/(1+p.beta), -p.w*r/(1+p.beta)⟩ := by
  apply Moments.ext <;> simp only [Params.step, Params.eps] <;>
    rw [hr] <;> unfold Params.curvature <;> field_simp [hb] <;> ring

theorem Params.equilibrium_fixed (p : Params) (hb : 1 + p.beta ≠ 0)
    (hu : p.totalLoad ≠ 1) : p.step p.equilibrium = p.equilibrium := by
  apply p.steady_of_balance _ hb
  have hden : 1-p.totalLoad ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hr : (1-p.totalLoad)*(p.additive/(1-p.totalLoad))=p.additive := by
    exact mul_div_cancel₀ _ hden
  change p.noise * _ + p.additive = (1-p.curvature)*_
  dsimp [Params.totalLoad] at hr
  dsimp [Params.totalLoad]
  linear_combination -hr

end
end SparseSGD
