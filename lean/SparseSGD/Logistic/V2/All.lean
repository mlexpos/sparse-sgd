import SparseSGD.Logistic.V2.Barbalat
import SparseSGD.Logistic.V2.Lyapunov
import SparseSGD.Logistic.V2.PositiveDeterminant
import SparseSGD.Logistic.V2.GlobalConvergence
import SparseSGD.Logistic.V2.Hurwitz
import SparseSGD.Logistic.V2.LyapunovCertificate
import SparseSGD.Logistic.V2.RecursionContraction
import SparseSGD.Logistic.V2.UniformRate
import SparseSGD.Logistic.V2.RecursionTame
import SparseSGD.Logistic.V2.LargeDeltaAlgebra
import SparseSGD.Logistic.V2.LargeDeltaPerturbation
import SparseSGD.Logistic.V2.WindowMapAlgebra
import SparseSGD.Logistic.V2.WindowUnitCircle

/-!
# V2 (revised appendix): composed results

This module imports every V2 module and states the composed v2 results:

* `prop_S` bundles v2 `prop:S` (i), (ii), (iii) of `source/v2/lr5_global_stability.tex`.
* `cor_recursion_tame'` is v2 `cor:recursion` (tame instantiation) with the uniform-entry
  hypothesis discharged by `dynamicField_uniformEntry`.
* `AssumptionW2` is v2 `ass:W2`, stated as a `Prop`-valued structure (a hypothesis to be
  passed explicitly, never an axiom).

The v1 source assumptions `SourceAssumptionS` and `SourceAssumptionW` remain in
`SparseSGD.Logistic.SourceAssumptions`, unchanged, and are marked there as v1.
-/

open Filter Topology

namespace SparseSGD.Logistic.V2
open SparseSGD.Logistic

/-- v2 `prop:S` (cells 3--4, global stability), all three parts.  For `r > 0`, `delta > 0`,
`Phi ≥ 0`:

(i) every physical initial state has a global forward solution, and every forward solution
from a physical state stays physical, is bounded and converges to the canonical equilibrium;

(ii) the field is differentiable at the equilibrium with the explicit Jacobian, and every
complex eigenvalue of that Jacobian has negative real part;

(iii) for every compact set `K` of physical states and every compact set `Pset` of parameters
`(delta, Phi, r)` in `{delta > 0, Phi ≥ 0, r > 0}`, the convergence is exponential with
constants uniform over `K × Pset` (proportional form).  The constant `C` depends on `K`; this
is not the all-physical-states uniform form of the v1 `SourceAssumptionS`. -/
theorem prop_S (r delta Phi : ℝ) (hr : 0 < r) (hdelta : 0 < delta) (hPhi : 0 ≤ Phi) :
    ((∀ y0 : DynamicState, dynamicPhysical y0 →
      ∃ y : ℝ → DynamicState, y 0 = y0 ∧
        (∀ t, 0 ≤ t → HasDerivAt y (dynamicField r delta Phi (y t)) t) ∧
        (∀ t, 0 ≤ t → dynamicPhysical (y t)) ∧
        Tendsto y atTop (𝓝 (dynamicCanonicalEquilibrium r delta Phi))) ∧
    (∀ y : ℝ → DynamicState,
      (∀ t, 0 ≤ t → HasDerivAt y (dynamicField r delta Phi (y t)) t) → dynamicPhysical (y 0) →
        (∀ t, 0 ≤ t → dynamicPhysical (y t)) ∧ (∃ M : ℝ, ∀ t, 0 ≤ t → ‖y t‖ ≤ M) ∧
        Tendsto y atTop (𝓝 (dynamicCanonicalEquilibrium r delta Phi)))) ∧
    (HasFDerivAt (dynamicField r delta Phi)
      (LinearMap.toContinuousLinearMap
        (Matrix.toLin' (jacobianMatrix
          (dynamicAlpha r (dynamicCanonicalEquilibrium r delta Phi))
          (positiveRoot r Phi) (equilibriumBulk r Phi) delta)))
      (dynamicCanonicalEquilibrium r delta Phi) ∧
    ∀ z : ℂ, Matrix.det (z • (1 : Matrix (Fin 5) (Fin 5) ℂ) -
      (jacobianMatrix
          (dynamicAlpha r (dynamicCanonicalEquilibrium r delta Phi))
          (positiveRoot r Phi) (equilibriumBulk r Phi) delta).map Complex.ofReal) = 0 →
      z.re < 0) ∧
    (∀ (K : Set DynamicState), IsCompact K → (∀ z ∈ K, dynamicPhysical z) →
      ∀ (Pset : Set (ℝ × ℝ × ℝ)), IsCompact Pset →
      (∀ q ∈ Pset, 0 < q.1 ∧ 0 ≤ q.2.1 ∧ 0 < q.2.2) →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ q ∈ Pset, ∀ y0 ∈ K, ∀ y : ℝ → DynamicState,
        y 0 = y0 → (∀ t, 0 ≤ t → HasDerivAt y (dynamicField q.2.2 q.1 q.2.1 (y t)) t) →
          ∀ t, 0 ≤ t → ‖y t - dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1‖ ≤
            C * Real.exp (-c * t) * ‖y0 - dynamicCanonicalEquilibrium q.2.2 q.1 q.2.1‖) :=
  ⟨prop_S_i r delta Phi hr hdelta hPhi, prop_S_ii r delta Phi hr hdelta hPhi,
    fun K hK hKphys Pset hPc hP => prop_S_iii_proportional K hK hKphys Pset hPc hP⟩

/-- v2 `cor:recursion` (tame drift recursion), with the uniform-entry hypothesis discharged by
v2 `prop:S` (iii) (`dynamicField_uniformEntry`).  For `r > 0`, `deltaS > 0`, `PhiS ≥ 0` and a
compact set `K` of physical states there are `C, c, varrho0, s > 0` such that, for every step
`h > 0` and parameters with `|delta - deltaS| ≤ deltaS/2`, `rho ∈ [0,1]` and
`varrho = |h| + |delta - deltaS| + |Phi - PhiS| + |nu| ≤ varrho0`, the tame drift map has a
fixed point within `C varrho` of the equilibrium, unique in the ball of radius `s`; orbits from
`K` converge to it at rate `exp(-c h k)`; orbits track every ODE solution within `C varrho`
uniformly in time; and Jacobian products along the orbit decay as `C exp(-c h m)`. -/
theorem cor_recursion_tame' (r deltaS PhiS : ℝ) (hr : 0 < r) (hd : 0 < deltaS) (hP : 0 ≤ PhiS)
    (K : Set DynamicState) (hK : IsCompact K) (hKphys : ∀ y ∈ K, dynamicPhysical y) :
    ∃ C c v0 s : ℝ, 0 < C ∧ 0 < c ∧ 0 < v0 ∧ v0 ≤ 1 ∧ 0 < s ∧ C * v0 ≤ s ∧
      ∀ h delta Phi nu rho : ℝ, 0 < h → |delta - deltaS| ≤ deltaS / 2 → 0 ≤ rho → rho ≤ 1 →
        |h| + |delta - deltaS| + |Phi - PhiS| + |nu| ≤ v0 →
        ∃ yh : DynamicState,
          ‖yh - dynamicCanonicalEquilibrium r deltaS PhiS‖ ≤
            C * (|h| + |delta - deltaS| + |Phi - PhiS| + |nu|) ∧
          tameDriftMap r h delta Phi nu rho yh = yh ∧
          (∀ z : DynamicState, ‖z - dynamicCanonicalEquilibrium r deltaS PhiS‖ ≤ s →
            tameDriftMap r h delta Phi nu rho z = z → z = yh) ∧
          ∀ y0 ∈ K,
            (∀ k : ℕ, ‖(tameDriftMap r h delta Phi nu rho)^[k] y0 - yh‖ ≤
              C * Real.exp (-(c * h * k))) ∧
            (∀ y : ℝ → DynamicState, IsODESol (dynamicField r deltaS PhiS) y0 y → ∀ k : ℕ,
              ‖(tameDriftMap r h delta Phi nu rho)^[k] y0 - y ((k : ℝ) * h)‖ ≤
                C * (|h| + |delta - deltaS| + |Phi - PhiS| + |nu|)) ∧
            (∀ j m : ℕ, ‖jacProd (tameDriftMap r h delta Phi nu rho)
                ((tameDriftMap r h delta Phi nu rho)^[j] y0) m‖ ≤ C * Real.exp (-(c * h * m))) :=
  cor_recursion_tame r deltaS PhiS hr hd hP K hK hKphys
    (dynamicField_uniformEntry r deltaS PhiS hr hd hP K hK hKphys)

/-- v2 `ass:W2` (curvature window and switch, cells 7--8), as an explicit hypothesis
structure.  It is a `Prop` to be passed as an argument, never an axiom, and no theorem in the
package consumes it.

Data: a path `eps ↦ Psi eps` of drift-recursion maps with fixed points `yfix eps`, the limiting
ceiling parameters `(theta, R)` of v2 `prop:W2` and the limiting curvature step `wstar`.
Content: `wstar` lies strictly below the ceiling `windowCritical theta R` (v2 `prop:W2`), and
there is a neighbourhood of the fixed point, of radius independent of `eps`, from which the
recursion converges to it at an envelope rate of order `eps` per step. -/
structure AssumptionW2 (Psi : ℝ → DynamicState → DynamicState) (yfix : ℝ → DynamicState)
    (theta R wstar : ℝ) : Prop where
  below_ceiling : wstar < windowCritical theta R
  local_convergence : ∃ ρ eps0 C c : ℝ, 0 < ρ ∧ 0 < eps0 ∧ 0 < C ∧ 0 < c ∧
    ∀ eps, 0 < eps → eps < eps0 → ∀ y0 : DynamicState, ‖y0 - yfix eps‖ ≤ ρ →
      ∀ k : ℕ, ‖(Psi eps)^[k] y0 - yfix eps‖ ≤ C * Real.exp (-(c * eps * k)) * ‖y0 - yfix eps‖

end SparseSGD.Logistic.V2
