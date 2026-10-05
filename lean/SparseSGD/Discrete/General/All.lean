import SparseSGD.Discrete.General.Renewal
import SparseSGD.Discrete.General.Tikhonov

/-!
# The momentum range `β ∈ [0,1)`: relaxed renewal statements

The live appendix chunks (`source/v2/chunks/`, snapshot of 2026-10-05) state the setup of the
master reduction for `β ∈ [0,1)` instead of `β ∈ [1/2,1)`: `ε = 1-β ∈ (0,1]`, and `β = 0` is
plain SGD.  The v1 modules `SparseSGD/Discrete/{Stability,RiskBound,StableKernel,FreeRisk}.lean`
keep the hypothesis `1/2 ≤ β` (their signatures are frozen because the comparison theorem and
its corollaries build on them).  This directory adds the relaxed statements as new declarations
with the suffix `_v2`:

* `Renewal`: `v2 lem:L2` (kernel masses, normalized kernel, `x_n = -(1-w)^n` at `β = 0`) and
  `v2 cor:stab` (uniform bound, geometric convergence, floor, necessity with the new hypothesis
  `(Σ₀)₁₁ > 0` or `β > 0`), plus `v2 cor:lift (i)` (rank at most one at `β = 0`).
* `Tikhonov`: `v2 cor:tikhonov` for every `ε ∈ (0,1]` (`cor_tikhonov_v2`).

The Jury criterion stays an explicit hypothesis (`External.JuryStability`) where the v1
statements used it; `mean_powers_tendsto_zero_beta_zero` proves the `β = 0` case directly.
-/
