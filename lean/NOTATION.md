# Notation: paper ↔ Lean

On 2026-10-05 the manuscript (draft, `paper/`)
changed notation and terminology. The Lean identifiers were not renamed. `λ` is a Lean
keyword and `ω²` is not an identifier, and renaming binders would break named arguments.
Docstrings and comments quote Lean terms in backticks, so those quotes use the Lean names.
Plain-text terminology in docstrings follows the paper: feedback, ambient temperature and
stiffness, never "load".

## Main quantities

| paper (current) | Lean | earlier manuscript |
|---|---|---|
| stiffness `ω² = ηp/ε`, the spring constant of the heavy ball | `Δ`, `delta`, `Delta`; `lsDelta`, `rawDelta`, `rayDelta` | `Δ`, "ratio of the timescales" |
| matched stiffness `ω̄²` | `matchedDelta` | `Δ̄` |
| natural frequency `ω = √(ω²)` | `Real.sqrt Δ` | `√Δ` |
| per-step curvature `λ = ηεp` | `w`, `Params.w` | `w` |
| noise feedback `H_n` | `Params.noise`, `un`, `lsNoiseLoad`, `resonantNoiseLoad`, `fixedLoadNoise` | `u_n`, "noise load" |
| curvature feedback `H_c = λ/(2(1+β))` | `Params.curvature`, `uc` | `u_c`, "curvature load" |
| total feedback `H = H_n + H_c` (stable iff `H < 1`) | `Params.totalLoad`, `u` | `u`, "load" |
| amplified feedback `H̃ = H_n/(1-H_c)` | `Params.renormNoise` | `ũ`, "renormalized load" |
| ambient temperature `φ` | `Params.additive`, `phi`, `lsAdditiveLoad` | `φ`, "additive / label-noise load" |
| amplified temperature `φ̃ = φ/(1-H_c)` | `Params.renormAdditive` | `φ̃` |
| LR ambient temperature `Φ = η(d-1)/(2B)` | `Phi`, `dynamicSourceLoad` | `Φ` |
| LR curvature factor `ϱ = e^{(θ²+R-r²)/2}` (equilibrium `ϱ*`) | `alpha`, `α` in the `Logistic` modules; `a` for `ϱ*` in `Logistic/V2/LargeDeltaAlgebra.lean` | `α` (`α*`) |
| learning-rate exponent `α` (critical `α_c`; `α_η` in the LR appendix) | `alpha` in the `Scaling` modules | `α` |

## Symbols the paper renamed to free the new ones

| paper (current) | earlier manuscript | where |
|---|---|---|
| damped frequency `Ω = √(ω² - 1/4)` | `ω` | renewal, master theorem, window chunks |
| eigenvalues and characteristic roots `z` (e.g. `z_±`, `z_0`, `z_j^±`) | `λ` (`λ_±`, `λ_0`, `λ_j^±`) | renewal, master theorem, Tikhonov, window, LR mechanisms; Lean names such as `smallDeltaLambdaPlus` |
| Bernstein parameter `s`, `s_*` | `λ`, `λ_*` | fluid-limit theorem (Theorem A) |
| W1 ratio `ψ = R*/(2(1+θ*²))` | `ρ` | `prop:W1` |
| fast-field Jacobian `Ξ` | `Ω` | proof of `prop:W1` |
| Lyapunov and curvature matrices `𝐇` (bold) | `H` | `prop:S` proof, chunk 01 remark |
| rates `r_SGD`, `r_mom`, `r_O` | `λ_SGD`, `λ_mom`, `λ_O` | `prop:helps-critical` |
| learning-clock rate written out as `η𝒜` or `ηp` | `z` | Tikhonov, phase dictionary, overview |

The frozen v1 sources in `source/` keep the earlier notation. The v2 snapshots in
`source/v2/` were refreshed on 2026-10-05 to the current text; the earlier hashes are
recorded in `source/v2/manifest.json`. Entries in `CORRECTIONS.md` and `WORKPLAN.md` dated
before 2026-10-05 use the earlier notation.
