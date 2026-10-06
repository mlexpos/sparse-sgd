import Mathlib

/-! Shared coordinates. Algebraic definitions deliberately allow signed feedback and temperatures.

## Notation bridge (paper of 2026-10-05 ↔ Lean)

The Lean identifiers keep the names of the earlier manuscript; docstrings quote Lean terms in
backticks and so use these names. The paper's current notation (see `NOTATION.md`) is:

| paper | Lean | earlier manuscript |
|---|---|---|
| stiffness `ω² = ηp/ε` (matched: `ω̄²`) | `Δ`, `delta`, `Delta`, `matchedDelta`, `lsDelta`, `rawDelta` | `Δ` (`Δ̄`) |
| per-step curvature `λ = ηεp` | `w`, `Params.w` | `w` |
| noise feedback `H_n` | `Params.noise`, `un`, `lsNoiseLoad`, `resonantNoiseLoad` | `u_n` (noise load) |
| curvature feedback `H_c = λ/(2(1+β))` | `Params.curvature`, `uc` | `u_c` (curvature load) |
| total feedback `H = H_n + H_c` | `Params.totalLoad`, `u` | `u` (load) |
| amplified feedback `H̃ = H_n/(1-H_c)` | `Params.renormNoise` | `ũ` |
| ambient temperature `φ` (amplified `φ̃`) | `Params.additive`, `phi`, `lsAdditiveLoad` (`Params.renormAdditive`) | `φ` (additive load) |
| LR ambient temperature `Φ` | `Phi`, `dynamicSourceLoad` | `Φ` |
| LR curvature factor `ϱ` | `alpha`, `α` in the `Logistic` modules | `α` |
| learning-rate exponent `α` | `alpha` in the `Scaling` modules | `α` |
| eigenvalues and roots `z` | e.g. `smallDeltaLambdaPlus`, `smallDeltaLambdaMinus` | `λ` |

Identifier names containing `Load` or `Delta` keep the earlier words. -/
namespace SparseSGD
noncomputable section

@[ext] structure Moments where
  R : ℝ
  V : ℝ
  C : ℝ

instance : Zero Moments := ⟨⟨0, 0, 0⟩⟩

def Moments.cov (s : Moments) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![s.R, s.C; s.C, s.V]

def Moments.psd (s : Moments) : Prop := s.cov.PosSemidef

def Moments.rankDefect (s : Moments) : ℝ := s.R * s.V - s.C ^ 2

structure Params where
  /-- Momentum `β`. -/
  beta : ℝ
  /-- Per-step curvature, `λ = ηεp` in the paper. -/
  w : ℝ
  /-- Noise feedback, `H_n` in the paper. -/
  noise : ℝ
  /-- Ambient temperature, `φ` in the paper. -/
  additive : ℝ

def Params.eps (p : Params) : ℝ := 1 - p.beta
/-- Curvature feedback, `H_c = λ/(2(1+β))` in the paper. -/
def Params.curvature (p : Params) : ℝ := p.w / (2 * (1 + p.beta))
/-- Total feedback, `H = H_n + H_c` in the paper; stability is `H < 1`. -/
def Params.totalLoad (p : Params) : ℝ := p.noise + p.curvature
/-- Amplified feedback, `H̃ = H_n/(1-H_c)` in the paper. -/
def Params.renormNoise (p : Params) : ℝ := p.noise / (1 - p.curvature)
/-- Amplified temperature, `φ̃ = φ/(1-H_c)` in the paper. -/
def Params.renormAdditive (p : Params) : ℝ := p.additive / (1 - p.curvature)
def Params.meanMatrix (p : Params) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - p.w, -p.beta; p.w, p.beta]

def kick : Fin 2 → ℝ := ![-1, 1]

def Params.step (p : Params) (s : Moments) : Moments :=
  let q := 2 * p.w * p.eps * (p.noise * s.R + p.additive)
  ⟨(1-p.w)^2*s.R + p.beta^2*s.V - 2*p.beta*(1-p.w)*s.C + q,
   p.w^2*s.R + p.beta^2*s.V + 2*p.w*p.beta*s.C + q,
   p.w*(1-p.w)*s.R - p.beta^2*s.V + p.beta*(1-2*p.w)*s.C - q⟩

def Params.trajectory (p : Params) (s : Moments) : ℕ → Moments
  | 0 => s
  | n + 1 => p.step (p.trajectory s n)

/-- Second-moment field of the stochastic heavy ball, with `delta` the stiffness `ω²`, `u` the
feedback `H` and `phi` the ambient temperature `φ` of the paper. -/
def continuumField (delta u phi : ℝ) (s : Moments) : Moments :=
  ⟨-2*delta*s.C, 2*s.C-2*s.V+2/delta*(u*s.R+phi), s.R-s.C-delta*s.V⟩

/-- Slow energy `S = R + ω² V - C` (paper notation), with `delta = ω²`. -/
def slowEnergy (delta : ℝ) (s : Moments) : ℝ := s.R + delta*s.V - s.C

end
end SparseSGD
