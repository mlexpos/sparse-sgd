import Mathlib

/-! Shared coordinates. Algebraic definitions deliberately allow signed loads. -/
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
  beta : ℝ
  w : ℝ
  noise : ℝ
  additive : ℝ

def Params.eps (p : Params) : ℝ := 1 - p.beta
def Params.curvature (p : Params) : ℝ := p.w / (2 * (1 + p.beta))
def Params.totalLoad (p : Params) : ℝ := p.noise + p.curvature
def Params.renormNoise (p : Params) : ℝ := p.noise / (1 - p.curvature)
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

def continuumField (delta u phi : ℝ) (s : Moments) : Moments :=
  ⟨-2*delta*s.C, 2*s.C-2*s.V+2/delta*(u*s.R+phi), s.R-s.C-delta*s.V⟩

def slowEnergy (delta : ℝ) (s : Moments) : ℝ := s.R + delta*s.V - s.C

end
end SparseSGD
