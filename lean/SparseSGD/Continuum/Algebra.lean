import SparseSGD.Foundations

/-! Algebraic identities for the continuum moment field. -/
namespace SparseSGD

theorem slowEnergy_field (delta u phi : ℝ) (s : Moments) (hδ : delta ≠ 0) :
    slowEnergy delta (continuumField delta u phi s) =
      -slowEnergy delta s + 2 * (u * s.R + phi) := by
  simp [slowEnergy, continuumField]
  field_simp
  <;> ring

theorem freeEnergy_dissipation (delta : ℝ) (s : Moments) :
    (continuumField delta 0 0 s).R +
        delta * (continuumField delta 0 0 s).V = -2 * delta * s.V := by
  simp [continuumField]
  ring

theorem rankDefect_field (delta u phi : ℝ) (s : Moments) (hδ : delta ≠ 0) :
    (continuumField delta u phi s).R * s.V +
        s.R * (continuumField delta u phi s).V -
        2 * s.C * (continuumField delta u phi s).C =
      -2 * s.rankDefect + 2 / delta * s.R * (u * s.R + phi) := by
  simp [continuumField, Moments.rankDefect]
  field_simp
  <;> ring

theorem continuumField_eq_zero_iff (delta u phi : ℝ) (s : Moments)
    (hδ : delta ≠ 0) (hu : u ≠ 1) :
    continuumField delta u phi s = 0 ↔
      s.R = phi / (1 - u) ∧ s.V = s.R / delta ∧ s.C = 0 := by
  constructor
  · intro h
    have hR : -2 * delta * s.C = 0 := by
      have := congrArg Moments.R h
      change -2 * delta * s.C = 0 at this
      exact this
    have hC : s.C = 0 := by
      have h2 : (2 * delta) ≠ 0 := mul_ne_zero (by norm_num) hδ
      have hmul : (2 * delta) * s.C = 0 := by nlinarith [hR]
      rcases mul_eq_zero.mp hmul with hz | hz
      · exact (h2 hz).elim
      · exact hz
    have hVeq : s.R - s.C - delta * s.V = 0 := by
      have := congrArg Moments.C h
      change s.R - s.C - delta * s.V = 0 at this
      exact this
    have hV : s.V = s.R / delta := by
      rw [hC] at hVeq
      field_simp
      linarith
    have hReq0 : 2 * s.C - 2 * s.V + 2 / delta * (u * s.R + phi) = 0 := by
      have := congrArg Moments.V h
      change 2 * s.C - 2 * s.V + 2 / delta * (u * s.R + phi) = 0 at this
      exact this
    rw [hC, hV] at hReq0
    have hR0 : (1 - u) * s.R = phi := by
      field_simp [hδ] at hReq0
      nlinarith [hReq0]
    refine ⟨?_, hV, hC⟩
    have hden : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    field_simp [hden]
    nlinarith [hR0]
  · rintro ⟨hR, hV, hC⟩
    apply Moments.ext
    · change -2 * delta * s.C = 0
      rw [hC]
      ring
    · change 2 * s.C - 2 * s.V + 2 / delta * (u * s.R + phi) = 0
      rw [hC, hV, hR]
      have hδ' : delta ≠ 0 := hδ
      have hu' : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
      field_simp [hδ', hu']
      ring
    · change s.R - s.C - delta * s.V = 0
      rw [hC, hV]
      have hδ' : delta ≠ 0 := hδ
      field_simp [hδ']
      ring

theorem existsUnique_continuum_equilibrium (delta u phi : ℝ)
    (hδ : delta ≠ 0) (hu : u ≠ 1) :
    ∃! s : Moments, continuumField delta u phi s = 0 := by
  let s : Moments := ⟨phi / (1 - u), (phi / (1 - u)) / delta, 0⟩
  refine ⟨s, ?_, ?_⟩
  · apply (continuumField_eq_zero_iff delta u phi s hδ hu).2
    simp [s]
  · intro t ht
    have h := (continuumField_eq_zero_iff delta u phi t hδ hu).1 ht
    cases t with
    | mk R V C =>
      simp_all [s]

end SparseSGD
