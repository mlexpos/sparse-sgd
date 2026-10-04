import SparseSGD.Logistic.Moments

open MeasureTheory ProbabilityTheory

namespace SparseSGD.Logistic
noncomputable section
set_option maxHeartbeats 800000

def sigmaPrime (t : ℝ) : ℝ := sigma t * (1 - sigma t)
def sigmaSecond (t : ℝ) : ℝ := sigmaPrime t * (1 - 2 * sigma t)
def sigmaSqSecond (t : ℝ) : ℝ := 2 * sigmaPrime t ^ 2 + 2 * sigma t * sigmaSecond t
def oneMinusSigmaSqSecond (t : ℝ) : ℝ :=
  2 * sigmaPrime t ^ 2 - 2 * (1 - sigma t) * sigmaSecond t

theorem hasDerivAt_sigma (t : ℝ) : HasDerivAt sigma (sigmaPrime t) t := by
  have he : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have hden : HasDerivAt (fun x : ℝ => 1 + Real.exp x) (Real.exp t) t :=
    he.const_add 1
  have hquot := he.div hden (by positivity : (1 + Real.exp t) ≠ 0)
  convert hquot using 1
  · funext x
    rfl
  · dsimp [sigmaPrime, sigma]
    field_simp

theorem hasDerivAt_sigmaPrime (t : ℝ) : HasDerivAt sigmaPrime (sigmaSecond t) t := by
  have h := hasDerivAt_sigma t
  have hone : HasDerivAt (fun x : ℝ => 1 - sigma x) (-sigmaPrime t) t :=
    h.const_sub 1
  convert h.mul hone using 1
  · funext x
    rfl
  · dsimp [sigmaPrime, sigmaSecond]
    ring

def classLogit0 {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (z : Fin d → ℝ) : ℝ :=
  inner ℝ theta (WithLp.toLp 2 z) + bias p mu

def classLogit1 {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (z : Fin d → ℝ) : ℝ :=
  inner ℝ theta (WithLp.toLp 2 z) + inner ℝ theta mu + bias p mu

private abbrev gaussianLaw (d : ℕ) := SparseSGD.Probability.standardGaussianProduct d

def coefA {d : ℕ} (p : unitInterval) (mu theta : Vec d) : ℝ :=
  (1 - (p : ℝ)) * ∫ z, sigmaPrime (classLogit0 p mu theta z) ∂gaussianLaw d +
    (p : ℝ) * ∫ z, sigmaPrime (classLogit1 p mu theta z) ∂gaussianLaw d

def coefB {d : ℕ} (p : unitInterval) (mu theta : Vec d) : ℝ :=
  (p : ℝ) * (∫ z, sigma (classLogit1 p mu theta z) ∂gaussianLaw d - 1)

def coefD0 {d : ℕ} (p : unitInterval) (mu theta : Vec d) : ℝ :=
  (1 - (p : ℝ)) * ∫ z, sigma (classLogit0 p mu theta z) ^ 2 ∂gaussianLaw d +
    (p : ℝ) * ∫ z, (1 - sigma (classLogit1 p mu theta z)) ^ 2 ∂gaussianLaw d

def coefDtheta {d : ℕ} (p : unitInterval) (mu theta : Vec d) : ℝ :=
  (1 - (p : ℝ)) * ∫ z, sigmaSqSecond (classLogit0 p mu theta z) ∂gaussianLaw d +
    (p : ℝ) * ∫ z, oneMinusSigmaSqSecond (classLogit1 p mu theta z) ∂gaussianLaw d

theorem sigmaPrime_pos (t : ℝ) : 0 < sigmaPrime t := by
  unfold sigmaPrime
  exact mul_pos (sigma_pos t) (sub_pos.mpr (sigma_lt_one t))

theorem sigmaPrime_le_one (t : ℝ) : sigmaPrime t ≤ 1 := by
  unfold sigmaPrime
  have h0 := sigma_pos t
  have h1 := sigma_lt_one t
  nlinarith

theorem sigmaPrime_abs_le_one (t : ℝ) : |sigmaPrime t| ≤ 1 := by
  rw [abs_of_nonneg (le_of_lt (sigmaPrime_pos t))]
  exact sigmaPrime_le_one t

theorem sigmaSecond_abs_le_one (t : ℝ) : |sigmaSecond t| ≤ 1 := by
  rw [sigmaSecond, abs_mul]
  have hprime := sigmaPrime_abs_le_one t
  have hsig := sigma_pos t
  have hsig1 := sigma_lt_one t
  have hfactor : |1 - 2 * sigma t| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  simpa using (mul_le_mul hprime hfactor (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))

theorem sigmaSqSecond_abs_le_four (t : ℝ) : |sigmaSqSecond t| ≤ 4 := by
  have hprime := sigmaPrime_abs_le_one t
  have hsecond := sigmaSecond_abs_le_one t
  have hsig : |sigma t| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sigma_pos t, sigma_lt_one t]
  have hprod : |sigma t| * |sigmaSecond t| ≤ 1 :=
    calc
      |sigma t| * |sigmaSecond t| ≤ 1 * 1 :=
        mul_le_mul hsig hsecond (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hterm₁ : |2 * sigmaPrime t ^ 2| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (sigmaPrime t))]
    norm_num
    nlinarith [sq_abs (sigmaPrime t), hprime]
  have hterm₂ : |2 * sigma t * sigmaSecond t| ≤ 2 := by
    rw [abs_mul, abs_mul]
    norm_num
    nlinarith [hprod]
  rw [sigmaSqSecond]
  calc
    |2 * sigmaPrime t ^ 2 + 2 * sigma t * sigmaSecond t| ≤
        |2 * sigmaPrime t ^ 2| + |2 * sigma t * sigmaSecond t| := abs_add_le _ _
    _ ≤ 4 := by linarith

theorem oneMinusSigmaSqSecond_abs_le_four (t : ℝ) :
    |oneMinusSigmaSqSecond t| ≤ 4 := by
  have hprime := sigmaPrime_abs_le_one t
  have hsecond := sigmaSecond_abs_le_one t
  have hsig : |sigma t| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sigma_pos t, sigma_lt_one t]
  have hfactor : |1 - sigma t| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sigma_pos t, sigma_lt_one t]
  have hprod : |1 - sigma t| * |sigmaSecond t| ≤ 1 :=
    calc
      |1 - sigma t| * |sigmaSecond t| ≤ 1 * 1 :=
        mul_le_mul hfactor hsecond (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hterm₁ : |2 * sigmaPrime t ^ 2| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (sigmaPrime t))]
    norm_num
    nlinarith [sq_abs (sigmaPrime t), hprime]
  have hterm₂ : |2 * (1 - sigma t) * sigmaSecond t| ≤ 2 := by
    rw [abs_mul, abs_mul]
    norm_num
    nlinarith [hprod]
  rw [oneMinusSigmaSqSecond]
  calc
    |2 * sigmaPrime t ^ 2 - 2 * (1 - sigma t) * sigmaSecond t| ≤
        |2 * sigmaPrime t ^ 2| + |2 * (1 - sigma t) * sigmaSecond t| := abs_sub _ _
    _ ≤ 4 := by linarith

private theorem measurable_classLogit0 {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    Measurable (classLogit0 p mu theta) := by
  unfold classLogit0
  fun_prop

private theorem measurable_classLogit1 {d : ℕ} (p : unitInterval) (mu theta : Vec d) :
    Measurable (classLogit1 p mu theta) := by
  unfold classLogit1
  fun_prop

private theorem measurable_sigmaPrime : Measurable sigmaPrime := by
  unfold sigmaPrime
  exact measurable_sigma.mul (measurable_const.sub measurable_sigma)

private theorem measurable_sigmaSecond : Measurable sigmaSecond := by
  unfold sigmaSecond
  exact measurable_sigmaPrime.mul (measurable_const.sub (measurable_sigma.const_mul 2))

private theorem measurable_sigmaSqSecond : Measurable sigmaSqSecond := by
  change Measurable (fun t : ℝ => 2 * sigmaPrime t ^ 2 + 2 * sigma t * sigmaSecond t)
  have hfirst : Measurable (fun t : ℝ => 2 * (sigmaPrime t * sigmaPrime t)) :=
    (measurable_sigmaPrime.mul measurable_sigmaPrime).const_mul 2
  have hsecond : Measurable (fun t : ℝ => (2 * sigma t) * sigmaSecond t) :=
    ((measurable_const : Measurable (fun _ : ℝ => (2 : ℝ))).mul measurable_sigma).mul
      measurable_sigmaSecond
  convert hfirst.add hsecond using 1
  · funext t
    simp only [Pi.add_apply]
    ring

private theorem measurable_oneMinusSigmaSqSecond : Measurable oneMinusSigmaSqSecond := by
  change Measurable (fun t : ℝ => 2 * sigmaPrime t ^ 2 - 2 * (1 - sigma t) * sigmaSecond t)
  have hfirst : Measurable (fun t : ℝ => 2 * (sigmaPrime t * sigmaPrime t)) :=
    (measurable_sigmaPrime.mul measurable_sigmaPrime).const_mul 2
  have hsecond : Measurable (fun t : ℝ => (2 * (1 - sigma t)) * sigmaSecond t) :=
    ((measurable_const : Measurable (fun _ : ℝ => (2 : ℝ))).mul
      ((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).sub measurable_sigma)).mul
        measurable_sigmaSecond
  convert hfirst.sub hsecond using 1
  · funext t
    simp only [Pi.sub_apply]
    ring

private theorem integrable_of_abs_le {d : ℕ} (f : (Fin d → ℝ) → ℝ) (C : ℝ)
    (hf : Measurable f) (hbound : ∀ z, |f z| ≤ C) : Integrable f (gaussianLaw d) := by
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards with z
  rw [Real.norm_eq_abs]
  exact hbound z

private theorem integrable_sigmaPrime {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (c : Bool) : Integrable (fun z => sigmaPrime
      (if c then classLogit1 p mu theta z else classLogit0 p mu theta z)) (gaussianLaw d) := by
  apply integrable_of_abs_le _ 1
  · by_cases hc : c
    · simpa [hc, Function.comp_def] using measurable_sigmaPrime.comp (measurable_classLogit1 p mu theta)
    · simpa [hc, Function.comp_def] using measurable_sigmaPrime.comp (measurable_classLogit0 p mu theta)
  · intro z
    exact sigmaPrime_abs_le_one _

theorem coefA_pos {d : ℕ} (p : unitInterval) (mu theta : Vec d)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) : 0 < coefA p mu theta := by
  unfold coefA
  have h0 : 0 < ∫ z, sigmaPrime (classLogit0 p mu theta z) ∂gaussianLaw d := by
    apply (integral_pos_iff_support_of_nonneg (fun z => (sigmaPrime_pos _).le)
      (integrable_of_abs_le _ 1 (by simpa [Function.comp_def] using measurable_sigmaPrime.comp (measurable_classLogit0 p mu theta))
        (fun z => sigmaPrime_abs_le_one _))).2
    rw [show Function.support (fun z : Fin d → ℝ => sigmaPrime (classLogit0 p mu theta z)) =
      Set.univ by ext z; simp [Function.support, ne_of_gt (sigmaPrime_pos _)]]
    simpa using (measure_univ_pos : 0 < (gaussianLaw d) Set.univ)
  have h1 : 0 < ∫ z, sigmaPrime (classLogit1 p mu theta z) ∂gaussianLaw d := by
    apply (integral_pos_iff_support_of_nonneg (fun z => (sigmaPrime_pos _).le)
      (integrable_of_abs_le _ 1 (by simpa [Function.comp_def] using measurable_sigmaPrime.comp (measurable_classLogit1 p mu theta))
        (fun z => sigmaPrime_abs_le_one _))).2
    rw [show Function.support (fun z : Fin d → ℝ => sigmaPrime (classLogit1 p mu theta z)) =
      Set.univ by ext z; simp [Function.support, ne_of_gt (sigmaPrime_pos _)]]
    simpa using (measure_univ_pos : 0 < (gaussianLaw d) Set.univ)
  have hp0' : 0 < (p : ℝ) := hp0
  have hnot : 0 < 1 - (p : ℝ) := by linarith
  positivity

end
end SparseSGD.Logistic
