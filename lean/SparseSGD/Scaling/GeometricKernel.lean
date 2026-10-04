import Mathlib.Analysis.SpecificLimits.Basic

namespace SparseSGD.Scaling
noncomputable section

/-- The geometric lag law, indexed from one so lag zero has no mass. -/
def geomLag (q : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1-q) * q^n

theorem geomLag_nonneg (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    0 ≤ geomLag q n := by
  cases n with
  | zero => simp [geomLag]
  | succ n => simp [geomLag]; positivity

theorem geomLag_hasSum_one (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (geomLag q) 1 := by
  have hcoef : (1-q) * (1-q)⁻¹ = 1 := by
    field_simp [ne_of_gt (by linarith : 0 < 1-q)]
  have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (1-q)
  have hg1 : HasSum (fun n : ℕ => (1-q)*q^n) 1 := by simpa [hcoef] using hg
  have ht : HasSum (fun n : ℕ => geomLag q (n+1)) 1 := by
    simpa [geomLag] using hg1
  exact (hasSum_nat_add_iff' 1).mp (by simpa [geomLag] using ht)

theorem geomLag_summable (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (geomLag q) := (geomLag_hasSum_one q hq0 hq1).summable

theorem pow_sub_le_of_unit_interval (a b : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha1 : a < 1) (hb1 : b < 1) (k : ℕ) :
    |a^k - b^k| ≤ |a - b| / (1-max a b) := by
  let m := max a b
  have hm0 : 0 ≤ m := le_max_of_le_left ha0
  have hm1 : m < 1 := max_lt_iff.mpr ⟨ha1,hb1⟩
  have ham : a ≤ m := le_max_left _ _
  have hbm : b ≤ m := le_max_right _ _
  induction k with
  | zero => simp only [pow_zero, sub_self, abs_zero]; positivity
  | succ k ih =>
      rw [pow_succ, pow_succ]
      calc
        |a^k * a - b^k * b| = |(a^k - b^k) * a + b^k * (a - b)| := by congr 1 <;> ring
        _ ≤ |a^k - b^k| * |a| + |b^k| * |a - b| := by
          calc
            _ ≤ |(a^k - b^k) * a| + |b^k * (a - b)| := abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_mul]
        _ ≤ (|a - b| / (1-m)) * m + m^k * |a - b| := by
          have hpow : |b^k| ≤ m^k := by
            rw [abs_of_nonneg (pow_nonneg hb0 _)]
            exact pow_le_pow_left₀ hb0 hbm _
          rw [abs_of_nonneg (by positivity : 0 ≤ a)]
          have ihm : |a^k - b^k| ≤ |a - b| / (1-m) := by simpa [m] using ih
          have hcoef : 0 ≤ |a - b| / (1-m) := div_nonneg (abs_nonneg _) (by linarith)
          have hfirst : |a^k - b^k| * a ≤ (|a - b| / (1-m))*m := by
            calc
              |a^k - b^k| * a ≤ (|a - b| / (1-m))*a := mul_le_mul_of_nonneg_right ihm ha0
              _ ≤ (|a - b| / (1-m))*m := mul_le_mul_of_nonneg_left ham hcoef
          exact add_le_add hfirst (mul_le_mul_of_nonneg_right hpow (abs_nonneg _))
        _ ≤ |a - b| / (1-m) := by
          have hden : 0 < 1-m := by linarith
          have hmle : m ≤ 1 := le_of_lt hm1
          have hmpow : m^k ≤ 1 := pow_le_one₀ hm0 hmle
          calc
            _ ≤ (|a - b| / (1-m))*m + 1*|a - b| := by
              exact add_le_add (le_of_eq rfl) (mul_le_mul_of_nonneg_right hmpow (abs_nonneg _))
            _ = |a - b| / (1-m) := by field_simp; ring
        _ ≤ |a - b| / (1-max a b) := by simpa [m]

def geomMajor (a b : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => (b-a)*a^n + (1-b)*(b^n-a^n)

theorem geomMajor_nonneg (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) (n : ℕ) :
    0 ≤ geomMajor a b n := by
  cases n with
  | zero => simp [geomMajor]
  | succ n =>
      simp only [geomMajor]
      have h1 : 0 ≤ b-a := by linarith
      have h2 : 0 ≤ 1-b := by linarith
      have h3 : 0 ≤ b^n-a^n := by
        exact sub_nonneg.mpr (pow_le_pow_left₀ ha hab n)
      positivity

theorem geomMajor_hasSum (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    HasSum (geomMajor a b) (2*(b-a)/(1-a)) := by
  have ha1 : a < 1 := lt_of_le_of_lt hab hb
  have hga := hasSum_geometric_of_lt_one ha ha1
  have hgb := hasSum_geometric_of_lt_one (by linarith : 0 ≤ b) hb
  have hd : HasSum (fun n : ℕ => b^n-a^n) ((1-b)⁻¹-(1-a)⁻¹) := hgb.sub hga
  have hfirst := hga.mul_left (b-a)
  have hsecond := hd.mul_left (1-b)
  have htail : HasSum (fun n : ℕ => geomMajor a b (n+1)) (2*(b-a)/(1-a)) := by
    have hsum := hfirst.add hsecond
    convert hsum using 1
    · ext n
      simp [geomMajor]
    · field_simp [ne_of_gt (by linarith : 0 < 1-a), ne_of_gt (by linarith : 0 < 1-b)]
      ring
  have hfull : HasSum (geomMajor a b) (2*(b-a)/(1-a)) :=
    (hasSum_nat_add_iff' (f := geomMajor a b) 1).mp (by simpa [geomMajor] using htail)
  exact hfull

theorem geomLag_tv_bound_ordered (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    Summable (fun n => |geomLag a n - geomLag b n|) ∧
    ∑' n, |geomLag a n - geomLag b n| ≤ 2*(b-a)/(1-b) := by
  have hmajor := (geomMajor_hasSum a b ha hab hb).summable
  have hpoint (n : ℕ) : |geomLag a n - geomLag b n| ≤ geomMajor a b n := by
    cases n with
    | zero => simp [geomLag, geomMajor]
    | succ n =>
        simp only [geomLag, geomMajor]
        have hpow : a^n ≤ b^n := pow_le_pow_left₀ ha hab n
        have hdiff : 0 ≤ b^n-a^n := by linarith
        have hcoeff : 0 ≤ 1-b := by linarith
        have hu : 0 ≤ (b-a)*a^n := mul_nonneg (by linarith) (pow_nonneg ha n)
        have hv : 0 ≤ (1-b)*(b^n-a^n) := mul_nonneg hcoeff hdiff
        have hid : (1-a)*a^n-(1-b)*b^n = (b-a)*a^n-(1-b)*(b^n-a^n) := by ring
        rw [abs_le]
        constructor <;> rw [hid] <;> linarith
  have habs : Summable (fun n => |geomLag a n - geomLag b n|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpoint hmajor
  have hsum := habs.tsum_le_tsum hpoint hmajor
  have hmajorSum := (geomMajor_hasSum a b ha hab hb).tsum_eq
  constructor
  · exact habs
  · calc
      ∑' n, |geomLag a n - geomLag b n| ≤ 2*(b-a)/(1-a) := by simpa [hmajorSum] using hsum
      _ ≤ 2*(b-a)/(1-b) := by
        apply div_le_div_of_nonneg_left (by nlinarith : 0 ≤ 2*(b-a))
        · linarith
        · linarith

theorem geomLag_tv_bound (a b : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha1 : a < 1) (hb1 : b < 1) :
    Summable (fun n => |geomLag a n - geomLag b n|) ∧
    ∑' n, |geomLag a n - geomLag b n| ≤ 2*|a-b|/(1-max a b) := by
  by_cases hab : a ≤ b
  · have h := geomLag_tv_bound_ordered a b ha0 hab hb1
    simpa [abs_of_nonpos (sub_nonpos.mpr hab), max_eq_right hab] using h
  · have hba : b ≤ a := le_of_not_ge hab
    have h := geomLag_tv_bound_ordered b a hb0 hba ha1
    simpa [abs_of_nonneg (sub_nonneg.mpr hba), max_eq_left hba,
      abs_sub_comm] using h
