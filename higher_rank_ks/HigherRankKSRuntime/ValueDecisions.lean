import HigherRankKSRuntime.Ledger

/-! Arithmetic correctness of finite additive-value decisions. These are
intermediate lemmas: derivative error bounds and the source-specific cap
are not assumed at any claimed public algorithmic endpoint. -/

noncomputable section
namespace HigherRankKSRuntime

def reportedBest (rplus rminus fplus fminus : ℝ) : ℝ :=
  if rplus ≤ rminus then fplus else fminus

theorem reportedBest_le_average {rplus rminus fplus fminus ν : ℝ}
    (hp : |rplus - fplus| ≤ ν) (hm : |rminus - fminus| ≤ ν) :
    reportedBest rplus rminus fplus fminus ≤ (fplus + fminus) / 2 + ν := by
  obtain ⟨hpL, hpU⟩ := abs_le.mp hp
  obtain ⟨hmL, hmU⟩ := abs_le.mp hm
  unfold reportedBest
  split_ifs with h
  · linarith
  · have hh : rminus < rplus := lt_of_not_ge h
    linarith

theorem reportedBest_descent {rplus rminus fplus fminus ν base gap : ℝ}
    (hp : |rplus - fplus| ≤ ν) (hm : |rminus - fminus| ≤ ν)
    (havg : (fplus + fminus) / 2 ≤ base - gap) :
    reportedBest rplus rminus fplus fminus ≤ base - gap + ν := by
  exact (reportedBest_le_average hp hm).trans (by linarith)

theorem reported_difference_error {r0 r1 f0 f1 ν : ℝ}
    (h0 : |r0 - f0| ≤ ν) (h1 : |r1 - f1| ≤ ν) :
    |(r1 - r0) - (f1 - f0)| ≤ 2 * ν := by
  obtain ⟨h0L, h0U⟩ := abs_le.mp h0
  obtain ⟨h1L, h1U⟩ := abs_le.mp h1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem preparation_accepted_descent {report actual scale ν : ℝ}
    (herr : |report - actual| ≤ 2 * ν)
    (hν : ν ≤ scale / 64) (haccept : report ≤ -scale / 4) :
    actual ≤ -(7 * scale / 32) := by
  obtain ⟨hL, hU⟩ := abs_le.mp herr
  linarith

theorem preparation_rejected_derivative {report actual deriv step p0 a M ν : ℝ}
    (hstepPos : 0 < step) (ha : 0 < a) (hp0 : 0 ≤ p0)
    (herr : |report - actual| ≤ 2 * ν)
    (htaylor : |actual / step - deriv| ≤ M * step / 2)
    (hν : ν ≤ step * p0 / (64 * a))
    (hstep : M * step ≤ p0 / (8 * a))
    (hreject : -(step * p0 / (4 * a)) < report) :
    -(p0 / (2 * a)) < deriv := by
  have heL : report - actual ≤ 2 * ν := (abs_le.mp herr).2
  have htL : actual / step - deriv ≤ M * step / 2 := (abs_le.mp htaylor).2
  have hnum : -(step * p0 / (4 * a)) - 2 * ν < actual := by linarith
  have hquot : (-(step * p0 / (4 * a)) - 2 * ν) / step < actual / step :=
    div_lt_div_of_pos_right hnum hstepPos
  have heq : (-(step * p0 / (4 * a)) - 2 * ν) / step =
      -(p0 / (4 * a)) - 2 * ν / step := by
    field_simp
    <;> ring
  have hν' : 2 * ν / step ≤ p0 / (32 * a) := by
    calc
      _ ≤ (2 * (step * p0 / (64 * a))) / step :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hν (by norm_num))
          (le_of_lt hstepPos)
      _ = _ := by field_simp; ring
  rw [heq] at hquot
  have hsum : -(p0 / (4 * a)) - p0 / (32 * a) - p0 / (16 * a) =
      -(11 * p0 / (32 * a)) := by ring
  have hM : M * step / 2 ≤ p0 / (16 * a) := by
    calc
      _ ≤ (p0 / (8 * a)) / 2 := div_le_div_of_nonneg_right hstep (by norm_num)
      _ = _ := by ring
  have hderiv : -(11 * p0 / (32 * a)) < deriv := by linarith
  have hcompare : -(p0 / (2 * a)) ≤ -(11 * p0 / (32 * a)) := by
    apply neg_le_neg
    apply (div_le_div_iff₀ (by positivity : 0 < 32 * a) (by positivity : 0 < 2 * a)).2
    nlinarith
  exact hcompare.trans_lt hderiv

theorem preparation_probe_cap {p p0 τ deriv a : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hp0 : p0 ≤ p)
    (hsource : deriv ≤ p / a - τ)
    (hderiv : -(p0 / (2 * a)) < deriv) :
    τ / p < 3 / (2 * a) := by
  have hτ : τ < p / a + p0 / (2 * a) := by linarith
  have hbound : p / a + p0 / (2 * a) ≤ 3 * p / (2 * a) := by
    have hden : 0 < 2 * a := by positivity
    have hp0div := div_le_div_of_nonneg_right hp0 (le_of_lt hden)
    calc
      _ ≤ p / a + p / (2 * a) := add_le_add_left hp0div _
      _ = _ := by ring
  apply (div_lt_iff₀ hp).2
  convert hτ.trans_le hbound using 1 <;> ring

end HigherRankKSRuntime
