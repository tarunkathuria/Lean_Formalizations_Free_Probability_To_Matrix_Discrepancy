import MatrixSpencer.KSEighthManuscriptLDL
import MatrixSpencer.MSManuscriptPaidStep

/-! Entrywise estimates for actual scalar Schur deletion. These support the
Jacobi-based real-arithmetic cleanup variant, without matrix inverse evaluation,
eigenvector choices, or a spectral-gap assumption. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptSchurEstimates
open KSEighthManuscriptLDL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem schur_entry (P : Matrix ι ι ℝ) (i a b : ι) :
    schur P i a b = P a b-P a i*P b i/P i i := by
  simp only [schur, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, column]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem schur_diagonal_loss (P : Matrix ι ι ℝ) (i a : ι) :
    P a a-schur P i a a = (P a i)^2/P i i := by
  rw [schur_entry]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem schur_perturbation_bound (P : Matrix ι ι ℝ) (i a b : ι) {g e : ℝ}
    (hg : 0 < g) (he : 0 ≤ e) (hpi : g ≤ P i i)
    (ha : |P a i| ≤ e) (hb : |P b i| ≤ e) :
    |schur P i a b-P a b| ≤ e^2/g := by
  have hp : 0 < P i i := hg.trans_le hpi
  rw [schur_entry]
  have hcalc : P a b-P a i*P b i/P i i-P a b = -(P a i*P b i/P i i) := by ring
  rw [hcalc, abs_neg, abs_div, abs_mul, abs_of_pos hp]
  have hnum : |P a i| * |P b i| ≤ e^2 := by
    nlinarith [mul_le_mul ha hb (abs_nonneg _) he]
  calc
    _ ≤ e^2/P i i := div_le_div_of_nonneg_right hnum hp.le
    _ ≤ e^2/g := div_le_div_of_nonneg_left (sq_nonneg e) hg hpi

theorem schur_trace_loss (P : Matrix ι ι ℝ) (i : ι) (hp : 0 < P i i) :
    realTrace P-realTrace (schur P i) = P i i+∑ a, if a=i then 0 else (P a i)^2/P i i := by
  have htr : realTrace P-realTrace (schur P i) = ∑ a, (P a i)^2/P i i := by
    rw [schur, realTrace_sub, realTrace_smul]
    change realTrace P-(realTrace P-(P i i)⁻¹*(∑ a, P a i*P a i)) = _
    rw [← Finset.sum_div]
    simp only [pow_two]
    ring
  rw [htr]
  calc
    (∑ a, (P a i)^2/P i i) =
        (∑ a : ι, if a=i then P i i else 0)+(∑ a, if a=i then 0 else (P a i)^2/P i i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hai : a=i
      · subst a
        simp only [if_true, add_zero]
        field_simp
      · simp [hai]
    _ = _ := by simp

theorem schur_trace_loss_le (P : Matrix ι ι ℝ) (i : ι) {g e : ℝ}
    (hg : 0 < g) (he : 0 ≤ e) (hpi : g ≤ P i i)
    (hoff : ∀ a, a ≠ i → |P a i| ≤ e) :
    realTrace P-realTrace (schur P i) ≤ P i i+(Fintype.card ι:ℝ)*(e^2/g) := by
  rw [schur_trace_loss P i (hg.trans_le hpi)]
  apply add_le_add_left
  calc
    (∑ a, if a=i then 0 else (P a i)^2/P i i) ≤ ∑ _a : ι, e^2/g := by
      apply Finset.sum_le_sum
      intro a _
      by_cases hai : a=i
      · simp only [hai, if_true]
        positivity
      · simp only [hai, if_false]
        have hpos : 0 ≤ (P a i)^2/P i i := div_nonneg (sq_nonneg _) (hg.trans_le hpi).le
        have hc : schur P i a a-P a a = -((P a i)^2/P i i) := by rw [schur_entry]; ring
        have hh := schur_perturbation_bound P i a a hg he hpi (hoff a hai) (hoff a hai)
        simpa only [hc, abs_neg, abs_of_nonneg hpos] using hh
    _ = _ := by simp

end MatrixSpencer.MSManuscriptSchurEstimates
