import MatrixSpencer.KSComplexTraceSource
import MatrixSpencer.KSComplexObjectiveBound
import MatrixSpencer.KSDebitUniformFloor

/-!
# Arithmetic bounds for the complex polynomial pieces of the KS objective

The source and center slope bounds are finite expressions in input entries.
They hold for arbitrary complex density perturbations and need no source
conditioning parameter. Conservative constants suffice for Cauchy estimates.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSComplexTraceBounds

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
open KSComplexTraceSource KSOwnerInputBounds

def sourceBudget (A : ι → Matrix n n ℂ) : ℝ :=
  1 + 1280 * (Fintype.card n : ℝ) * ∑ i, matrixBound (A i) ^ 2

def slopeBudget (A : ι → Matrix n n ℂ) : ℝ :=
  1 + ∑ i, matrixBound (A i)

theorem sourceBudget_pos (A : ι → Matrix n n ℂ) : 0 < sourceBudget A := by
  have h : 0 ≤ ∑ i, matrixBound (A i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold sourceBudget
  positivity

theorem slopeBudget_pos (A : ι → Matrix n n ℂ) : 0 < slopeBudget A := by
  have h : 0 ≤ ∑ i, matrixBound (A i) :=
    Finset.sum_nonneg (fun _ _ => (matrixBound_pos _).le)
  unfold slopeBudget
  linarith

theorem owner_norm_le {x h : ℝ} (hx : |x| ≤ 1) (hh : |h| ≤ 2)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(64 : ℂ) * (1 - ((x : ℂ) + z * (h : ℂ)) ^ 2)‖ ≤ 640 := by
  have ha : ‖(x : ℂ) + z * (h : ℂ)‖ ≤ 3 := by
    apply (norm_add_le _ _).trans
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have hm := mul_le_mul hz hh (abs_nonneg h) (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have hb := norm_sub_le (1 : ℂ) (((x : ℂ) + z * (h : ℂ)) ^ 2)
  rw [norm_one, norm_pow] at hb
  rw [norm_mul]
  norm_num only [Complex.norm_ofNat]
  have hc := pow_le_pow_left₀ (norm_nonneg _) ha 2
  nlinarith

/-- Absolute source control on a larger neighborhood than the final
analytic radius. No positivity is required of the complex density S. -/
theorem source_norm_le_budget (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x h : ι → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hh : ∀ i, |h i| ≤ 2) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (S : Matrix n n ℂ) (hS : ‖S‖ ≤ 2) :
    ‖source A x h (z, S)‖ ≤ sourceBudget A := by
  have he (i : ι) : ‖A i‖ ≤ matrixBound (A i) :=
    norm_le_matrixBound _ (hA i).isHermitian
  calc _ ≤ ∑ i, ‖((64 : ℂ) * (1 - ((x i : ℂ) + z * (h i : ℂ)) ^ 2) *
        Matrix.trace (A i * S)) • A i‖ := norm_sum_le _ _
    _ ≤ ∑ i, 1280 * (Fintype.card n : ℝ) * matrixBound (A i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, norm_mul]
      have hbi : 0 ≤ matrixBound (A i) := (matrixBound_pos _).le
      have hnorm := he i
      have ht := KSComplexObjectiveBound.norm_trace_mul_le_card_mul_norm (A i) S
      have ht' : ‖Matrix.trace (A i * S)‖ ≤
          (Fintype.card n : ℝ) * matrixBound (A i) * 2 := by
        exact ht.trans (by gcongr)
      have ho := owner_norm_le (hx i) (hh i) hz
      calc _ ≤ 640 * ((Fintype.card n : ℝ) * matrixBound (A i) * 2) *
          matrixBound (A i) := by gcongr
        _ = _ := by ring
    _ ≤ sourceBudget A := by
      rw [← Finset.mul_sum]
      unfold sourceBudget
      linarith

theorem slope_norm_le (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (h : ι → ℝ) (hh : ∀ i, |h i| ≤ 2) :
    ‖∑ i, h i • A i‖ ≤ 2 * slopeBudget A := by
  calc _ ≤ ∑ i, ‖h i • A i‖ := norm_sum_le _ _
    _ ≤ ∑ i, 2 * matrixBound (A i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hh i) (norm_le_matrixBound _
        (hA i)) (norm_nonneg _) (by norm_num)
    _ ≤ 2 * slopeBudget A := by rw [← Finset.mul_sum]; unfold slopeBudget; linarith

theorem center_norm_le (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (h : ι → ℝ) (hh : ∀ i, |h i| ≤ 2)
    (H : Matrix n n ℂ) {R : ℝ} (hH : ‖H‖ ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖H + z • (∑ i, h i • A i)‖ ≤ R + 2 * slopeBudget A := by
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  have hb := slope_norm_le A hA h hh
  have hm := mul_le_mul hz hb (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  linarith

/-- Restriction to any retained label predicate decreases the source budget. -/
theorem sourceBudget_restrict (A : ι → Matrix n n ℂ) (P : ι → Prop) [DecidablePred P] :
    sourceBudget (fun i : {i // P i} => A i) ≤ sourceBudget A := by
  let f := fun i => matrixBound (A i) ^ 2
  have hs := Fintype.sum_subtype_add_sum_subtype P f
  have hn : 0 ≤ ∑ i : {i // ¬P i}, f i := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hle : (∑ i : {i // P i}, f i) ≤ ∑ i, f i := by linarith
  unfold sourceBudget
  exact add_le_add_left (mul_le_mul_of_nonneg_left hle (by positivity)) _

theorem slopeBudget_restrict (A : ι → Matrix n n ℂ) (P : ι → Prop) [DecidablePred P] :
    slopeBudget (fun i : {i // P i} => A i) ≤ slopeBudget A := by
  let f := fun i => matrixBound (A i)
  have hs := Fintype.sum_subtype_add_sum_subtype P f
  have hn : 0 ≤ ∑ i : {i // ¬P i}, f i :=
    Finset.sum_nonneg (fun _ _ => (matrixBound_pos _).le)
  have hle : (∑ i : {i // P i}, f i) ≤ ∑ i, f i := by linarith
  unfold slopeBudget
  exact add_le_add_left hle _

end MatrixSpencer.KSComplexTraceBounds
