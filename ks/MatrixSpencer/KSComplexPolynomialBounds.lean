import MatrixSpencer.KSComplexSpinSource
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
namespace MatrixSpencer.KSComplexPolynomialBounds

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
open KSComplexSpinSource KSOwnerInputBounds

def sourceBudget (v : ι → n → ℂ) : ℝ :=
  1 + 1280 * (Fintype.card (n ⊕ n) : ℝ) * ∑ i, matrixBound (atom v i) ^ 2

def slopeBudget (v : ι → n → ℂ) : ℝ :=
  1 + ∑ i, matrixBound (signedLift (KSRankOne.atom (v i)))

theorem sourceBudget_pos (v : ι → n → ℂ) : 0 < sourceBudget v := by
  have h : 0 ≤ ∑ i, matrixBound (atom v i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold sourceBudget
  positivity

theorem slopeBudget_pos (v : ι → n → ℂ) : 0 < slopeBudget v := by
  have h : 0 ≤ ∑ i, matrixBound (signedLift (KSRankOne.atom (v i))) :=
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
theorem source_norm_le_budget (v : ι → n → ℂ) (x h : ι → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hh : ∀ i, |h i| ≤ 2) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hS : ‖S‖ ≤ 2) :
    ‖source v x h (z, S)‖ ≤ sourceBudget v := by
  have he (i : ι) : ‖atom v i‖ ≤ matrixBound (atom v i) :=
    norm_le_matrixBound _ (atom_posSemidef v i).isHermitian
  calc _ ≤ ∑ i, ‖((64 : ℂ) * (1 - ((x i : ℂ) + z * (h i : ℂ)) ^ 2) *
        Matrix.trace (atom v i * S)) • atom v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, 1280 * (Fintype.card (n ⊕ n) : ℝ) * matrixBound (atom v i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, norm_mul]
      have hbi : 0 ≤ matrixBound (atom v i) := (matrixBound_pos _).le
      have hnorm := he i
      have ht := KSComplexObjectiveBound.norm_trace_mul_le_card_mul_norm (atom v i) S
      have ht' : ‖Matrix.trace (atom v i * S)‖ ≤
          (Fintype.card (n ⊕ n) : ℝ) * matrixBound (atom v i) * 2 := by
        exact ht.trans (by gcongr)
      have ho := owner_norm_le (hx i) (hh i) hz
      calc _ ≤ 640 * ((Fintype.card (n ⊕ n) : ℝ) * matrixBound (atom v i) * 2) *
          matrixBound (atom v i) := by gcongr
        _ = _ := by ring
    _ ≤ sourceBudget v := by
      rw [← Finset.mul_sum]
      unfold sourceBudget
      linarith

theorem slope_norm_le (v : ι → n → ℂ) (h : ι → ℝ) (hh : ∀ i, |h i| ≤ 2) :
    ‖∑ i, h i • signedLift (KSRankOne.atom (v i))‖ ≤ 2 * slopeBudget v := by
  calc _ ≤ ∑ i, ‖h i • signedLift (KSRankOne.atom (v i))‖ := norm_sum_le _ _
    _ ≤ ∑ i, 2 * matrixBound (signedLift (KSRankOne.atom (v i))) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hh i) (norm_le_matrixBound _
        (signedLift_isHermitian (KSRankOne.atom_isHermitian (v i)))) (norm_nonneg _) (by norm_num)
    _ ≤ 2 * slopeBudget v := by rw [← Finset.mul_sum]; unfold slopeBudget; linarith

theorem center_norm_le (v : ι → n → ℂ) (h : ι → ℝ) (hh : ∀ i, |h i| ≤ 2)
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) {R : ℝ} (hH : ‖H‖ ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖H + z • (∑ i, h i • signedLift (KSRankOne.atom (v i)))‖ ≤ R + 2 * slopeBudget v := by
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  have hb := slope_norm_le v h hh
  have hm := mul_le_mul hz hb (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  linarith

variable {N : ℕ}

/-- Removing frozen owners decreases the input-entry source budget. -/
theorem sourceBudget_restrict (v : Fin N → n → ℂ) (x : Fin N → ℝ) :
    sourceBudget (fun i : KSLiveCurve.Live 1 x => v i) ≤ sourceBudget v := by
  let f := fun i : Fin N => matrixBound (atom v i) ^ 2
  have hs := Fintype.sum_subtype_add_sum_subtype (fun i : Fin N => |x i| < 1) f
  have hn : 0 ≤ ∑ i : {i : Fin N // ¬ |x i| < 1}, f i := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hle : (∑ i : KSLiveCurve.Live 1 x, f i) ≤ ∑ i, f i := by linarith
  unfold sourceBudget
  exact add_le_add_left (mul_le_mul_of_nonneg_left hle (by positivity)) _

/-- The full input also bounds every live center slope. -/
theorem slopeBudget_restrict (v : Fin N → n → ℂ) (x : Fin N → ℝ) :
    slopeBudget (fun i : KSLiveCurve.Live 1 x => v i) ≤ slopeBudget v := by
  let f := fun i : Fin N => matrixBound (signedLift (KSRankOne.atom (v i)))
  have hs := Fintype.sum_subtype_add_sum_subtype (fun i : Fin N => |x i| < 1) f
  have hn : 0 ≤ ∑ i : {i : Fin N // ¬ |x i| < 1}, f i :=
    Finset.sum_nonneg (fun _ _ => (matrixBound_pos _).le)
  have hle : (∑ i : KSLiveCurve.Live 1 x, f i) ≤ ∑ i, f i := by linarith
  unfold slopeBudget
  exact add_le_add_left hle _

end MatrixSpencer.KSComplexPolynomialBounds
