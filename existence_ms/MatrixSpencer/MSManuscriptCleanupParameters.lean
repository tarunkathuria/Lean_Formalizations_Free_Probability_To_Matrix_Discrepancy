import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Arithmetic residual and per-entry debit for the real Jacobi/Schur cleanup. -/
noncomputable section
namespace MatrixSpencer.MSManuscriptCleanupParameters

def tolerance (d : ℕ) (δ : ℝ) : ℝ := δ/(16*((d:ℝ)+1))
def entryLoss (d : ℕ) (δ : ℝ) : ℝ := 8*(tolerance d δ)^2/δ

theorem tolerance_pos (d : ℕ) {δ : ℝ} (hδ : 0 < δ) : 0 < tolerance d δ := by
  unfold tolerance; positivity

theorem tolerance_identity (d : ℕ) (δ : ℝ) : 16*((d:ℝ)+1)*tolerance d δ = δ := by
  unfold tolerance
  have h : (16:ℝ)*((d:ℝ)+1) ≠ 0 := by positivity
  field_simp

theorem entryLoss_eq (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    entryLoss d δ = tolerance d δ/(2*((d:ℝ)+1)) := by
  unfold entryLoss tolerance
  field_simp
  ring

theorem entryLoss_nonneg (d : ℕ) {δ : ℝ} (hδ : 0 < δ) : 0 ≤ entryLoss d δ := by
  rw [entryLoss_eq d hδ]
  exact div_nonneg (tolerance_pos d hδ).le (by positivity)

theorem total_entryLoss_le (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (d:ℝ)*entryLoss d δ ≤ tolerance d δ/2 := by
  rw [entryLoss_eq d hδ]
  have ht := (tolerance_pos d hδ).le
  have hd : (0:ℝ) < 2*((d:ℝ)+1) := by positivity
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  have he : ((d:ℝ)*(tolerance d δ/(2*((d:ℝ)+1))))*2 =
      ((d:ℝ)*tolerance d δ)/((d:ℝ)+1) := by field_simp
  rw [he]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

theorem tolerance_le (d : ℕ) {δ : ℝ} (hδ : 0 < δ) : tolerance d δ ≤ δ/16 := by
  have he := tolerance_identity d δ
  have ht := (tolerance_pos d hδ).le
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

theorem row_bound (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    2*(d:ℝ)*tolerance d δ+(d:ℝ)*entryLoss d δ ≤ δ := by
  have he := tolerance_identity d δ
  have ht := tolerance_pos d hδ
  have hl := total_entryLoss_le d hδ
  nlinarith

theorem pivot_loss_le (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (d:ℝ)*entryLoss d δ ≤ δ/2 := by
  have he := tolerance_le d hδ
  have hl := total_entryLoss_le d hδ
  linarith

end MatrixSpencer.MSManuscriptCleanupParameters
