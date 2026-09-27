import MatrixSpencer.Statement
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The independently audited target for the separate rectangular goal.
All norms remain explicitly Euclidean operator norms, and n counts matrices. -/

open scoped BigOperators Matrix
namespace MatrixSpencer

/-- The natural aspect-ratio logarithm, regularized at d=n by log 2. -/
noncomputable def rectangularLog (n d : ℕ) : ℝ := Real.log (2 * (d : ℝ) / (n : ℝ))

/-- The sharp rectangular assertion with a prescribed universal constant. -/
def rectangularStatementWithConstant (C : ℝ) : Prop :=
  ∀ (n d : ℕ), 1 ≤ n → n ≤ d →
    ∀ (B : Fin n → CMatrix d),
      (∀ i, (B i).IsHermitian) →
      (∀ i, spectralNorm (B i) ≤ 1) →
      ∃ ε : Fin n → ℝ, IsFullSigning ε ∧
        spectralNorm (signedSum B ε) ≤ C * Real.sqrt ((n : ℝ) * rectangularLog n d)

/-- One positive constant is chosen before both dimensions and the input family. -/
def rectangularStatement : Prop := ∃ C : ℝ, 0 < C ∧ rectangularStatementWithConstant C

theorem rectangular_ratio_ge_two {n d : ℕ} (hn : 1 ≤ n) (hd : n ≤ d) :
    (2 : ℝ) ≤ 2 * (d : ℝ) / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply (le_div_iff₀ hnpos).mpr
  have hnd : (n : ℝ) ≤ d := by exact_mod_cast hd
  linarith

theorem log_two_le_rectangularLog {n d : ℕ} (hn : 1 ≤ n) (hd : n ≤ d) :
    Real.log 2 ≤ rectangularLog n d :=
  Real.log_le_log (by norm_num : (0 : ℝ) < 2) (rectangular_ratio_ge_two hn hd)

theorem rectangularLog_pos {n d : ℕ} (hn : 1 ≤ n) (hd : n ≤ d) :
    0 < rectangularLog n d :=
  (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le (log_two_le_rectangularLog hn hd)

theorem rectangularLog_diagonal {n : ℕ} (hn : 1 ≤ n) : rectangularLog n n = Real.log 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold rectangularLog
  congr 1
  field_simp

end MatrixSpencer
