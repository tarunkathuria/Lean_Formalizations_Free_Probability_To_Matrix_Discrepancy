import MatrixSpencer.KSFullManuscriptValueOracle

/-!
# Polynomial size of the concrete SDP reduction

For physical complex dimension `d`, the actual affine pencil has `4d²-1`
real variables and a single real PSD constraint of order `10d`. A bisection
feasibility query adds one affine objective halfspace. The complete dense
pencil data (constant and one coefficient matrix per variable) has exactly
`400d⁴` real entries, excluding the objective vector and scalar threshold.
These are sizes of the actual pencil used by the verified report. Polynomial solver contracts are explicit structure parameters, not added axioms.
-/

open Matrix
noncomputable section
namespace MatrixSpencer.KSFullManuscriptProgramSize

open KSFullManuscriptAffineData KSFullManuscriptAffineObjective
open KSFullManuscriptSDPBlockPencil
variable {d : ℕ}

theorem variableCount (a : Fin d) : dimension a = 4 * d ^ 2 - 1 := by
  simpa only [Fintype.card_fin] using dimension_eq a

theorem pencilOrder : matrixSize (Fin d) = 10 * d := by
  simp only [matrixSize, RealIndex, ComplexIndex, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Exact dense storage count of the actual affine matrix coefficients. -/
theorem pencilEntries (a : Fin d) :
    (dimension a + 1) * matrixSize (Fin d) ^ 2 = 400 * d ^ 4 := by
  have hd : 1 ≤ d := by have ha := a.isLt; omega
  have hs : 1 ≤ 4 * d ^ 2 := by have hp : 1 ≤ d ^ 2 := one_le_pow₀ hd; omega
  rw [variableCount, pencilOrder, Nat.sub_add_cancel hs]
  ring

/-- The number of real affine objective coefficients, including its offset. -/
theorem objectiveEntries (a : Fin d) : dimension a + 1 = 4 * d ^ 2 := by
  have hd : 1 ≤ d := by have ha := a.isLt; omega
  have hs : 1 ≤ 4 * d ^ 2 := by have hp : 1 ≤ d ^ 2 := one_le_pow₀ hd; omega
  rw [variableCount, Nat.sub_add_cancel hs]

/-- The full-cube sign lift doubles the physical complex dimension. -/
theorem doubledVariableCount (a : Fin (d + d)) : dimension a = 16 * d ^ 2 - 1 := by
  rw [variableCount]
  congr 1
  ring

theorem doubledPencilOrder : matrixSize (Fin (d + d)) = 20 * d := by
  rw [pencilOrder]
  ring

theorem doubledPencilEntries (a : Fin (d + d)) :
    (dimension a + 1) * matrixSize (Fin (d + d)) ^ 2 = 6400 * d ^ 4 := by
  rw [pencilEntries]
  ring

theorem spinLabelCount (N : ℕ) : Fintype.card (Fin N × Fin 4) = 4 * N := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  omega

end MatrixSpencer.KSFullManuscriptProgramSize
