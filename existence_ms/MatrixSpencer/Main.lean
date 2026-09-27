import MatrixSpencer.FullSigningIteration
import MatrixSpencer.SigningExtraction

/-!
# The square-regime Matrix Spencer theorem

The actual p=2/Tsallis-one-half epoch and phase construction proves the full
signing theorem for complex Hermitian Euclidean contractions. The constant
is universal and is chosen before both sizes and the input family.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer

/-- An explicit universal constant from the fully formalized p=2 construction. -/
def matrixSpencerSquareConstant : ℝ := 4 * squarePhaseCost + 5

theorem matrixSpencerSquareConstant_eq : matrixSpencerSquareConstant = 4345437 := by
  norm_num [matrixSpencerSquareConstant, squarePhaseCost]

theorem matrixSpencerSquareConstant_pos : 0 < matrixSpencerSquareConstant := by
  rw [matrixSpencerSquareConstant_eq]
  norm_num

/-- Every family of n Hermitian d-by-d contractions with d≤n has a full
real signing of Euclidean operator norm at most C sqrt(n). -/
theorem matrix_spencer_square_with_constant : squareStatementWithConstant matrixSpencerSquareConstant := by
  intro N D hDN B hB hN
  by_cases hD : D = 0
  · subst D
    obtain ⟨ε, hε, hnorm⟩ := zeroDimension_signing B
    exact ⟨ε, hε, by rw [hnorm]; exact mul_nonneg matrixSpencerSquareConstant_pos.le (Real.sqrt_nonneg _)⟩
  · have hDpos : 0 < D := Nat.pos_of_ne_zero hD
    letI : NeZero D := ⟨hD⟩
    have hnorm : ∀ i, ‖signedLift (B i)‖ ≤ 1 := by
      intro i
      rw [signedLift_norm (hB i)]
      exact hN i
    have hcard : Fintype.card (Fin D ⊕ Fin D) ≤ 2 * Fintype.card (Fin N) := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    obtain ⟨x, hx, hpotential⟩ := exists_actual_bounded_full_coloring
      (fun i => signedLift (B i)) (fun i => signedLift_isHermitian (hB i)) hnorm hcard
    exact SigningExtraction.extract_signing_of_remainingPotential_le hDpos B hB x hx
      (by simpa only [Fintype.card_fin, matrixSpencerSquareConstant] using hpotential)

/-- The exact universally quantified square-regime target, with no analytic,
epoch, phase, or completion premise. -/
theorem matrix_spencer_square : squareStatement :=
  ⟨matrixSpencerSquareConstant, matrixSpencerSquareConstant_pos, matrix_spencer_square_with_constant⟩

end MatrixSpencer
