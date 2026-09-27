import MatrixSpencer.Statement
import MatrixSpencer.SignedLift
import MatrixSpencer.OwnerBounds

/-!
# Extracting the exact square-regime signing statement

These elementary bridges preserve the explicit Euclidean operator norm,
the original number of matrices, and the full real signing. The last theorem
is conditional on an explicitly stated potential-completion result; it is
not the Matrix Spencer theorem until that premise has been proved.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer

variable {N D : ℕ}
local instance squareConclusionCStar : CStarAlgebra (CMatrix D) := {}

theorem signedSum_eq_real_sum (B : Fin N → CMatrix D) (x : Fin N → ℝ) :
    signedSum B x = ∑ i, x i • B i := by
  unfold signedSum
  apply Finset.sum_congr rfl
  intro i _
  ext a b
  simp only [Matrix.smul_apply]
  rfl

/-- The doubled physical matrix controls the original Euclidean norm. -/
theorem spectralNorm_signedSum_le_lifted_base [Nonempty (Fin D)]
    (B : Fin N → CMatrix D) (hB : ∀ i, (B i).IsHermitian)
    (x : Fin N → ℝ) (hx : IsFullSigning x) :
    spectralNorm (signedSum B x) ≤
      baseDensityPotential (∑ i, x i • signedLift (B i)) 1 := by
  rw [spectralNorm_eq_scopedMatrixNorm]
  have h := norm_le_signedLift_densityPotential
    (signedSum_isHermitian_of_fullSigning B x hB hx)
    (fun _ : Empty => (0 : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ))
    (by norm_num : (0 : ℝ) ≤ 1)
  rw [signedSum_eq_real_sum, signedLift_sum_smul] at h
  exact h

/-- The initial doubled potential has the original square-root label budget. -/
theorem lifted_initial_potential_le_five [Nonempty (Fin D)]
    (B : Fin N → CMatrix D) (hB : ∀ i, (B i).IsHermitian)
    (hN : ∀ i, spectralNorm (B i) ≤ 1) (hDN : D ≤ N) :
    ownerPotential 0 (fun i => signedLift (B i)) 1 1 ≤ 5 * Real.sqrt (N : ℝ) := by
  have hnorm : ∀ i, ‖signedLift (B i)‖ ≤ 1 := by
    intro i
    rw [signedLift_norm (hB i)]
    exact hN i
  have hcard : Fintype.card (Fin D ⊕ Fin D) ≤ 2 * Fintype.card (Fin N) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  simpa only [Fintype.card_fin] using ownerPotential_initial_le_five
    (fun i => signedLift (B i)) (fun i => signedLift_isHermitian (hB i)) hnorm hcard

/-- A fully quantified potential-completion theorem suffices for the frozen
target, with dimension zero handled separately and a universal constant. -/
theorem squareStatement_of_lifted_potential_completion {K : ℝ} (hK : 0 ≤ K)
    (hcomplete : ∀ (N D : ℕ), D ≤ N → 0 < D →
      ∀ (B : Fin N → CMatrix D), (∀ i, (B i).IsHermitian) →
        (∀ i, spectralNorm (B i) ≤ 1) →
        ∃ x : Fin N → ℝ, IsFullSigning x ∧
          baseDensityPotential (∑ i, x i • signedLift (B i)) 1 ≤
            ownerPotential 0 (fun i => signedLift (B i)) 1 1 + K * Real.sqrt (N : ℝ)) :
    squareStatement := by
  refine ⟨K + 5, by linarith, ?_⟩
  intro N D hDN B hB hN
  by_cases hD : D = 0
  · subst D
    obtain ⟨x, hx, hn⟩ := zeroDimension_signing B
    exact ⟨x, hx, by rw [hn]; positivity⟩
  · have hDpos : 0 < D := Nat.pos_of_ne_zero hD
    letI : NeZero D := ⟨hD⟩
    obtain ⟨x, hx, hb⟩ := hcomplete N D hDN hDpos B hB hN
    have hn := spectralNorm_signedSum_le_lifted_base B hB x hx
    have hi := lifted_initial_potential_le_five B hB hN hDN
    refine ⟨x, hx, ?_⟩
    nlinarith

end MatrixSpencer
