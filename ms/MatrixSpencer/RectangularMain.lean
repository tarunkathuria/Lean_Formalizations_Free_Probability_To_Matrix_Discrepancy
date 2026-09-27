import MatrixSpencer.DyadicFullSigningIteration
import MatrixSpencer.DyadicGlobalEpochInputs
import MatrixSpencer.RectangularTunedParameters
import MatrixSpencer.RectangularStatement

/-!
# The sharp rectangular Matrix Spencer theorem

The actual dyadic Tsallis construction supplies the finite epochs and phases.
The exponent, regularizer weight, and response coefficient are chosen once
from the original matrix count and doubled physical dimension.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section

/-- One explicit constant, independent of both sizes and the input family. -/
def matrixSpencerRectangularConstant : ℝ := 162 * (6 * (304 * 23) + 2)

theorem matrixSpencerRectangularConstant_eq : matrixSpencerRectangularConstant = 6796548 := by
  norm_num [matrixSpencerRectangularConstant]

theorem matrixSpencerRectangularConstant_pos : 0 < matrixSpencerRectangularConstant := by
  norm_num [matrixSpencerRectangularConstant]

/-- Every n Hermitian d-by-d Euclidean contractions, 1≤n≤d, have a full
real signing at the sharp square-root logarithmic scale. -/
theorem matrix_spencer_rectangular_with_constant :
    rectangularStatementWithConstant matrixSpencerRectangularConstant := by
  classical
  intro N D hNpos hND A hA hnorm
  have hDpos : 0 < D := by omega
  letI : NeZero D := ⟨Nat.ne_of_gt hDpos⟩
  let m := RectangularTunedParameters.depth N D
  let θ := RectangularTunedParameters.weight N D
  let β := RectangularTunedParameters.coefficient N D
  have hm : 1 ≤ m := RectangularTunedParameters.depth_positive N D
  have hθ : 0 < θ := RectangularTunedParameters.weight_positive hNpos hND
  have hβ : 2 ≤ β := RectangularTunedParameters.coefficient_two_le hNpos hND
  have hinputs : DyadicPhasePotential.HasEpochInputs (Fin D ⊕ Fin D) m θ β N :=
    hasEpochInputs_globalCoefficient (Fin D ⊕ Fin D) m θ N
  have hliftNorm : ∀ i, ‖signedLift (A i)‖ ≤ 1 := by
    intro i
    rw [signedLift_norm (hA i), ← spectralNorm_eq_scopedMatrixNorm]
    exact hnorm i
  obtain ⟨x, hx, hpotential⟩ := DyadicFullSigningIteration.exists_bounded_full_coloring
    m hm θ hθ β hβ N hinputs (fun i => signedLift (A i))
    (fun i => signedLift_isHermitian (hA i)) hliftNorm (by simp)
  have hpotential' : rectangularRemainingPotential m θ 0 (fun i => signedLift (A i))
      (fun i => signedLift_isHermitian (hA i)) x ≤
      2 * Real.sqrt (N : ℝ) +
        θ * (2 * (D : ℝ)) ^ (1 / (2 : ℝ) ^ m) / (1 - 1 / (2 : ℝ) ^ m) +
        (304 * 23) * (β + 1) * Real.sqrt (N : ℝ) := by
    simpa only [Fintype.card_fin, Fintype.card_sum, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat, ← two_mul] using hpotential
  have hledger := RectangularTunedParameters.ledger_le hNpos hND
    (K := (304 * 23 : ℝ)) (by norm_num)
  have hbound : rectangularRemainingPotential m θ 0 (fun i => signedLift (A i))
      (fun i => signedLift_isHermitian (hA i)) x ≤
      matrixSpencerRectangularConstant * Real.sqrt ((N : ℝ) * rectangularLog N D) :=
    hpotential'.trans (by
      simpa only [m, θ, β, RectangularTunedParameters.exponent,
        matrixSpencerRectangularConstant, rectangularLog] using hledger)
  exact extract_signing_of_rectangularRemainingPotential_le hDpos hm hθ.le A hA x hx hbound

/-- The exact target, with all analytic, preparation, epoch and phase inputs discharged. -/
theorem matrix_spencer_rectangular : rectangularStatement :=
  ⟨matrixSpencerRectangularConstant, matrixSpencerRectangularConstant_pos,
    matrix_spencer_rectangular_with_constant⟩

end
end MatrixSpencer
