import MatrixSpencer.RectangularRidgeAffineSDP
import MatrixSpencer.RectangularRidgePrimitiveParameters

/-! The actual comparison-tuned rectangular ridge potential is the attained
maximum of an affine real SDP with polynomially bounded coefficient arrays.
This is a value-oracle representation theorem, not a total walk runtime
theorem. Both the tuning and the objective are the new numerical variant. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgePrimitiveSDP
open DyadicSDPCoordinates RectangularRidgeTuning

theorem exists_maximizer {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D)
    (a : Fin D) (H : Matrix (Fin D) (Fin D) ℂ)
    (A : Fin N → Matrix (Fin D) (Fin D) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.PosSemidef) :
    let m := depth N D hN
    let θ := RectangularRidgePrimitiveParameters.weight N D hN
    ∃ x : Space m a, x ∈ DyadicOwnerSDP.feasible m a A hA C hC ∧
      RectangularRidgeAffineSDP.objective m (depth_positive N D hN) a H θ (1/(D : ℝ)) x =
        RectangularRidgePotential.potential H (covarianceKraus A C) m θ (1/(D : ℝ)) ∧
      ∀ y ∈ DyadicOwnerSDP.feasible m a A hA C hC,
        RectangularRidgeAffineSDP.objective m (depth_positive N D hN) a H θ (1/(D : ℝ)) y ≤
          RectangularRidgeAffineSDP.objective m (depth_positive N D hN) a H θ (1/(D : ℝ)) x :=
  RectangularRidgeAffineSDP.exists_maximizer _ (depth_positive N D hN) a H A hA C hC
    (RectangularRidgePrimitiveParameters.weight_positive hN hND) (by positivity)

/-- Counts of the actual variable and constraint types, with a fixed-degree
polynomial bound on every dense real affine-LMI coefficient entry. -/
theorem actual_size_bounds {N D : ℕ} (hN : 1 ≤ N) (a : Fin D) :
    let m := depth N D hN
    dimension m a ≤ (D+4)*D^2 ∧
    Fintype.card (DyadicSDPAffineData.Constraint m) ≤ 2*D+3 ∧
    DyadicSDPAffineData.matrixSize (Fin D) = 4*D ∧
    Fintype.card (DyadicSDPAffineData.Constraint m) * (dimension m a+1) *
      (DyadicSDPAffineData.matrixSize (Fin D))^2 ≤ 16*(2*D+3)*(D+4)*D^4 := by
  dsimp only
  have hh := DyadicOwnerSDP.actual_size_bounds (depth N D hN) a
  simp only [Fintype.card_fin, DyadicSDPProgramSize.variableCount,
    DyadicSDPProgramSize.constraintCount, DyadicSDPProgramSize.blockOrder] at hh
  have hd := depth_le N D hN
  refine ⟨?_, ?_, hh.2.2.1, ?_⟩
  · rw [hh.1]
    exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_right _ (by omega))
  · rw [hh.2.1]
    omega
  · rw [hh.2.2.2]
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_left _ (by omega)
    · omega

end MatrixSpencer.RectangularRidgePrimitiveSDP
