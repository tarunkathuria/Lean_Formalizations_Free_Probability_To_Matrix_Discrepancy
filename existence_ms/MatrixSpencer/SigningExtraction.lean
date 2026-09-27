import MatrixSpencer.SigningPotential
import MatrixSpencer.SquareConclusion

/-! Pointwise extraction of an ordinary full signing from an actual completed
lifted cube point. The conclusion uses the explicit Euclidean spectral norm
and the original number of matrices. No completion or phase oracle occurs. -/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer
namespace SigningExtraction

variable {N D : ℕ}

lemma fullSigning_of_live_card_zero (x : EuclideanSpace ℝ (Fin N))
    (hx : Fintype.card (PhaseRestriction.Live x) = 0) :
    IsFullSigning (WithLp.ofLp x) := full_signs_of_live_card_zero x hx

lemma lifted_center_eq_sum [Nonempty (Fin D)]
    (B : Fin N → CMatrix D) (hB : ∀ i, (B i).IsHermitian)
    (x : EuclideanSpace ℝ (Fin N)) :
    (epochCenter 0 (fun i => signedLift (B i)) (fun i => signedLift_isHermitian (hB i)) x :
      Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ) =
      ∑ i, WithLp.ofLp x i • signedLift (B i) := by
  rw [epochCenter_coe]
  change (0 : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ) +
    (∑ i, WithLp.ofLp x i • signedLift (B i)) = _
  rw [zero_add]

/-- The doubled physical center is exactly the signed lift of the original combination. -/
lemma lifted_center_eq_signedLift [Nonempty (Fin D)]
    (B : Fin N → CMatrix D) (hB : ∀ i, (B i).IsHermitian)
    (x : EuclideanSpace ℝ (Fin N)) :
    (epochCenter 0 (fun i => signedLift (B i)) (fun i => signedLift_isHermitian (hB i)) x :
      Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ) =
      signedLift (signedSum B (WithLp.ofLp x)) := by
  rw [lifted_center_eq_sum B hB x, signedSum_eq_real_sum, signedLift_sum_smul]

/-- A completed lifted point bounds the original signed sum in Euclidean spectral norm. -/
theorem spectralNorm_le_remainingPotential [Nonempty (Fin D)]
    (B : Fin N → CMatrix D) (hB : ∀ i, (B i).IsHermitian)
    (x : EuclideanSpace ℝ (Fin N))
    (hx : Fintype.card (PhaseRestriction.Live x) = 0) :
    spectralNorm (signedSum B (WithLp.ofLp x)) ≤
      PhaseRestriction.remainingPotential 0 (fun i => signedLift (B i))
        (fun i => signedLift_isHermitian (hB i)) x := by
  have hnorm := spectralNorm_signedSum_le_lifted_base B hB (WithLp.ofLp x)
    (fullSigning_of_live_card_zero x hx)
  have hbase := base_le_remainingPotential 0 (fun i => signedLift (B i))
    (fun i => signedLift_isHermitian (hB i)) x
  rw [lifted_center_eq_sum B hB x] at hbase
  exact hnorm.trans hbase

/-- Pointwise conclusion for an actual completed point; the constant and count are unchanged. -/
theorem extract_signing_of_remainingPotential_le (hD : 0 < D)
    (B : Fin N → CMatrix D) (hB : ∀ i, (B i).IsHermitian)
    (x : EuclideanSpace ℝ (Fin N))
    (hx : Fintype.card (PhaseRestriction.Live x) = 0) {C : ℝ}
    (hpotential : PhaseRestriction.remainingPotential 0 (fun i => signedLift (B i))
      (fun i => signedLift_isHermitian (hB i)) x ≤ C * Real.sqrt (N : ℝ)) :
    ∃ ε : Fin N → ℝ, IsFullSigning ε ∧
      spectralNorm (signedSum B ε) ≤ C * Real.sqrt (N : ℝ) := by
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  exact ⟨WithLp.ofLp x, fullSigning_of_live_card_zero x hx,
    (spectralNorm_le_remainingPotential B hB x hx).trans hpotential⟩

end SigningExtraction
end MatrixSpencer
