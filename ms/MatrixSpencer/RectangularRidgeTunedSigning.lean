import MatrixSpencer.RectangularRidgeFullAssembly
import MatrixSpencer.RectangularRidgeSigningBudget

/-!
# Tuned initial and terminal spectral bounds

The exact fixed mixed regularizer is tuned at the original matrix count and
the signed physical dimension. A supplied completed accounting inequality
is converted to the ordinary two-sided discrepancy bound, with all constants
visible. No completion premise is hidden in the definitions.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeTunedSigning
open RectangularRidgeRemainingPotential RectangularRidgePrimitiveParameters
open RectangularRidgeUniformResponse RectangularRidgeTuning RectangularRidgeSigningBudget
variable {N D : ℕ}

theorem initial_lifted_le (hN : 1 ≤ N) (hND : N ≤ 2 * D) [Nonempty (Fin D)]
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian) (hAn : ∀ i, spectralNorm (A i) ≤ 1) :
    potential (depth N (2 * D) hN) (weight N (2 * D) hN) (1 / (2 * (D : ℝ))) 0
      (fun i => signedLift (A i)) (fun i => signedLift_isHermitian (hA i))
        (0 : EuclideanSpace ℝ (Fin N)) ≤ initialBudget N (2 * D) hN := by
  have hnorm : ∀ i, ‖signedLift (A i)‖ ≤ 1 := by
    intro i
    rw [signedLift_norm (hA i), ← spectralNorm_eq_scopedMatrixNorm]
    exact hAn i
  have hh := initial_le (depth_positive N (2 * D) hN) (weight_positive hN hND).le
    (show 0 ≤ (1 / (2 * (D : ℝ))) by positivity)
    (fun i => signedLift (A i)) (fun i => signedLift_isHermitian (hA i)) hnorm
  simpa only [initialBudget, exponent, order, Fintype.card_sum, Fintype.card_fin,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, two_mul] using hh

/-- Actual completed full-universe ledgers give the standard rectangular
spectral order, including the doubled physical dimension inside the log. -/
theorem completed_spectral_bound (hN : 1 ≤ N) (hND : N ≤ 2 * D) [Nonempty (Fin D)]
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian) (hAn : ∀ i, spectralNorm (A i) ≤ 1)
    (x : EuclideanSpace ℝ (Fin N)) (hx : liveCount x = 0) {K : ℝ} (hK : 0 ≤ K)
    (haccount : potential (depth N (2 * D) hN) (weight N (2 * D) hN) (1 / (2 * (D : ℝ)))
        0 (fun i => signedLift (A i)) (fun i => signedLift_isHermitian (hA i)) x ≤
      potential (depth N (2 * D) hN) (weight N (2 * D) hN) (1 / (2 * (D : ℝ)))
        0 (fun i => signedLift (A i)) (fun i => signedLift_isHermitian (hA i)) 0 +
          4 * (152 * K * (coefficient N (2 * D) hN + 1) + 64) * Real.sqrt (N : ℝ)) :
    IsFullSigning (WithLp.ofLp x) ∧ spectralNorm (signedSum A (WithLp.ofLp x)) ≤
      (84 + 1944 * (152 * K + 64)) *
        Real.sqrt ((N : ℝ) * (1 + Real.log ((2 * (D : ℝ)) / N))) := by
  have hs := SigningExtraction.fullSigning_of_live_card_zero x ((liveCount_eq x).symm.trans hx)
  have hl := spectralNorm_le (depth_positive N (2 * D) hN) (weight_positive hN hND).le
    (show 0 ≤ (1 / (2 * (D : ℝ))) by positivity) A hA x hx
  have hi := initial_lifted_le hN hND A hA hAn
  have hb := totalBudget_le hN hND hK
  simp only [scale, Nat.cast_mul, Nat.cast_ofNat] at hb
  exact ⟨hs, hl.trans (haccount.trans ((add_le_add_right hi _).trans hb))⟩

end MatrixSpencer.RectangularRidgeTunedSigning
