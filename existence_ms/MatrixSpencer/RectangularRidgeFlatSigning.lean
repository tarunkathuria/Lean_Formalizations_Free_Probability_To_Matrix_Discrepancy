import MatrixSpencer.RectangularRidgeTunedSigning
import MatrixSpencer.MSManuscriptMatrixReindex

/-! The finite-index signed lift used by the actual rectangular algorithm.
The original two-sided operator norm is recovered by reindexing a witnessing
density. No change of regularizer or comparison of different optimizers is
needed. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeFlatSigning
open RectangularRidgeRemainingPotential RectangularRidgePrimitiveParameters
open RectangularRidgeUniformResponse RectangularRidgeTuning RectangularRidgeSigningBudget
variable {N D : ℕ}

def flat (A : Fin N → CMatrix D) (i : Fin N) : CMatrix (D + D) :=
  (signedLift (A i)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem flat_hermitian (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian) :
    ∀ i, (flat A i).IsHermitian :=
  fun i => (signedLift_isHermitian (hA i)).submatrix _

theorem flat_contraction [Nonempty (Fin D)] (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) : ∀ i, ‖flat A i‖ ≤ 1 := by
  intro i
  rw [flat, MSManuscriptMatrixReindex.norm_reindex, signedLift_norm (hA i),
    ← spectralNorm_eq_scopedMatrixNorm]
  exact hAn i

theorem flat_center [Nonempty (Fin D)] (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ (Fin N)) :
    (epochCenter 0 (flat A) (flat_hermitian A hA) x : CMatrix (D + D)) =
      (signedLift (signedSum A (WithLp.ofLp x))).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  have hh := MSManuscriptMatrixReindex.epochCenter_reindex finSumFinEquiv.symm
    (0 : selfAdjoint (Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ))
    (fun i => signedLift (A i)) (fun i => signedLift_isHermitian (hA i)) x
  rw [SigningExtraction.lifted_center_eq_signedLift A hA x] at hh
  simpa only [MSManuscriptMatrixReindex.selfAdjointReindex, ZeroMemClass.coe_zero,
    Matrix.submatrix_zero, flat, flat_hermitian] using hh

theorem norm_le_flat_base [Nonempty (Fin D)] [Nonempty (Fin (D + D))]
    {B : CMatrix D} (hB : B.IsHermitian) {m : ℕ} (hm : 1 ≤ m)
    {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) :
    ‖B‖ ≤ RectangularRidgeOwnerBounds.basePotential m
      ((signedLift B).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) θ κ := by
  obtain ⟨S, hS, hval⟩ := exists_signedLift_density_norm hB
  have hh := RectangularRidgeOwnerBounds.trace_le_base m hm
    ((signedLift B).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) hθ hκ
    (KSOwnerReindex.density_reindex S finSumFinEquiv.symm hS)
  simpa only [Matrix.submatrix_mul_equiv, KSOwnerReindex.realTrace_reindex, hval] using hh

theorem spectralNorm_le [Nonempty (Fin D)] [Nonempty (Fin (D + D))]
    {m : ℕ} (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ (Fin N)) (hx : liveCount x = 0) :
    spectralNorm (signedSum A (WithLp.ofLp x)) ≤
      potential m θ κ 0 (flat A) (flat_hermitian A hA) x := by
  have hs := SigningExtraction.fullSigning_of_live_card_zero x ((liveCount_eq x).symm.trans hx)
  rw [spectralNorm_eq_scopedMatrixNorm]
  have hn := norm_le_flat_base (signedSum_isHermitian_of_fullSigning A _ hA hs) hm hθ hκ
  have hb := base_le m θ κ 0 (flat A) (flat_hermitian A hA) x
  rw [flat_center A hA x] at hb
  exact hn.trans hb

theorem initial_flat_le [Nonempty (Fin D)] [Nonempty (Fin (D + D))]
    (hN : 1 ≤ N) (hND : N ≤ D + D) (A : Fin N → CMatrix D)
    (hA : ∀ i, (A i).IsHermitian) (hAn : ∀ i, spectralNorm (A i) ≤ 1) :
    potential (depth N (D + D) hN) (weight N (D + D) hN) (1 / ((D + D : ℕ) : ℝ)) 0
      (flat A) (flat_hermitian A hA) 0 ≤ initialBudget N (D + D) hN := by
  have hh := initial_le (depth_positive N (D + D) hN) (weight_positive hN hND).le
    (show 0 ≤ (1 / ((D + D : ℕ) : ℝ)) by positivity)
    (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn)
  simpa only [initialBudget, exponent, order, Fintype.card_fin, Nat.cast_pow] using hh

theorem completed_spectral_bound [Nonempty (Fin D)] [Nonempty (Fin (D + D))]
    (hN : 1 ≤ N) (hND : N ≤ D + D) (A : Fin N → CMatrix D)
    (hA : ∀ i, (A i).IsHermitian) (hAn : ∀ i, spectralNorm (A i) ≤ 1)
    (x : EuclideanSpace ℝ (Fin N)) (hx : liveCount x = 0) {K : ℝ} (hK : 0 ≤ K)
    (haccount : potential (depth N (D + D) hN) (weight N (D + D) hN)
        (1 / ((D + D : ℕ) : ℝ)) 0 (flat A) (flat_hermitian A hA) x ≤
      potential (depth N (D + D) hN) (weight N (D + D) hN)
        (1 / ((D + D : ℕ) : ℝ)) 0 (flat A) (flat_hermitian A hA) 0 +
          4 * (152 * K * (coefficient N (D + D) hN + 1) + 64) * Real.sqrt (N : ℝ)) :
    IsFullSigning (WithLp.ofLp x) ∧ spectralNorm (signedSum A (WithLp.ofLp x)) ≤
      (84 + 1944 * (152 * K + 64)) *
        Real.sqrt ((N : ℝ) * (1 + Real.log ((2 * (D : ℝ)) / N))) := by
  have hs := SigningExtraction.fullSigning_of_live_card_zero x ((liveCount_eq x).symm.trans hx)
  have hl := spectralNorm_le (depth_positive N (D + D) hN) (weight_positive hN hND).le
    (show 0 ≤ (1 / ((D + D : ℕ) : ℝ)) by positivity) A hA x hx
  have hi := initial_flat_le hN hND A hA hAn
  have hb := totalBudget_le hN hND hK
  simp only [scale, Nat.cast_add] at hb
  rw [show (D : ℝ) + D = 2 * D by ring] at hb
  exact ⟨hs, hl.trans (haccount.trans ((add_le_add_right hi _).trans hb))⟩

end MatrixSpencer.RectangularRidgeFlatSigning
