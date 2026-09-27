import FaithfulMS.RectangularDirectOriginal

/-! Pure existence through the actual direct-primal-density walk.
The only hypotheses are the original dimensions, Hermitian input matrices,
and contraction bounds. SDP solutions are selected mathematically from proved
attainment; no solver, work bound, or favorable-walk premise is assumed. -/
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectExistence
open RectangularDirectOriginal
variable {N D : ℕ}

private theorem positive_exists_signing (hN : 1 ≤ N) (hND : N ≤ D)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) :
    ∃ ε : Fin N → ℝ, IsFullSigning ε ∧ spectralNorm (signedSum A ε) ≤ discrepancyBound N D := by
  classical
  let P := output hN hND FaithfulMS.DirectSDP.exactService A hA hAn 1
  have hp := output_probability hN hND FaithfulMS.DirectSDP.exactService A hA hAn 1
  have hx : ∃ z, (P.value z).isSome = true := by
    by_contra hn
    have hz : ∀ z, (P.value z).isSome = false := by simpa using hn
    change 1 - (1 / 2 : ℝ) ^ 1 ≤ ∑ z, P.weight z * (if (P.value z).isSome then 1 else 0) at hp
    simp only [hz, Bool.false_eq_true, ↓reduceIte, mul_zero, Finset.sum_const_zero] at hp
    norm_num at hp
  obtain ⟨z, hz⟩ := hx
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hz
  exact ⟨WithLp.ofLp y.val, output_sound hN hND FaithfulMS.DirectSDP.exactService
    A hA hAn 1 z y hy⟩

theorem exists_signing (hND : N ≤ D)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) :
    ∃ ε : Fin N → ℝ, IsFullSigning ε ∧ spectralNorm (signedSum A ε) ≤ discrepancyBound N D := by
  by_cases hN : N = 0
  · subst N
    refine ⟨fun _ => 1, isFullSigning_one 0, ?_⟩
    simp [signedSum, discrepancyBound]
  · exact positive_exists_signing (by omega) hND A hA hAn

#print axioms exists_signing
end MatrixSpencer.RectangularDirectExistence
