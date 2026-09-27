import MatrixSpencer.RectangularRidgeOriginalAlgorithm
import MatrixSpencer.RectangularRidgePolynomialMajorant

/-! Final rectangular Matrix Spencer statements for the actual finite walk.
For a fixed polynomial affine-SDP solver the work polynomial is chosen before
the dimensions, matrices and confidence exponent. Full signing, original
spectral norm, success probability and all-branch runtime refer to the same
sampler and counted implementation. The unconditional existence corollary
does not require a polynomial solver. -/
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeEndToEnd
open RectangularRidgeOriginalAlgorithm
open RectangularRidgePhaseAssembly (Point)
open RectangularRidgeEpochInput (margin)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private theorem doubled_bounded {f : ℕ → ℕ → ℕ → ℕ} (hf : NatPolynomialBound.Bounded f) :
    NatPolynomialBound.Bounded (fun N D k => f N (D + D) k) := by
  obtain ⟨C, e, hf⟩ := hf
  refine ⟨C * 2 ^ e, e, ?_⟩
  intro N D k
  have hh := Nat.pow_le_pow_left (show N + (D + D) + k + 2 ≤ 2 * (N + D + k + 2) by omega) e
  have hm := Nat.mul_le_mul_left C hh
  rw [mul_pow, ← mul_assoc] at hm
  exact (hf N (D + D) k).trans hm

theorem budget_polynomial (S : RectangularRidgeConvexValue.PolynomialSolver) :
    NatPolynomialBound.Bounded (budget S) := by
  have hmain := doubled_bounded (RectangularRidgePolynomialMajorant.budget_bounded S)
  change NatPolynomialBound.Bounded (fun N D k =>
    RectangularRidgePolynomialRuntime.budget S N (D + D) k + 1000 * (N + D + 1) ^ 3 + 5)
  apply NatPolynomialBound.add
  · apply NatPolynomialBound.add hmain
    apply NatPolynomialBound.mul (NatPolynomialBound.constant 1000)
    apply NatPolynomialBound.pow
    exact NatPolynomialBound.add (NatPolynomialBound.add NatPolynomialBound.first
      NatPolynomialBound.second) (NatPolynomialBound.constant 1)
  · exact NatPolynomialBound.constant 5

theorem exists_uniform_budget (S : RectangularRidgeConvexValue.PolynomialSolver) :
    ∃ C e : ℕ, 0 < C ∧ ∀ N D k : ℕ,
      budget S N D k ≤ C * (N + D + k + 2) ^ e ∧
      RectangularRidgePolynomialRuntime.randomDraws N (D + D) k ≤ C * (N + D + k + 2) ^ e := by
  obtain ⟨C, e, hh⟩ := NatPolynomialBound.add (budget_polynomial S)
    (doubled_bounded RectangularRidgePolynomialMajorant.randomDraws_bounded)
  refine ⟨C + 1, e, by omega, ?_⟩
  intro N D k
  have hp := hh N D k
  dsimp only at hp
  have hm := Nat.mul_le_mul_right ((N + D + k + 2) ^ e) (show C ≤ C + 1 by omega)
  constructor <;> omega

/-- Complete finite-walk correctness, confidence and polynomial execution.
The sole computational assumption is the displayed polynomial SDP solver. -/
theorem polynomial_algorithm (S : RectangularRidgeConvexValue.PolynomialSolver) :
    ∃ C e : ℕ, 0 < C ∧ ∀ (N D : ℕ) (hN : 1 ≤ N) (hND : N ≤ D)
      (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
      (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ),
      (∀ (z : (output hN hND S.solver A hA hAn k).Draws) (y : Point (N := N) (margin N)),
        (output hN hND S.solver A hA hAn k).value z = some y →
          IsFullSigning (WithLp.ofLp y.val) ∧
            spectralNorm (signedSum A (WithLp.ofLp y.val)) ≤ discrepancyBound N D) ∧
      (1 - (1 / 2 : ℝ) ^ k ≤ ∑ z, (output hN hND S.solver A hA hAn k).weight z *
        (if ((output hN hND S.solver A hA hAn k).value z).isSome then 1 else 0)) ∧
      (∀ z : (output hN hND S.solver A hA hAn k).Draws, ∃ cost draws,
        (implementation hN hND S A hA hAn k).Executes z
          ((output hN hND S.solver A hA hAn k).value z) cost draws ∧
            cost ≤ C * (N + D + k + 2) ^ e ∧ draws ≤ C * (N + D + k + 2) ^ e) := by
  obtain ⟨C, e, hC, hbudget⟩ := exists_uniform_budget S
  refine ⟨C, e, hC, ?_⟩
  intro N D hN hND A hA hAn k
  refine ⟨output_sound hN hND S.solver A hA hAn k,
    output_probability hN hND S.solver A hA hAn k, ?_⟩
  intro z
  obtain ⟨cost, draws, he, hc, hr⟩ := execution_bounded hN hND S A hA hAn k z
  exact ⟨cost, draws, he, hc.trans (hbudget N D k).1, hr.trans (hbudget N D k).2⟩

/-- Unconditional existence on the entire rectangular domain, including the
empty family. The positive-dimensional proof uses the walk's success mass. -/
theorem exists_signing {N D : ℕ} (hND : N ≤ D)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) :
    ∃ ε : Fin N → ℝ, IsFullSigning ε ∧ spectralNorm (signedSum A ε) ≤ discrepancyBound N D := by
  by_cases hN : N = 0
  · subst N
    refine ⟨fun _ => 1, isFullSigning_one 0, ?_⟩
    simp [signedSum, discrepancyBound]
  · exact RectangularRidgeOriginalAlgorithm.exists_signing (by omega) hND A hA hAn

end MatrixSpencer.RectangularRidgeEndToEnd
