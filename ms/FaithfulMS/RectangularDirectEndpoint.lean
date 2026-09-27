import FaithfulMS.RectangularDirectSampling
import FaithfulMS.RectangularDirectBudget

/-! Original-input rectangular algorithm with a derived stochastic code law.
The event below includes actual counted execution, its operation and draw
bounds, a complete signing, and its original operator-norm bound. Its mass is
computed compositionally from the measured uniform-input movement selector,
not supplied as an extra probability-law hypothesis. -/
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.RectangularDirectSampling
open MatrixSpencer MSCountedSampler
open RectangularDirectOriginal RectangularDirectOriginalRuntime
open RectangularSampling
open RectangularRidgePhaseAssembly (Point)
open RectangularRidgeEpochInput (margin)
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run

namespace Endpoint
variable {N D : ℕ}

def Good (A : Fin N → CMatrix D) (out : Option (Point (N := N) (margin N))) : Prop :=
  ∃ y, out = some y ∧ IsFullSigning (WithLp.ofLp y.val) ∧
    spectralNorm (signedSum A (WithLp.ofLp y.val)) ≤ discrepancyBound N D

theorem bounded_execution_probability (hN : 1 ≤ N) (hND : N ≤ D)
    (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ) :
    let E := implementation hN hND S W A hA hAn k
    let code := OriginalAlgorithm.implementation_refinement hN hND S W A hA hAn k
    1 - (1 / 2 : ℝ) ^ k ≤ ∑ z, code.mass z *
      (if ∃ out cost draws, E.Executes z out cost draws ∧ cost ≤ budget S W N D k ∧
        draws ≤ RectangularDirectPolynomialRuntime.randomDraws N (D + D) k ∧ Good A out
      then 1 else 0) := by
  dsimp only
  rw [RectangularSampling.Refinement.bounded_event
    (OriginalAlgorithm.implementation_refinement hN hND S W A hA hAn k)
    (implementation_bounded hN hND S W A hA hAn k)]
  refine (output_probability hN hND S.service A hA hAn k).trans (le_of_eq ?_)
  unfold MSManuscriptAdaptive.Sampler.expectation
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  cases hv : (output hN hND S.service A hA hAn k).value z with
  | none => simp [Good]
  | some y =>
    have hy := output_sound hN hND S.service A hA hAn k z y hv
    simp only [Option.isSome_some, ↓reduceIte]
    exact (if_pos ⟨y, rfl, hy⟩).symm

/-- Uniform polynomial operation/draw bounds and high-probability signing
for the derived stochastic semantics of the same concrete implementation. -/
theorem polynomial_algorithm (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) :
    ∃ C e : ℕ, 0 < C ∧ ∀ (N D : ℕ) (hN : 1 ≤ N) (hND : N ≤ D)
      (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
      (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ),
      let E := implementation hN hND S W A hA hAn k
      let code := OriginalAlgorithm.implementation_refinement hN hND S W A hA hAn k
      (1 - (1 / 2 : ℝ) ^ k ≤ ∑ z, code.mass z *
        (if ∃ out cost draws, E.Executes z out cost draws ∧
          cost ≤ C * (N + D + k + 2) ^ e ∧ draws ≤ C * (N + D + k + 2) ^ e ∧
          Good A out then 1 else 0)) ∧
      (∀ z, ∃ cost draws, E.Executes z
        ((output hN hND S.service A hA hAn k).value z) cost draws ∧
          cost ≤ C * (N + D + k + 2) ^ e ∧ draws ≤ C * (N + D + k + 2) ^ e) := by
  obtain ⟨C, e, hC, hb⟩ := RectangularDirectBudget.exists_uniform_budget S W
  refine ⟨C, e, hC, ?_⟩
  intro N D hN hND A hA hAn k
  dsimp only
  constructor
  · refine (bounded_execution_probability hN hND S W A hA hAn k).trans ?_
    apply Finset.sum_le_sum
    intro z hz
    apply mul_le_mul_of_nonneg_left _
      ((OriginalAlgorithm.implementation_refinement hN hND S W A hA hAn k).mass_nonneg z)
    split_ifs with hg hh hh
    · exact le_rfl
    · obtain ⟨out, cost, draws, he, hc, hr, hgood⟩ := hg
      exact False.elim (hh ⟨out, cost, draws, he,
        hc.trans (hb N D k).1, hr.trans (hb N D k).2, hgood⟩)
    · norm_num
    · exact le_rfl
  · intro z
    obtain ⟨cost, draws, he, hc, hr⟩ := execution_bounded hN hND S W A hA hAn k z
    exact ⟨cost, draws, he, hc.trans (hb N D k).1, hr.trans (hb N D k).2⟩

#print axioms bounded_execution_probability
#print axioms polynomial_algorithm
end Endpoint
end FaithfulMS.RectangularDirectSampling
