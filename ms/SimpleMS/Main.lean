import MatrixSpencer.MSSquareEndToEnd
import MatrixSpencer.RectangularRidgeEndToEnd
import MatrixSpencer.MSManuscriptNumericalExplicit
import SimpleMS.MaterializedFrame

/-!
# Endpoints for the revised scaled-projection Matrix Spencer walk

In this isolated project, both numerical epoch definitions use
`SimpleMS.Movement.covariance`: one half of the projection onto the eigenvalues
of the prepared covariance at least one half, intersected with the frozen and
radial constraints. `SimpleMS.UniformSampler` samples the two signs of each
retained projection eigenvector with equal mass. These are the actual samplers
and counted implementations occurring in the following endpoints.

Runtime is in real arithmetic augmented by exact eigendecomposition and the
explicit polynomial SDP solver. `CountedSpectralSampler.EVDExecutes` defines the
EVD leaf; `MaterializedFrame.frame_evd_execution` identifies its computed input.
Existence conclusions below do not assume either computational service.
-/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
namespace SimpleMS
open MatrixSpencer

namespace Square
open MSCountedSampler MSSquarePolynomialRuntime
theorem polynomial_runtime_and_constant_success
    (P : KSPolynomialConvexSolver.PolynomialSolver) :
    ∃ p q : MvPolynomial (Fin 3) ℕ,
      (∀ N D,
        MvPolynomial.eval ![N,D,0] p=operations P N D (retries N) ∧
        MvPolynomial.eval ![N,D,0] q=draws N D (retries N)) ∧
      ∀ (N D : ℕ) (A : Fin N → CMatrix D)
        (hA : ∀i,(A i).IsHermitian) (hN : ∀i,spectralNorm (A i) ≤ 1), D ≤ N →
        let r:=retries N
        let S:=MSConvexRawInput.output P A hA hN r
        let E:=implementation P A hA hN r
        let code:=implementation_refinement P A hA hN r
        let B:=MvPolynomial.eval ![N,D,0] p
        let R:=MvPolynomial.eval ![N,D,0] q
        Bounded E B R ∧
        (∀z,∃k rand,E.Executes z (S.value z) k rand ∧ k ≤ B ∧ rand ≤ R) ∧
        (∀z σ k rand,E.Executes z (some σ) k rand →
          IsFullSigning σ ∧ spectralNorm (signedSum A σ) ≤ 10651761*Real.sqrt (N:ℝ)) ∧
        (1:ℝ)/2 ≤ ∑z,code.mass z *
          (if ∃out k rand,E.Executes z out k rand ∧ k ≤ B ∧ rand ≤ R ∧
            (∃σ,out=some σ ∧ IsFullSigning σ ∧
              spectralNorm (signedSum A σ) ≤ 10651761*Real.sqrt (N:ℝ)) then 1 else 0) :=
  MSSquareEndToEnd.polynomial_runtime_and_constant_success P

/-- Existence from the revised finite walk, with no computational assumption. -/
theorem exists_signing {N D : ℕ} (A : Fin N → CMatrix D)
    (hA : ∀i,(A i).IsHermitian) (hN : ∀i,spectralNorm (A i)≤1) (hDN : D≤N) :
    ∃σ : Fin N → ℝ, IsFullSigning σ ∧
      spectralNorm (signedSum A σ)≤10651761*Real.sqrt (N:ℝ) :=
  MSManuscriptNumericalExplicit.exists_full_signing A hA hN hDN

end Square

namespace Rectangular
open RectangularRidgeOriginalAlgorithm
open RectangularRidgePhaseAssembly (Point)
open RectangularRidgeEpochInput (margin)
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
            cost ≤ C * (N + D + k + 2) ^ e ∧ draws ≤ C * (N + D + k + 2) ^ e) := RectangularRidgeEndToEnd.polynomial_algorithm S

/-- Existence from the revised finite walk, with no computational assumption. -/
theorem exists_signing {N D : ℕ} (hND : N≤D) (A : Fin N → CMatrix D)
    (hA : ∀i,(A i).IsHermitian) (hN : ∀i,spectralNorm (A i)≤1) :
    ∃σ : Fin N → ℝ, IsFullSigning σ ∧
      spectralNorm (signedSum A σ)≤discrepancyBound N D :=
  RectangularRidgeEndToEnd.exists_signing hND A hA hN

end Rectangular

/-- This identity checks the covariance inside the actual shared epoch state. -/
theorem actual_epoch_covariance {N : ℕ} (s : MSManuscriptNumericalEpochLedger.State N) :
    MSManuscriptNumericalEpochLedger.Q s =
      (1/2:ℝ) • euclideanProjectionMatrix
        (highSpace s.owner.physical ⊓ legalSpace (frozenCoordinates s.point) s.point) := rfl

end SimpleMS
