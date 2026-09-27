import FaithfulMS.SquareDirectEndpoint
import FaithfulMS.RectangularDirectEndpoint
import FaithfulMS.RectangularDirectConcretePrograms

/-! Public algorithmic Matrix Spencer theorems for the direct-density route.
N counts input matrices and D is their matrix dimension. The displayed
polynomial service concerns exact affine-SDP optimization in the stipulated
real-arithmetic/EVD model. Matrix transport, covariance preparation, movement,
acceptance, retries and their work bounds are proved implementations.

The separate existence project eliminates the solver parameter entirely.
These runtime statements express probability through the derived finite
conditional kernels of the implemented uniform movement sampler. -/
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.Main
open MatrixSpencer MSCountedSampler
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
attribute [local instance] Classical.propDecidable

/-- Square Matrix Spencer, including D≤N. The confidence parameter k gives
failure at most 2⁻ᵏ, and a single dimension polynomial bounds every execution. -/
theorem matrix_spencer_square (P : DirectSDP.PolynomialService) :
    ∃ C e : ℕ, 0<C ∧ ∀ (N D : ℕ) (A : Fin N→CMatrix D)
      (hA : ∀i,(A i).IsHermitian) (hN : ∀i,spectralNorm (A i)≤1) (hDN : D≤N) (k : ℕ),
      let r := SquareDirectPolynomial.confidenceRetries N k
      let E := SquareDirectRuntime.implementation P A hA hN r
      let code := SquareDirectSampling.Runtime.implementation P A hA hN r
      (1-(1/2:ℝ)^k ≤ ∑ z,code.mass z *
        (if ∃ out cost draws, E.Executes z out cost draws ∧
          cost≤C*(N+D+k+2)^e ∧ draws≤C*(N+D+k+2)^e ∧
          (∃σ, out=some σ ∧ IsFullSigning σ ∧
            spectralNorm (signedSum A σ)≤10651761*Real.sqrt (N:ℝ)) then 1 else 0)) ∧
      (∀ z, ∃ cost draws, E.Executes z ((SquareDirectRuntime.sampler P A hA hN r).value z)
        cost draws ∧ cost≤C*(N+D+k+2)^e ∧ draws≤C*(N+D+k+2)^e) :=
  SquareDirectEndpoint.polynomial_algorithm P

/-- Rectangular Matrix Spencer for positive N≤D. Local implementations are
instantiated from the same affine SDP service; no response, acceptance,
preparation or probability-law premise is supplied by the caller. -/
theorem matrix_spencer_rectangular (P : DirectSDP.PolynomialService) :
    ∃ C e : ℕ, 0<C ∧ ∀ (N D : ℕ) (hN : 1≤N) (hND : N≤D)
      (A : Fin N→CMatrix D) (hA : ∀i,(A i).IsHermitian)
      (hAn : ∀i,spectralNorm (A i)≤1) (k : ℕ),
      let W := RectangularDirectConcretePrograms.programs P
      let E := RectangularDirectOriginalRuntime.implementation hN hND P W A hA hAn k
      let code := RectangularDirectSampling.OriginalAlgorithm.implementation_refinement
        hN hND P W A hA hAn k
      (1-(1/2:ℝ)^k ≤ ∑ z,code.mass z *
        (if ∃ out cost draws, E.Executes z out cost draws ∧
          cost≤C*(N+D+k+2)^e ∧ draws≤C*(N+D+k+2)^e ∧
          (∃y, out=some y ∧ IsFullSigning (WithLp.ofLp y.val) ∧
            spectralNorm (signedSum A (WithLp.ofLp y.val))≤
              8102676*Real.sqrt ((N:ℝ)*(1+Real.log ((2*(D:ℝ))/N)))) then 1 else 0)) ∧
      (∀ z, ∃ cost draws, E.Executes z
        ((RectangularDirectOriginal.output hN hND P.service A hA hAn k).value z)
        cost draws ∧ cost≤C*(N+D+k+2)^e ∧ draws≤C*(N+D+k+2)^e) :=
  RectangularDirectSampling.Endpoint.polynomial_algorithm P
    (RectangularDirectConcretePrograms.programs P)

#print axioms matrix_spencer_square
#print axioms matrix_spencer_rectangular
end FaithfulMS.Main
