import MatrixSpencer.MSSquarePolynomialSampling
import MatrixSpencer.MSSquareRuntimePolynomialCertificate

/-! A single original-input endpoint for the square Matrix Spencer program.
The two natural polynomials bound all scalar operations and fresh uniform-real
draws after the standard retry choice. The probability is the Markov law of
the actual counted program, including its literal cumulative-weight selector.
The permitted polynomial convex solver is the only supplied service. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSSquareEndToEnd
open MSCountedSampler MSSquarePolynomialRuntime
set_option maxHeartbeats 2400000
set_option maxRecDepth 16000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run

/-- Polynomial total real-RAM cost and constant-probability full signing,
for every original square-regime input, including zero physical dimension.
The third polynomial variable is set to zero because the retry count has
already been replaced by its prescribed polynomial in the input size. -/
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
              spectralNorm (signedSum A σ) ≤ 10651761*Real.sqrt (N:ℝ)) then 1 else 0) := by
  obtain ⟨p,hp⟩:=MSSquareRuntimePolynomialCertificate.constant_success_operations_polynomial P
  obtain ⟨q,hq⟩:=MSSquareRuntimePolynomialCertificate.constant_success_draws_polynomial
  refine ⟨p,q,?_,?_⟩
  · intro N D
    exact ⟨hp N D 0,hq N D 0⟩
  intro N D A hA hN hDN
  dsimp only
  rw [hp N D 0,hq N D 0]
  refine ⟨implementation_bounded P A hA hN (retries N),
    execution_bounded P A hA hN (retries N),?_,
    bounded_execution_probability P A hA hN hDN⟩
  intro z σ k rand h
  have hs:=execution_sound P A hA hN hDN (retries N) z σ k rand h
  exact ⟨hs.1,hs.2.1⟩

end MatrixSpencer.MSSquareEndToEnd
