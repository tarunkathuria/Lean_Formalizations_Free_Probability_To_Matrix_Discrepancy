import MatrixSpencer.MSConvexNumericalExplicit

/-! Original-input square Matrix Spencer algorithm using the permitted
polynomial convex value solver. This module supplies actual output correctness
and success probability; total primitive runtime accounting is separate.
The only solver input is PolynomialSolver, with its explicit SDP contract. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSConvexPolynomialInput
open MSManuscriptAdaptive MSManuscriptNumericalHalfPhase
variable {N D : ℕ}
attribute [local instance] Classical.propDecidable

def output (P : KSPolynomialConvexSolver.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i)≤1) (r : ℕ) : Sampler (Option (Fin N → ℝ)) :=
  letI := MSConvexOwnerValue.Oracle.ofSolver P.solver
  MSConvexNumericalExplicit.output A hA hN r

theorem output_sound (P : KSPolynomialConvexSolver.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i)≤1) (hDN : D≤N) (r : ℕ)
    (z : (output P A hA hN r).Draws) (σ : Fin N → ℝ)
    (ho : (output P A hA hN r).value z=some σ) :
    IsFullSigning σ ∧ spectralNorm (signedSum A σ)≤10651761*Real.sqrt (N:ℝ) := by
  letI := MSConvexOwnerValue.Oracle.ofSolver P.solver
  exact MSConvexNumericalExplicit.output_sound A hA hN hDN r z σ ho

theorem output_event_probability (P : KSPolynomialConvexSolver.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i)≤1) (r : ℕ) :
    1-((N+1:ℕ):ℝ)*((epochCalls:ℝ)*epochFailure r)≤
      ∑z,(output P A hA hN r).weight z*
        (if ((output P A hA hN r).value z).isSome then 1 else 0) := by
  letI := MSConvexOwnerValue.Oracle.ofSolver P.solver
  exact MSConvexNumericalExplicit.output_event_probability A hA hN r

theorem constant_success (P : KSPolynomialConvexSolver.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i)≤1) :
    (1:ℝ)/2≤∑z,(output P A hA hN (MSManuscriptRetryBudget.retries N epochCalls)).weight z*
      (if ((output P A hA hN (MSManuscriptRetryBudget.retries N epochCalls)).value z).isSome then 1 else 0) := by
  letI := MSConvexOwnerValue.Oracle.ofSolver P.solver
  exact MSConvexNumericalExplicit.constant_success A hA hN

theorem valid_output_probability (P : KSPolynomialConvexSolver.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i)≤1) (hDN : D≤N) :
    let S:=output P A hA hN (MSManuscriptRetryBudget.retries N epochCalls)
    (1:ℝ)/2≤∑z,S.weight z*(if ∃σ,S.value z=some σ ∧ IsFullSigning σ ∧
      spectralNorm (signedSum A σ)≤10651761*Real.sqrt (N:ℝ) then 1 else 0) := by
  letI := MSConvexOwnerValue.Oracle.ofSolver P.solver
  exact MSConvexNumericalExplicit.valid_output_probability A hA hN hDN

end MatrixSpencer.MSConvexPolynomialInput
