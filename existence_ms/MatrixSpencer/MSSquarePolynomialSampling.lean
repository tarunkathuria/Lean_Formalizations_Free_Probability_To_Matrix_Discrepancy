import MatrixSpencer.MSCountedOriginalSampling
import MatrixSpencer.MSSquarePolynomialRuntime

/-! End-to-end stochastic refinement of the original-input square Matrix
Spencer program. The probability below is the finite Markov semantics of
the actual counted code, whose sole random primitive is the measured
uniform-real cumulative scan. It includes full-signing correctness and the
complete operation/draw bounds on every successful execution. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer
open MSCountedSampler RealRAM PhaseRestriction MSManuscriptPhase
set_option maxHeartbeats 2400000
set_option maxRecDepth 16000
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run

namespace MSCountedSquareProcess
variable {ι n : Type} [Fintype ι] [LinearOrder ι] [Fintype n] [DecidableEq n] [Nonempty n]
  {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
variable (P : KSPolynomialConvexSolver.PolynomialSolver)
  (L : MSPoint.Table ι) (hL : MSLabelTable.Ordered L) (e : Fin d≃n) (hd : 0<d)
  (A : ι→Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1)

def phase_refinement (x : Point (ι:=ι) (signingEpsilon ι))
    (hx : 0<Fintype.card (Live x.val)) (r : ℕ) :
    Refinement (phase P L hL e hd A hA hN x hx r) :=
  MSCountedOriginalPhases.phase_refinement P e hd A hA hN x hx
    (MSEpochFactorySetup.liveTable L x.val).value
    (fun y hy => routines L hL e hd A hA hN x.val y (MSCountedOriginalPhases.live_large y hy)) r

def implementation_refinement (r : ℕ) (start : Point (ι:=ι) (signingEpsilon ι)) :
    Refinement (implementation P L hL e hd A hA hN r start) :=
  MSCountedNumericalFullSigning.output_refinement 0 A hA hN (signingEpsilon ι)
    (MSManuscriptNumericalHalfPhase.epochFailure r) (provider P e hd A hA hN r)
    (by change 0≤(301/800:ℝ)^r; positivity) L
    (fun x hx => phase P L hL e hd A hA hN x hx r)
    (fun x hx => phase_refinement P L hL e hd A hA hN x hx r)
    (fun x => (MSPhaseSetup.setup L e A hA x.val).cost+1) start
end MSCountedSquareProcess

namespace MSSquarePolynomialRuntime
variable {N D : ℕ}
local instance : CStarAlgebra (Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ) := {}
variable (P : KSPolynomialConvexSolver.PolynomialSolver)
  (A : Fin N→CMatrix D) (hA : ∀i,(A i).IsHermitian) (hN : ∀i,spectralNorm (A i)≤1)

def point_refinement (r : ℕ) (hd : 0<D) :
    Refinement (pointImplementation P A hA hN r hd) := by
  letI : NeZero D := ⟨hd.ne'⟩
  letI : Nonempty (Fin (D+D)) := Fin.pos_iff_nonempty.mp (by omega)
  exact MSCountedSquareProcess.implementation_refinement P (MSPoint.finTable N)
    (MSLabelTable.fin_ordered N) finSumFinEquiv.symm (by omega)
    (fun i=>signedLift (A i)) (fun i=>signedLift_isHermitian (hA i))
    (MSManuscriptNumericalComposition.lifted_contractions A hA hN) r
    ⟨0,signing_zero_regular⟩

def implementation_refinement (r : ℕ) : Refinement (implementation P A hA hN r) :=
  MSCountedNumericalSampling.original P A hA hN r (pointImplementation P A hA hN r)
    (point_refinement P A hA hN r)

section Event
attribute [local instance] Classical.propDecidable

/-- Constant success for the same counted stochastic code, including its
full runtime bounds. There is no supplied probability-law premise. -/
theorem bounded_execution_probability (hDN : D≤N) :
    let r := retries N
    let E := implementation P A hA hN r
    let code := implementation_refinement P A hA hN r
    (1:ℝ)/2 ≤ ∑ z, code.mass z *
      (if ∃ out k q, E.Executes z out k q ∧ k≤operations P N D r ∧ q≤draws N D r ∧
        (∃ σ, out=some σ ∧ IsFullSigning σ ∧
          spectralNorm (signedSum A σ)≤10651761*Real.sqrt (N:ℝ)) then 1 else 0) := by
  dsimp only
  rw [Refinement.bounded_event (implementation_refinement P A hA hN (retries N))
    (implementation_bounded P A hA hN (retries N))]
  refine (constant_success P A hA hN hDN).trans (le_of_eq ?_)
  unfold MSManuscriptAdaptive.Sampler.expectation
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hg : ∃ σ, (MSConvexRawInput.output P A hA hN (retries N)).value z=some σ ∧
      IsFullSigning σ ∧ spectralNorm (signedSum A σ)≤10651761*Real.sqrt (N:ℝ)
  · simp only [if_pos hg]
  · simp only [if_neg hg]

end Event
end MSSquarePolynomialRuntime
end MatrixSpencer
