import FaithfulMS.SquareDirectProcess
import FaithfulMS.SquareDirectOriginalOutput

/-! Original-input square Matrix Spencer: complete counted finite execution,
full-signing correctness, and constant success. The explicitly permitted
convex solver is the only computational service supplied by the caller.
Random draws are implemented by the counted uniform-real categorical scan. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.SquareDirectRuntime
open MatrixSpencer
open MSCountedSampler MSManuscriptAdaptive
variable {N D : ℕ}
local instance : CStarAlgebra (Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ) := {}
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run

variable (P : DirectSDP.PolynomialService)
    (A : Fin N→CMatrix D) (hA : ∀i,(A i).IsHermitian) (hN : ∀i,spectralNorm (A i)≤1)

def sampler (r : ℕ) := @SquareDirectExplicit.output ⟨P.service⟩ N D A hA hN r

def pointImplementation (r : ℕ) (hd : 0<D) :
    Implementation (SquareDirectOriginalOutput.pointSampler P A hA hN r hd) := by
  letI : NeZero D:=⟨hd.ne'⟩
  letI : Nonempty (Fin (D+D)):=Fin.pos_iff_nonempty.mp (by omega)
  exact SquareDirectProcess.implementation P (RealRAM.MSPoint.finTable N)
    (RealRAM.MSLabelTable.fin_ordered N) finSumFinEquiv.symm (by omega)
    (fun i=>signedLift (A i)) (fun i=>signedLift_isHermitian (hA i))
    (MSManuscriptNumericalComposition.lifted_contractions A hA hN) r
    ⟨0,signing_zero_regular⟩

def operations (P : DirectSDP.PolynomialService) (N D r : ℕ) : ℕ :=
  SquareDirectProcess.operations P N (D+D) r+1100*(N+D+1)^3

def draws (N D r : ℕ) : ℕ := SquareDirectProcess.draws N (D+D) r

theorem pointImplementation_bounded (r : ℕ) (hd : 0<D) :
    Bounded (pointImplementation P A hA hN r hd) (SquareDirectProcess.operations P N (D+D) r)
      (draws N D r) := by
  letI : NeZero D:=⟨hd.ne'⟩
  letI : Nonempty (Fin (D+D)):=Fin.pos_iff_nonempty.mp (by omega)
  have h:=SquareDirectProcess.implementation_bounded P (RealRAM.MSPoint.finTable N)
    (RealRAM.MSLabelTable.fin_ordered N) finSumFinEquiv.symm (by omega)
    (fun i=>signedLift (A i)) (fun i=>signedLift_isHermitian (hA i))
    (MSManuscriptNumericalComposition.lifted_contractions A hA hN) r
    ⟨0,signing_zero_regular⟩
  simpa only [Fintype.card_fin] using h

def implementation (r : ℕ) : Implementation (sampler P A hA hN r) :=
  SquareDirectOriginalOutput.implementation P A hA hN r (pointImplementation P A hA hN r)

theorem implementation_bounded (r : ℕ) :
    Bounded (implementation P A hA hN r) (operations P N D r) (draws N D r) :=
  SquareDirectOriginalOutput.implementation_bounded P A hA hN r (pointImplementation P A hA hN r)
    (pointImplementation_bounded P A hA hN r)

theorem execution_bounded (r : ℕ) (z : (sampler P A hA hN r).Draws) :
    ∃cost rand,(implementation P A hA hN r).Executes z
      ((sampler P A hA hN r).value z) cost rand ∧
      cost≤operations P N D r ∧ rand≤draws N D r :=
  MSCountedSampler.execution_bounded (implementation P A hA hN r)
    (implementation_bounded P A hA hN r) z

theorem execution_sound (hDN : D≤N) (r : ℕ)
    (z : (sampler P A hA hN r).Draws) (σ : Fin N→ℝ) (cost rand : ℕ)
    (h : (implementation P A hA hN r).Executes z (some σ) cost rand) :
    IsFullSigning σ ∧ spectralNorm (signedSum A σ)≤10651761*Real.sqrt (N:ℝ) ∧
      cost≤operations P N D r ∧ rand≤draws N D r := by
  have hv := (implementation P A hA hN r).result z (some σ) cost rand h
  have hs := @SquareDirectExplicit.output_sound ⟨P.service⟩ N D A hA hN hDN r z σ hv.symm
  exact ⟨hs.1,hs.2,implementation_bounded P A hA hN r z (some σ) cost rand h⟩

def retries (N : ℕ) := MSManuscriptRetryBudget.retries N MSManuscriptNumericalHalfPhase.epochCalls

section Event
attribute [local instance] Classical.propDecidable

theorem constant_success (hDN : D≤N) :
    let S:=sampler P A hA hN (retries N)
    (1:ℝ)/2≤∑z,S.weight z*(if ∃σ,S.value z=some σ ∧ IsFullSigning σ ∧
      spectralNorm (signedSum A σ)≤10651761*Real.sqrt (N:ℝ) then 1 else 0) :=
  @SquareDirectExplicit.valid_output_probability ⟨P.service⟩ N D A hA hN hDN

end Event

end FaithfulMS.SquareDirectRuntime
