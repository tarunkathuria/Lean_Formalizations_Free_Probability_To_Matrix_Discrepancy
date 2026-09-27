import FaithfulMS.RectangularSamplingComposition
import FaithfulMS.RectangularDirectOriginalRuntime
/-! The counted direct-density walk has the conditional uniform-input law
specified by its analytic finite sampler, including adaptive preparations,
rejected retries, and completed phases. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.RectangularDirectSampling
open MatrixSpencer MSManuscriptAdaptive MSCountedSampler
open RectangularSampling
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run
namespace EpochWork
open RectangularRidgeEpochInput RectangularDirectEpochRun RectangularDirectEpochWork
variable {N d : ℕ} [Nonempty (Fin d)]
attribute [local instance] Classical.propDecidable

def next_refinement (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) (R : Routines solver a c)
    (code : ∀ s hfloor hnt, RectangularSampling.Refinement (R.movement s hfloor hnt)) (s : Certified c) :
    RectangularSampling.Refinement (next solver a c R s) := by
  unfold RectangularDirectEpochWork.next
  split
  · exact .congr _ (.overhead (.pure s 0) _)
  · split
    · exact .congr _ (.overhead (.pure _ 0) _)
    · exact .congr _ (.overhead (code _ _ _) _)

def run_refinement (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) (R : Routines solver a c)
    (code : ∀ s hfloor hnt, RectangularSampling.Refinement (R.movement s hfloor hnt))
    (k : ℕ) (s : Certified c) : RectangularSampling.Refinement (RectangularDirectEpochWork.run solver a c R k s) :=
  .congr _ (.iterate (next_refinement solver a c R code) k s)

def output_refinement (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) (R : Routines solver a c)
    (code : ∀ s hfloor hnt, RectangularSampling.Refinement (R.movement s hfloor hnt)) :
    RectangularSampling.Refinement (RectangularDirectEpochWork.output solver a c R) :=
  .overhead (run_refinement solver a c R code _ _) _
end EpochWork

namespace CompiledEpoch
open RectangularRidgeEpochInput RectangularDirectCompiledEpoch
variable {N d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}

def implementation_refinement (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S)
    (a : Fin d) (c : Config N d) : RectangularSampling.Refinement (implementation S W a c) :=
  .overhead (EpochWork.output_refinement S.service a c (routines S W a c)
    (fun s hfloor hnt => .uniformMovement c s hfloor hnt)) _
end CompiledEpoch

namespace AcceptedEpoch
open RectangularRidgeEpochInput RectangularDirectCountedAcceptedEpoch
variable {N d : ℕ} [Nonempty (Fin d)]

def implementation_refinement (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S)
    (a : Fin d) (c : Config N d) (r : ℕ) : RectangularSampling.Refinement (implementation S W a c r) :=
  .congr _ (.retry (CompiledEpoch.implementation_refinement S W a c) _ r)
end AcceptedEpoch

namespace EpochFactory
open RectangularRidgeEpochInput RectangularDirectCountedEpochFactory
variable {N d : ℕ} [Nonempty (Fin d)]

def sample_refinement (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S)
    (a : Fin d) (c : Config N d) (r : ℕ) : RectangularSampling.Refinement (sample S W a c r) :=
  .congr _ (.map (AcceptedEpoch.implementation_refinement S W a c r) _)

def implementation_refinement (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d) (r : ℕ)
    (x : RectangularRidgePhaseAssembly.Point (N := N) (margin N))
    (hx : 32 ≤ RectangularRidgeRemainingPotential.liveCount x.val) :
    RectangularSampling.Refinement (implementation S W a A hA hAn hN hND r x hx) :=
  .overhead (sample_refinement S W a _ r) _
end EpochFactory

namespace PolynomialRuntime
open RectangularDirectPolynomialRuntime RectangularDirectPolynomialAlgorithm
open RectangularRidgeRetryParameters (retries)
variable {N d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}

def implementation_refinement (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d) (k : ℕ) :
    RectangularSampling.Refinement (implementation S W a A hA hAn hN hND k) :=
  .overhead (Full.output_refinement _ _ _ _ _ _ _ _ _
    (EpochFactory.implementation_refinement S W a A hA hAn hN hND (retries N d k)) _ _ _ _ _ _) _
end PolynomialRuntime

namespace OriginalAlgorithm
open RectangularDirectOriginalRuntime RectangularRidgeFlatSigning
variable {N D : ℕ}

def implementation_refinement (hN : 1 ≤ N) (hND : N ≤ D)
    (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ) :
    RectangularSampling.Refinement (implementation hN hND S W A hA hAn k) := by
  letI : NeZero D := ⟨by omega⟩
  letI : NeZero (D + D) := ⟨by omega⟩
  exact .overhead (PolynomialRuntime.implementation_refinement S W ⟨0, by omega⟩
    (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn) hN (by omega) k) _
end OriginalAlgorithm

end FaithfulMS.RectangularDirectSampling
