import MatrixSpencer.RectangularRidgeEpochAcceptance

/-! The concrete finite numerical epoch instantiates the original-universe
phase and full-signing sampler, with a proved geometric retry failure bound. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeEpochFactory
open RectangularRidgeEpochInput RectangularRidgeEpochRun RectangularRidgeEpochAcceptance
open RectangularRidgePhaseAssembly (Point EpochFactory)
open MSManuscriptAdaptive (Sampler failure)
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgeEpochFactoryCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeEpochFactorySpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
attribute [local irreducible] RectangularRidgeEpochRun.run

def project (c : Config N d) (s : Certified c) : Point (N:=N) (margin N) × ℝ :=
  (⟨s.val.point,s.property.1.regular⟩,s.val.time)

def sample (solver : RectangularRidgeConvexValue.Solver) (a : Fin d) (c : Config N d) (r : ℕ) :
    Sampler (Option (Point (N:=N) (margin N) × ℝ)) :=
  (accepted solver a c r).map (Option.map (project c))

theorem sample_sound (solver : RectangularRidgeConvexValue.Solver) (a : Fin d) (c : Config N d)
    (r : ℕ) (z : (sample solver a c r).Draws) (y : Point (N:=N) (margin N) × ℝ)
    (ho : (sample solver a c r).value z=some y) :
    FiniteHalfPhase.EpochAdvance (potential c) (duration c/2) 27 c.start y.1.val y.2 :=
  Sampler.map_option_sound (accepted solver a c r) (project c) (GoodEndpoint c)
    (fun w : Point (N:=N) (margin N) × ℝ => FiniteHalfPhase.EpochAdvance (potential c) (duration c/2) 27 c.start w.1.val w.2)
    (accepted_sound solver a c r) (fun s hs => hs) z y ho

theorem sample_failure_le (solver : RectangularRidgeConvexValue.Solver) (a : Fin d) (c : Config N d) (r : ℕ) :
    (sample solver a c r).expectation failure ≤ (19/50 : ℝ)^r := by
  rw [sample,Sampler.failure_map]
  exact accepted_failure_le solver a c r

def input (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d)
    (x : Point (N:=N) (margin N)) (hx : 32 ≤ RectangularRidgeRemainingPotential.liveCount x.val) : Config N d where
  atoms := A
  hermitian := hA
  contractions := hAn
  count_pos := hN
  rectangular := hND
  start := x.val
  start_regular := x.property
  live_large := hx

def factory (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d) (r : ℕ) :
    EpochFactory (RectangularRidgeRemainingPotential.potential (RectangularRidgeTuning.depth N d hN)
      (RectangularRidgePrimitiveParameters.weight N d hN) (1/(d:ℝ)) 0 A hA)
      (margin N) (RectangularRidgeUniformResponse.duration N d hN/2) 27 ((19/50:ℝ)^r) where
  sample x hx := sample solver a (input A hA hAn hN hND x hx) r
  sound x hx := sample_sound solver a (input A hA hAn hN hND x hx) r
  failure_le x hx := sample_failure_le solver a (input A hA hAn hN hND x hx) r

end MatrixSpencer.RectangularRidgeEpochFactory
