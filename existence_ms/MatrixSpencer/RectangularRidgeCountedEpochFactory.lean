import MatrixSpencer.RectangularRidgeCountedAcceptedEpoch
import MatrixSpencer.RectangularRidgeEpochFactory

/-! The concrete counted accepted epoch is inserted into the proved epoch
factory. Projection reads the existing point/time fields; configuration
construction copies existing input references and erases only proofs. -/
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeCountedEpochFactory
open RectangularRidgeEpochInput RectangularRidgeEpochRun
open MSManuscriptAdaptive MSCountedSampler
open RealRAM.JacobiIteration (Counted)
variable {N d : ℕ} [Nonempty (Fin d)]

def project (c : Config N d) : Option (Certified c) →
    Counted (Option (RectangularRidgePhaseAssembly.Point (N := N) (margin N) × ℝ))
  | none => ⟨none, 1⟩
  | some s => ⟨some (RectangularRidgeEpochFactory.project c s), 4⟩

omit [Nonempty (Fin d)] in
theorem project_value (c : Config N d) (s : Option (Certified c)) :
    (project c s).value = s.map (RectangularRidgeEpochFactory.project c) := by
  cases s <;> rfl

def sample (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (r : ℕ) :
    Implementation (RectangularRidgeEpochFactory.sample S.solver a c r) :=
  congr (by
    have he : (fun s => (project c s).value) = Option.map (RectangularRidgeEpochFactory.project c) := by
      funext s
      exact project_value c s
    rw [he]
    rfl)
    (map (RectangularRidgeCountedAcceptedEpoch.implementation S a c r) (project c))

theorem sample_bounded (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (r : ℕ) :
    Bounded (sample S a c r) (RectangularRidgeCountedAcceptedEpoch.operations S N d r + 6)
      (RectangularRidgeCountedAcceptedEpoch.randomDraws N d r) := by
  apply congr_bounded
  exact map_bounded _ (project c) (RectangularRidgeCountedAcceptedEpoch.implementation_bounded S a c r)
    (fun s => by cases s <;> norm_num [project])

def implementation (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d) (r : ℕ)
    (x : RectangularRidgePhaseAssembly.Point (N := N) (margin N))
    (hx : 32 ≤ RectangularRidgeRemainingPotential.liveCount x.val) :
    Implementation ((RectangularRidgeEpochFactory.factory S.solver a A hA hAn hN hND r).sample x hx) :=
  overhead (sample S a (RectangularRidgeEpochFactory.input A hA hAn hN hND x hx) r) 4

theorem implementation_bounded (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d) (r : ℕ)
    (x : RectangularRidgePhaseAssembly.Point (N := N) (margin N))
    (hx : 32 ≤ RectangularRidgeRemainingPotential.liveCount x.val) :
    Bounded (implementation S a A hA hAn hN hND r x hx)
      (RectangularRidgeCountedAcceptedEpoch.operations S N d r + 10)
      (RectangularRidgeCountedAcceptedEpoch.randomDraws N d r) := by
  have hh := overhead_bounded _ 4
    (sample_bounded S a (RectangularRidgeEpochFactory.input A hA hAn hN hND x hx) r)
  simpa only [Nat.add_assoc] using hh

end MatrixSpencer.RectangularRidgeCountedEpochFactory
