import FaithfulMS.RectangularDirectPrograms
import FaithfulMS.RectangularDirectCountedAcceptedEpoch
import FaithfulMS.RectangularDirectEpochFactory

/-! The concrete counted accepted epoch is inserted into the proved epoch
factory. Projection reads the existing point/time fields; configuration
construction copies existing input references and erases only proofs. -/
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectCountedEpochFactory
open RectangularRidgeEpochInput RectangularDirectEpochRun
open MSManuscriptAdaptive MSCountedSampler
open RealRAM.JacobiIteration (Counted)
variable {N d : ℕ} [Nonempty (Fin d)]

def project (c : Config N d) : Option (Certified c) →
    Counted (Option (RectangularRidgePhaseAssembly.Point (N := N) (margin N) × ℝ))
  | none => ⟨none, 1⟩
  | some s => ⟨some (RectangularDirectEpochFactory.project c s), 4⟩

omit [Nonempty (Fin d)] in
theorem project_value (c : Config N d) (s : Option (Certified c)) :
    (project c s).value = s.map (RectangularDirectEpochFactory.project c) := by
  cases s <;> rfl

def sample (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (c : Config N d) (r : ℕ) :
    Implementation (RectangularDirectEpochFactory.sample S.service a c r) :=
  congr (by
    have he : (fun s => (project c s).value) = Option.map (RectangularDirectEpochFactory.project c) := by
      funext s
      exact project_value c s
    rw [he]
    rfl)
    (map (RectangularDirectCountedAcceptedEpoch.implementation S W a c r) (project c))

theorem sample_bounded (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (c : Config N d) (r : ℕ) :
    Bounded (sample S W a c r) (RectangularDirectCountedAcceptedEpoch.operations S W N d r + 6)
      (RectangularDirectCountedAcceptedEpoch.randomDraws N d r) := by
  apply congr_bounded
  exact map_bounded _ (project c) (RectangularDirectCountedAcceptedEpoch.implementation_bounded S W a c r)
    (fun s => by cases s <;> norm_num [project])

def implementation (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d) (r : ℕ)
    (x : RectangularRidgePhaseAssembly.Point (N := N) (margin N))
    (hx : 32 ≤ RectangularRidgeRemainingPotential.liveCount x.val) :
    Implementation ((RectangularDirectEpochFactory.factory S.service a A hA hAn hN hND r).sample x hx) :=
  overhead (sample S W a (RectangularDirectEpochFactory.input A hA hAn hN hND x hx) r) 4

theorem implementation_bounded (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d) (r : ℕ)
    (x : RectangularRidgePhaseAssembly.Point (N := N) (margin N))
    (hx : 32 ≤ RectangularRidgeRemainingPotential.liveCount x.val) :
    Bounded (implementation S W a A hA hAn hN hND r x hx)
      (RectangularDirectCountedAcceptedEpoch.operations S W N d r + 10)
      (RectangularDirectCountedAcceptedEpoch.randomDraws N d r) := by
  have hh := overhead_bounded _ 4
    (sample_bounded S W a (RectangularDirectEpochFactory.input A hA hAn hN hND x hx) r)
  simpa only [Nat.add_assoc] using hh

end MatrixSpencer.RectangularDirectCountedEpochFactory
