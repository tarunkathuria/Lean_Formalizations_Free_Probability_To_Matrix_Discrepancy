import FaithfulMS.RectangularDirectOriginal
import FaithfulMS.RectangularDirectPolynomialRuntime
noncomputable section
namespace MatrixSpencer.RectangularDirectOriginalRuntime
open RectangularDirectOriginal RectangularRidgeFlatSigning MSCountedSampler
variable {N D : ℕ}
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
def budget (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (N D k : ℕ) : ℕ :=
  RectangularDirectPolynomialRuntime.budget S W N (D + D) k + 1000 * (N + D + 1) ^ 3 + 5

def implementation (hN : 1 ≤ N) (hND : N ≤ D) (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ) :
    Implementation (output hN hND S.service A hA hAn k) := by
  letI : NeZero D := ⟨by omega⟩
  letI : NeZero (D + D) := ⟨by omega⟩
  exact MSCountedSampler.overhead
    (RectangularDirectPolynomialRuntime.implementation S W ⟨0, by omega⟩
      (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn) hN (by omega) k)
    ((RealRAM.MSOriginalInput.setup A).cost + 5)

theorem implementation_bounded (hN : 1 ≤ N) (hND : N ≤ D) (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ) :
    Bounded (implementation hN hND S W A hA hAn k) (budget S W N D k)
      (RectangularDirectPolynomialRuntime.randomDraws N (D + D) k) := by
  letI : NeZero D := ⟨by omega⟩
  letI : NeZero (D + D) := ⟨by omega⟩
  have hb := MSCountedSampler.overhead_bounded
    (RectangularDirectPolynomialRuntime.implementation S W ⟨0, by omega⟩
      (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn) hN (by omega) k)
    ((RealRAM.MSOriginalInput.setup A).cost + 5)
    (RectangularDirectPolynomialRuntime.implementation_bounded S W ⟨0, by omega⟩
      (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn) hN (by omega) k)
  have hs := RealRAM.MSOriginalInput.setup_cost A
  intro z out cost draws he
  have hh := hb z out cost draws he
  unfold budget
  constructor <;> omega

/-- Every prospective branch, successful or failed, has a finite execution
within the same explicit polynomial operation and random-draw budgets. -/
theorem execution_bounded (hN : 1 ≤ N) (hND : N ≤ D) (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ)
    (z : (output hN hND S.service A hA hAn k).Draws) :
    ∃ cost draws, (implementation hN hND S W A hA hAn k).Executes z
      ((output hN hND S.service A hA hAn k).value z) cost draws ∧
        cost ≤ budget S W N D k ∧ draws ≤ RectangularDirectPolynomialRuntime.randomDraws N (D + D) k :=
  MSCountedSampler.execution_bounded (implementation hN hND S W A hA hAn k)
    (implementation_bounded hN hND S W A hA hAn k) z


end MatrixSpencer.RectangularDirectOriginalRuntime
