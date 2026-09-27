import FaithfulMS.RectangularDirectPolynomialAlgorithm
import MatrixSpencer.RectangularRidgeFlatSigning
import MatrixSpencer.RectangularRidgeExactValue
import MatrixSpencer.RealRAMMSOriginalInput

/-! End-to-end rectangular Matrix Spencer on the original Hermitian matrices.
The sampler is the actual finite walk on the explicitly materialized signed
lift. Successful outputs are full signings with the two-sided operator bound.
All branches have the counted real-RAM cost bound, including preprocessing.
Only runtime uses the permitted polynomial affine-SDP solver contract. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectOriginal
open RectangularRidgeFlatSigning
open MSManuscriptAdaptive (Sampler)
open MSCountedSampler (Implementation Bounded)
open RectangularRidgePhaseAssembly (Point)
open RectangularRidgeEpochInput (margin)
variable {N D : ℕ}
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def output (hN : 1 ≤ N) (hND : N ≤ D) (solver : RectangularDirectSolver.Service)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ) :
    Sampler (Option (Point (N := N) (margin N))) := by
  letI : NeZero D := ⟨by omega⟩
  letI : NeZero (D + D) := ⟨by omega⟩
  exact RectangularDirectPolynomialAlgorithm.output solver ⟨0, by omega⟩
    (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn) hN (by omega) k

def discrepancyBound (N D : ℕ) : ℝ :=
  8102676 * Real.sqrt ((N : ℝ) * (1 + Real.log ((2 * (D : ℝ)) / N)))

theorem output_sound (hN : 1 ≤ N) (hND : N ≤ D) (solver : RectangularDirectSolver.Service)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ)
    (z : (output hN hND solver A hA hAn k).Draws) (y : Point (N := N) (margin N))
    (ho : (output hN hND solver A hA hAn k).value z = some y) :
    IsFullSigning (WithLp.ofLp y.val) ∧
      spectralNorm (signedSum A (WithLp.ofLp y.val)) ≤ discrepancyBound N D := by
  letI : NeZero D := ⟨by omega⟩
  letI : NeZero (D + D) := ⟨by omega⟩
  have hh := RectangularDirectPolynomialAlgorithm.output_sound solver ⟨0, by omega⟩
    (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn) hN (by omega) k z y ho
  have hf := completed_spectral_bound hN (show N ≤ D + D by omega) A hA hAn y.val hh.1
    (K := 27) (by norm_num) hh.2
  norm_num only [discrepancyBound, mul_add, mul_one, Nat.cast_ofNat] at hf ⊢
  convert hf using 1 <;> norm_num

theorem output_probability (hN : 1 ≤ N) (hND : N ≤ D) (solver : RectangularDirectSolver.Service)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ) :
    1 - (1 / 2 : ℝ) ^ k ≤ ∑ z, (output hN hND solver A hA hAn k).weight z *
      (if ((output hN hND solver A hA hAn k).value z).isSome then 1 else 0) := by
  letI : NeZero D := ⟨by omega⟩
  letI : NeZero (D + D) := ⟨by omega⟩
  exact RectangularDirectPolynomialAlgorithm.output_probability solver ⟨0, by omega⟩
    (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn) hN (by omega) k

/-- The finite array constructor supplies precisely the family used by the
walk. The extra fields it constructs are harmless and also charged. -/
theorem preprocessing_value (A : Fin N → CMatrix D) :
    (RealRAM.MSOriginalInput.setup A).value.flat = flat A :=
  RealRAM.MSOriginalInput.flat_value A

end MatrixSpencer.RectangularDirectOriginal
