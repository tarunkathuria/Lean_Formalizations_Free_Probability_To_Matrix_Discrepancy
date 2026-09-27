import MatrixSpencer.RectangularRidgePolynomialRuntime
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
namespace MatrixSpencer.RectangularRidgeOriginalAlgorithm
open RectangularRidgeFlatSigning
open MSManuscriptAdaptive (Sampler)
open MSCountedSampler (Implementation Bounded)
open RectangularRidgePhaseAssembly (Point)
open RectangularRidgeEpochInput (margin)
variable {N D : ℕ}
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def output (hN : 1 ≤ N) (hND : N ≤ D) (solver : RectangularRidgeConvexValue.Solver)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ) :
    Sampler (Option (Point (N := N) (margin N))) := by
  letI : NeZero D := ⟨by omega⟩
  letI : NeZero (D + D) := ⟨by omega⟩
  exact RectangularRidgePolynomialAlgorithm.output solver ⟨0, by omega⟩
    (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn) hN (by omega) k

def discrepancyBound (N D : ℕ) : ℝ :=
  8102676 * Real.sqrt ((N : ℝ) * (1 + Real.log ((2 * (D : ℝ)) / N)))

theorem output_sound (hN : 1 ≤ N) (hND : N ≤ D) (solver : RectangularRidgeConvexValue.Solver)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ)
    (z : (output hN hND solver A hA hAn k).Draws) (y : Point (N := N) (margin N))
    (ho : (output hN hND solver A hA hAn k).value z = some y) :
    IsFullSigning (WithLp.ofLp y.val) ∧
      spectralNorm (signedSum A (WithLp.ofLp y.val)) ≤ discrepancyBound N D := by
  letI : NeZero D := ⟨by omega⟩
  letI : NeZero (D + D) := ⟨by omega⟩
  have hh := RectangularRidgePolynomialAlgorithm.output_sound solver ⟨0, by omega⟩
    (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn) hN (by omega) k z y ho
  have hf := completed_spectral_bound hN (show N ≤ D + D by omega) A hA hAn y.val hh.1
    (K := 27) (by norm_num) hh.2
  norm_num only [discrepancyBound, mul_add, mul_one, Nat.cast_ofNat] at hf ⊢
  convert hf using 1 <;> norm_num

theorem output_probability (hN : 1 ≤ N) (hND : N ≤ D) (solver : RectangularRidgeConvexValue.Solver)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ) :
    1 - (1 / 2 : ℝ) ^ k ≤ ∑ z, (output hN hND solver A hA hAn k).weight z *
      (if ((output hN hND solver A hA hAn k).value z).isSome then 1 else 0) := by
  letI : NeZero D := ⟨by omega⟩
  letI : NeZero (D + D) := ⟨by omega⟩
  exact RectangularRidgePolynomialAlgorithm.output_probability solver ⟨0, by omega⟩
    (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn) hN (by omega) k

/-- The finite array constructor supplies precisely the family used by the
walk. The extra fields it constructs are harmless and also charged. -/
theorem preprocessing_value (A : Fin N → CMatrix D) :
    (RealRAM.MSOriginalInput.setup A).value.flat = flat A :=
  RealRAM.MSOriginalInput.flat_value A

def budget (S : RectangularRidgeConvexValue.PolynomialSolver) (N D k : ℕ) : ℕ :=
  RectangularRidgePolynomialRuntime.budget S N (D + D) k + 1000 * (N + D + 1) ^ 3 + 5

def implementation (hN : 1 ≤ N) (hND : N ≤ D) (S : RectangularRidgeConvexValue.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ) :
    Implementation (output hN hND S.solver A hA hAn k) := by
  letI : NeZero D := ⟨by omega⟩
  letI : NeZero (D + D) := ⟨by omega⟩
  exact MSCountedSampler.overhead
    (RectangularRidgePolynomialRuntime.implementation S ⟨0, by omega⟩
      (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn) hN (by omega) k)
    ((RealRAM.MSOriginalInput.setup A).cost + 5)

theorem implementation_bounded (hN : 1 ≤ N) (hND : N ≤ D) (S : RectangularRidgeConvexValue.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ) :
    Bounded (implementation hN hND S A hA hAn k) (budget S N D k)
      (RectangularRidgePolynomialRuntime.randomDraws N (D + D) k) := by
  letI : NeZero D := ⟨by omega⟩
  letI : NeZero (D + D) := ⟨by omega⟩
  have hb := MSCountedSampler.overhead_bounded
    (RectangularRidgePolynomialRuntime.implementation S ⟨0, by omega⟩
      (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn) hN (by omega) k)
    ((RealRAM.MSOriginalInput.setup A).cost + 5)
    (RectangularRidgePolynomialRuntime.implementation_bounded S ⟨0, by omega⟩
      (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn) hN (by omega) k)
  have hs := RealRAM.MSOriginalInput.setup_cost A
  intro z out cost draws he
  have hh := hb z out cost draws he
  unfold budget
  constructor <;> omega

/-- Every prospective branch, successful or failed, has a finite execution
within the same explicit polynomial operation and random-draw budgets. -/
theorem execution_bounded (hN : 1 ≤ N) (hND : N ≤ D) (S : RectangularRidgeConvexValue.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ)
    (z : (output hN hND S.solver A hA hAn k).Draws) :
    ∃ cost draws, (implementation hN hND S A hA hAn k).Executes z
      ((output hN hND S.solver A hA hAn k).value z) cost draws ∧
        cost ≤ budget S N D k ∧ draws ≤ RectangularRidgePolynomialRuntime.randomDraws N (D + D) k :=
  MSCountedSampler.execution_bounded (implementation hN hND S A hA hAn k)
    (implementation_bounded hN hND S A hA hAn k) z

/-- Pure existence follows from positive mass of the actual walk, using an
exact value specification. This does not assert computation of suprema. -/
theorem exists_signing (hN : 1 ≤ N) (hND : N ≤ D) (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) :
    ∃ ε : Fin N → ℝ, IsFullSigning ε ∧ spectralNorm (signedSum A ε) ≤ discrepancyBound N D := by
  classical
  let P := output hN hND RectangularRidgeExactValue.exactSolver A hA hAn 1
  have hp := output_probability hN hND RectangularRidgeExactValue.exactSolver A hA hAn 1
  have hx : ∃ z, (P.value z).isSome = true := by
    by_contra hn
    have hz : ∀ z, (P.value z).isSome = false := by simpa using hn
    change 1 - (1 / 2 : ℝ) ^ 1 ≤ ∑ z, P.weight z * (if (P.value z).isSome then 1 else 0) at hp
    simp only [hz, Bool.false_eq_true, ↓reduceIte, mul_zero, Finset.sum_const_zero] at hp
    norm_num at hp
  obtain ⟨z, hz⟩ := hx
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hz
  exact ⟨WithLp.ofLp y.val, output_sound hN hND RectangularRidgeExactValue.exactSolver
    A hA hAn 1 z y hy⟩

end MatrixSpencer.RectangularRidgeOriginalAlgorithm
