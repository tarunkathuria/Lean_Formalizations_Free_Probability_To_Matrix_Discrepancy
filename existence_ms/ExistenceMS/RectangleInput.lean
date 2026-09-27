import ExistenceMS.RectangleWalk
import ExistenceMS.ExactValue
import MatrixSpencer.RectangularRidgeFlatSigning

/-! Original matrix input and positive-mass extraction for the revised
rectangular walk. The value specification is constructed in this package. -/
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace ExistenceMS.RectangleInput
open MatrixSpencer
open RectangularRidgeFlatSigning
open MSManuscriptAdaptive (Sampler)
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
  exact RectangleWalk.output solver ⟨0, by omega⟩
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
  have hh := RectangleWalk.output_sound solver ⟨0, by omega⟩
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
  exact RectangleWalk.output_probability solver ⟨0, by omega⟩
    (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn) hN (by omega) k

/-- Pure existence follows from positive mass of the actual walk, using an
exact value specification. This does not assert computation of suprema. -/
theorem exists_signing (hN : 1 ≤ N) (hND : N ≤ D) (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) :
    ∃ ε : Fin N → ℝ, IsFullSigning ε ∧ spectralNorm (signedSum A ε) ≤ discrepancyBound N D := by
  classical
  let P := output hN hND ExactValue.family A hA hAn 1
  have hp := output_probability hN hND ExactValue.family A hA hAn 1
  have hx : ∃ z, (P.value z).isSome = true := by
    by_contra hn
    have hz : ∀ z, (P.value z).isSome = false := by simpa using hn
    change 1 - (1 / 2 : ℝ) ^ 1 ≤ ∑ z, P.weight z * (if (P.value z).isSome then 1 else 0) at hp
    simp only [hz, Bool.false_eq_true, ↓reduceIte, mul_zero, Finset.sum_const_zero] at hp
    norm_num at hp
  obtain ⟨z, hz⟩ := hx
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hz
  exact ⟨WithLp.ofLp y.val, output_sound hN hND ExactValue.family
    A hA hAn 1 z y hy⟩

end ExistenceMS.RectangleInput
