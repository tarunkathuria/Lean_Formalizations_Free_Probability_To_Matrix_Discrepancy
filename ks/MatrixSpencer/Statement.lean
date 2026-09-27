import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Real.Sqrt

/-!
# The precise square-regime Matrix Spencer proposition

The norm below is defined on continuous linear endomorphisms of Euclidean
space, so it is the spectral operator norm, independently of any matrix
norm scope. The proposition `squareStatement` is a target definition, not
an assertion that the Matrix Spencer theorem has already been proved.
-/

open scoped BigOperators Matrix

namespace MatrixSpencer

/-- Complex square matrices in physical dimension `d`. -/
abbrev CMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- The Euclidean operator norm, explicitly avoiding any implicit matrix norm. -/
noncomputable def spectralNorm {d : ℕ} (A : CMatrix d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A‖

/-- A full signing coefficient is exactly one of the two real signs. -/
def IsSign (s : ℝ) : Prop := s = 1 ∨ s = -1

/-- Every coordinate receives a sign; no zero or unassigned coordinate is allowed. -/
def IsFullSigning {n : ℕ} (ε : Fin n → ℝ) : Prop :=
  ∀ i, IsSign (ε i)

/-- The real signed combination of a complex matrix family. -/
noncomputable def signedSum {n d : ℕ}
    (B : Fin n → CMatrix d) (ε : Fin n → ℝ) : CMatrix d :=
  ∑ i, (ε i : ℂ) • B i

/-- The square-regime conclusion with one prescribed constant for all sizes. -/
def squareStatementWithConstant (C : ℝ) : Prop :=
  ∀ (n d : ℕ), d ≤ n →
    ∀ (B : Fin n → CMatrix d),
      (∀ i, (B i).IsHermitian) →
      (∀ i, spectralNorm (B i) ≤ 1) →
      ∃ ε : Fin n → ℝ,
        IsFullSigning ε ∧
        spectralNorm (signedSum B ε) ≤ C * Real.sqrt (n : ℝ)

/--
The intended Matrix Spencer theorem: one universal positive real constant,
chosen before the matrix count, dimension, and input family.

Allowing zero natural-number parameters adds only trivial cases. In the
nontrivial case, `n` counts matrices and `d ≤ n` bounds physical dimension.
-/
def squareStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ squareStatementWithConstant C

theorem spectralNorm_eq_euclideanOperatorNorm {d : ℕ} (A : CMatrix d) :
    spectralNorm A =
      ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A :
        EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))‖ :=
  rfl

open scoped Matrix.Norms.L2Operator in
theorem spectralNorm_eq_scopedMatrixNorm {d : ℕ} (A : CMatrix d) :
    spectralNorm A = ‖A‖ := by
  exact (Matrix.cstar_norm_def A).symm

theorem isHermitian_iff_conjTranspose_eq {d : ℕ} (A : CMatrix d) :
    A.IsHermitian ↔ Aᴴ = A :=
  Iff.rfl

theorem isHermitian_iff_isSelfAdjoint {d : ℕ} (A : CMatrix d) :
    A.IsHermitian ↔ IsSelfAdjoint A :=
  Iff.rfl

theorem spectralNorm_nonneg {d : ℕ} (A : CMatrix d) :
    0 ≤ spectralNorm A :=
  norm_nonneg _

@[simp] theorem spectralNorm_zero (d : ℕ) :
    spectralNorm (0 : CMatrix d) = 0 := by
  simp [spectralNorm]

@[simp] theorem spectralNorm_neg {d : ℕ} (A : CMatrix d) :
    spectralNorm (-A) = spectralNorm A := by
  simp [spectralNorm]

theorem IsSign.abs_eq_one {s : ℝ} (hs : IsSign s) : |s| = 1 := by
  rcases hs with h | h
  · simp [h]
  · simp [h]

theorem IsSign.sq_eq_one {s : ℝ} (hs : IsSign s) : s ^ 2 = 1 := by
  rcases hs with h | h
  · simp [h]
  · simp [h]

theorem IsSign.neg {s : ℝ} (hs : IsSign s) : IsSign (-s) := by
  rcases hs with h | h
  · right
    simp [h]
  · left
    simp [h]

theorem isFullSigning_one (n : ℕ) :
    IsFullSigning (fun _ : Fin n => (1 : ℝ)) := by
  intro i
  exact Or.inl rfl

theorem IsFullSigning.neg {n : ℕ} {ε : Fin n → ℝ}
    (hε : IsFullSigning ε) : IsFullSigning (fun i => -ε i) := by
  intro i
  exact (hε i).neg

theorem signedSum_isHermitian_of_fullSigning {n d : ℕ}
    (B : Fin n → CMatrix d) (ε : Fin n → ℝ)
    (hB : ∀ i, (B i).IsHermitian) (hε : IsFullSigning ε) :
    (signedSum B ε).IsHermitian := by
  unfold signedSum Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases hε i with hi | hi
  · simpa [hi] using (hB i).eq
  · simpa [hi] using (hB i).neg.eq

theorem spectralNorm_sign_smul {d : ℕ} (A : CMatrix d)
    {s : ℝ} (hs : IsSign s) :
    spectralNorm ((s : ℂ) • A) = spectralNorm A := by
  rcases hs with h | h
  · simp [h]
  · simp [h]

@[simp] theorem signedSum_zeroCount {d : ℕ}
    (B : Fin 0 → CMatrix d) (ε : Fin 0 → ℝ) :
    signedSum B ε = 0 := by
  simp [signedSum]

@[simp] theorem spectralNorm_zeroDimension (A : CMatrix 0) :
    spectralNorm A = 0 := by
  have hA : A = 0 := Subsingleton.elim _ _
  rw [hA]
  exact spectralNorm_zero 0

/-- Empty families admit a full signing with zero discrepancy. -/
theorem zeroCount_signing {d : ℕ} (B : Fin 0 → CMatrix d) :
    ∃ ε : Fin 0 → ℝ,
      IsFullSigning ε ∧ spectralNorm (signedSum B ε) = 0 := by
  refine ⟨fun _ => 1, isFullSigning_one 0, ?_⟩
  simp

/-- Dimension zero is trivial, regardless of the number of labels. -/
theorem zeroDimension_signing {n : ℕ} (B : Fin n → CMatrix 0) :
    ∃ ε : Fin n → ℝ,
      IsFullSigning ε ∧ spectralNorm (signedSum B ε) = 0 := by
  exact ⟨fun _ => 1, isFullSigning_one n, spectralNorm_zeroDimension _⟩

/-- One contraction admits a full signing with the sharp bound `sqrt 1`. -/
theorem oneCount_signing {d : ℕ} (B : Fin 1 → CMatrix d)
    (hB : spectralNorm (B 0) ≤ 1) :
    ∃ ε : Fin 1 → ℝ,
      IsFullSigning ε ∧
        spectralNorm (signedSum B ε) ≤ Real.sqrt (1 : ℝ) := by
  refine ⟨fun _ => 1, isFullSigning_one 1, ?_⟩
  simpa [signedSum] using hB

end MatrixSpencer
