import MatrixSpencer.KSJacobiTraceSqrt
import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# A certified complex trace-square-root report by explicit realification

The numerical input is the real block matrix `[[re A, -im A], [im A, re A]]`.
The real Jacobi trace report runs at tolerance `2ν` and its output is divided by
two. Positive matrix square roots occur only in the specification and proof.
No spectral vector, matrix square root, resolvent, or positive lower eigenvalue
bound is supplied to the numerical procedure. Singular and empty matrices are
included. This module makes no claim about a formal operation-cost model.
-/

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace MatrixSpencer.KSComplexTraceSqrt

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise real arithmetic block representation of a complex matrix. -/
def realification (A : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks (A.map Complex.re) (-(A.map Complex.im))
    (A.map Complex.im) (A.map Complex.re)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem realification_inl_inl (A : Matrix ι ι ℂ) (i j : ι) :
    realification A (.inl i) (.inl j) = (A i j).re := rfl
omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem realification_inl_inr (A : Matrix ι ι ℂ) (i j : ι) :
    realification A (.inl i) (.inr j) = -(A i j).im := rfl
omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem realification_inr_inl (A : Matrix ι ι ℂ) (i j : ι) :
    realification A (.inr i) (.inl j) = (A i j).im := rfl
omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem realification_inr_inr (A : Matrix ι ι ℂ) (i j : ι) :
    realification A (.inr i) (.inr j) = (A i j).re := rfl

omit [DecidableEq ι] in
theorem realification_mul (A B : Matrix ι ι ℂ) :
    realification (A * B) = realification A * realification B := by
  ext (i | i) (j | j) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Complex.mul_re, Complex.mul_im,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib] <;> ring

omit [Fintype ι] [DecidableEq ι] in
theorem realification_conjTranspose (A : Matrix ι ι ℂ) :
    realification Aᴴ = (realification A)ᵀ := by
  ext (i | i) (j | j) <;> simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]

theorem realification_posSemidef (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    (realification A).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hB, realification_mul]
  change (realification Bᴴ * realification B).PosSemidef
  rw [realification_conjTranspose]
  simpa only [Matrix.conjTranspose, star_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (realification B)

theorem realification_sqrt (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    CFC.sqrt (realification A) = realification (CFC.sqrt A) := by
  apply CFC.sqrt_unique
  · rw [← realification_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact (realification_posSemidef _ (CFC.sqrt_nonneg A).posSemidef).nonneg

omit [DecidableEq ι] in
theorem realification_trace (A : Matrix ι ι ℂ) :
    realTrace (realification A) = 2 * realTrace A := by
  simp [realTrace, Matrix.trace, Matrix.diag, Fintype.sum_sum_type, two_mul]

theorem realification_traceSqrt (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    KSJacobiTraceSqrt.traceSqrt (realification A) = 2 * realTrace (CFC.sqrt A) := by
  rw [KSJacobiTraceSqrt.traceSqrt, realification_sqrt A hA, realification_trace]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem sqrt_submatrix_equiv (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (e : κ ≃ ι) :
    CFC.sqrt (A.submatrix e e) = (CFC.sqrt A).submatrix e e := by
  apply CFC.sqrt_unique
  · rw [Matrix.submatrix_mul_equiv, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact ((CFC.sqrt_nonneg A).posSemidef.submatrix e).nonneg

omit [DecidableEq ι] [DecidableEq κ] in
theorem trace_submatrix_equiv (A : Matrix ι ι ℝ) (e : κ ≃ ι) :
    realTrace (A.submatrix e e) = realTrace A := by
  change (∑ i, A (e i) (e i)) = ∑ i, A i i
  exact e.sum_comp (fun i => A i i)

theorem traceSqrt_submatrix_equiv (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (e : κ ≃ ι) :
    KSJacobiTraceSqrt.traceSqrt (A.submatrix e e) = KSJacobiTraceSqrt.traceSqrt A := by
  rw [KSJacobiTraceSqrt.traceSqrt, sqrt_submatrix_equiv A hA e, trace_submatrix_equiv]
  rfl

variable {d : ℕ}

/-- Explicit block representation, with the two copies reindexed to `Fin (d+d)`. -/
def realificationFin (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin (d+d)) (Fin (d+d)) ℝ :=
  (realification A).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem realificationFin_posSemidef (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) :
    (realificationFin A).PosSemidef :=
  (realification_posSemidef A hA).submatrix _

theorem realificationFin_traceSqrt (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) :
    KSJacobiTraceSqrt.traceSqrt (realificationFin A) = 2 * realTrace (CFC.sqrt A) := by
  rw [realificationFin, traceSqrt_submatrix_equiv _ (realification_posSemidef A hA),
    realification_traceSqrt A hA]

/-- The actual report: real Jacobi arithmetic at twice the tolerance, then division by two. -/
def report (A : Matrix (Fin d) (Fin d) ℂ) (ν : ℝ) : ℝ :=
  KSJacobiTraceSqrt.report (realificationFin A) (2 * ν) / 2

/-- Certified absolute error for arbitrary complex PSD inputs, including singular inputs. -/
theorem report_accuracy (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef)
    {ν : ℝ} (hν : 0 < ν) : |report A ν - realTrace (CFC.sqrt A)| ≤ ν := by
  have h := KSJacobiTraceSqrt.report_accuracy (realificationFin A)
    (realificationFin_posSemidef A hA) (ν := 2 * ν) (by positivity)
  rw [realificationFin_traceSqrt A hA] at h
  unfold report
  apply abs_le.mpr
  have h' := abs_le.mp h
  constructor <;> linarith [h'.1, h'.2]

/-- The empty input returns zero without requiring a positive tolerance. -/
theorem report_empty (A : Matrix (Fin 0) (Fin 0) ℂ) (ν : ℝ) : report A ν = 0 := by
  simp [report, KSJacobiTraceSqrt.report]

end MatrixSpencer.KSComplexTraceSqrt
