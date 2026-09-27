import MatrixSpencer.KSComplexTraceSqrt
import MatrixSpencer.KSJacobiMatrixProjection
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Realification geometry for the complex matrix projection report

All coordinate transformations below are explicit real/imaginary entry formulas.
The complex extraction is averaging with the fixed complex structure, followed
by reading the resulting real blocks. No spectral choices occur in these maps.
-/

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace MatrixSpencer.KSComplexProjectionGeometry

open KSComplexTraceSqrt KSJacobiMatrixProjection
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fixed real complex structure. -/
def complexStructure : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks 0 (-1) 1 0

/-- Arithmetic extraction of the averaged complex-linear component. -/
def extract (P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) : Matrix ι ι ℂ := fun i j =>
  ⟨(P (.inl i) (.inl j) + P (.inr i) (.inr j)) / 2,
   (P (.inr i) (.inl j) - P (.inl i) (.inr j)) / 2⟩

/-- A fixed compression matrix used only to prove positivity of the arithmetic extraction. -/
def compression : Matrix (ι ⊕ ι) ι ℂ :=
  Matrix.fromRows 1 (-Complex.I • (1 : Matrix ι ι ℂ))

theorem complexStructure_orthogonal :
    (complexStructure (ι := ι))ᵀ * complexStructure = 1 := by
  ext (i | i) (j | j) <;>
    simp [complexStructure, Matrix.transpose_apply, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.one_apply, eq_comm]

theorem complexStructure_twist (P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    conjugate complexStructure P = Matrix.fromBlocks
      (P.submatrix Sum.inr Sum.inr) (-(P.submatrix Sum.inr Sum.inl))
      (-(P.submatrix Sum.inl Sum.inr)) (P.submatrix Sum.inl Sum.inl) := by
  ext (i | i) (j | j) <;>
    simp [conjugate, complexStructure, Matrix.transpose_apply, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.one_apply]

theorem realification_extract (P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    realification (extract P) = (1 / 2 : ℝ) • (P + conjugate complexStructure P) := by
  rw [complexStructure_twist]
  ext (i | i) (j | j) <;> simp [extract, Matrix.submatrix_apply] <;> ring

omit [Fintype ι] [DecidableEq ι] in
theorem extract_realification (A : Matrix ι ι ℂ) : extract (realification A) = A := by
  ext i j
  apply Complex.ext <;> simp [extract]

theorem extract_compression (P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    extract P = (1 / 2 : ℝ) • (compressionᴴ * realMatrixEmbedding P * compression) := by
  ext i j
  apply Complex.ext <;>
    simp [extract, compression, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_sum_type, Matrix.one_apply, apply_ite, Complex.mul_re, Complex.mul_im] <;> ring

theorem extract_posSemidef (P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (hP : P.PosSemidef) :
    (extract P).PosSemidef := by
  rw [extract_compression]
  exact ((realMatrixEmbedding_posSemidef P hP).conjTranspose_mul_mul_same compression).smul
    (by norm_num)

theorem realification_reflects_posSemidef (A : Matrix ι ι ℂ)
    (hA : (realification A).PosSemidef) : A.PosSemidef := by
  simpa only [extract_realification] using extract_posSemidef (realification A) hA

omit [Fintype ι] [DecidableEq ι] in
theorem realification_sub (A B : Matrix ι ι ℂ) :
    realification (A - B) = realification A - realification B := by
  ext (i | i) (j | j) <;> simp
  ring

omit [Fintype ι] in
theorem realification_scalar (a : ℝ) :
    realification (a • (1 : Matrix ι ι ℂ)) = a • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
  ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [hij]

theorem realification_le_iff {A B : Matrix ι ι ℂ} : realification A ≤ realification B ↔ A ≤ B := by
  rw [Matrix.le_iff, Matrix.le_iff, ← realification_sub]
  exact ⟨realification_reflects_posSemidef _, realification_posSemidef _⟩

omit [Fintype ι] [DecidableEq ι] in
theorem realification_symmetric (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (realification A).IsSymm := by
  change (realification A)ᵀ = realification A
  rw [← realification_conjTranspose, hA.eq]

omit [Fintype ι] [DecidableEq ι] in
theorem extract_sub (P Q : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    extract (P - Q) = extract P - extract Q := by
  ext i j
  apply Complex.ext <;> simp [extract] <;> ring

omit [Fintype ι] in
theorem extract_scalar (a : ℝ) :
    extract (a • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)) = a • (1 : Matrix ι ι ℂ) := by
  rw [← realification_scalar, extract_realification]

omit [Fintype ι] [DecidableEq ι] in
theorem extract_hermitian (P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (hP : P.IsSymm) :
    (extract P).IsHermitian := by
  ext i j
  apply Complex.ext <;> simp [Matrix.conjTranspose_apply, extract]
  · rw [hP.apply (.inl i) (.inl j), hP.apply (.inr i) (.inr j)]
  · rw [hP.apply (.inl i) (.inr j), hP.apply (.inr i) (.inl j)]
    ring

omit [DecidableEq ι] in
theorem extract_trace (P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    realTrace (extract P) = Matrix.trace P / 2 := by
  simp only [realTrace, Matrix.trace, Matrix.diag, extract, RCLike.re_to_complex,
    map_sum, Fintype.sum_sum_type]
  change (∑ i, (P (.inl i) (.inl i) + P (.inr i) (.inr i)) / 2) = _
  rw [← Finset.sum_div, Finset.sum_add_distrib]

/-- Real Euclidean inner product of the real and imaginary matrix-entry coordinates. -/
def complexInner (A B : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ∑ j, ((A i j).re * (B i j).re + (A i j).im * (B i j).im)

/-- The squared ordinary complex Frobenius norm. -/
def complexEnergy (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

omit [DecidableEq ι] in
theorem complexEnergy_nonneg (A : Matrix ι ι ℂ) : 0 ≤ complexEnergy A :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [DecidableEq ι] in
theorem complexInner_self (A : Matrix ι ι ℂ) : complexInner A A = complexEnergy A := by
  simp only [complexInner, complexEnergy, Complex.sq_norm, Complex.normSq_apply]

omit [DecidableEq ι] in
theorem realification_inner (A B : Matrix ι ι ℂ) :
    frobeniusInner (realification A) (realification B) = 2 * complexInner A B := by
  simp only [frobeniusInner, complexInner, Fintype.sum_sum_type,
    realification_inl_inl, realification_inl_inr, realification_inr_inl, realification_inr_inr,
    neg_mul_neg, Finset.sum_add_distrib]
  ring

omit [DecidableEq ι] in
theorem realification_energy (A : Matrix ι ι ℂ) :
    KSJacobiStep.frobeniusEnergy (realification A) = 2 * complexEnergy A := by
  rw [← frobeniusInner_self, realification_inner, complexInner_self]

omit [DecidableEq ι] in
theorem extract_energy_le (P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    complexEnergy (extract P) ≤ KSJacobiStep.frobeniusEnergy P / 2 := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (f := fun i =>
      ∑ j, ‖extract P i j‖ ^ 2) (g := fun i => ∑ j,
      (P (.inl i) (.inl j) ^ 2 + P (.inl i) (.inr j) ^ 2 +
        P (.inr i) (.inl j) ^ 2 + P (.inr i) (.inr j) ^ 2) / 2) (by
    intro i _
    apply Finset.sum_le_sum
    intro j _
    simp only [extract, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (P (.inl i) (.inl j) - P (.inr i) (.inr j)),
      sq_nonneg (P (.inr i) (.inl j) + P (.inl i) (.inr j))])
  convert h using 1
  simp only [KSJacobiStep.frobeniusEnergy, Fintype.sum_sum_type,
    Finset.sum_add_distrib, ← Finset.sum_div]
  ring

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem reindex_inner (A B : Matrix ι ι ℝ) (e : κ ≃ ι) :
    frobeniusInner (A.submatrix e e) (B.submatrix e e) = frobeniusInner A B := by
  unfold frobeniusInner
  change (∑ i, ∑ j, A (e i) (e j) * B (e i) (e j)) = ∑ i, ∑ j, A i j * B i j
  calc
    _ = ∑ i, ∑ j, A (e i) j * B (e i) j := by
      apply Finset.sum_congr rfl
      intro i _
      exact e.sum_comp (fun j => A (e i) j * B (e i) j)
    _ = _ := e.sum_comp (fun i => ∑ j, A i j * B i j)

omit [DecidableEq ι] [DecidableEq κ] in
theorem reindex_energy (A : Matrix ι ι ℝ) (e : κ ≃ ι) :
    KSJacobiStep.frobeniusEnergy (A.submatrix e e) = KSJacobiStep.frobeniusEnergy A := by
  rw [← frobeniusInner_self, reindex_inner, frobeniusInner_self]

omit [Fintype ι] [Fintype κ] in
theorem reindex_scalar (a : ℝ) (e : κ ≃ ι) :
    (a • (1 : Matrix ι ι ℝ)).submatrix e e = a • (1 : Matrix κ κ ℝ) := by
  ext i j
  simp [Matrix.submatrix_apply, Matrix.one_apply, e.injective.eq_iff]

theorem reindex_feasible (A : Matrix ι ι ℝ) (e : κ ≃ ι) {a s : ℝ}
    (hA : Feasible a s A) : Feasible a s (A.submatrix e e) := by
  refine ⟨hA.1.submatrix e, ?_, ?_⟩
  · apply Matrix.le_iff.mpr
    have h := (Matrix.le_iff.mp hA.2.1).submatrix e
    change (A.submatrix e e - (a • (1 : Matrix ι ι ℝ)).submatrix e e).PosSemidef at h
    rw [reindex_scalar] at h
    exact h
  · have h := trace_submatrix_equiv A e
    change Matrix.trace (A.submatrix e e) = Matrix.trace A at h
    exact h.trans hA.2.2

omit [DecidableEq ι] [DecidableEq κ] in
theorem reindex_conjugate (U A : Matrix ι ι ℝ) (e : κ ≃ ι) :
    conjugate (U.submatrix e e) (A.submatrix e e) = (conjugate U A).submatrix e e := by
  simp only [conjugate, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]

variable {d : ℕ}

/-- Move a real `2d` matrix to its two labelled blocks, using a fixed finite equivalence. -/
def toBlocks (P : Matrix (Fin (d+d)) (Fin (d+d)) ℝ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ :=
  P.submatrix finSumFinEquiv finSumFinEquiv

def extractFin (P : Matrix (Fin (d+d)) (Fin (d+d)) ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  extract (toBlocks P)

def complexStructureFin : Matrix (Fin (d+d)) (Fin (d+d)) ℝ :=
  (complexStructure (ι := Fin d)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem toBlocks_realificationFin (A : Matrix (Fin d) (Fin d) ℂ) :
    toBlocks (realificationFin A) = realification A := by
  ext i j
  change realification A (finSumFinEquiv.symm (finSumFinEquiv i))
    (finSumFinEquiv.symm (finSumFinEquiv j)) = realification A i j
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem extractFin_realificationFin (A : Matrix (Fin d) (Fin d) ℂ) :
    extractFin (realificationFin A) = A := by
  rw [extractFin, toBlocks_realificationFin, extract_realification]

theorem extractFin_sub (P Q : Matrix (Fin (d+d)) (Fin (d+d)) ℝ) :
    extractFin (P - Q) = extractFin P - extractFin Q := by
  change extract (toBlocks P - toBlocks Q) = extract (toBlocks P) - extract (toBlocks Q)
  exact extract_sub _ _

theorem extractFin_energy_le (P : Matrix (Fin (d+d)) (Fin (d+d)) ℝ) :
    complexEnergy (extractFin P) ≤ KSJacobiStep.frobeniusEnergy P / 2 := by
  have h := extract_energy_le (toBlocks P)
  rw [toBlocks, reindex_energy] at h
  exact h

theorem realificationFin_inner (A B : Matrix (Fin d) (Fin d) ℂ) :
    frobeniusInner (realificationFin A) (realificationFin B) = 2 * complexInner A B := by
  rw [realificationFin, realificationFin, reindex_inner, realification_inner]

theorem realificationFin_energy (A : Matrix (Fin d) (Fin d) ℂ) :
    KSJacobiStep.frobeniusEnergy (realificationFin A) = 2 * complexEnergy A := by
  rw [realificationFin, reindex_energy, realification_energy]

/-- Full complex Hermitian density domain, with a floor and prescribed real trace. -/
def ComplexFeasible (a s : ℝ) (P : Matrix ι ι ℂ) : Prop :=
  P.IsHermitian ∧ a • (1 : Matrix ι ι ℂ) ≤ P ∧ realTrace P = s

theorem realification_feasible {a s : ℝ} (A : Matrix ι ι ℂ) (hA : ComplexFeasible a s A) :
    Feasible a (2 * s) (realification A) := by
  refine ⟨realification_symmetric A hA.1, ?_, ?_⟩
  · rw [← realification_scalar]
    exact realification_le_iff.mpr hA.2.1
  · change realTrace (realification A) = 2 * s
    rw [realification_trace, hA.2.2]

theorem extract_feasible {a s : ℝ} (P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (hP : Feasible a (2 * s) P) : ComplexFeasible a s (extract P) := by
  refine ⟨extract_hermitian P hP.1, ?_, ?_⟩
  · apply Matrix.le_iff.mpr
    have h := extract_posSemidef (P - a • 1) (Matrix.le_iff.mp hP.2.1)
    rw [extract_sub, extract_scalar] at h
    exact h
  · rw [extract_trace, hP.2.2]
    ring

theorem realificationFin_feasible {a s : ℝ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : ComplexFeasible a s A) : Feasible a (2 * s) (realificationFin A) :=
  reindex_feasible _ _ (realification_feasible A hA)

theorem extractFin_feasible {a s : ℝ} (P : Matrix (Fin (d+d)) (Fin (d+d)) ℝ)
    (hP : Feasible a (2 * s) P) : ComplexFeasible a s (extractFin P) :=
  extract_feasible _ (reindex_feasible P finSumFinEquiv hP)

theorem realificationFin_symmetric (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    (realificationFin A).IsSymm := (realification_symmetric A hA).submatrix _

theorem realificationFin_sub (A B : Matrix (Fin d) (Fin d) ℂ) :
    realificationFin (A - B) = realificationFin A - realificationFin B := by
  unfold realificationFin
  rw [realification_sub]
  rfl

theorem toBlocks_inverse (P : Matrix (Fin (d+d)) (Fin (d+d)) ℝ) :
    (toBlocks P).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = P := by
  ext i j
  change P (finSumFinEquiv (finSumFinEquiv.symm i))
    (finSumFinEquiv (finSumFinEquiv.symm j)) = P i j
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem realificationFin_extractFin (P : Matrix (Fin (d+d)) (Fin (d+d)) ℝ) :
    realificationFin (extractFin P) =
      (1 / 2 : ℝ) • (P + conjugate complexStructureFin P) := by
  unfold realificationFin extractFin
  rw [realification_extract]
  change (1 / 2 : ℝ) • ((toBlocks P).submatrix finSumFinEquiv.symm finSumFinEquiv.symm +
    (conjugate complexStructure (toBlocks P)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) = _
  rw [← reindex_conjugate, toBlocks_inverse]
  rfl

theorem complexStructureFin_orthogonal :
    (complexStructureFin (d := d))ᵀ * complexStructureFin = 1 := by
  unfold complexStructureFin
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, complexStructure_orthogonal]
  simp

theorem complexStructure_fixes_realification (A : Matrix ι ι ℂ) :
    conjugate complexStructure (realification A) = realification A := by
  rw [complexStructure_twist]
  ext (i | i) (j | j) <;> simp

theorem complexStructureFin_fixes_realification (A : Matrix (Fin d) (Fin d) ℂ) :
    conjugate complexStructureFin (realificationFin A) = realificationFin A := by
  unfold complexStructureFin realificationFin
  rw [reindex_conjugate, complexStructure_fixes_realification]

theorem realificationFin_extractFin_of_fixed (P : Matrix (Fin (d+d)) (Fin (d+d)) ℝ)
    (hP : conjugate complexStructureFin P = P) : realificationFin (extractFin P) = P := by
  rw [realificationFin_extractFin, hP]
  module

end MatrixSpencer.KSComplexProjectionGeometry
