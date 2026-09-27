import MatrixSpencer.SpectralDensity
import MatrixSpencer.OwnerBounds

/-!
# The common signed block lift

The lift of each input is B ⊕ (−B). Real combinations commute with this
construction. The actual potential of the lifted center controls the
original Euclidean operator norm.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace MatrixSpencer

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance signedLiftBaseCStarAlgebra : CStarAlgebra (Matrix n n ℂ) := {}
local instance signedLiftSumCStarAlgebra : CStarAlgebra (Matrix (n ⊕ n) (n ⊕ n) ℂ) := {}

def signedLift (B : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks B 0 0 (-B)

omit [Fintype n] [DecidableEq n] in
theorem signedLift_isHermitian {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    (signedLift B).IsHermitian :=
  Matrix.IsHermitian.fromBlocks hB (by simp) hB.neg

/-- Positive block-diagonal matrices are positive, without invertibility assumptions. -/
theorem posSemidef_fromBlocks_diagonal {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix n n ℂ} {B : Matrix m m ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self
    (Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B))
  simpa only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq,
    (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    CFC.sqrt_mul_sqrt_self A hA.nonneg, CFC.sqrt_mul_sqrt_self B hB.nonneg] using h

/-- Block order is the actual positive-semidefinite order. -/
theorem fromBlocks_diagonal_mono {m : Type*} [Fintype m] [DecidableEq m]
    {A A' : Matrix n n ℂ} {B B' : Matrix m m ℂ} (hA : A ≤ A') (hB : B ≤ B') :
    Matrix.fromBlocks A 0 0 B ≤ Matrix.fromBlocks A' 0 0 B' := by
  have hp := posSemidef_fromBlocks_diagonal (sub_nonneg.mpr hA).posSemidef
    (sub_nonneg.mpr hB).posSemidef
  have heq : Matrix.fromBlocks (A' - A) 0 0 (B' - B) =
      Matrix.fromBlocks A' 0 0 B' - Matrix.fromBlocks A 0 0 B := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks]
  rw [heq] at hp
  exact sub_nonneg.mp hp.nonneg

/-- A Hermitian norm bound follows from both spectral order bounds. -/
theorem hermitian_norm_le_of_order [Nonempty n] {B : Matrix n n ℂ} (hB : B.IsHermitian)
    {r : ℝ} (hlo : -(r • (1 : Matrix n n ℂ)) ≤ B) (hhi : B ≤ r • (1 : Matrix n n ℂ)) :
    ‖B‖ ≤ r := by
  have hu : B ≤ algebraMap ℝ (Matrix n n ℂ) r := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hhi
  have hl : algebraMap ℝ (Matrix n n ℂ) (-r) ≤ B := by
    simpa only [Algebra.algebraMap_eq_smul_one, neg_smul] using hlo
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum hB with h | h
  · exact (le_algebraMap_iff_spectrum_le hB).mp hu _ h
  · have hh := (algebraMap_le_iff_le_spectrum hB).mp hl _ h
    linarith

/-- The lift preserves the contraction hypothesis in the spectral norm. -/
theorem signedLift_norm_le [Nonempty n] {B : Matrix n n ℂ} (hB : B.IsHermitian)
    {r : ℝ} (hN : ‖B‖ ≤ r) : ‖signedLift B‖ ≤ r := by
  have hu : B ≤ r • (1 : Matrix n n ℂ) := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self hB
    rw [Algebra.algebraMap_eq_smul_one] at h
    exact h.trans (smul_le_smul_of_nonneg_right hN zero_le_one)
  have hun : -B ≤ r • (1 : Matrix n n ℂ) := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self hB.neg
    rw [Algebra.algebraMap_eq_smul_one, norm_neg] at h
    exact h.trans (smul_le_smul_of_nonneg_right hN zero_le_one)
  have hl : -(r • (1 : Matrix n n ℂ)) ≤ B := neg_le.mp hun
  have hln : -(r • (1 : Matrix n n ℂ)) ≤ -B := neg_le_neg hu
  have hdiag : Matrix.fromBlocks (r • (1 : Matrix n n ℂ)) 0 0 (r • (1 : Matrix n n ℂ)) =
      r • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
    simpa only [smul_zero, Matrix.fromBlocks_one] using
      (Matrix.fromBlocks_smul r (1 : Matrix n n ℂ) (0 : Matrix n n ℂ)
        (0 : Matrix n n ℂ) (1 : Matrix n n ℂ)).symm
  have hdiagNeg : Matrix.fromBlocks (-(r • (1 : Matrix n n ℂ))) 0 0
      (-(r • (1 : Matrix n n ℂ))) = -(r • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ)) := by
    have hn := (Matrix.fromBlocks_neg (r • (1 : Matrix n n ℂ)) (0 : Matrix n n ℂ)
      (0 : Matrix n n ℂ) (r • (1 : Matrix n n ℂ))).symm
    simp only [neg_zero] at hn
    rw [hdiag] at hn
    exact hn
  apply hermitian_norm_le_of_order (signedLift_isHermitian hB)
  · have h := fromBlocks_diagonal_mono hl hln
    rw [hdiagNeg] at h
    exact h
  · have h := fromBlocks_diagonal_mono hu hun
    rw [hdiag] at h
    exact h

omit [Fintype n] [DecidableEq n] in
theorem signedLift_sum_smul {ι : Type*} [Fintype ι]
    (B : ι → Matrix n n ℂ) (x : ι → ℝ) :
    signedLift (∑ i, x i • B i) = ∑ i, x i • signedLift (B i) := by
  ext i j
  cases i <;> cases j <;>
    simp [signedLift, Matrix.sum_apply, Matrix.smul_apply, Finset.sum_neg_distrib]

def leftDensity (S : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks S 0 0 0

def rightDensity (S : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks 0 0 0 S

theorem leftDensity_mem {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    leftDensity S ∈ densitySet := by
  refine ⟨posSemidef_fromBlocks_diagonal hS.1 Matrix.PosSemidef.zero, ?_⟩
  simpa [leftDensity, realTrace, Matrix.trace, Matrix.diag, Fintype.sum_sum_type] using hS.2

theorem rightDensity_mem {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    rightDensity S ∈ densitySet := by
  refine ⟨posSemidef_fromBlocks_diagonal Matrix.PosSemidef.zero hS.1, ?_⟩
  simpa [rightDensity, realTrace, Matrix.trace, Matrix.diag, Fintype.sum_sum_type] using hS.2

omit [DecidableEq n] in
theorem realTrace_signedLift_left (B S : Matrix n n ℂ) :
    realTrace (signedLift B * leftDensity S) = realTrace (B * S) := by
  simp [signedLift, leftDensity, Matrix.fromBlocks_multiply, realTrace,
    Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

omit [DecidableEq n] in
theorem realTrace_signedLift_right (B S : Matrix n n ℂ) :
    realTrace (signedLift B * rightDensity S) = -realTrace (B * S) := by
  simp [signedLift, rightDensity, Matrix.fromBlocks_multiply, realTrace,
    Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

/-- A concrete lifted density realizes the original spectral norm as a trace pairing. -/
theorem exists_signedLift_density_norm [Nonempty n]
    {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    ∃ S ∈ densitySet, realTrace (signedLift B * S) = ‖B‖ := by
  have hs := CStarAlgebra.norm_or_neg_norm_mem_spectrum hB
  rw [hB.spectrum_real_eq_range_eigenvalues] at hs
  rcases hs with ⟨i, hi⟩ | ⟨i, hi⟩
  · refine ⟨leftDensity (eigenDensity hB i), leftDensity_mem (eigenDensity_mem hB i), ?_⟩
    rw [realTrace_signedLift_left, realTrace_mul_eigenDensity, hi]
  · refine ⟨rightDensity (eigenDensity hB i), rightDensity_mem (eigenDensity_mem hB i), ?_⟩
    rw [realTrace_signedLift_right, realTrace_mul_eigenDensity, hi, neg_neg]

/-- The actual lifted potential controls the original discrepancy norm. -/
theorem norm_le_signedLift_densityPotential [Nonempty n]
    {ι : Type*} [Fintype ι] {B : Matrix n n ℂ} (hB : B.IsHermitian)
    (K : ι → Matrix (n ⊕ n) (n ⊕ n) ℂ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ‖B‖ ≤ densityPotential (signedLift B) K θ := by
  obtain ⟨S, hS, hval⟩ := exists_signedLift_density_norm hB
  rw [← hval]
  exact realTrace_le_densityPotential _ K hθ hS

/-- Equality of the original and lifted Euclidean operator norms. -/
theorem signedLift_norm [Nonempty n] {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    ‖signedLift B‖ = ‖B‖ := by
  apply le_antisymm (signedLift_norm_le hB le_rfl)
  obtain ⟨S, hS, hval⟩ := exists_signedLift_density_norm hB
  rw [← hval]
  exact realTrace_mul_density_le_norm (signedLift_isHermitian hB) hS

end MatrixSpencer
