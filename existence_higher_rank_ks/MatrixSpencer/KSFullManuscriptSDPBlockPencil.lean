import MatrixSpencer.KSFullManuscriptSDPCoordinates
import MatrixSpencer.KSComplexProjectionGeometry
import MatrixSpencer.SignedLift



open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptSDPBlockPencil

open KSFullManuscriptSDPIdentity KSComplexTraceSqrt KSComplexProjectionGeometry
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

abbrev ComplexIndex (n : Type*) := n ⊕ ((n ⊕ n) ⊕ (n ⊕ n))
abbrev RealIndex (n : Type*) := ComplexIndex n ⊕ ComplexIndex n

def block (B : ι → Matrix n n ℂ) (lam : ℝ) (S Y Z : Matrix n n ℂ) :
    Matrix (ComplexIndex n) (ComplexIndex n) ℂ :=
  Matrix.fromBlocks Y 0 0 (Matrix.fromBlocks
    (Matrix.fromBlocks S Z Zᴴ (krausChannel B S + lam • 1)) 0 0
    (Matrix.fromBlocks S Y Y 1))

def deltaBlock (B : ι → Matrix n n ℂ) (S Y Z : Matrix n n ℂ) :
    Matrix (ComplexIndex n) (ComplexIndex n) ℂ :=
  Matrix.fromBlocks Y 0 0 (Matrix.fromBlocks
    (Matrix.fromBlocks S Z Zᴴ (krausChannel B S)) 0 0
    (Matrix.fromBlocks S Y Y 0))

omit [DecidableEq n] in
theorem channel_add (B : ι → Matrix n n ℂ) (S T : Matrix n n ℂ) :
    krausChannel B (S + T) = krausChannel B S + krausChannel B T := by
  simpa only [one_smul] using krausChannel_weighted_add B S T 1 1

omit [DecidableEq n] in
theorem channel_smul (B : ι → Matrix n n ℂ) (r : ℝ) (S : Matrix n n ℂ) :
    krausChannel B (r • S) = r • krausChannel B S := by
  simp only [krausChannel, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

omit [DecidableEq n] in
theorem channel_hermitian (B : ι → Matrix n n ℂ) {S : Matrix n n ℂ} (hS : S.IsHermitian) :
    (krausChannel B S).IsHermitian := by
  unfold krausChannel Matrix.IsHermitian
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hS.eq, Matrix.mul_assoc]

theorem block_hermitian (B : ι → Matrix n n ℂ) (lam : ℝ) {S Y Z : Matrix n n ℂ}
    (hS : S.IsHermitian) (hY : Y.IsHermitian) : (block B lam S Y Z).IsHermitian := by
  have hi : (lam • (1 : Matrix n n ℂ)).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_one]
  have hF := Matrix.IsHermitian.fromBlocks hS (rfl : Zᴴ = Zᴴ)
    ((channel_hermitian B hS).add hi)
  have hR := Matrix.IsHermitian.fromBlocks hS hY.eq Matrix.isHermitian_one
  exact Matrix.IsHermitian.fromBlocks hY (by simp)
    (Matrix.IsHermitian.fromBlocks hF (by simp) hR)

omit [DecidableEq n] in
theorem deltaBlock_hermitian (B : ι → Matrix n n ℂ) {S Y Z : Matrix n n ℂ}
    (hS : S.IsHermitian) (hY : Y.IsHermitian) : (deltaBlock B S Y Z).IsHermitian := by
  have hF := Matrix.IsHermitian.fromBlocks hS (rfl : Zᴴ = Zᴴ) (channel_hermitian B hS)
  have hR := Matrix.IsHermitian.fromBlocks hS hY.eq Matrix.isHermitian_zero
  exact Matrix.IsHermitian.fromBlocks hY (by simp)
    (Matrix.IsHermitian.fromBlocks hF (by simp) hR)

omit [Fintype ι] in
theorem diagonal_psd_iff {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix n n ℂ} {D : Matrix m m ℂ} :
    (Matrix.fromBlocks A 0 0 D).PosSemidef ↔ A.PosSemidef ∧ D.PosSemidef := by
  constructor
  · intro h
    constructor
    · simpa only [Matrix.submatrix, Matrix.fromBlocks_apply₁₁] using h.submatrix Sum.inl
    · simpa only [Matrix.submatrix, Matrix.fromBlocks_apply₂₂] using h.submatrix Sum.inr
  · rintro ⟨hA,hD⟩
    exact posSemidef_fromBlocks_diagonal hA hD

theorem block_psd_iff (B : ι → Matrix n n ℂ) (lam : ℝ) (S Y Z : Matrix n n ℂ) :
    (block B lam S Y Z).PosSemidef ↔ Y.PosSemidef ∧
      (Matrix.fromBlocks S Z Zᴴ (krausChannel B S + lam • 1)).PosSemidef ∧
      (Matrix.fromBlocks S Y Y 1).PosSemidef := by
  simp only [block, diagonal_psd_iff]

theorem real_block_psd_iff (B : ι → Matrix n n ℂ) (lam : ℝ) (S Y Z : Matrix n n ℂ)
    (htr : realTrace S = 1) :
    (realification (block B lam S Y Z)).PosSemidef ↔ Feasible (krausChannel B) lam S Y Z := by
  rw [show (realification (block B lam S Y Z)).PosSemidef ↔
      (block B lam S Y Z).PosSemidef from
    ⟨realification_reflects_posSemidef _, realification_posSemidef _⟩,
    block_psd_iff]
  simp only [Feasible, htr, true_and]

omit [DecidableEq n] in
theorem deltaBlock_add (B : ι → Matrix n n ℂ) (S Y Z S' Y' Z' : Matrix n n ℂ) :
    deltaBlock B (S + S') (Y + Y') (Z + Z') = deltaBlock B S Y Z + deltaBlock B S' Y' Z' := by
  simp only [deltaBlock, Matrix.conjTranspose_add, channel_add, Matrix.fromBlocks_add,
    add_zero]

omit [DecidableEq n] in
theorem deltaBlock_smul (B : ι → Matrix n n ℂ) (r : ℝ) (S Y Z : Matrix n n ℂ) :
    deltaBlock B (r • S) (r • Y) (r • Z) = r • deltaBlock B S Y Z := by
  simp only [deltaBlock, Matrix.conjTranspose_smul, star_trivial, channel_smul,
    Matrix.fromBlocks_smul, smul_zero]

theorem block_affine (B : ι → Matrix n n ℂ) (lam : ℝ) (S Y Z S' Y' Z' : Matrix n n ℂ) :
    block B lam (S + S') (Y + Y') (Z + Z') = block B lam S Y Z + deltaBlock B S' Y' Z' := by
  simp only [block, deltaBlock, Matrix.conjTranspose_add, channel_add,
    Matrix.fromBlocks_add, add_zero]
  congr 3
  abel

omit [Fintype ι] [Fintype n] [DecidableEq n] in
theorem realification_add (A D : Matrix n n ℂ) : realification (A + D) = realification A + realification D := by
  ext (i | i) (j | j) <;> simp
  ring

omit [Fintype ι] [Fintype n] [DecidableEq n] in
theorem realification_smul (r : ℝ) (A : Matrix n n ℂ) : realification (r • A) = r • realification A := by
  ext (i | i) (j | j) <;> simp [Complex.real_smul]

end MatrixSpencer.KSFullManuscriptSDPBlockPencil
