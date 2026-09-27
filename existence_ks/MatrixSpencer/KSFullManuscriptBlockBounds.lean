import MatrixSpencer.KSComplexOwnerPerturbation
import MatrixSpencer.KSFullManuscriptFidelityBlockUpper

/-!
# Entry bounds for the actual fidelity SDP block

The elementary positive-Gram Cauchy--Schwarz bound gives an explicit outer
radius in the finite matrix-entry coordinate chart, including singular blocks.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptBlockBounds
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
open KSComplexOwnerPerturbation (column)

theorem sqrt_column_inner {P : Matrix n n ℂ} (hP : P.PosSemidef) (i j : n) :
    inner ℂ (column (CFC.sqrt P) i) (column (CFC.sqrt P) j) = P i j := by
  have hg : (CFC.sqrt P)ᴴ*CFC.sqrt P=P := by
    rw [(CFC.sqrt_nonneg P).posSemidef.isHermitian.eq, CFC.sqrt_mul_sqrt_self P hP.nonneg]
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  change ((CFC.sqrt P)ᴴ*CFC.sqrt P) i j=P i j
  rw [hg]

theorem sqrt_column_norm_sq {P : Matrix n n ℂ} (hP : P.PosSemidef) (i : n) :
    ‖column (CFC.sqrt P) i‖^2 = (P i i).re := by
  have he := congrArg Complex.re (sqrt_column_inner hP i i)
  change RCLike.re (inner ℂ (column (CFC.sqrt P) i) (column (CFC.sqrt P) i)) = _ at he
  rwa [inner_self_eq_norm_sq] at he

theorem diagonal_nonneg {P : Matrix n n ℂ} (hP : P.PosSemidef) (i : n) : 0 ≤ (P i i).re := by
  rw [← sqrt_column_norm_sq hP i]
  exact sq_nonneg _

theorem entry_sq_le_diagonal {P : Matrix n n ℂ} (hP : P.PosSemidef) (i j : n) :
    ‖P i j‖^2 ≤ (P i i).re*(P j j).re := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (column (CFC.sqrt P) i) (column (CFC.sqrt P) j)
  rw [sqrt_column_inner hP] at h
  have hs := pow_le_pow_left₀ (norm_nonneg (P i j)) h 2
  rwa [mul_pow, sqrt_column_norm_sq hP i, sqrt_column_norm_sq hP j] at hs

theorem diagonal_le_trace {P : Matrix n n ℂ} (hP : P.PosSemidef) (i : n) :
    (P i i).re ≤ realTrace P := by
  have he : realTrace P = ∑ j, (P j j).re := by simp [realTrace, Matrix.trace]
  rw [he]
  exact Finset.single_le_sum (fun j _ => diagonal_nonneg hP j) (Finset.mem_univ i)

theorem diagonal_le_scalar {T : Matrix n n ℂ} {V : ℝ}
    (hT : T ≤ V • (1 : Matrix n n ℂ)) (i : n) : (T i i).re ≤ V := by
  have h := diagonal_nonneg (Matrix.le_iff.mp hT) i
  have he : ((V • (1 : Matrix n n ℂ)-T) i i).re = V-(T i i).re := by simp
  rw [he] at h
  linarith

/-- The original off-diagonal SDP entries have a dimension-free bound. -/
theorem block_entry_sq_le {S Z T : Matrix n n ℂ} {V : ℝ}
    (hblock : (Matrix.fromBlocks S Z Zᴴ T).PosSemidef)
    (htrace : realTrace S = 1) (hT : T ≤ V • (1 : Matrix n n ℂ)) (i j : n) :
    ‖Z i j‖^2 ≤ V := by
  have hS : S.PosSemidef := by
    simpa only [Matrix.submatrix, Matrix.fromBlocks_apply₁₁] using hblock.submatrix Sum.inl
  have hTpos : T.PosSemidef := by
    simpa only [Matrix.submatrix, Matrix.fromBlocks_apply₂₂] using hblock.submatrix Sum.inr
  have hc := entry_sq_le_diagonal hblock (Sum.inl i) (Sum.inr j)
  simp only [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂] at hc
  have hs : (S i i).re ≤ 1 := by simpa only [htrace] using diagonal_le_trace hS i
  have ht := diagonal_le_scalar hT j
  have hv : 0 ≤ V := (diagonal_nonneg hTpos j).trans ht
  exact hc.trans ((mul_le_mul hs ht (diagonal_nonneg hTpos j) zero_le_one).trans_eq (one_mul V))

theorem block_entry_le {S Z T : Matrix n n ℂ} {V : ℝ}
    (hblock : (Matrix.fromBlocks S Z Zᴴ T).PosSemidef)
    (htrace : realTrace S = 1) (hT : T ≤ V • (1 : Matrix n n ℂ)) (i j : n) :
    ‖Z i j‖ ≤ Real.sqrt V := by
  have hs := block_entry_sq_le hblock htrace hT i j
  have hv : 0 ≤ V := (sq_nonneg ‖Z i j‖).trans hs
  exact (Real.le_sqrt (norm_nonneg _) hv).mpr hs

end MatrixSpencer.KSFullManuscriptBlockBounds
