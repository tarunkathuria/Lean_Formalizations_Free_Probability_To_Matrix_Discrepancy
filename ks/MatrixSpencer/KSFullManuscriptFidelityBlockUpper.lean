import MatrixSpencer.KSFullManuscriptFidelityBlock
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# The fidelity SDP block upper bound

A positive block gives every transport-dual trace bound by testing it on
the explicitly stacked inverse-square-root/square-root matrices. Faithful
transport minimizers and continuity then identify its off-diagonal trace
bound with actual fidelity, including singular source and density matrices.
-/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptFidelityBlockUpper

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem realTrace_conjTranspose (X : Matrix n n ℂ) : realTrace Xᴴ = realTrace X := by
  simp [realTrace]

theorem block_transport_bound {S M X Z : Matrix n n ℂ}
    (hblock : (Matrix.fromBlocks S X Xᴴ M).PosSemidef) (hZ : Z.PosDef) :
    2 * realTrace X ≤ transportCost S M Z := by
  let V := CFC.sqrt Z
  let U := V⁻¹
  letI : Invertible V := hZ.posDef_sqrt.isUnit.invertible
  have hV : V.IsHermitian := hZ.posDef_sqrt.isHermitian
  have hU : U.IsHermitian := hZ.posDef_sqrt.inv.isHermitian
  have hVU : V * U = 1 := Matrix.mul_inv_of_invertible _
  have hUV : U * V = 1 := Matrix.inv_mul_of_invertible _
  have hVV : V * V = Z := CFC.sqrt_mul_sqrt_self Z hZ.posSemidef.nonneg
  have hUU : U * U = Z⁻¹ := by
    calc
      _ = (V * V)⁻¹ := (Matrix.mul_inv_rev V V).symm
      _ = Z⁻¹ := congrArg (fun A : Matrix n n ℂ => A⁻¹) hVV
  have hp := hblock.conjTranspose_mul_mul_same (Matrix.fromRows U (-V))
  have he : (Matrix.fromRows U (-V))ᴴ * Matrix.fromBlocks S X Xᴴ M * Matrix.fromRows U (-V) =
      U * S * U - U * X * V - V * Xᴴ * U + V * M * V := by
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.conjTranspose_neg, hU.eq, hV.eq,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    noncomm_ring
  rw [he] at hp
  have hu : realTrace (U * S * U) = realTrace (S * Z⁻¹) := by
    rw [realTrace_mul_cycle, hUU, realTrace_mul_comm]
  have hv : realTrace (V * M * V) = realTrace (M * Z) := by
    rw [realTrace_mul_cycle, hVV, realTrace_mul_comm]
  have hx : realTrace (U * X * V) = realTrace X := by
    rw [realTrace_mul_cycle, hVU, Matrix.one_mul]
  have hx' : realTrace (V * Xᴴ * U) = realTrace X := by
    rw [realTrace_mul_cycle, hUV, Matrix.one_mul, realTrace_conjTranspose]
  have hh := realTrace_nonneg hp
  rw [realTrace_add, realTrace_sub, realTrace_sub, hu, hv, hx, hx'] at hh
  unfold transportCost
  linarith

theorem block_trace_le_fidelity_posDef {S M X : Matrix n n ℂ}
    (hS : S.PosDef) (hM : M.PosDef) (hblock : (Matrix.fromBlocks S X Xᴴ M).PosSemidef) :
    realTrace X ≤ fidelity S M := by
  obtain ⟨Z, hZ, hvalue, _⟩ := fidelity_variational_posDef hS hM
  have hh := block_transport_bound hblock hZ
  rw [hvalue] at hh
  linarith

theorem block_trace_le_fidelity {S M X : Matrix n n ℂ}
    (hblock : (Matrix.fromBlocks S X Xᴴ M).PosSemidef) :
    realTrace X ≤ fidelity S M := by
  have hS : S.PosSemidef := by
    simpa only [Matrix.submatrix, Matrix.fromBlocks_apply₁₁] using hblock.submatrix Sum.inl
  have hM : M.PosSemidef := by
    simpa only [Matrix.submatrix, Matrix.fromBlocks_apply₂₂] using hblock.submatrix Sum.inr
  apply ge_of_tendsto (fidelity_regularize_tendsto hS hM)
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hreg : (Matrix.fromBlocks (regularize S r) X Xᴴ (regularize M r)).PosSemidef := by
    have hh := (regularize_posDef hblock hr).posSemidef
    convert hh using 1
    simp only [regularize, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul,
      smul_zero, Matrix.fromBlocks_add, add_zero]
  exact block_trace_le_fidelity_posDef (regularize_posDef hS hr) (regularize_posDef hM hr) hreg

/-- The density-positive fidelity SDP representation, with an actual attaining
block and the global upper bound for every feasible off-diagonal block. -/
theorem fidelity_block_representation {S M : Matrix n n ℂ}
    (hS : S.PosDef) (hM : M.PosSemidef) :
    (∃ X : Matrix n n ℂ, (Matrix.fromBlocks S X Xᴴ M).PosSemidef ∧ realTrace X = fidelity S M) ∧
    (∀ X : Matrix n n ℂ, (Matrix.fromBlocks S X Xᴴ M).PosSemidef → realTrace X ≤ fidelity S M) :=
  ⟨KSFullManuscriptFidelityBlock.exists_attaining_block hS hM,
    fun _ hX => block_trace_le_fidelity hX⟩

end MatrixSpencer.KSFullManuscriptFidelityBlockUpper
