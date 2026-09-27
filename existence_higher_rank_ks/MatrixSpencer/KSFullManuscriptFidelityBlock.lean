import MatrixSpencer.FidelityBounds

/-!
# Constructive fidelity attainment in the SDP block

For a positive definite density `S` and an arbitrary PSD source `M`, the
off-diagonal block is explicitly `sqrt(S) R sqrt(S)⁻¹`, where
`R = sqrt(sqrt(S) M sqrt(S))`. It attains the actual fidelity trace even
when the source is singular. This is an analytic SDP representation lemma;
the numerical routine need not evaluate this attaining block.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptFidelityBlock

variable {n : Type*} [Fintype n] [DecidableEq n]

def witness (S M : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt S * fidelityCore S M * (CFC.sqrt S)⁻¹

theorem witness_schur {S M : Matrix n n ℂ} (hS : S.PosDef) (hM : M.PosSemidef) :
    (witness S M)ᴴ * S⁻¹ * witness S M = M := by
  letI : Invertible S := hS.isUnit.invertible
  letI : Invertible (CFC.sqrt S) := hS.posDef_sqrt.isUnit.invertible
  have hs := hS.posDef_sqrt.isHermitian
  have hi := hS.posDef_sqrt.inv.isHermitian
  have hf : (fidelityCore S M).IsHermitian := (CFC.sqrt_nonneg _).posSemidef.isHermitian
  have hsinv : S⁻¹ = (CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹ := by
    calc
      _ = (CFC.sqrt S * CFC.sqrt S)⁻¹ :=
        congrArg (fun A : Matrix n n ℂ => A⁻¹) (CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg).symm
      _ = _ := Matrix.mul_inv_rev _ _
  calc
    _ = (CFC.sqrt S)⁻¹ * (fidelityCore S M * fidelityCore S M) * (CFC.sqrt S)⁻¹ := by
      simp only [witness, Matrix.conjTranspose_mul, hs.eq, hi.eq, hf.eq, hsinv,
        Matrix.mul_assoc, Matrix.inv_mul_cancel_left_of_invertible,
        Matrix.mul_inv_cancel_left_of_invertible]
    _ = (CFC.sqrt S)⁻¹ * (CFC.sqrt S * M * CFC.sqrt S) * (CFC.sqrt S)⁻¹ := by
      rw [fidelityCore_mul_self hM]
    _ = M := by
      simp only [Matrix.mul_assoc, Matrix.inv_mul_cancel_left_of_invertible,
        Matrix.mul_inv_of_invertible, Matrix.mul_one]

theorem witness_block_posSemidef {S M : Matrix n n ℂ}
    (hS : S.PosDef) (hM : M.PosSemidef) :
    (Matrix.fromBlocks S (witness S M) (witness S M)ᴴ M).PosSemidef := by
  letI : Invertible S := hS.isUnit.invertible
  apply (hS.fromBlocks₁₁ (witness S M) M).mpr
  rw [witness_schur hS hM, sub_self]
  exact Matrix.PosSemidef.zero

theorem witness_trace {S M : Matrix n n ℂ} (hS : S.PosDef) :
    realTrace (witness S M) = fidelity S M := by
  letI : Invertible (CFC.sqrt S) := hS.posDef_sqrt.isUnit.invertible
  rw [witness, realTrace_mul_comm, Matrix.inv_mul_cancel_left_of_invertible]
  rfl

/-- A faithful density admits an actual attaining SDP block for every PSD
source, including rank zero. -/
theorem exists_attaining_block {S M : Matrix n n ℂ}
    (hS : S.PosDef) (hM : M.PosSemidef) :
    ∃ X : Matrix n n ℂ, (Matrix.fromBlocks S X Xᴴ M).PosSemidef ∧
      realTrace X = fidelity S M :=
  ⟨witness S M, witness_block_posSemidef hS hM, witness_trace hS⟩

end MatrixSpencer.KSFullManuscriptFidelityBlock
