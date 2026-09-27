import MatrixSpencer.FidelityContinuity

/-!
# Exact fidelity compression

An isometric embedding preserves positive square roots and trace. Applying
fidelity symmetry puts the supported source inside the first square root, which
gives an exact compression identity for an arbitrary PSD density. The density
need not be supported on, or commute with, the source support.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MatrixSpencer

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- Cyclic trace for rectangular factors. -/
theorem realTrace_rectangular_mul_comm (A : Matrix n m ℂ) (B : Matrix m n ℂ) :
    realTrace (A * B) = realTrace (B * A) :=
  congrArg RCLike.re (Matrix.trace_mul_comm A B)

omit [DecidableEq n] in
/-- Trace is unchanged by extending an operator isometrically by zero. -/
theorem realTrace_isometry_embedding (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix m m ℂ) : realTrace (V * A * Vᴴ) = realTrace A := by
  rw [realTrace_rectangular_mul_comm (V * A) Vᴴ, ← Matrix.mul_assoc, hV, Matrix.one_mul]

/-- The positive square root commutes with isometric extension by zero. -/
theorem sqrt_isometry_embedding (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    CFC.sqrt (V * A * Vᴴ) = V * CFC.sqrt A * Vᴴ := by
  apply CFC.sqrt_unique
  · calc
      (V * CFC.sqrt A * Vᴴ) * (V * CFC.sqrt A * Vᴴ) =
          V * CFC.sqrt A * (Vᴴ * V) * CFC.sqrt A * Vᴴ := by
            simp only [Matrix.mul_assoc]
      _ = V * A * Vᴴ := by
        rw [hV, Matrix.mul_one, Matrix.mul_assoc V (CFC.sqrt A) (CFC.sqrt A),
          CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact ((CFC.sqrt_nonneg A).posSemidef.mul_mul_conjTranspose_same V).nonneg

/-- Source-first fidelity reduces exactly to the embedded source space. -/
theorem fidelity_isometry_source_first (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {S : Matrix n n ℂ} {M : Matrix m m ℂ}
    (hS : S.PosSemidef) (hM : M.PosSemidef) :
    fidelity (V * M * Vᴴ) S = fidelity M (Vᴴ * S * V) := by
  have hcompressed : (Vᴴ * S * V).PosSemidef := hS.conjTranspose_mul_mul_same V
  have hinner : (CFC.sqrt M * (Vᴴ * S * V) * CFC.sqrt M).PosSemidef := by
    simpa only [(CFC.sqrt_nonneg M).posSemidef.isHermitian.eq] using
      hcompressed.conjTranspose_mul_mul_same (CFC.sqrt M)
  have hfactor : (V * CFC.sqrt M * Vᴴ) * S * (V * CFC.sqrt M * Vᴴ) =
      V * (CFC.sqrt M * (Vᴴ * S * V) * CFC.sqrt M) * Vᴴ := by
    simp only [Matrix.mul_assoc]
  unfold fidelity fidelityCore
  rw [sqrt_isometry_embedding V hV hM, hfactor,
    sqrt_isometry_embedding V hV hinner, realTrace_isometry_embedding V hV]

/-- Exact fidelity compression, with no support or commutation restriction on the density. -/
theorem fidelity_isometry_compression (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {S : Matrix n n ℂ} {M : Matrix m m ℂ}
    (hS : S.PosSemidef) (hM : M.PosSemidef) :
    fidelity S (V * M * Vᴴ) = fidelity (Vᴴ * S * V) M := by
  rw [fidelity_symm hS (hM.mul_mul_conjTranspose_same V),
    fidelity_isometry_source_first V hV hS hM,
    fidelity_symm hM (hS.conjTranspose_mul_mul_same V)]

omit [DecidableEq n] in
/-- Positive definiteness of the density survives compression to any isometric subspace. -/
theorem posDef_isometry_compression (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {S : Matrix n n ℂ} (hS : S.PosDef) : (Vᴴ * S * V).PosDef := by
  apply hS.conjTranspose_mul_mul_same
  intro x y hxy
  have h := congrArg (fun z => Vᴴ *ᵥ z) hxy
  simpa only [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec] using h

end MatrixSpencer
