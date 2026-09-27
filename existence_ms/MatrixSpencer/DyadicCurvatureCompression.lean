import MatrixSpencer.DyadicRoot
import MatrixSpencer.TsallisSuperoperator
import MatrixSpencer.FidelityCompression

/-! A positive inverse-curvature model and its physical compression inequality.
The model is explicit. This module does not identify it with the actual
inverse Hessian of a power regularizer. -/

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer
namespace DyadicCurvatureCompression

variable {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]
local instance curvatureModelCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance curvatureModelSpace {j : Type*} [Fintype j] [DecidableEq j] :
    NormedSpace ℝ (selfAdjoint (Matrix j j ℂ)) := inferInstance
local instance curvatureModelFiniteDimensional {j : Type*} [Fintype j] [DecidableEq j] :
    FiniteDimensional ℝ (selfAdjoint (Matrix j j ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix j j ℂ)))

def inverseModel (m : ℕ) (c : ℝ) (S X : Matrix n n ℂ) : Matrix n n ℂ :=
  c • (S * X * dyadicRoot m S + dyadicRoot m S * X * S)

lemma inverseModel_isHermitian (m : ℕ) (c : ℝ) {S X : Matrix n n ℂ}
    (hS : S.PosSemidef) (hX : X.IsHermitian) : (inverseModel m c S X).IsHermitian := by
  have hR := (dyadicRoot_posSemidef m hS).isHermitian
  change (inverseModel m c S X)ᴴ = inverseModel m c S X
  simp only [inverseModel, Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, hS.isHermitian.eq, hR.eq, hX.eq, Matrix.mul_assoc]
  rw [add_comm]

lemma inverseModel_quadratic (m : ℕ) (c : ℝ) (S X : Matrix n n ℂ) :
    realTrace (X * inverseModel m c S X) = (2 * c) * realTrace (X * S * X * dyadicRoot m S) := by
  simp only [inverseModel, Matrix.mul_smul, realTrace_smul, Matrix.mul_add, realTrace_add]
  have he : realTrace (X * (dyadicRoot m S * X * S)) =
      realTrace (X * S * X * dyadicRoot m S) := by
    simpa only [Matrix.mul_assoc] using realTrace_mul_comm (X * dyadicRoot m S) (X * S)
  rw [he]
  simp only [← Matrix.mul_assoc]
  ring

lemma inverseModel_quadratic_nonneg (m : ℕ) {c : ℝ} (hc : 0 ≤ c)
    {S X : Matrix n n ℂ} (hS : S.PosSemidef) (hX : X.IsHermitian) :
    0 ≤ realTrace (X * inverseModel m c S X) := by
  rw [inverseModel_quadratic]
  have hXSX : (X * S * X).PosSemidef := by
    simpa only [hX.eq] using hS.conjTranspose_mul_mul_same X
  exact mul_nonneg (mul_nonneg (by norm_num) hc)
    (realTrace_mul_nonneg hXSX (dyadicRoot_posSemidef m hS))

lemma inverseModel_quadratic_pos (m : ℕ) {c : ℝ} (hc : 0 < c)
    {S X : Matrix n n ℂ} (hS : S.PosDef) (hX : X.IsHermitian) (hX0 : X ≠ 0) :
    0 < realTrace (X * inverseModel m c S X) := by
  rw [inverseModel_quadratic]
  have h := realTrace_twoSided_pos hS (dyadicRoot_posDef m hS) hX0
  rw [hX.eq] at h
  apply mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hc)
  simpa only [Matrix.mul_assoc] using h

omit [DecidableEq k] in
/-- Compress the full model only after applying it to the embedded perturbation. -/
lemma inverseModel_compression_apply (m : ℕ) (c : ℝ) (S : Matrix n n ℂ)
    (V : Matrix n k ℂ) (B : Matrix k k ℂ) :
    Vᴴ * inverseModel m c S (V * B * Vᴴ) * V =
      c • ((Vᴴ * S * V) * B * (Vᴴ * dyadicRoot m S * V) +
        (Vᴴ * dyadicRoot m S * V) * B * (Vᴴ * S * V)) := by
  simp only [inverseModel, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

omit [DecidableEq k] in
lemma compressed_model_quadratic (m : ℕ) (c : ℝ) (S : Matrix n n ℂ)
    (V : Matrix n k ℂ) (B : Matrix k k ℂ) :
    realTrace (B * (Vᴴ * inverseModel m c S (V * B * Vᴴ) * V)) =
      (2 * c) * realTrace ((B * (Vᴴ * S * V) * B) * (Vᴴ * dyadicRoot m S * V)) := by
  rw [inverseModel_compression_apply]
  simp only [Matrix.mul_smul, realTrace_smul, Matrix.mul_add, realTrace_add]
  have he : realTrace (B * ((Vᴴ * dyadicRoot m S * V) * B * (Vᴴ * S * V))) =
      realTrace (B * (Vᴴ * S * V) * B * (Vᴴ * dyadicRoot m S * V)) := by
    simpa only [Matrix.mul_assoc] using
      realTrace_mul_comm (B * (Vᴴ * dyadicRoot m S * V)) (B * (Vᴴ * S * V))
  rw [he]
  simp only [← Matrix.mul_assoc]
  ring

/-- Exact quadratic compression bound, on the full embedded density perturbation. -/
theorem inverseModel_compression_quadratic_le (m : ℕ) {c : ℝ} (hc : 0 ≤ c)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) (V : Matrix n k ℂ) (hV : Vᴴ * V = 1)
    {B : Matrix k k ℂ} (hB : B.IsHermitian) :
    realTrace (B * (Vᴴ * inverseModel m c S (V * B * Vᴴ) * V)) ≤
      realTrace (B * inverseModel m c (Vᴴ * S * V) B) := by
  rw [compressed_model_quadratic, inverseModel_quadratic]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hc)
  have hBSB : (B * (Vᴴ * S * V) * B).PosSemidef := by
    simpa only [hB.eq] using
      (hS.conjTranspose_mul_mul_same V).conjTranspose_mul_mul_same B
  exact realTrace_mul_mono hBSB (dyadicRoot_isometry_compression_le m hS V hV)

omit [DecidableEq n] [DecidableEq k] in
lemma embedding_compression_pairing (V : Matrix n k ℂ) (B : Matrix k k ℂ) (X : Matrix n n ℂ) :
    realTrace ((V * B * Vᴴ) * X) = realTrace (B * (Vᴴ * X * V)) := by
  calc
    _ = realTrace (V * (B * Vᴴ * X)) := by simp only [Matrix.mul_assoc]
    _ = realTrace ((B * Vᴴ * X) * V) := realTrace_rectangular_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem inverseModel_supported_force_quadratic_le (m : ℕ) {c : ℝ} (hc : 0 ≤ c)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) (V : Matrix n k ℂ) (hV : Vᴴ * V = 1)
    {B : Matrix k k ℂ} (hB : B.IsHermitian) :
    realTrace ((V * B * Vᴴ) * inverseModel m c S (V * B * Vᴴ)) ≤
      realTrace (B * inverseModel m c (Vᴴ * S * V) B) := by
  rw [embedding_compression_pairing]
  exact inverseModel_compression_quadratic_le m hc hS V hV hB

/-- The model as an actual real-linear map on Hermitian matrices. -/
def inverseModelLinearMap (m : ℕ) (c : ℝ) (S : Matrix n n ℂ) (hS : S.PosSemidef) :
    selfAdjoint (Matrix n n ℂ) →ₗ[ℝ] selfAdjoint (Matrix n n ℂ) where
  toFun X := ⟨inverseModel m c S X, inverseModel_isHermitian m c hS X.property⟩
  map_add' X Y := by
    apply Subtype.ext
    change inverseModel m c S ((X : Matrix n n ℂ) + Y) =
      inverseModel m c S X + inverseModel m c S Y
    simp only [inverseModel, Matrix.mul_add, Matrix.add_mul, smul_add]
    abel
  map_smul' r X := by
    apply Subtype.ext
    change inverseModel m c S (r • (X : Matrix n n ℂ)) = r • inverseModel m c S X
    simp only [inverseModel, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_smul, mul_comm]

@[simp] lemma inverseModelLinearMap_apply (m : ℕ) (c : ℝ)
    (S : Matrix n n ℂ) (hS : S.PosSemidef) (X : selfAdjoint (Matrix n n ℂ)) :
    (inverseModelLinearMap m c S hS X : Matrix n n ℂ) = inverseModel m c S X := rfl

theorem inverseModelLinearMap_injective (m : ℕ) {c : ℝ} (hc : 0 < c)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    Function.Injective (inverseModelLinearMap m c S hS.posSemidef) := by
  intro X Y hXY
  apply sub_eq_zero.mp
  by_contra hne
  have hmatrix : ((X - Y : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) ≠ 0 := by
    intro h
    apply hne
    exact Subtype.ext h
  have hp := inverseModel_quadratic_pos m hc hS (X - Y).property hmatrix
  have hz : inverseModelLinearMap m c S hS.posSemidef (X - Y) = 0 := by
    rw [map_sub, hXY, sub_self]
  have hm : inverseModel m c S ((X - Y : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) = 0 :=
    congrArg (fun T : selfAdjoint (Matrix n n ℂ) => (T : Matrix n n ℂ)) hz
  rw [hm, Matrix.mul_zero, realTrace_zero] at hp
  exact lt_irrefl _ hp

/-- Strict positive curvature gives a genuine finite-dimensional continuous equivalence. -/
def inverseModelEquiv (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : Matrix n n ℂ) (hS : S.PosDef) :
    selfAdjoint (Matrix n n ℂ) ≃L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (LinearEquiv.ofBijective (inverseModelLinearMap m c S hS.posSemidef)
    ⟨inverseModelLinearMap_injective m hc hS,
      LinearMap.injective_iff_surjective.mp (inverseModelLinearMap_injective m hc hS)⟩).toContinuousLinearEquiv

@[simp] lemma inverseModelEquiv_apply (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : Matrix n n ℂ) (hS : S.PosDef) (X : selfAdjoint (Matrix n n ℂ)) :
    (inverseModelEquiv m c hc S hS X : Matrix n n ℂ) = inverseModel m c S X := rfl

lemma inverseModelEquiv_symm_solve (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : Matrix n n ℂ) (hS : S.PosDef) (B : selfAdjoint (Matrix n n ℂ)) :
    inverseModel m c S ((inverseModelEquiv m c hc S hS).symm B) = (B : Matrix n n ℂ) := by
  rw [← inverseModelEquiv_apply m c hc S hS, ContinuousLinearEquiv.apply_symm_apply]

/-- The model is self-adjoint in the real trace pairing. -/
lemma inverseModel_trace_symmetric (m : ℕ) (c : ℝ) (S X Y : Matrix n n ℂ) :
    realTrace (X * inverseModel m c S Y) = realTrace (inverseModel m c S X * Y) := by
  simp only [inverseModel, Matrix.mul_smul, Matrix.smul_mul, realTrace_smul,
    Matrix.mul_add, Matrix.add_mul, realTrace_add]
  have h1 : realTrace (X * (S * Y * dyadicRoot m S)) =
      realTrace ((dyadicRoot m S * X * S) * Y) := by
    simpa only [Matrix.mul_assoc] using realTrace_mul_comm (X * S * Y) (dyadicRoot m S)
  have h2 : realTrace (X * (dyadicRoot m S * Y * S)) = realTrace ((S * X * dyadicRoot m S) * Y) := by
    simpa only [Matrix.mul_assoc] using realTrace_mul_comm (X * dyadicRoot m S * Y) S
  rw [h1, h2]
  ring

/-- Full complex Hilbert–Schmidt coordinate representation of the same model. -/
def inverseModelSuper (m : ℕ) (c : ℝ) (S : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  c • (twoSidedSuper S (dyadicRoot m S) + twoSidedSuper (dyadicRoot m S) S)

lemma inverseModelSuper_posDef (m : ℕ) {c : ℝ} (hc : 0 < c)
    {S : Matrix n n ℂ} (hS : S.PosDef) : (inverseModelSuper m c S).PosDef :=
  ((twoSidedSuper_posDef hS (dyadicRoot_posDef m hS)).add
    (twoSidedSuper_posDef (dyadicRoot_posDef m hS) hS)).smul hc

lemma inverseModelSuper_mulVec (m : ℕ) (c : ℝ) (S : Matrix n n ℂ) (x : n × n → ℂ) :
    inverseModelSuper m c S *ᵥ x = matrixVector (inverseModel m c S (matrixUnvector x)) := by
  simp only [inverseModelSuper, Matrix.smul_mulVec, Matrix.add_mulVec, twoSidedSuper_mulVec]
  rfl

end DyadicCurvatureCompression
end MatrixSpencer
