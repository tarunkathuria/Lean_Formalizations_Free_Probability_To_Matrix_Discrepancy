import MatrixSpencer.KSFullManuscriptSDPBlockPencil
import MatrixSpencer.KSFullManuscriptAffinePSD

/-!
# Actual affine real data for the full density SDP

The coefficients are obtained by applying the fixed entry chart to coordinate
unit vectors and forming the actual realified SDP blocks. Finite index
reindexing only labels these coordinates and matrix rows by `Fin`. No spectral
basis or optimization oracle is used to construct this pencil.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptAffineData

open KSFullManuscriptSDPCoordinates KSFullManuscriptSDPBlockPencil
open KSComplexTraceSqrt KSComplexProjectionGeometry
variable {n ι : Type*} [Fintype n] [LinearOrder n] [Fintype ι]

abbrev dimension (a : n) := Fintype.card (Index a)
abbrev matrixSize (n : Type*) [Fintype n] := Fintype.card (RealIndex n)
abbrev Space (a : n) := EuclideanSpace ℝ (Fin (dimension a))

def entries (a : n) (x : Space a) : Index a → ℝ := fun p => x (Fintype.equivFin (Index a) p)

def complexLinear (a : n) (B : ι → Matrix n n ℂ) : (Index a → ℝ) →ₗ[ℝ]
    Matrix (ComplexIndex n) (ComplexIndex n) ℂ where
  toFun x := deltaBlock B (densityLinear a x) (regularizerLinear a x) (fidelityLinear a x)
  map_add' x y := by
    change deltaBlock B (densityLinear a (x + y)) (regularizerLinear a (x + y))
      (fidelityLinear a (x + y)) = _
    simp only [map_add]
    exact deltaBlock_add B _ _ _ _ _ _
  map_smul' r x := by
    change deltaBlock B (densityLinear a (r • x)) (regularizerLinear a (r • x))
      (fidelityLinear a (r • x)) = _
    simp only [map_smul, RingHom.id_apply]
    exact deltaBlock_smul B r _ _ _

def realLinear (a : n) (B : ι → Matrix n n ℂ) : (Index a → ℝ) →ₗ[ℝ]
    Matrix (RealIndex n) (RealIndex n) ℝ where
  toFun x := realification (complexLinear a B x)
  map_add' x y := by rw [map_add, KSFullManuscriptSDPBlockPencil.realification_add]
  map_smul' r x := by rw [map_smul, KSFullManuscriptSDPBlockPencil.realification_smul]; rfl

theorem realLinear_symmetric (a : n) (B : ι → Matrix n n ℂ) (x : Index a → ℝ) :
    (realLinear a B x).IsSymm :=
  realification_symmetric _ (deltaBlock_hermitian B (densityLinear a x).property (regularizerLinear a x).property)

def finiteLinear (a : n) (B : ι → Matrix n n ℂ) : Space a →ₗ[ℝ]
    Matrix (Fin (matrixSize n)) (Fin (matrixSize n)) ℝ where
  toFun x := (realLinear a B (entries a x)).submatrix
    (Fintype.equivFin (RealIndex n)).symm (Fintype.equivFin (RealIndex n)).symm
  map_add' x y := by
    change (realLinear a B (entries a x + entries a y)).submatrix _ _ = _
    rw [map_add, Matrix.submatrix_add]
    rfl
  map_smul' r x := by
    change (realLinear a B (r • entries a x)).submatrix _ _ = _
    rw [map_smul, Matrix.submatrix_smul]
    rfl

def constant (_a : n) (B : ι → Matrix n n ℂ) (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) (lam : ℝ) :
    Matrix (Fin (matrixSize n)) (Fin (matrixSize n)) ℝ :=
  (realification (block B lam S₀ Y₀ 0)).submatrix
    (Fintype.equivFin (RealIndex n)).symm (Fintype.equivFin (RealIndex n)).symm

def unit (a : n) (i : Fin (dimension a)) : Space a := WithLp.toLp 2 (Pi.single i 1)

theorem finiteLinear_symmetric (a : n) (B : ι → Matrix n n ℂ) (x : Space a) :
    (finiteLinear a B x).IsSymm :=
  (realLinear_symmetric a B _).submatrix _

theorem constant_symmetric (a : n) (B : ι → Matrix n n ℂ) (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) (lam : ℝ) :
    (constant a B S₀ Y₀ lam).IsSymm :=
  (realification_symmetric _ (block_hermitian B lam S₀.property Y₀.property)).submatrix _

/-- All real coefficients of the concrete density SDP. -/
def data (a : n) (B : ι → Matrix n n ℂ) (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) (lam : ℝ) :
    KSFullManuscriptAffinePSD.Data (dimension a) (matrixSize n) where
  constant := constant a B S₀ Y₀ lam
  coefficient i := finiteLinear a B (unit a i)
  constant_symmetric := constant_symmetric a B S₀ Y₀ lam
  coefficient_symmetric i := finiteLinear_symmetric a B (unit a i)

theorem sum_units (a : n) (x : Space a) : ∑ i, x i • unit a i = x := by
  simpa only [unit, PiLp.basisFun_repr, PiLp.basisFun_apply] using
    (PiLp.basisFun 2 ℝ (Fin (dimension a))).sum_repr x

theorem matrixAt_eq (a : n) (B : ι → Matrix n n ℂ) (S₀ Y₀ : selfAdjoint (Matrix n n ℂ))
    (lam : ℝ) (x : Space a) :
    KSFullManuscriptAffinePSD.matrixAt (data a B S₀ Y₀ lam) x =
      constant a B S₀ Y₀ lam + finiteLinear a B x := by
  change constant a B S₀ Y₀ lam + ∑ i, x i • finiteLinear a B (unit a i) = _
  have hh := congrArg (finiteLinear a B) (sum_units a x)
  simpa only [map_sum, map_smul] using congrArg (fun M => constant a B S₀ Y₀ lam + M) hh

theorem matrixAt_physical (a : n) (B : ι → Matrix n n ℂ) (S₀ Y₀ : selfAdjoint (Matrix n n ℂ))
    (lam : ℝ) (x : Space a) :
    KSFullManuscriptAffinePSD.matrixAt (data a B S₀ Y₀ lam) x =
      (realification (block B lam (density a S₀ (entries a x))
        (regularizer a Y₀ (entries a x)) (fidelityLinear a (entries a x)))).submatrix
        (Fintype.equivFin (RealIndex n)).symm (Fintype.equivFin (RealIndex n)).symm := by
  rw [matrixAt_eq]
  change (realification (block B lam S₀ Y₀ 0)).submatrix _ _ +
    (realification (deltaBlock B (densityLinear a (entries a x))
      (regularizerLinear a (entries a x)) (fidelityLinear a (entries a x)))).submatrix _ _ = _
  change (realification (block B lam S₀ Y₀ 0) +
    realification (deltaBlock B (densityLinear a (entries a x))
      (regularizerLinear a (entries a x)) (fidelityLinear a (entries a x)))).submatrix _ _ = _
  rw [← KSFullManuscriptSDPBlockPencil.realification_add, ← block_affine]
  simp only [zero_add]
  rfl

/-- The numerical real matrix inequality is equivalent to the original
complex semidefinite constraints at precisely the decoded variables. -/
theorem target_iff (a : n) (B : ι → Matrix n n ℂ) (S₀ Y₀ : selfAdjoint (Matrix n n ℂ))
    (htr : realTrace (S₀ : Matrix n n ℂ) = 1) (lam : ℝ) (x : Space a) :
    x ∈ KSFullManuscriptAffinePSD.target (data a B S₀ Y₀ lam) ↔
      KSFullManuscriptSDPIdentity.Feasible (krausChannel B) lam
        (density a S₀ (entries a x)) (regularizer a Y₀ (entries a x)) (fidelityLinear a (entries a x)) := by
  change (KSFullManuscriptAffinePSD.matrixAt _ x).PosSemidef ↔ _
  rw [matrixAt_physical, Matrix.posSemidef_submatrix_equiv]
  apply real_block_psd_iff
  rw [density_trace, htr]

end MatrixSpencer.KSFullManuscriptAffineData
