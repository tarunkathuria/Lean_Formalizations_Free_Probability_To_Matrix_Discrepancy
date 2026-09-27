import MatrixSpencer.TsallisSuperoperator
import MatrixSpencer.BalancedFreeHessian
import MatrixSpencer.KrausContraction

/-!
# Coordinate representation of the actual balanced density Hessian

The full complex extension restricts to the differentiated real Hermitian
operator. In particular, subsequent operator estimates apply to that Hessian.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

local instance balancedSuperCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance balancedSuperNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance balancedSuperFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

omit [DecidableEq n] in
theorem krausSuper_matrixVector (D : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    krausSuper D *ᵥ matrixVector X = matrixVector (krausChannel D X) := by
  funext ij
  exact krausSuper_mulVec D X ij.1 ij.2

def balancedDefectSuper (B : ι → Matrix n n ℂ) (Z : Matrix n n ℂ) :
    Matrix (n × n) (n × n) ℂ := 1 - krausSuper (balancedKraus B Z)

theorem balancedDefectSuper_represents (B : ι → Matrix n n ℂ) (Z : Matrix n n ℂ)
    (X : selfAdjoint (Matrix n n ℂ)) :
    balancedDefectSuper B Z *ᵥ matrixVector X = matrixVector (balancedDefect B Z X) := by
  rw [balancedDefectSuper, Matrix.sub_mulVec, Matrix.one_mulVec, krausSuper_matrixVector]
  rfl

def balancedFreeSuper (B : ι → Matrix n n ℂ) (S Z : Matrix n n ℂ) :
    Matrix (n × n) (n × n) ℂ :=
  balancedDefectSuper B Z * (jordanSuper (balancedDensity S Z))⁻¹ * balancedDefectSuper B Z

theorem balancedFreeSuper_posSemidef (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) {S Z : Matrix n n ℂ}
    (hS : S.PosDef) (hZ : Z.PosDef) : (balancedFreeSuper B S Z).PosSemidef := by
  have hd : (balancedDefectSuper B Z).IsHermitian :=
    Matrix.isHermitian_one.sub
      (KrausContraction.super_hermitian _ (balancedKraus_isHermitian B hB Z))
  have h := (jordanSuper_posDef (balancedDensity_posDef hS hZ)).inv.posSemidef
    |>.conjTranspose_mul_mul_same (balancedDefectSuper B Z)
  simpa only [hd.eq, balancedFreeSuper] using h

theorem balancedFreeSuper_represents (B : ι → Matrix n n ℂ)
    (S Z : Matrix n n ℂ) (hS : S.PosDef) (hZ : Z.PosDef)
    (X : selfAdjoint (Matrix n n ℂ)) :
    balancedFreeSuper B S Z *ᵥ matrixVector X =
      matrixVector (balancedFreeHessian B S Z hS hZ X) := by
  rw [balancedFreeSuper, ← Matrix.mulVec_mulVec, balancedDefectSuper_represents,
    ← Matrix.mulVec_mulVec, jordanSuper_inv_mulVec (balancedDensity_posDef hS hZ),
    matrixUnvector_vector]
  change balancedDefectSuper B Z *ᵥ
    matrixVector ((balancedSylvesterEquiv S Z hS hZ).symm (balancedDefect B Z X)) = _
  rw [balancedDefectSuper_represents]
  rfl

def balancedFullSuper (B : ι → Matrix n n ℂ) (θ : ℝ) (S Z : Matrix n n ℂ) :
    Matrix (n × n) (n × n) ℂ :=
  balancedFreeSuper B S Z + balancedTsallisSuper θ S Z

theorem balancedFullSuper_posDef (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef) :
    (balancedFullSuper B θ S Z).PosDef :=
  Matrix.PosDef.posSemidef_add (balancedFreeSuper_posSemidef B hB hS hZ)
    (balancedTsallisSuper_posDef hθ hS hZ)

/-- The full complex matrix represents the actual pulled-back negative second derivative. -/
theorem balancedFullSuper_actual_hessian (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian)
    (θ : ℝ) (hθ : 0 < θ) (S X Y : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM);
    -(fderiv ℝ (fun T => fderiv ℝ (hermitianDensityObjective H B θ) T) S (G X) (G Y)) =
      RCLike.re (star (matrixVector Y) ⬝ᵥ
        (balancedFullSuper B θ S Z *ᵥ matrixVector X)) := by
  dsimp only
  rw [fderiv_fderiv_hermitianDensityObjective_apply H B θ S _ _ hS hM,
    balancedFreeHessian_actual_hessian B hB S X Y hS hM,
    balancedNegativeTsallisEquiv_actual_hessian θ hθ.ne' S hS _ (transportOptimizer_posDef hS hM),
    balancedFullSuper, Matrix.add_mulVec,
    balancedFreeSuper_represents B (S : Matrix n n ℂ) _ hS (transportOptimizer_posDef hS hM),
    balancedTsallisSuper_represents θ hθ S hS _ (transportOptimizer_posDef hS hM),
    dotProduct_add, map_add, matrixVector_dotProduct, matrixVector_dotProduct]
  change -(-realTrace (_ * (Y : Matrix n n ℂ)) + -realTrace (_ * (Y : Matrix n n ℂ))) =
    realTrace ((Y : Matrix n n ℂ)ᴴ * _) + realTrace ((Y : Matrix n n ℂ)ᴴ * _)
  rw [show (Y : Matrix n n ℂ)ᴴ = Y from Y.property,
    realTrace_mul_comm (Y : Matrix n n ℂ), realTrace_mul_comm (Y : Matrix n n ℂ)]
  ring

end MatrixSpencer
