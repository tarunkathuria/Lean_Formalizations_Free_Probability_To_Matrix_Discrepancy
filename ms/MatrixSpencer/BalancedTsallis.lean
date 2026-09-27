import MatrixSpencer.BalancedTransport
import MatrixSpencer.TsallisHessian

/-!
# The actual Tsallis Hessian in balanced coordinates

The frozen coordinate change is congruence by sqrt Z. The Hessian is
pulled back in the real trace pairing; its inverse retains both terms.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace MatrixSpencer

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance balancedTsallisCStarAlgebra : CStarAlgebra (Matrix n n ℂ) := {}
local instance balancedTsallisNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance balancedTsallisFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

def balancedCoordinateEquiv (Z : Matrix n n ℂ) (hZ : Z.PosDef) :
    selfAdjoint (Matrix n n ℂ) ≃L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (hermitianCongruenceEquiv (CFC.sqrt Z) hZ.posDef_sqrt).toContinuousLinearEquiv

@[simp] theorem balancedCoordinateEquiv_coe (Z : Matrix n n ℂ) (hZ : Z.PosDef)
    (X : selfAdjoint (Matrix n n ℂ)) :
    (balancedCoordinateEquiv Z hZ X : Matrix n n ℂ) = CFC.sqrt Z * X * CFC.sqrt Z := rfl

@[simp] theorem balancedCoordinateEquiv_symm_coe (Z : Matrix n n ℂ) (hZ : Z.PosDef)
    (X : selfAdjoint (Matrix n n ℂ)) :
    ((balancedCoordinateEquiv Z hZ).symm X : Matrix n n ℂ) =
      transportInverseSqrt Z * X * transportInverseSqrt Z := rfl

omit [DecidableEq n] in
theorem realTrace_congruence_pairing (Q X Y : Matrix n n ℂ) :
    realTrace ((Q * X * Q) * Y) = realTrace (X * (Q * Y * Q)) := by
  simpa only [Matrix.mul_assoc] using realTrace_mul_comm Q (X * Q * Y)

/-- Pullback of the actual negative Tsallis Hessian through the frozen coordinate map. -/
def balancedNegativeTsallisEquiv (θ : ℝ) (hθ : θ ≠ 0)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (Z : Matrix n n ℂ) (hZ : Z.PosDef) :
    selfAdjoint (Matrix n n ℂ) ≃L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  ((balancedCoordinateEquiv Z hZ).trans (negativeTsallisHessianEquiv θ hθ S hS)).trans
    (balancedCoordinateEquiv Z hZ)

/-- Exact inverse formula with the two noncommuting balanced matrices P and R. -/
theorem balancedNegativeTsallisEquiv_symm_coe (θ : ℝ) (hθ : θ ≠ 0)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (Z : Matrix n n ℂ) (hZ : Z.PosDef) (B : selfAdjoint (Matrix n n ℂ)) :
    ((balancedNegativeTsallisEquiv θ hθ S hS Z hZ).symm B : Matrix n n ℂ) =
      θ⁻¹ • (balancedDensity S Z * B * balancedRoot S Z +
        balancedRoot S Z * B * balancedDensity S Z) := by
  change ((balancedCoordinateEquiv Z hZ).symm
    ((negativeTsallisHessianEquiv θ hθ S hS).symm
      ((balancedCoordinateEquiv Z hZ).symm B)) : Matrix n n ℂ) = _
  rw [balancedCoordinateEquiv_symm_coe, negativeTsallisHessianEquiv_symm_apply,
    balancedCoordinateEquiv_symm_coe]
  simp only [balancedDensity, balancedRoot, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- Its trace pairing is precisely the pullback of the already-proved actual second derivative. -/
theorem balancedNegativeTsallisEquiv_actual_hessian (θ : ℝ) (hθ : θ ≠ 0)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (Z : Matrix n n ℂ) (hZ : Z.PosDef) (X Y : selfAdjoint (Matrix n n ℂ)) :
    fderiv ℝ (fun T => fderiv ℝ (tsallisPotential θ (n := n)) T) S
      (balancedCoordinateEquiv Z hZ X) (balancedCoordinateEquiv Z hZ Y) =
      -realTrace ((balancedNegativeTsallisEquiv θ hθ S hS Z hZ X : Matrix n n ℂ) * (Y : Matrix n n ℂ)) := by
  rw [fderiv_fderiv_tsallisPotential_apply θ hθ S _ _ hS]
  congr 1
  change realTrace ((negativeTsallisHessianEquiv θ hθ S hS
      (balancedCoordinateEquiv Z hZ X) : Matrix n n ℂ) *
      (CFC.sqrt Z * (Y : Matrix n n ℂ) * CFC.sqrt Z)) =
    realTrace ((CFC.sqrt Z * (negativeTsallisHessianEquiv θ hθ S hS
      (balancedCoordinateEquiv Z hZ X) : Matrix n n ℂ) * CFC.sqrt Z) * (Y : Matrix n n ℂ))
  exact (realTrace_congruence_pairing _ _ _).symm

end MatrixSpencer
