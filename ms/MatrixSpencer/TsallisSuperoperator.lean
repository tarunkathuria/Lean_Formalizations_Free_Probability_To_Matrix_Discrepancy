import MatrixSpencer.SuperoperatorCoordinates
import MatrixSpencer.BalancedTsallis

/-!
# The full complex balanced Tsallis operator

The two-sided physical multiplications are represented on explicit
Hilbert--Schmidt coordinates. Their positive definiteness is proved on
all complex matrices, without assuming physical factors commute.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace MatrixSpencer

variable {n : Type*} [Fintype n] [DecidableEq n]

def twoSidedSuper (P R : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  matrixSuper ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ R))

@[simp] theorem twoSidedSuper_mulVec (P R : Matrix n n ℂ) (x : n × n → ℂ) :
    twoSidedSuper P R *ᵥ x = matrixVector (P * matrixUnvector x * R) := by
  simpa only [Matrix.mul_assoc] using
    matrixSuper_mulVec ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ R)) x

theorem twoSidedSuper_entry (P R : Matrix n n ℂ) (ij kl : n × n) :
    twoSidedSuper P R ij kl = P ij.1 kl.1 * R kl.2 ij.2 := by
  classical
  rcases ij with ⟨i,j⟩
  rcases kl with ⟨k,l⟩
  simp [twoSidedSuper, matrixSuper, LinearMap.toMatrix'_apply, matrixVectorEquiv,
    matrixVector, matrixUnvector, Matrix.mul_apply, Prod.mk.injEq, eq_comm, ite_and]

theorem twoSidedSuper_isHermitian {P R : Matrix n n ℂ}
    (hP : P.IsHermitian) (hR : R.IsHermitian) : (twoSidedSuper P R).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro ij kl
  simp only [twoSidedSuper_entry, StarMul.star_mul]
  rw [hP.apply ij.1 kl.1, hR.apply kl.2 ij.2]
  exact mul_comm _ _

/-- Positive left and right physical factors give a strictly positive trace form. -/
theorem realTrace_twoSided_pos {P R X : Matrix n n ℂ}
    (hP : P.PosDef) (hR : R.PosDef) (hX : X ≠ 0) :
    0 < realTrace (Xᴴ * (P * X * R)) := by
  have hn : X * CFC.sqrt R ≠ 0 := by
    intro h
    apply hX
    exact hR.posDef_sqrt.isUnit.mul_right_cancel (by simpa using h)
  have h := realTrace_weighted_square_pos hP hn
  have heq : realTrace ((X * CFC.sqrt R)ᴴ * P * (X * CFC.sqrt R)) =
      realTrace (Xᴴ * (P * X * R)) := by
    rw [Matrix.conjTranspose_mul, hR.posDef_sqrt.isHermitian.eq]
    calc
      _ = realTrace ((Xᴴ * P * X) * (CFC.sqrt R * CFC.sqrt R)) := by
        simpa only [Matrix.mul_assoc] using
          realTrace_mul_comm (CFC.sqrt R) (Xᴴ * P * X * CFC.sqrt R)
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self R hR.posSemidef.nonneg]; simp only [Matrix.mul_assoc]
  rwa [heq] at h

theorem twoSidedSuper_posDef {P R : Matrix n n ℂ}
    (hP : P.PosDef) (hR : R.PosDef) : (twoSidedSuper P R).PosDef := by
  have hh := twoSidedSuper_isHermitian hP.isHermitian hR.isHermitian
  refine ⟨hh, ?_⟩
  intro x hx
  apply RCLike.pos_iff.mpr
  refine ⟨?_, hh.im_star_dotProduct_mulVec_self x⟩
  have hX : matrixUnvector x ≠ 0 := by
    intro h
    apply hx
    have hv := congrArg matrixVector h
    simpa only [matrixVector_unvector] using hv
  rw [twoSidedSuper_mulVec]
  change 0 < RCLike.re (star (matrixVector (matrixUnvector x)) ⬝ᵥ
    matrixVector (P * matrixUnvector x * R))
  rw [matrixVector_dotProduct]
  exact realTrace_twoSided_pos hP hR hX

/-- The full complex extension of the balanced inverse Tsallis Hessian. -/
def balancedTsallisInverseSuper (θ : ℝ) (S Z : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  θ⁻¹ • (twoSidedSuper (balancedDensity S Z) (balancedRoot S Z) +
    twoSidedSuper (balancedRoot S Z) (balancedDensity S Z))

theorem balancedTsallisInverseSuper_posDef {θ : ℝ} (hθ : 0 < θ)
    {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef) :
    (balancedTsallisInverseSuper θ S Z).PosDef := by
  apply Matrix.PosDef.smul
  · exact (twoSidedSuper_posDef (balancedDensity_posDef hS hZ) (balancedRoot_posDef hS hZ)).add
      (twoSidedSuper_posDef (balancedRoot_posDef hS hZ) (balancedDensity_posDef hS hZ))
  · exact inv_pos.mpr hθ

theorem balancedTsallisInverseSuper_mulVec (θ : ℝ) (S Z : Matrix n n ℂ) (x : n × n → ℂ) :
    balancedTsallisInverseSuper θ S Z *ᵥ x =
      matrixVector (θ⁻¹ • (balancedDensity S Z * matrixUnvector x * balancedRoot S Z +
        balancedRoot S Z * matrixUnvector x * balancedDensity S Z)) := by
  simp only [balancedTsallisInverseSuper, Matrix.smul_mulVec, Matrix.add_mulVec, twoSidedSuper_mulVec]
  rfl

/-- On physical Hermitian inputs this is the actual inverse Hessian, not an unrelated operator. -/
theorem balancedTsallisInverseSuper_represents (θ : ℝ) (hθ : θ ≠ 0)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (Z : Matrix n n ℂ) (hZ : Z.PosDef) (B : selfAdjoint (Matrix n n ℂ)) :
    balancedTsallisInverseSuper θ S Z *ᵥ matrixVector B =
      matrixVector ((balancedNegativeTsallisEquiv θ hθ S hS Z hZ).symm B) := by
  rw [balancedTsallisInverseSuper_mulVec, matrixUnvector_vector,
    balancedNegativeTsallisEquiv_symm_coe]

/-- The full complex Tsallis Hessian uses the ordinary matrix inverse. -/
def balancedTsallisSuper (θ : ℝ) (S Z : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  (balancedTsallisInverseSuper θ S Z)⁻¹

theorem balancedTsallisSuper_posDef {θ : ℝ} (hθ : 0 < θ)
    {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef) :
    (balancedTsallisSuper θ S Z).PosDef :=
  (balancedTsallisInverseSuper_posDef hθ hS hZ).inv

/-- Its restriction to Hermitian matrices is exactly the differentiated balanced Hessian. -/
theorem balancedTsallisSuper_represents (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (Z : Matrix n n ℂ) (hZ : Z.PosDef) (B : selfAdjoint (Matrix n n ℂ)) :
    balancedTsallisSuper θ S Z *ᵥ matrixVector B =
      matrixVector (balancedNegativeTsallisEquiv θ hθ.ne' S hS Z hZ B) := by
  have hp := balancedTsallisInverseSuper_posDef hθ hS hZ
  letI := hp.isUnit.invertible
  apply Matrix.mulVec_injective_iff_isUnit.mpr hp.isUnit
  rw [balancedTsallisSuper, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
    Matrix.one_mulVec, balancedTsallisInverseSuper_represents θ hθ.ne' S hS Z hZ,
    ContinuousLinearEquiv.symm_apply_apply]

end MatrixSpencer
