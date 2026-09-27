import MatrixSpencer.BalancedSuperoperator

/-!
# Exact Jordan whitening

All square roots and inverses below are actual coordinate matrices. The
channel is conjugated in its original order, without a commutation premise.
-/

open scoped Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section
namespace MatrixSpencer

variable {m : Type*} [Fintype m] [DecidableEq m]

theorem transportInverseSqrt_square {J : Matrix m m ℂ} (hJ : J.PosDef) :
    transportInverseSqrt J * transportInverseSqrt J = J⁻¹ := by
  rw [transportInverseSqrt, ← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self J hJ.posSemidef.nonneg]

def whitenedChannel (J K : Matrix m m ℂ) : Matrix m m ℂ :=
  transportInverseSqrt J * K * CFC.sqrt J

def whitenedRegularizer (J Q : Matrix m m ℂ) : Matrix m m ℂ :=
  CFC.sqrt J * Q⁻¹ * CFC.sqrt J

def whitenedFull (J K Q : Matrix m m ℂ) : Matrix m m ℂ :=
  (1 - whitenedChannel J K)ᴴ * (1 - whitenedChannel J K) + whitenedRegularizer J Q

theorem whitenedRegularizer_posDef {J Q : Matrix m m ℂ}
    (hJ : J.PosDef) (hQ : Q.PosDef) : (whitenedRegularizer J Q).PosDef := by
  have h := hQ.inv.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.mpr hJ.posDef_sqrt.isUnit)
  simpa only [whitenedRegularizer, hJ.posDef_sqrt.isHermitian.eq] using h

theorem whitenedFull_posDef {J Q : Matrix m m ℂ}
    (hJ : J.PosDef) (hQ : Q.PosDef) (K : Matrix m m ℂ) :
    (whitenedFull J K Q).PosDef :=
  Matrix.PosDef.posSemidef_add (Matrix.posSemidef_conjTranspose_mul_self _)
    (whitenedRegularizer_posDef hJ hQ)

theorem whitenedRegularizer_inv {J Q : Matrix m m ℂ}
    (hQ : Q.PosDef) :
    (whitenedRegularizer J Q)⁻¹ = transportInverseSqrt J * Q * transportInverseSqrt J := by
  letI := hQ.isUnit.invertible
  simp only [whitenedRegularizer, Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible,
    transportInverseSqrt, Matrix.mul_assoc]

theorem whitened_defect {J : Matrix m m ℂ} (hJ : J.PosDef) (K : Matrix m m ℂ) :
    1 - whitenedChannel J K = transportInverseSqrt J * (1 - K) * CFC.sqrt J := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, transportInverseSqrt_mul_sqrt hJ]
  rfl

/-- The squared whitened defect is the exact congruence of the free Hessian. -/
theorem whitened_free {J K : Matrix m m ℂ}
    (hJ : J.PosDef) (hK : K.IsHermitian) :
    (1 - whitenedChannel J K)ᴴ * (1 - whitenedChannel J K) =
      CFC.sqrt J * ((1 - K) * J⁻¹ * (1 - K)) * CFC.sqrt J := by
  rw [whitened_defect hJ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hJ.posDef_sqrt.isHermitian.eq, (transportInverseSqrt_posDef hJ).isHermitian.eq,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hK.eq]
  calc
    _ = CFC.sqrt J * ((1 - K) *
        (transportInverseSqrt J * transportInverseSqrt J) * (1 - K)) * CFC.sqrt J := by
      noncomm_ring
    _ = _ := by rw [transportInverseSqrt_square hJ]

/-- Exact full normal form, including both Jordan square-root factors. -/
theorem whitenedFull_eq {J K : Matrix m m ℂ}
    (hJ : J.PosDef) (hK : K.IsHermitian) (Q : Matrix m m ℂ) :
    whitenedFull J K Q =
      CFC.sqrt J * ((1 - K) * J⁻¹ * (1 - K) + Q⁻¹) * CFC.sqrt J := by
  rw [whitenedFull, whitened_free hJ hK, Matrix.mul_add, Matrix.add_mul]
  rfl

/-- In the coupled inverse term the middle Jordan factors cancel exactly. -/
theorem whitened_coupling_eq {J K Q : Matrix m m ℂ}
    (hJ : J.PosDef) (hK : K.IsHermitian) (hQ : Q.PosDef) :
    whitenedChannel J K * (whitenedRegularizer J Q)⁻¹ * (whitenedChannel J K)ᴴ =
      transportInverseSqrt J * K * Q * K * transportInverseSqrt J := by
  rw [whitenedRegularizer_inv hQ, whitenedChannel, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hJ.posDef_sqrt.isHermitian.eq,
    (transportInverseSqrt_posDef hJ).isHermitian.eq, hK.eq]
  calc
    _ = transportInverseSqrt J * K * (CFC.sqrt J * transportInverseSqrt J) * Q *
      (transportInverseSqrt J * CFC.sqrt J) * K * transportInverseSqrt J := by noncomm_ring
    _ = _ := by rw [sqrt_mul_transportInverseSqrt hJ, transportInverseSqrt_mul_sqrt hJ,
      Matrix.mul_one, Matrix.mul_one]

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

/-- Instantiation at the actual balanced physical data. -/
def balancedWhitenedFull (B : ι → Matrix n n ℂ) (θ : ℝ) (S Z : Matrix n n ℂ) :
    Matrix (n × n) (n × n) ℂ :=
  whitenedFull (jordanSuper (balancedDensity S Z)) (krausSuper (balancedKraus B Z))
    (balancedTsallisInverseSuper θ S Z)

theorem balancedWhitenedFull_eq (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (θ : ℝ) {S Z : Matrix n n ℂ}
    (hS : S.PosDef) (hZ : Z.PosDef) :
    balancedWhitenedFull B θ S Z =
      CFC.sqrt (jordanSuper (balancedDensity S Z)) * balancedFullSuper B θ S Z *
        CFC.sqrt (jordanSuper (balancedDensity S Z)) :=
  whitenedFull_eq (jordanSuper_posDef (balancedDensity_posDef hS hZ))
    (KrausContraction.super_hermitian _ (balancedKraus_isHermitian B hB Z)) _

theorem balancedWhitenedFull_posDef (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ)
    {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef) :
    (balancedWhitenedFull B θ S Z).PosDef :=
  whitenedFull_posDef (jordanSuper_posDef (balancedDensity_posDef hS hZ))
    (balancedTsallisInverseSuper_posDef hθ hS hZ) _

end MatrixSpencer
