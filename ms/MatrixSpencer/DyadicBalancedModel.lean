import MatrixSpencer.DyadicCurvatureCompression
import MatrixSpencer.DyadicTraceInterpolation
import MatrixSpencer.BalancedBudgets

/-! Exact balanced coordinates for the positive inverse-curvature model.
The model's inverse is distinguished from the actual regularizer Hessian. -/

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer
namespace DyadicBalancedModel

variable {n ι : Type*} [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
local instance balancedDyadicCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance balancedDyadicSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance balancedDyadicFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

def balancedDyadicRoot (m : ℕ) (S Z : Matrix n n ℂ) : Matrix n n ℂ :=
  transportInverseSqrt Z * dyadicRoot m S * transportInverseSqrt Z

lemma balancedDyadicRoot_posSemidef (m : ℕ) {S Z : Matrix n n ℂ}
    (hS : S.PosSemidef) (hZ : Z.PosDef) : (balancedDyadicRoot m S Z).PosSemidef := by
  simpa only [balancedDyadicRoot, (transportInverseSqrt_posDef hZ).isHermitian.eq] using
    (dyadicRoot_posSemidef m hS).conjTranspose_mul_mul_same (transportInverseSqrt Z)

lemma balancedDyadicRoot_posDef (m : ℕ) {S Z : Matrix n n ℂ}
    (hS : S.PosDef) (hZ : Z.PosDef) : (balancedDyadicRoot m S Z).PosDef := by
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr (transportInverseSqrt_posDef hZ).isUnit
  simpa only [balancedDyadicRoot, (transportInverseSqrt_posDef hZ).isHermitian.eq] using
    (dyadicRoot_posDef m hS).conjTranspose_mul_mul_same hi

@[simp] lemma balancedDyadicRoot_one (S Z : Matrix n n ℂ) :
    balancedDyadicRoot 1 S Z = balancedRoot S Z := rfl

def balancedInverseModel (m : ℕ) (c : ℝ) (S Z X : Matrix n n ℂ) : Matrix n n ℂ :=
  c • (balancedDensity S Z * X * balancedDyadicRoot m S Z +
    balancedDyadicRoot m S Z * X * balancedDensity S Z)

/-- The exact inverse-coordinate congruence, retaining multiplication order. -/
lemma inverseModel_balanced_pullback (m : ℕ) (c : ℝ) (S Z B : Matrix n n ℂ) :
    transportInverseSqrt Z * DyadicCurvatureCompression.inverseModel m c S
      (transportInverseSqrt Z * B * transportInverseSqrt Z) * transportInverseSqrt Z =
        balancedInverseModel m c S Z B := by
  simp only [DyadicCurvatureCompression.inverseModel, balancedInverseModel, balancedDensity,
    balancedDyadicRoot, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc]

/-- Pullback of the model curvature (the inverse of the explicit model). -/
def balancedCurvatureEquiv (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : Matrix n n ℂ) (hS : S.PosDef) (Z : Matrix n n ℂ) (hZ : Z.PosDef) :
    selfAdjoint (Matrix n n ℂ) ≃L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  ((balancedCoordinateEquiv Z hZ).trans
    (DyadicCurvatureCompression.inverseModelEquiv m c hc S hS).symm).trans
      (balancedCoordinateEquiv Z hZ)

lemma balancedCurvatureEquiv_symm_coe (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : Matrix n n ℂ) (hS : S.PosDef) (Z : Matrix n n ℂ) (hZ : Z.PosDef)
    (B : selfAdjoint (Matrix n n ℂ)) :
    ((balancedCurvatureEquiv m c hc S hS Z hZ).symm B : Matrix n n ℂ) =
      balancedInverseModel m c S Z B := by
  change ((balancedCoordinateEquiv Z hZ).symm
    (DyadicCurvatureCompression.inverseModelEquiv m c hc S hS
      ((balancedCoordinateEquiv Z hZ).symm B)) : Matrix n n ℂ) = _
  rw [balancedCoordinateEquiv_symm_coe, DyadicCurvatureCompression.inverseModelEquiv_apply,
    balancedCoordinateEquiv_symm_coe, inverseModel_balanced_pullback]

lemma balancedCurvatureEquiv_pairing (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : Matrix n n ℂ) (hS : S.PosDef) (Z : Matrix n n ℂ) (hZ : Z.PosDef)
    (X Y : selfAdjoint (Matrix n n ℂ)) :
    realTrace ((balancedCurvatureEquiv m c hc S hS Z hZ X : Matrix n n ℂ) * (Y : Matrix n n ℂ)) =
      realTrace (((DyadicCurvatureCompression.inverseModelEquiv m c hc S hS).symm
        (balancedCoordinateEquiv Z hZ X) : Matrix n n ℂ) *
          (balancedCoordinateEquiv Z hZ Y : Matrix n n ℂ)) := by
  change realTrace ((CFC.sqrt Z * _ * CFC.sqrt Z) * (Y : Matrix n n ℂ)) = _
  exact realTrace_congruence_pairing _ _ _

/-- Full complex Hilbert--Schmidt extension of the same balanced inverse model. -/
def balancedInverseModelSuper (m : ℕ) (c : ℝ) (S Z : Matrix n n ℂ) :
    Matrix (n × n) (n × n) ℂ :=
  c • (twoSidedSuper (balancedDensity S Z) (balancedDyadicRoot m S Z) +
    twoSidedSuper (balancedDyadicRoot m S Z) (balancedDensity S Z))

lemma balancedInverseModelSuper_posDef (m : ℕ) {c : ℝ} (hc : 0 < c)
    {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef) :
    (balancedInverseModelSuper m c S Z).PosDef :=
  ((twoSidedSuper_posDef (balancedDensity_posDef hS hZ) (balancedDyadicRoot_posDef m hS hZ)).add
    (twoSidedSuper_posDef (balancedDyadicRoot_posDef m hS hZ) (balancedDensity_posDef hS hZ))).smul hc

lemma balancedInverseModelSuper_mulVec (m : ℕ) (c : ℝ) (S Z : Matrix n n ℂ)
    (x : n × n → ℂ) :
    balancedInverseModelSuper m c S Z *ᵥ x =
      matrixVector (balancedInverseModel m c S Z (matrixUnvector x)) := by
  simp only [balancedInverseModelSuper, Matrix.smul_mulVec, Matrix.add_mulVec,
    twoSidedSuper_mulVec]
  rfl

lemma balancedInverseModelSuper_represents (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : Matrix n n ℂ) (hS : S.PosDef) (Z : Matrix n n ℂ) (hZ : Z.PosDef)
    (B : selfAdjoint (Matrix n n ℂ)) :
    balancedInverseModelSuper m c S Z *ᵥ matrixVector B =
      matrixVector ((balancedCurvatureEquiv m c hc S hS Z hZ).symm B) := by
  rw [balancedInverseModelSuper_mulVec, matrixUnvector_vector, balancedCurvatureEquiv_symm_coe]

def balancedCurvatureSuper (m : ℕ) (c : ℝ) (S Z : Matrix n n ℂ) :
    Matrix (n × n) (n × n) ℂ := (balancedInverseModelSuper m c S Z)⁻¹

lemma balancedCurvatureSuper_posDef (m : ℕ) {c : ℝ} (hc : 0 < c)
    {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef) :
    (balancedCurvatureSuper m c S Z).PosDef :=
  (balancedInverseModelSuper_posDef m hc hS hZ).inv

lemma balancedCurvatureSuper_represents (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : Matrix n n ℂ) (hS : S.PosDef) (Z : Matrix n n ℂ) (hZ : Z.PosDef)
    (B : selfAdjoint (Matrix n n ℂ)) :
    balancedCurvatureSuper m c S Z *ᵥ matrixVector B =
      matrixVector (balancedCurvatureEquiv m c hc S hS Z hZ B) := by
  have hp := balancedInverseModelSuper_posDef m hc hS hZ
  letI := hp.isUnit.invertible
  apply Matrix.mulVec_injective_iff_isUnit.mpr hp.isUnit
  rw [balancedCurvatureSuper, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
    Matrix.one_mulVec, balancedInverseModelSuper_represents m c hc S hS Z hZ,
    ContinuousLinearEquiv.symm_apply_apply]

lemma transportInverseSqrt_square {Z : Matrix n n ℂ} (hZ : Z.PosDef) :
    transportInverseSqrt Z * transportInverseSqrt Z = Z⁻¹ := by
  rw [transportInverseSqrt, ← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self Z hZ.posSemidef.nonneg]

/-- Correlated trace interpolation uses the actual inverse transport, not a norm estimate. -/
theorem balancedDyadicRoot_trace_le (m : ℕ) (hm : 1 ≤ m)
    {S Z X : Matrix n n ℂ} (hS : S.PosSemidef) (hZ : Z.PosDef) (hX : X.PosSemidef) :
    realTrace (balancedDyadicRoot m S Z * X) ≤
      realTrace (Z⁻¹ * X) ^ (1 - 2 / (2 : ℝ) ^ m) *
        realTrace (balancedRoot S Z * X) ^ (2 / (2 : ℝ) ^ m) := by
  have h := DyadicTraceInterpolation.correlated_trace_dyadic_le m hm
    (transportInverseSqrt Z) hS hX
  simpa only [(transportInverseSqrt_posDef hZ).isHermitian.eq,
    transportInverseSqrt_square hZ, balancedDyadicRoot, balancedRoot] using h

/-- The missing balanced endpoint is exactly the actual source trace. -/
theorem realTrace_inverseTransport_balancedDensity {S M Z : Matrix n n ℂ}
    (hZ : Z.PosDef) (htransport : Z * M * Z = S) :
    realTrace (Z⁻¹ * balancedDensity S Z) = realTrace M := by
  rw [balancedDensity_eq_source_congruence hZ htransport, ← transportInverseSqrt_square hZ]
  calc
    _ = realTrace ((transportInverseSqrt Z * transportInverseSqrt Z * CFC.sqrt Z * M) *
        CFC.sqrt Z) := by simp only [Matrix.mul_assoc]
    _ = realTrace ((CFC.sqrt Z * transportInverseSqrt Z) *
        (transportInverseSqrt Z * CFC.sqrt Z) * M) := by
      rw [realTrace_mul_comm]
      simp only [Matrix.mul_assoc]
    _ = realTrace M := by rw [sqrt_mul_transportInverseSqrt hZ,
      transportInverseSqrt_mul_sqrt hZ, Matrix.one_mul, Matrix.one_mul]

/-- At actual covariance transport this endpoint costs only the retained label count. -/
theorem balancedTransport_inverseDensity_budget (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    {S : Matrix n n ℂ} (hS : S.PosDef) (htrace : realTrace S ≤ 1)
    (hM : (covarianceSource A C S).PosDef) :
    let Z := transportOptimizer S (covarianceSource A C S)
    realTrace (Z⁻¹ * balancedDensity S Z) ≤ (Fintype.card ι : ℝ) := by
  dsimp only
  rw [realTrace_inverseTransport_balancedDensity (transportOptimizer_posDef hS hM)
    (transportOptimizer_solve hS hM)]
  have hsource := realTrace_covarianceSource_le_card A hA hN hC0 hC1 hS.posSemidef
  have hlast := mul_le_mul_of_nonneg_left htrace (Nat.cast_nonneg (Fintype.card ι) :
    (0 : ℝ) ≤ Fintype.card ι)
  simpa only [mul_one] using hsource.trans hlast

/-- All three physical budgets share the same actual transport and retained label count. -/
theorem balancedTransport_three_budgets (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    {S : Matrix n n ℂ} (hS : S.PosDef) (htrace : realTrace S ≤ 1)
    (hM : (covarianceSource A C S).PosDef) :
    let Z := transportOptimizer S (covarianceSource A C S)
    realTrace (balancedDensity S Z) ≤ Real.sqrt (Fintype.card ι : ℝ) ∧
      realTrace (balancedRoot S Z * balancedRoot S Z) ≤ (Fintype.card ι : ℝ) ∧
      realTrace (Z⁻¹ * balancedDensity S Z) ≤ (Fintype.card ι : ℝ) := by
  have h := balancedTransport_covariance_budgets A hA hN hC0 hC1 hS htrace hM
  exact ⟨h.1, h.2, balancedTransport_inverseDensity_budget A hA hN hC0 hC1 hS htrace hM⟩

end DyadicBalancedModel
end MatrixSpencer
