import HigherRankKS.SylvesterMetric
import MatrixSpencer.FidelityHessian

/-! The actual differentiated transport equation becomes the Sylvester
equation after balancing by the positive square root of the transport. -/

open Matrix MatrixSpencer
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS.BalancedTransportResponse

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance balancedResponseCStar : CStarAlgebra (Matrix n n ℂ) := {}

theorem normalized_transport_solve (Z M U X Y : Matrix n n ℂ) (hZ : IsUnit Z)
    (hres : U * M * (Z * Z) + (Z * Z) * M * U = X - (Z * Z) * Y * (Z * Z)) :
    sylvester (Z * M * Z) (Z⁻¹ * U * Z⁻¹) = Z⁻¹ * X * Z⁻¹ - Z * Y * Z := by
  have hi := Matrix.nonsing_inv_mul Z (Z.isUnit_iff_isUnit_det.mp hZ)
  have hir := Matrix.mul_nonsing_inv Z (Z.isUnit_iff_isUnit_det.mp hZ)
  have hl (B : Matrix n n ℂ) : Z⁻¹ * (Z * B) = B := by rw [← Matrix.mul_assoc, hi, Matrix.one_mul]
  have hr (B : Matrix n n ℂ) : Z * (Z⁻¹ * B) = B := by rw [← Matrix.mul_assoc, hir, Matrix.one_mul]
  have h := congrArg (fun B => Z⁻¹ * B * Z⁻¹) hres
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc, hl, hir, Matrix.mul_one] at h
  simp only [sylvester_apply, Matrix.mul_assoc, hl, hr]
  rw [add_comm]
  exact h

/-- The transport response cost is exactly the inverse-Sylvester energy
of the balanced mismatch, with its actual inverse solution. -/
theorem normalized_transport_energy (Z M U X Y : Matrix n n ℂ) (hZ : IsUnit Z)
    (hP : (Z * M * Z).PosDef)
    (hres : U * M * (Z * Z) + (Z * Z) * M * U = X - (Z * Z) * Y * (Z * Z)) :
    SylvesterMetric.energy (Z * M * Z) hP (Z⁻¹ * X * Z⁻¹ - Z * Y * Z) =
      2 * realTrace ((Z * Z)⁻¹ * U * M * U) := by
  let P := Z * M * Z
  let V := Z⁻¹ * U * Z⁻¹
  let R := Z⁻¹ * X * Z⁻¹ - Z * Y * Z
  have hsolve : sylvester P V = R := normalized_transport_solve Z M U X Y hZ hres
  have hinv : SylvesterMetric.inverse P hP R = V := by
    apply (sylvesterEquiv P hP).injective
    exact (SylvesterMetric.inverse_solve P hP R).trans hsolve.symm
  have hi := Matrix.nonsing_inv_mul Z (Z.isUnit_iff_isUnit_det.mp hZ)
  have hir := Matrix.mul_nonsing_inv Z (Z.isUnit_iff_isUnit_det.mp hZ)
  have hr (B : Matrix n n ℂ) : Z * (Z⁻¹ * B) = B := by rw [← Matrix.mul_assoc, hir, Matrix.one_mul]
  have htrace : realTrace (P * V * V) = realTrace ((Z * Z)⁻¹ * U * M * U) := by
    calc
      _ = realTrace (Z * (M * U * Z⁻¹ * Z⁻¹ * U * Z⁻¹)) := by
        simp only [P, V, Matrix.mul_assoc, hr]
      _ = realTrace ((M * U * Z⁻¹ * Z⁻¹ * U * Z⁻¹) * Z) := realTrace_mul_comm _ _
      _ = realTrace (M * U * Z⁻¹ * Z⁻¹ * U) := by rw [Matrix.mul_assoc _ Z⁻¹ Z, hi, Matrix.mul_one]
      _ = realTrace ((Z⁻¹ * Z⁻¹ * U) * (M * U)) := by
        simpa only [Matrix.mul_assoc] using realTrace_mul_comm (M * U) (Z⁻¹ * Z⁻¹ * U)
      _ = _ := by rw [Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
  have hcycle : realTrace (V * P * V) = realTrace (P * V * V) := by
    simpa only [Matrix.mul_assoc] using realTrace_mul_comm V (P * V)
  change realTrace (R * SylvesterMetric.inverse P hP R) = _
  rw [hinv, ← hsolve, sylvester_apply, Matrix.add_mul, realTrace_add, hcycle, htrace]
  ring

def weight (S M : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt (transportOptimizer S M) * M * CFC.sqrt (transportOptimizer S M)

theorem weight_posDef {S M : Matrix n n ℂ} (hS : S.PosDef) (hM : M.PosDef) :
    (weight S M).PosDef := by
  have hZ := (transportOptimizer_posDef hS hM).posDef_sqrt
  simpa only [weight, hZ.isHermitian.eq] using
    hM.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hZ.isUnit)

def mismatch (T X Y : Matrix n n ℂ) : Matrix n n ℂ :=
  (CFC.sqrt T)⁻¹ * X * (CFC.sqrt T)⁻¹ - CFC.sqrt T * Y * CFC.sqrt T

/-- The exact joint fidelity Hessian is minus the inverse-Sylvester energy
of the balanced density/source mismatch. The transport is the actual
constructed optimizer, not an arbitrary transport certificate. -/
theorem doubleFidelity_hessian_eq_energy
    (S M X Y : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    fderiv ℝ (fderiv ℝ (doubleFidelity (n := n))) (S, M) (X, Y) (X, Y) =
      -SylvesterMetric.energy (weight (S : Matrix n n ℂ) (M : Matrix n n ℂ)) (weight_posDef hS hM)
        (mismatch (transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ))
          (X : Matrix n n ℂ) (Y : Matrix n n ℂ)) := by
  let T := transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ)
  let U := fderiv ℝ jointTransportOptimizer (S, M) (X, Y)
  have hT : T.PosDef := transportOptimizer_posDef hS hM
  have hsquare : CFC.sqrt T * CFC.sqrt T = T := CFC.sqrt_mul_sqrt_self T hT.posSemidef.nonneg
  have hres : U * (M : Matrix n n ℂ) * (CFC.sqrt T * CFC.sqrt T) +
      (CFC.sqrt T * CFC.sqrt T) * (M : Matrix n n ℂ) * U =
      (X : Matrix n n ℂ) - (CFC.sqrt T * CFC.sqrt T) * (Y : Matrix n n ℂ) *
        (CFC.sqrt T * CFC.sqrt T) := by
    simpa only [hsquare] using fderiv_jointTransportOptimizer_solve S M X Y hS hM
  have he := normalized_transport_energy (CFC.sqrt T) M U X Y hT.posDef_sqrt.isUnit
    (weight_posDef hS hM) hres
  rw [hsquare] at he
  rw [fderiv_fderiv_doubleFidelity_quadratic S M X Y hS hM]
  change -2 * realTrace (T⁻¹ * U * (M : Matrix n n ℂ) * U) =
    -SylvesterMetric.energy (CFC.sqrt T * (M : Matrix n n ℂ) * CFC.sqrt T)
      (weight_posDef hS hM) ((CFC.sqrt T)⁻¹ * (X : Matrix n n ℂ) * (CFC.sqrt T)⁻¹ -
        CFC.sqrt T * (Y : Matrix n n ℂ) * CFC.sqrt T)
  rw [he]
  ring

end HigherRankKS.BalancedTransportResponse
