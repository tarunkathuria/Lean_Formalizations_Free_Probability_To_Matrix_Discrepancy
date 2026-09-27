import MatrixSpencer.BalancedTsallis
import MatrixSpencer.DensityHessian

/-!
# The actual free Hessian in balanced coordinates

All congruences are frozen at the actual transport point. The channel and
Sylvester inverse retain their order; no commutation between them is assumed.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MatrixSpencer
noncomputable section
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance balancedFreeCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance balancedFreeNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance balancedFreeFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

/-- The concrete defect of the balanced Kraus channel. -/
def balancedDefect (B : ι → Matrix n n ℂ) (Z : Matrix n n ℂ) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  ContinuousLinearMap.id ℝ _ - hermitianKrausChannel (balancedKraus B Z)

theorem balancedKraus_channel_physical (B : ι → Matrix n n ℂ) (Z Y : Matrix n n ℂ) :
    krausChannel (balancedKraus B Z) Y =
      CFC.sqrt Z * krausChannel B (CFC.sqrt Z * Y * CFC.sqrt Z) * CFC.sqrt Z := by
  simp only [krausChannel, balancedKraus, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.conjTranspose_mul, (CFC.sqrt_nonneg Z).posSemidef.isHermitian.eq,
    Matrix.mul_assoc]

/-- Congruencing the differentiated transport equation gives the ordinary balanced Sylvester equation. -/
theorem balanced_transport_sylvester_of_residual (M Z U Y V : Matrix n n ℂ) (hZ : Z.PosDef)
    (hres : U * M * Z + Z * M * U =
      CFC.sqrt Z * Y * CFC.sqrt Z - Z * V * Z) :
    (CFC.sqrt Z * M * CFC.sqrt Z) * (transportInverseSqrt Z * U * transportInverseSqrt Z) +
      (transportInverseSqrt Z * U * transportInverseSqrt Z) * (CFC.sqrt Z * M * CFC.sqrt Z) =
        Y - CFC.sqrt Z * V * CFC.sqrt Z := by
  calc
    _ = CFC.sqrt Z * M * (CFC.sqrt Z * transportInverseSqrt Z) * U * transportInverseSqrt Z +
        transportInverseSqrt Z * U * (transportInverseSqrt Z * CFC.sqrt Z) * M * CFC.sqrt Z := by
      noncomm_ring
    _ = CFC.sqrt Z * M * U * transportInverseSqrt Z + transportInverseSqrt Z * U * M * CFC.sqrt Z := by
      rw [sqrt_mul_transportInverseSqrt hZ, transportInverseSqrt_mul_sqrt hZ,
        Matrix.mul_one, Matrix.mul_one]
    _ = transportInverseSqrt Z * (U * M * Z + Z * M * U) * transportInverseSqrt Z := by
      rw [Matrix.mul_add, Matrix.add_mul]
      conv_rhs =>
        lhs
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
          matrix_mul_transportInverseSqrt hZ]
      conv_rhs =>
        rhs
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
          transportInverseSqrt_mul_self_matrix hZ]
      noncomm_ring
    _ = transportInverseSqrt Z *
        (CFC.sqrt Z * Y * CFC.sqrt Z - Z * V * Z) * transportInverseSqrt Z := by rw [hres]
    _ = (transportInverseSqrt Z * CFC.sqrt Z) * Y * (CFC.sqrt Z * transportInverseSqrt Z) -
        (transportInverseSqrt Z * Z) * V * (Z * transportInverseSqrt Z) := by noncomm_ring
    _ = _ := by
      rw [transportInverseSqrt_mul_sqrt hZ, sqrt_mul_transportInverseSqrt hZ,
        transportInverseSqrt_mul_self_matrix hZ, matrix_mul_transportInverseSqrt hZ,
        Matrix.one_mul, Matrix.mul_one]

omit [Fintype ι] in
theorem realTrace_balanced_inverse_pair (Z U V : Matrix n n ℂ) (hZ : Z.PosDef) :
    realTrace ((transportInverseSqrt Z * U * transportInverseSqrt Z) *
      (CFC.sqrt Z * V * CFC.sqrt Z)) = realTrace (U * V) := by
  rw [realTrace_congruence_pairing]
  have heq : transportInverseSqrt Z * (CFC.sqrt Z * V * CFC.sqrt Z) *
      transportInverseSqrt Z = V := by
    calc
      _ = (transportInverseSqrt Z * CFC.sqrt Z) * V *
          (CFC.sqrt Z * transportInverseSqrt Z) := by noncomm_ring
      _ = _ := by rw [transportInverseSqrt_mul_sqrt hZ, sqrt_mul_transportInverseSqrt hZ,
        Matrix.one_mul, Matrix.mul_one]
  rw [heq]

omit [Fintype ι] in
theorem matrixInverse_mul_sqrt_balanced (Z : Matrix n n ℂ) (hZ : Z.PosDef) :
    Z⁻¹ * CFC.sqrt Z = transportInverseSqrt Z := by
  rw [← matrix_mul_transportInverseSqrt hZ, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul Z (Z.isUnit_iff_isUnit_det.mp hZ.isUnit), Matrix.one_mul]

omit [Fintype ι] in
theorem sqrt_mul_matrixInverse_balanced (Z : Matrix n n ℂ) (hZ : Z.PosDef) :
    CFC.sqrt Z * Z⁻¹ = transportInverseSqrt Z := by
  rw [← transportInverseSqrt_mul_self_matrix hZ, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv Z (Z.isUnit_iff_isUnit_det.mp hZ.isUnit), Matrix.mul_one]

omit [Fintype ι] in
theorem realTrace_balanced_transport_inverse_pair (Z U Y : Matrix n n ℂ) (hZ : Z.PosDef) :
    realTrace (Z⁻¹ * U * Z⁻¹ * (CFC.sqrt Z * Y * CFC.sqrt Z)) =
      realTrace ((transportInverseSqrt Z * U * transportInverseSqrt Z) * Y) := by
  rw [realTrace_congruence_pairing]
  have heq : Z⁻¹ * (CFC.sqrt Z * Y * CFC.sqrt Z) * Z⁻¹ =
      transportInverseSqrt Z * Y * transportInverseSqrt Z := by
    calc
      _ = (Z⁻¹ * CFC.sqrt Z) * Y * (CFC.sqrt Z * Z⁻¹) := by noncomm_ring
      _ = _ := by rw [matrixInverse_mul_sqrt_balanced Z hZ, sqrt_mul_matrixInverse_balanced Z hZ]
  rw [heq, ← realTrace_congruence_pairing]

/-- The ordinary Sylvester equivalence with coefficient equal to the balanced density. -/
def balancedSylvesterEquiv (S Z : Matrix n n ℂ) (hS : S.PosDef) (hZ : Z.PosDef) :
    selfAdjoint (Matrix n n ℂ) ≃L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (sylvesterHermitianEquiv (balancedDensity S Z) (balancedDensity_posDef hS hZ)).toContinuousLinearEquiv

@[simp] theorem balancedSylvesterEquiv_coe (S Z : Matrix n n ℂ)
    (hS : S.PosDef) (hZ : Z.PosDef) (Y : selfAdjoint (Matrix n n ℂ)) :
    (balancedSylvesterEquiv S Z hS hZ Y : Matrix n n ℂ) =
      balancedDensity S Z * (Y : Matrix n n ℂ) + (Y : Matrix n n ℂ) * balancedDensity S Z := rfl

/-- The balanced derivative of the actual optimizing transport, in physical source directions. -/
def balancedTransportResponse (B : ι → Matrix n n ℂ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
  let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
  G.symm.toContinuousLinearMap.comp
    ((fderiv ℝ (jointHermitianTransport (n := n)) (krausSourceJoint B S)).comp
      ((krausSourceJoint B).comp G.toContinuousLinearMap))

theorem balancedTransportResponse_coe (B : ι → Matrix n n ℂ)
    (S Y : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
    (balancedTransportResponse B S hS hM Y : Matrix n n ℂ) = transportInverseSqrt Z *
      fderiv ℝ jointTransportOptimizer (S, hermitianKrausChannel B S)
        (G Y, hermitianKrausChannel B (G Y)) * transportInverseSqrt Z := by
  dsimp only
  change transportInverseSqrt _ *
    (fderiv ℝ jointHermitianTransport (S, hermitianKrausChannel B S)
      (_, _) : Matrix n n ℂ) * transportInverseSqrt _ = _
  rw [fderiv_jointHermitianTransport_coe S (hermitianKrausChannel B S) _ _ hS hM]
  rfl

/-- The actual transport response equals J_P inverse applied to the concrete channel defect. -/
theorem balancedTransportResponse_eq (B : ι → Matrix n n ℂ)
    (S Y : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    balancedTransportResponse B S hS hM Y =
      (balancedSylvesterEquiv (S : Matrix n n ℂ) Z hS (transportOptimizer_posDef hS hM)).symm
        (balancedDefect B Z Y) := by
  dsimp only
  let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
  have hZ : Z.PosDef := transportOptimizer_posDef hS hM
  let G := balancedCoordinateEquiv Z hZ
  let X := G Y
  let V := hermitianKrausChannel B X
  let U := fderiv ℝ jointTransportOptimizer (S, hermitianKrausChannel B S) (X, V)
  apply (balancedSylvesterEquiv (S : Matrix n n ℂ) Z hS hZ).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [balancedSylvesterEquiv_coe, balancedTransportResponse_coe B S Y hS hM,
    balancedDensity_eq_source_congruence hZ (transportOptimizer_solve hS hM)]
  change (CFC.sqrt Z * krausChannel B (S : Matrix n n ℂ) * CFC.sqrt Z) *
      (transportInverseSqrt Z * U * transportInverseSqrt Z) +
    (transportInverseSqrt Z * U * transportInverseSqrt Z) *
      (CFC.sqrt Z * krausChannel B (S : Matrix n n ℂ) * CFC.sqrt Z) =
      (Y : Matrix n n ℂ) - krausChannel (balancedKraus B Z) (Y : Matrix n n ℂ)
  rw [balancedKraus_channel_physical B Z Y]
  exact balanced_transport_sylvester_of_residual _ Z U Y V hZ
    (fderiv_jointTransportOptimizer_solve S (hermitianKrausChannel B S) X V hS hM)

/-- The exact balanced free negative-Hessian operator, with both defect factors retained. -/
def balancedFreeHessian (B : ι → Matrix n n ℂ) (S Z : Matrix n n ℂ)
    (hS : S.PosDef) (hZ : Z.PosDef) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (balancedDefect B Z).comp ((balancedSylvesterEquiv S Z hS hZ).symm.toContinuousLinearMap.comp
    (balancedDefect B Z))

/-- The actual pulled-back free Hessian pairs the balanced transport derivative with the defect. -/
theorem balanced_free_hessian_residual_pair (B : ι → Matrix n n ℂ)
    (S Y Y' : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
    fderiv ℝ (fun T => fderiv ℝ (krausSourceFidelity B) T) S (G Y) (G Y') =
      -realTrace ((balancedTransportResponse B S hS hM Y : Matrix n n ℂ) *
        (balancedDefect B Z Y' : Matrix n n ℂ)) := by
  dsimp only
  let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
  have hZ : Z.PosDef := transportOptimizer_posDef hS hM
  let G := balancedCoordinateEquiv Z hZ
  let U := fderiv ℝ jointTransportOptimizer (S, hermitianKrausChannel B S)
    (G Y, hermitianKrausChannel B (G Y))
  rw [fderiv_fderiv_krausSourceFidelity_apply B S (G Y) (G Y') hS hM]
  change fderiv ℝ (fun P => fderiv ℝ (doubleFidelity (n := n)) P)
    (S, hermitianKrausChannel B S) (G Y, hermitianKrausChannel B (G Y))
      (G Y', hermitianKrausChannel B (G Y')) = _
  rw [fderiv_fderiv_doubleFidelity_apply S (hermitianKrausChannel B S)
    (G Y) (hermitianKrausChannel B (G Y)) (G Y') (hermitianKrausChannel B (G Y')) hS hM]
  rw [balancedTransportResponse_coe B S Y hS hM]
  change -realTrace (Z⁻¹ * U * Z⁻¹ * (CFC.sqrt Z * (Y' : Matrix n n ℂ) * CFC.sqrt Z)) +
      realTrace (U * krausChannel B (CFC.sqrt Z * (Y' : Matrix n n ℂ) * CFC.sqrt Z)) =
    -realTrace ((transportInverseSqrt Z * U * transportInverseSqrt Z) *
      ((Y' : Matrix n n ℂ) - krausChannel (balancedKraus B Z) (Y' : Matrix n n ℂ)))
  rw [realTrace_balanced_transport_inverse_pair Z U Y' hZ]
  have hsecond : realTrace (U * krausChannel B (CFC.sqrt Z * (Y' : Matrix n n ℂ) * CFC.sqrt Z)) =
      realTrace ((transportInverseSqrt Z * U * transportInverseSqrt Z) *
        krausChannel (balancedKraus B Z) (Y' : Matrix n n ℂ)) := by
    rw [balancedKraus_channel_physical]
    exact (realTrace_balanced_inverse_pair Z U _ hZ).symm
  rw [hsecond, Matrix.mul_sub, realTrace_sub]
  ring

/-- Hermitian Kraus matrices make the concrete defect self-adjoint in the trace pairing. -/
theorem balancedDefect_trace_selfadjoint (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (Z : Matrix n n ℂ)
    (X Y : selfAdjoint (Matrix n n ℂ)) :
    realTrace ((balancedDefect B Z X : Matrix n n ℂ) * (Y : Matrix n n ℂ)) =
      realTrace ((X : Matrix n n ℂ) * (balancedDefect B Z Y : Matrix n n ℂ)) := by
  change realTrace (((X : Matrix n n ℂ) - krausChannel (balancedKraus B Z) (X : Matrix n n ℂ)) *
      (Y : Matrix n n ℂ)) = realTrace ((X : Matrix n n ℂ) *
      ((Y : Matrix n n ℂ) - krausChannel (balancedKraus B Z) (Y : Matrix n n ℂ)))
  rw [Matrix.sub_mul, Matrix.mul_sub, realTrace_sub, realTrace_sub,
    realTrace_krausChannel_selfadjoint _ (balancedKraus_isHermitian B hB Z)]

/-- Exact balanced normal form of the actual negative free Hessian:
`(Id − Φ) ∘ J_P⁻¹ ∘ (Id − Φ)`, with no commutation premise. -/
theorem balancedFreeHessian_actual_hessian (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (S Y Y' : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
    fderiv ℝ (fun T => fderiv ℝ (krausSourceFidelity B) T) S (G Y) (G Y') =
      -realTrace ((balancedFreeHessian B (S : Matrix n n ℂ) Z hS
        (transportOptimizer_posDef hS hM) Y : Matrix n n ℂ) * (Y' : Matrix n n ℂ)) := by
  dsimp only
  rw [balanced_free_hessian_residual_pair B S Y Y' hS hM,
    balancedTransportResponse_eq B S Y hS hM]
  congr 1
  exact (balancedDefect_trace_selfadjoint B hB _ _ Y').symm

/-- The exact normal form retains the nonnegative free-curvature quadratic form. -/
theorem balancedFreeHessian_quadratic_nonneg (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (S Y : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    0 ≤ realTrace ((balancedFreeHessian B (S : Matrix n n ℂ) Z hS
      (transportOptimizer_posDef hS hM) Y : Matrix n n ℂ) * (Y : Matrix n n ℂ)) := by
  have hn := fderiv_fderiv_krausSourceFidelity_quadratic_nonpos B S
    (balancedCoordinateEquiv _ (transportOptimizer_posDef hS hM) Y) hS hM
  rw [balancedFreeHessian_actual_hessian B hB S Y Y hS hM] at hn
  exact neg_nonpos.mp hn

end
end MatrixSpencer
