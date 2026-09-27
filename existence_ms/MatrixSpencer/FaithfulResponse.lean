import MatrixSpencer.JordanWhitening
import MatrixSpencer.OptimizerResponse
import MatrixSpencer.ComplexInverseComparison

/-!
# The actual constrained response in balanced coordinates

The force and the response below are the physical center direction and the
actual inverse of the trace-zero Hessian. The energy identity is proved from
the normal equation, not supplied as an optimization hypothesis.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

local instance faithfulResponseCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance faithfulResponseNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance faithfulResponseFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

/-- The actual constrained inverse solves the full normal equation on every trace-zero test. -/
theorem densityResponseDerivative_normal (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef)
    (X : selfAdjoint (Matrix n n ℂ)) (W : densityTangent (n := n)) :
    densityNegativeHessian H B θ S (densityResponseDerivative H B θ hθ S hS hM X) W =
      realTrace ((X : Matrix n n ℂ) * ((W : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) := by
  let U := (densityTangentHessianEquiv H B θ hθ S hS hM).symm (densityCenterFunctional X)
  change densityTangentHessianEquiv H B θ hθ S hS hM U W = densityCenterFunctional X W
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- Testing with the actual response identifies its energy with the response quadratic form. -/
theorem densityResponseDerivative_energy (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef)
    (X : selfAdjoint (Matrix n n ℂ)) :
    densityNegativeHessian H B θ S (densityResponseDerivative H B θ hθ S hS hM X)
      (densityResponseDerivative H B θ hθ S hS hM X) =
      realTrace ((X : Matrix n n ℂ) * (densityResponseDerivative H B θ hθ S hS hM X : Matrix n n ℂ)) := by
  exact densityResponseDerivative_normal H B θ hθ S hS hM X
    ((densityTangentHessianEquiv H B θ hθ S hS hM).symm (densityCenterFunctional X))

omit [Fintype ι] in
/-- The balanced force is the dual of the frozen density coordinate change. -/
theorem balanced_force_pairing (Z : Matrix n n ℂ) (hZ : Z.PosDef)
    (X V : selfAdjoint (Matrix n n ℂ)) :
    RCLike.re (star (matrixVector (balancedCoordinateEquiv Z hZ X : Matrix n n ℂ)) ⬝ᵥ
      matrixVector ((balancedCoordinateEquiv Z hZ).symm V : Matrix n n ℂ)) =
      realTrace ((X : Matrix n n ℂ) * (V : Matrix n n ℂ)) := by
  rw [matrixVector_dotProduct]
  change realTrace ((balancedCoordinateEquiv Z hZ X : Matrix n n ℂ)ᴴ *
    ((balancedCoordinateEquiv Z hZ).symm V : Matrix n n ℂ)) = _
  rw [show (balancedCoordinateEquiv Z hZ X : Matrix n n ℂ)ᴴ =
    (balancedCoordinateEquiv Z hZ X : Matrix n n ℂ) from (balancedCoordinateEquiv Z hZ X).property,
    realTrace_mul_comm, balancedCoordinateEquiv_coe, balancedCoordinateEquiv_symm_coe,
    realTrace_balanced_inverse_pair Z V X hZ, realTrace_mul_comm]

/-- The actual constrained response has exactly the balanced full-Hessian energy. -/
theorem balanced_response_energy (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
    let V := densityResponseDerivative H B θ hθ S hS hM X
    let y := matrixVector (G.symm V)
    RCLike.re (star y ⬝ᵥ (balancedFullSuper B θ S Z *ᵥ y)) =
      realTrace ((X : Matrix n n ℂ) * (V : Matrix n n ℂ)) := by
  dsimp only
  rw [← balancedFullSuper_actual_hessian H B hB θ hθ S _ _ hS hM]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  exact densityResponseDerivative_energy H B θ hθ S hS hM X

/-- The actual response attains this trial value in the unrestricted balanced variational form. -/
theorem balanced_response_trial_value (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
    let V := densityResponseDerivative H B θ hθ S hS hM X
    let y := matrixVector (G.symm V)
    2 * RCLike.re (star (matrixVector (G X)) ⬝ᵥ y) -
      RCLike.re (star y ⬝ᵥ (balancedFullSuper B θ S Z *ᵥ y)) =
      realTrace ((V : Matrix n n ℂ) * (X : Matrix n n ℂ)) := by
  dsimp only
  rw [balanced_force_pairing, balanced_response_energy H B hB θ hθ S X hS hM,
    realTrace_mul_comm (X : Matrix n n ℂ)]
  ring

/-- The actual trace-constrained response is bounded by the unrestricted balanced inverse. -/
theorem densityResponseDerivative_le_balanced_inverse (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
    realTrace ((densityResponseDerivative H B θ hθ S hS hM X : Matrix n n ℂ) * (X : Matrix n n ℂ)) ≤
      ComplexInverseComparison.quadratic (balancedFullSuper B θ S Z)⁻¹ (matrixVector (G X)) := by
  dsimp only
  rw [← balanced_response_trial_value H B hB θ hθ S X hS hM]
  exact ComplexInverseComparison.inverse_variational_le
    (balancedFullSuper_posDef B hB hθ hS (transportOptimizer_posDef hS hM)) _ _

omit [Fintype ι] in
/-- Inverting the exact Jordan congruence preserves both inverse square-root factors. -/
theorem sqrt_inverse_congruence (J A : Matrix n n ℂ) (hJ : J.PosDef) :
    CFC.sqrt J * (CFC.sqrt J * A * CFC.sqrt J)⁻¹ * CFC.sqrt J = A⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  change CFC.sqrt J * (transportInverseSqrt J * (A⁻¹ * transportInverseSqrt J)) * CFC.sqrt J = A⁻¹
  calc
    _ = (CFC.sqrt J * transportInverseSqrt J) * A⁻¹ *
        (transportInverseSqrt J * CFC.sqrt J) := by noncomm_ring
    _ = _ := by rw [sqrt_mul_transportInverseSqrt hJ, transportInverseSqrt_mul_sqrt hJ,
      Matrix.one_mul, Matrix.mul_one]

theorem balancedFullSuper_inverse_congruence (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (θ : ℝ) {S Z : Matrix n n ℂ}
    (hS : S.PosDef) (hZ : Z.PosDef) :
    (balancedFullSuper B θ S Z)⁻¹ =
      CFC.sqrt (jordanSuper (balancedDensity S Z)) * (balancedWhitenedFull B θ S Z)⁻¹ *
        CFC.sqrt (jordanSuper (balancedDensity S Z)) := by
  rw [balancedWhitenedFull_eq B hB θ hS hZ,
    sqrt_inverse_congruence _ _ (jordanSuper_posDef (balancedDensity_posDef hS hZ))]

theorem balanced_inverse_response_eq_whitened (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (θ : ℝ) {S Z : Matrix n n ℂ}
    (hS : S.PosDef) (hZ : Z.PosDef) (f : n × n → ℂ) :
    ComplexInverseComparison.quadratic (balancedFullSuper B θ S Z)⁻¹ f =
      ComplexInverseComparison.quadratic (balancedWhitenedFull B θ S Z)⁻¹
        (CFC.sqrt (jordanSuper (balancedDensity S Z)) *ᵥ f) := by
  have hh := (jordanSuper_posDef (balancedDensity_posDef hS hZ)).posDef_sqrt.isHermitian
  rw [balancedFullSuper_inverse_congruence B hB θ hS hZ]
  conv_lhs => arg 1; rhs; rw [← hh.eq]
  rw [ComplexInverseComparison.quadratic_congruence, hh.eq]

/-- Exact actual-potential response bound in the coordinates used by the spectral estimate. -/
theorem potential_hessian_le_whitened_inverse [Nonempty n]
    (H X : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    (hM : (krausChannel B (densityOptimizer (H : Matrix n n ℂ) B θ)).PosDef) :
    let S := hermitianDensityOptimizer (H : Matrix n n ℂ) B θ
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef
      (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
      (hermitianDensityOptimizer_source_posDef (H : Matrix n n ℂ) B θ hM))
    fderiv ℝ (fun K => fderiv ℝ (hermitianDensityPotential B θ) K) H X X ≤
      ComplexInverseComparison.quadratic (balancedWhitenedFull B θ S Z)⁻¹
        (CFC.sqrt (jordanSuper (balancedDensity S Z)) *ᵥ matrixVector (G X)) := by
  dsimp only
  rw [fderiv_fderiv_hermitianDensityPotential_apply H X X B hθ hM,
    ← balanced_inverse_response_eq_whitened B hB θ
      (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
      (transportOptimizer_posDef (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
        (hermitianDensityOptimizer_source_posDef (H : Matrix n n ℂ) B θ hM))]
  exact densityResponseDerivative_le_balanced_inverse (H : Matrix n n ℂ) B hB θ hθ _ X
    (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
    (hermitianDensityOptimizer_source_posDef (H : Matrix n n ℂ) B θ hM)

end MatrixSpencer
