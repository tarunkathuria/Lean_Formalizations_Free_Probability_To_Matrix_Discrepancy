import MatrixSpencer.DyadicSingularResponseTransfer
import MatrixSpencer.DyadicObservedCapResponse
import MatrixSpencer.FaithfulResponse

/-! The reduced model inverse in exact balanced and whitened coordinates.
The free curvature is the actual fidelity Hessian; the regularizer curvature
is the inverse of the explicit comparison model. -/

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer
namespace DyadicModelBalancedResponse
open DyadicSingularResponseTransfer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance modelBalancedCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance modelBalancedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance modelBalancedFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

def balancedModelFullSuper (B : ι → Matrix n n ℂ) (m : ℕ) (c : ℝ) (S Z : Matrix n n ℂ) :
    Matrix (n × n) (n × n) ℂ :=
  balancedFreeSuper B S Z + DyadicBalancedModel.balancedCurvatureSuper m c S Z

lemma balancedModelFullSuper_posDef (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (m : ℕ) {c : ℝ} (hc : 0 < c)
    {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef) :
    (balancedModelFullSuper B m c S Z).PosDef :=
  Matrix.PosDef.posSemidef_add (balancedFreeSuper_posSemidef B hB hS hZ)
    (DyadicBalancedModel.balancedCurvatureSuper_posDef m hc hS hZ)

/-- The explicit model matrix represents exactly the pulled-back model bilinear form. -/
theorem modelDensityBilinear_balanced (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S X Y : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
    modelDensityBilinear B m c hc S hS (G X) (G Y) =
      RCLike.re (star (matrixVector Y) ⬝ᵥ (balancedModelFullSuper B m c S Z *ᵥ matrixVector X)) := by
  dsimp only
  rw [modelDensityBilinear_apply, balancedFreeHessian_actual_hessian B hB S X Y hS hM,
    modelCurvatureBilinear_apply, ← DyadicBalancedModel.balancedCurvatureEquiv_pairing m c hc
      (S : Matrix n n ℂ) hS _ (transportOptimizer_posDef hS hM) X Y]
  rw [balancedModelFullSuper, Matrix.add_mulVec,
    balancedFreeSuper_represents B (S : Matrix n n ℂ) _ hS (transportOptimizer_posDef hS hM),
    DyadicBalancedModel.balancedCurvatureSuper_represents m c hc (S : Matrix n n ℂ) hS _
      (transportOptimizer_posDef hS hM), dotProduct_add, map_add,
    matrixVector_dotProduct, matrixVector_dotProduct]
  change -(-realTrace (_ * (Y : Matrix n n ℂ))) + realTrace (_ * (Y : Matrix n n ℂ)) =
    realTrace ((Y : Matrix n n ℂ)ᴴ * _) + realTrace ((Y : Matrix n n ℂ)ᴴ * _)
  rw [show (Y : Matrix n n ℂ)ᴴ = Y from Y.property,
    realTrace_mul_comm (Y : Matrix n n ℂ), realTrace_mul_comm (Y : Matrix n n ℂ)]
  ring

lemma modelDensityInverse_normal (B : ι → Matrix n n ℂ) (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (X Y : selfAdjoint (Matrix n n ℂ)) :
    modelDensityBilinear B m c hc S hS
      ((modelDensityEquiv B m c hc S hS).symm (tracePairing (X : Matrix n n ℂ))) Y =
        tracePairing (X : Matrix n n ℂ) Y := by
  change modelDensityEquiv B m c hc S hS
    ((modelDensityEquiv B m c hc S hS).symm (tracePairing (X : Matrix n n ℂ))) Y = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

lemma modelDensityInverse_balanced_energy (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
    let U := (modelDensityEquiv B m c hc S hS).symm (tracePairing (X : Matrix n n ℂ))
    let y := matrixVector (G.symm U)
    RCLike.re (star y ⬝ᵥ (balancedModelFullSuper B m c S Z *ᵥ y)) =
      realTrace ((X : Matrix n n ℂ) * (U : Matrix n n ℂ)) := by
  dsimp only
  rw [← modelDensityBilinear_balanced B hB m c hc S _ _ hS hM]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  exact modelDensityInverse_normal B m c hc S hS X _

lemma modelDensityInverse_balanced_trial (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
    let U := (modelDensityEquiv B m c hc S hS).symm (tracePairing (X : Matrix n n ℂ))
    let y := matrixVector (G.symm U)
    2 * RCLike.re (star (matrixVector (G X)) ⬝ᵥ y) -
      RCLike.re (star y ⬝ᵥ (balancedModelFullSuper B m c S Z *ᵥ y)) =
      tracePairing (X : Matrix n n ℂ) U := by
  dsimp only
  rw [balanced_force_pairing, modelDensityInverse_balanced_energy B hB m c hc S X hS hM,
    tracePairing_apply]
  ring

lemma modelDensityInverse_le_balanced_inverse (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
    tracePairing (X : Matrix n n ℂ)
      ((modelDensityEquiv B m c hc S hS).symm (tracePairing (X : Matrix n n ℂ))) ≤
      ComplexInverseComparison.quadratic (balancedModelFullSuper B m c S Z)⁻¹ (matrixVector (G X)) := by
  dsimp only
  rw [← modelDensityInverse_balanced_trial B hB m c hc S X hS hM]
  exact ComplexInverseComparison.inverse_variational_le
    (balancedModelFullSuper_posDef B hB m hc hS (transportOptimizer_posDef hS hM)) _ _

def balancedModelWhitenedFull (B : ι → Matrix n n ℂ) (m : ℕ) (c : ℝ) (S Z : Matrix n n ℂ) :
    Matrix (n × n) (n × n) ℂ :=
  whitenedFull (jordanSuper (balancedDensity S Z)) (krausSuper (balancedKraus B Z))
    (DyadicBalancedModel.balancedInverseModelSuper m c S Z)

lemma balancedModelWhitenedFull_eq (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian)
    (m : ℕ) (c : ℝ) {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef) :
    balancedModelWhitenedFull B m c S Z =
      CFC.sqrt (jordanSuper (balancedDensity S Z)) * balancedModelFullSuper B m c S Z *
        CFC.sqrt (jordanSuper (balancedDensity S Z)) :=
  whitenedFull_eq (jordanSuper_posDef (balancedDensity_posDef hS hZ))
    (KrausContraction.super_hermitian _ (balancedKraus_isHermitian B hB Z)) _

lemma balancedModel_inverse_response_eq_whitened (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (m : ℕ) (c : ℝ) {S Z : Matrix n n ℂ}
    (hS : S.PosDef) (hZ : Z.PosDef) (f : n × n → ℂ) :
    ComplexInverseComparison.quadratic (balancedModelFullSuper B m c S Z)⁻¹ f =
      ComplexInverseComparison.quadratic (balancedModelWhitenedFull B m c S Z)⁻¹
        (CFC.sqrt (jordanSuper (balancedDensity S Z)) *ᵥ f) := by
  have hh := (jordanSuper_posDef (balancedDensity_posDef hS hZ)).posDef_sqrt.isHermitian
  have he : (balancedModelFullSuper B m c S Z)⁻¹ =
      CFC.sqrt (jordanSuper (balancedDensity S Z)) * (balancedModelWhitenedFull B m c S Z)⁻¹ *
        CFC.sqrt (jordanSuper (balancedDensity S Z)) := by
    rw [balancedModelWhitenedFull_eq B hB m c hS hZ,
      sqrt_inverse_congruence _ _ (jordanSuper_posDef (balancedDensity_posDef hS hZ))]
  rw [he]
  conv_lhs => arg 1; rhs; rw [← hh.eq]
  rw [ComplexInverseComparison.quadratic_congruence, hh.eq]

/-- Actual normal equations of the reduced model give its observed whitened bound. -/
theorem modelDensityInverse_le_whitened_inverse (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
    tracePairing (X : Matrix n n ℂ)
      ((modelDensityEquiv B m c hc S hS).symm (tracePairing (X : Matrix n n ℂ))) ≤
      ComplexInverseComparison.quadratic (balancedModelWhitenedFull B m c S Z)⁻¹
        (CFC.sqrt (jordanSuper (balancedDensity S Z)) *ᵥ matrixVector (G X)) := by
  dsimp only
  rw [← balancedModel_inverse_response_eq_whitened B hB m c hS (transportOptimizer_posDef hS hM)]
  exact modelDensityInverse_le_balanced_inverse B hB m c hc S X hS hM

end DyadicModelBalancedResponse
end MatrixSpencer
