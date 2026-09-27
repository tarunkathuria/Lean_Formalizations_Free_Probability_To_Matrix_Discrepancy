import MatrixSpencer.DyadicSingularResponseTransfer
import MatrixSpencer.DyadicPotentialResponse

/-! The actual optimized dyadic potential transfers to the reduced model
curvature for every supported force. The original Kraus source may be singular,
and the reduced density need not have trace one. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

namespace MatrixSpencer
namespace DyadicSupportedPotentialResponse
noncomputable section

set_option maxHeartbeats 600000

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

local instance dyadicSupportedPotentialCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance dyadicSupportedPotentialSpace {j : Type*} [Fintype j] [DecidableEq j] :
    NormedSpace ℝ (selfAdjoint (Matrix j j ℂ)) := inferInstance

open DyadicSingularResponseTransfer

/-- The actual trace-zero optimizer response is bounded by the reduced model inverse. -/
theorem response_supported_le_model (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (F : selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ)) :
    let X := hermitianRectangularEmbeddingCLM (krausSupportEmbedding B) F
    realTrace ((dyadicDensityResponseDerivative H B m hm θ hθ S hS X : Matrix n n ℂ) *
      (X : Matrix n n ℂ)) ≤
      tracePairing (F : Matrix _ _ ℂ)
        ((reducedModelDensityEquiv B m θ hθ S hS).symm (tracePairing (F : Matrix _ _ ℂ))) := by
  dsimp only
  rw [realTrace_mul_comm]
  change densityCenterFunctional (hermitianRectangularEmbeddingCLM (krausSupportEmbedding B) F)
    ((dyadicDensityTangentHessianEquiv H B m hm θ hθ S hS).symm
      (densityCenterFunctional (hermitianRectangularEmbeddingCLM (krausSupportEmbedding B) F))) ≤ _
  simp only [densityCenterFunctional_supported_pullback B F]
  have ht := constrained_inverse_response_le_model (n := n) (ι := ι) H B hB m hm θ hθ S hS
    (tracePairing (F : Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ))
  dsimp only at ht
  exact ht

/-- The genuine supremum-potential Hessian is bounded by the reduced comparison inverse. -/
theorem potential_hessian_supported_le_model [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (F : selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ)) :
    let S := hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) B m θ
    let X := hermitianRectangularEmbeddingCLM (krausSupportEmbedding B) F
    fderiv ℝ (fun K => fderiv ℝ (hermitianDyadicDensityPotential B m θ) K) H X X ≤
      tracePairing (F : Matrix _ _ ℂ)
        ((reducedModelDensityEquiv B m θ hθ S
          (hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) B m hm θ hθ)).symm
            (tracePairing (F : Matrix _ _ ℂ))) := by
  dsimp only
  rw [fderiv_fderiv_hermitianDyadicDensityPotential_apply H _ _ B m hm θ hθ]
  exact response_supported_le_model (n := n) (ι := ι) (H : Matrix n n ℂ) B hB m hm θ hθ
    (hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) B m θ)
    (hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) B m hm θ hθ) F

end
end DyadicSupportedPotentialResponse
end MatrixSpencer
