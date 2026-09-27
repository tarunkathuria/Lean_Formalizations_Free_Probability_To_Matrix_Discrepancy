import MatrixSpencer.MSManuscriptFrameFamily
import MatrixSpencer.MSManuscriptGammaSmoothness
import MatrixSpencer.RectangularRidgeOwnerShavingDerivative
import MatrixSpencer.RectangularRidgePaidQueries

/-! Transport of the actual reduced numerical cap to supported physical
coefficient directions. The proof compares derivatives of identical shaved
potential functions, so no equality of arbitrarily chosen optimizers is assumed. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeSupportedCap
variable {N k d : ℕ} [Nonempty (Fin d)]
local instance ridgeSupportedCapCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 300000
attribute [local irreducible] RectangularRidgePotential.optimizer
open RectangularRidgePaidQueries (gram)

def value (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix (Fin N) (Fin N) ℝ) (m : ℕ) (θ κ : ℝ) : ℝ :=
  regularizedOwnerPotential H A C (RectangularRidgeCovarianceCalculus.regularizer m θ κ)

theorem supported_quadratic_eq (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i, (A i).IsHermitian)
    (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1)
    {K : Matrix (Fin k) (Fin k) ℝ} (hK : K.PosDef) (m : ℕ) (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (u : EuclideanSpace ℝ (Fin N))
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (covarianceLift U K)).toLinearMap) :
    WithLp.ofLp u ⬝ᵥ (gram H A (covarianceLift U K) m θ κ *ᵥ WithLp.ofLp u) =
      (Uᵀ*ᵥWithLp.ofLp u) ⬝ᵥ (gram H (mixFamily A U) K m θ κ *ᵥ (Uᵀ*ᵥWithLp.ofLp u)) := by
  have huRaw := covariance_mem_mulVec_range hu
  rw [covarianceLift_range_of_posDef U hU hK] at huRaw
  let v : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (Uᵀ*ᵥWithLp.ofLp u)
  have hv := MSManuscriptGammaSmoothness.range_mem_of_posDef hK v
  have hp := hasDerivAt_ridgeOwnerPotential_supported_shave H A hA
    (covarianceLift_posSemidef U hK.posSemidef) u hu m hm θ κ hθ hκ
  have hr := hasDerivAt_ridgeOwnerPotential_supported_shave H (mixFamily A U)
    (mixFamily_isHermitian A U hA) hK.posSemidef v hv m hm θ κ hθ hκ
  have he : (fun s : ℝ => value (H : Matrix (Fin d) (Fin d) ℂ) A
      (covarianceLift U K-s • realRankOne (WithLp.ofLp u)) m θ κ) =
      (fun s : ℝ => value (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U)
        (K-s • realRankOne (WithLp.ofLp v)) m θ κ) := by
    funext s
    change value (H : Matrix (Fin d) (Fin d) ℂ) A
      (covarianceLift U K-s • Matrix.vecMulVec (WithLp.ofLp u) (WithLp.ofLp u)) m θ κ = _
    rw [← covarianceLift_supported_shave U hU K huRaw s]
    exact regularizedOwnerPotential_covarianceLift (H : Matrix (Fin d) (Fin d) ℂ) A U _ _
  change HasDerivAt (fun s : ℝ => value (H : Matrix (Fin d) (Fin d) ℂ) A
    (covarianceLift U K-s • realRankOne (WithLp.ofLp u)) m θ κ) _ 0 at hp
  rw [he] at hp
  exact neg_injective (hp.unique hr)

theorem supported_cap (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i, (A i).IsHermitian)
    (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1)
    {K : Matrix (Fin k) (Fin k) ℝ} (hK : K.PosDef) (m : ℕ) (hm : 1 ≤ m) {θ κ t : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (hcap : gram H (mixFamily A U) K m θ κ ≤ t • (1 : Matrix (Fin k) (Fin k) ℝ))
    (u : EuclideanSpace ℝ (Fin N))
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (covarianceLift U K)).toLinearMap) :
    WithLp.ofLp u ⬝ᵥ (gram H A (covarianceLift U K) m θ κ *ᵥ WithLp.ofLp u) ≤
      t*(WithLp.ofLp u ⬝ᵥ WithLp.ofLp u) := by
  have huRaw := covariance_mem_mulVec_range hu
  rw [covarianceLift_range_of_posDef U hU hK] at huRaw
  let v := Uᵀ*ᵥWithLp.ofLp u
  have hvec : WithLp.ofLp u ᵥ* U = v := by
    ext i
    simp [v, Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  have hnorm : v ⬝ᵥ v = WithLp.ofLp u ⬝ᵥ WithLp.ofLp u := by
    calc
      _ = WithLp.ofLp u ⬝ᵥ (U*ᵥv) := by
        conv_rhs => rw [dotProduct_mulVec, hvec]
      _ = _ := by rw [covarianceIsometry_range_projection U hU huRaw]
  have hc := (Matrix.le_iff.mp hcap).2 v
  change 0 ≤ v ⬝ᵥ ((t • (1 : Matrix (Fin k) (Fin k) ℝ)-gram H (mixFamily A U) K m θ κ)*ᵥv) at hc
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_sub,dotProduct_smul] at hc
  rw [supported_quadratic_eq H A hA U hU hK m hm hθ hκ u hu]
  change v ⬝ᵥ (gram H (mixFamily A U) K m θ κ *ᵥv) ≤ _
  rw [← hnorm]
  exact sub_nonneg.mp hc

theorem stored_supported_cap (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i, (A i).IsHermitian)
    (O : MSManuscriptSupportedOwner.Owner N) (m : ℕ) (hm : 1 ≤ m) {δ θ κ t : ℝ}
    (hδ : 0 < δ) (hO : O.Valid δ) (hθ : 0 < θ) (hκ : 0 < κ)
    (hcap : gram H (mixFamily A O.frame) O.matrix m θ κ ≤
      t • (1 : Matrix (Fin O.dim) (Fin O.dim) ℝ))
    (u : EuclideanSpace ℝ (Fin N))
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) O.physical).toLinearMap) :
    WithLp.ofLp u ⬝ᵥ (gram H A O.physical m θ κ *ᵥ WithLp.ofLp u) ≤
      t*(WithLp.ofLp u ⬝ᵥ WithLp.ofLp u) :=
  supported_cap H A hA O.frame hO.1 (MSManuscriptGammaSmoothness.posDef_of_floor hδ hO.2) m hm hθ hκ hcap u hu

end MatrixSpencer.RectangularRidgeSupportedCap
