import MatrixSpencer.FixedFaceSampler
import MatrixSpencer.DyadicFiniteOwnerDrift

/-! A common dyadic drift mesh for every dominated covariance on a fixed face. -/
open Set Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι κ n : Type*} [Fintype ι] [Fintype κ] [Fintype n]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq n]
local instance dyadicFixedFaceSamplerCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicFixedFaceSamplerPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicFixedFaceSamplerCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix κ κ ℝ)) := inferInstance

/-- Every dominated covariance is handled by one mesh for the fixed face U.
The mesh depends on U, the center radius, and the positive floor; it does not
depend on the current K, the sampler eigenbasis, or the chosen Q. -/
theorem uniform_dyadicOwner_sampler_drift_on_fixedFace [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (U : Matrix ι κ ℝ) (hU : Uᵀ * U = 1) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (R : ℝ) {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, δ ≤ (1 / 2 : ℝ) ∧
      ∀ (H : selfAdjoint (Matrix n n ℂ)) (K : selfAdjoint (Matrix κ κ ℝ)),
      ‖H‖ ≤ R → a • (1 : Matrix κ κ ℝ) ≤ (K : Matrix κ κ ℝ) →
      (K : Matrix κ κ ℝ) ≤ 1 →
      ∀ (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef), Q ≤ covarianceLift U K →
      0 < realTrace Q → ∀ h ∈ Icc (0 : ℝ) δ,
        (∑ s, covarianceSampleWeight hQ s *
          (dyadicOwnerPotential (H + h • ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)) A
              (covarianceLift U K - h ^ 2 • Q) m θ - dyadicOwnerPotential H A (covarianceLift U K) m θ)) ≤
          h ^ 2 * realTrace (Q * dyadicOwnerCoefficientResponse A hA (covarianceLift U K) m θ H) + ε * h ^ 2 := by
  obtain ⟨B, _hB, hBbound⟩ :=
    (CovarianceCompactChart.isCompact_nonnegative_interval (1 : Matrix κ κ ℝ)).isBounded.exists_pos_norm_le
  obtain ⟨δ, hδ, hb⟩ := uniform_covarianceSample_dyadicOwner_drift_fixedFace A hA U m hm θ hθ R
    (Real.sqrt (Fintype.card ι) * ∑ i, ‖A i‖) B ha hε
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  intro H K hH hfloor hKcap Q hQ hQC htrace h hh
  let L : selfAdjoint (Matrix κ κ ℝ) :=
    ⟨Uᵀ * Q * U, (covarianceFace_compress_posSemidef U hQ).isHermitian⟩
  have hL : (L : Matrix κ κ ℝ).PosSemidef := covarianceFace_compress_posSemidef U hQ
  have hLcap : (L : Matrix κ κ ℝ) ≤ 1 := (covarianceFace_compress_le U hU K hQC).trans hKcap
  have hLnorm : ‖L‖ ≤ B := hBbound L ⟨hL.nonneg, hLcap⟩
  have hQl : Q = covarianceLift U L := (covarianceFace_reconstruct_of_le U hU K hQ hQC).symm
  have hQcap : Q ≤ 1 := hQC.trans (covarianceLift_le_one U hU hKcap)
  exact hb H K L hH hfloor hKcap hLnorm hL Q hQ hQl htrace
    (fun s _ => covarianceSample_owner_norm_le A hA hQ hQcap s)
    h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩


end
end MatrixSpencer
