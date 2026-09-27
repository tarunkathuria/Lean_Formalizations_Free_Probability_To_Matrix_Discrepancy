import MatrixSpencer.FiniteOwnerDrift
import MatrixSpencer.DyadicFixedFaceOwnerTaylor

/-! Finite averaging of the actual dyadic potential Hessian and covariance payment. -/
open Set Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι κ n : Type*} [Fintype ι] [Fintype κ] [Fintype n]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq n]
local instance dyadicFiniteOwnerDriftCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicFiniteOwnerDriftPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicFiniteOwnerDriftCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix κ κ ℝ)) := inferInstance

/-- One mesh controls the expected actual potential increment for every bounded
state and spectral sampler in a fixed coefficient face. The PSD covariance
payment is discarded after proving its sign. -/
theorem uniform_covarianceSample_dyadicOwner_drift_fixedFace [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (U : Matrix ι κ ℝ)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (R V B : ℝ) {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (H : selfAdjoint (Matrix n n ℂ)) (K L : selfAdjoint (Matrix κ κ ℝ)),
      ‖H‖ ≤ R → a • (1 : Matrix κ κ ℝ) ≤ (K : Matrix κ κ ℝ) →
      (K : Matrix κ κ ℝ) ≤ 1 → ‖L‖ ≤ B → (L : Matrix κ κ ℝ).PosSemidef →
      ∀ (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef), Q = covarianceLift U L →
      0 < realTrace Q →
      (∀ s, 0 < covarianceSampleWeight hQ s →
        ‖ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)‖ ≤ V) →
      ∀ h ∈ Icc (0 : ℝ) δ,
        (∑ s, covarianceSampleWeight hQ s *
          (dyadicOwnerPotential (H + h • ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)) A
              (covarianceLift U K - h ^ 2 • Q) m θ - dyadicOwnerPotential H A (covarianceLift U K) m θ)) ≤
          h ^ 2 * realTrace (Q * dyadicOwnerCoefficientResponse A hA (covarianceLift U K) m θ H) + ε * h ^ 2 := by
  obtain ⟨δ, hδ, hb⟩ := uniform_dyadicOwner_matched_taylor_fixedFace A hA U m hm θ hθ R V B ha hε
  refine ⟨δ, hδ, ?_⟩
  intro H K L hH hfloor hcap hLnorm hL Q hQ hQl htrace hV h hh
  let S := hermitianDyadicDensityOptimizer H (covarianceKraus (mixFamily A U) K) m θ
  let v := fun s => ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)
  have hK : (K : Matrix κ κ ℝ).PosDef :=
    CovarianceCompactChart.posDef_of_scalar_floor ha hfloor
  have hpayment : 0 ≤ covarianceDerivativeFunctional (mixFamily A U) K S L :=
    covarianceDerivativeFunctional_dyadic_nonneg (mixFamily A U) (mixFamily_isHermitian A U hA) m hm θ hθ H K L hK hL
  apply finite_weighted_second_order_drift (covarianceSampleWeight hQ) _
    (fun s => tracePairing S (v s))
    (fun s => (1 / 2 : ℝ) * dyadicOwnerCenterHessian A (covarianceLift U K) m θ H (v s) (v s))
    h ε _ (covarianceSampleWeight_nonneg hQ htrace) (covarianceSampleWeight_sum hQ htrace)
    (covarianceSample_owner_linear_mean A hA hQ S)
    (covarianceSample_dyadicOwner_hessian A hA (covarianceLift U K) m θ H hQ htrace)
  intro s hs
  have hp : ((H, K), v s, L) ∈
      CovarianceCompactChart.parameterChart R a V B (1 : Matrix κ κ ℝ) := by
    exact ⟨⟨by simpa using hH, hfloor, hcap⟩,
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hV s hs),
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hLnorm)⟩
  have he := (abs_le.mp (hb ((H, K), v s, L) hp h hh)).2
  rw [← hQl] at he
  change dyadicOwnerPotential (H + h • v s) A (covarianceLift U K - h ^ 2 • Q) m θ -
      dyadicOwnerPotential H A (covarianceLift U K) m θ - h * tracePairing S (v s) -
      h ^ 2 * ((1 / 2 : ℝ) * dyadicOwnerCenterHessian A (covarianceLift U K) m θ H (v s) (v s) -
        covarianceDerivativeFunctional (mixFamily A U) K S L) ≤ ε * h ^ 2 at he
  have hpaid := mul_nonneg (sq_nonneg h) hpayment
  dsimp only [v]
  linarith

end
end MatrixSpencer
