import MatrixSpencer.PositiveCovarianceSampler
import MatrixSpencer.OwnerCertificate

/-!
# Exact tangent moments of the positive finite sampler

The linear statistic and its variance are evaluated in the original
coefficient labels. Zero-weight outcomes have already been removed.
-/

open scoped BigOperators MatrixOrder
open Matrix
noncomputable section
namespace MatrixSpencer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coefficientLinearStatistic (g : ι → ℝ) : EuclideanSpace ℝ ι →ₗ[ℝ] ℝ where
  toFun u := g ⬝ᵥ WithLp.ofLp u
  map_add' _ _ := dotProduct_add _ _ _
  map_smul' a u := by
    change g ⬝ᵥ (a • WithLp.ofLp u) = a • (g ⬝ᵥ WithLp.ofLp u)
    rw [dotProduct_smul]

theorem positive_covarianceSample_linear_mean {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) (g : ι → ℝ) :
    (∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s *
      (g ⬝ᵥ WithLp.ofLp (covarianceSampleIncrement hQ s))) = 0 := by
  have hh := congrArg (coefficientLinearStatistic g) (positive_covarianceSample_mean_zero hQ htrace)
  simpa only [map_sum, map_smul, map_zero, smul_eq_mul, coefficientLinearStatistic,
    LinearMap.coe_mk, AddHom.coe_mk] using hh

theorem positive_covarianceSample_linear_variance {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) (g : ι → ℝ) :
    (∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s *
      (g ⬝ᵥ WithLp.ofLp (covarianceSampleIncrement hQ s)) ^ 2) = g ⬝ᵥ (Q *ᵥ g) := by
  have hh := positive_covarianceSample_quadratic hQ htrace (realRankOne g)
  rw [realTrace_mul_comm, realTrace_rankOne_mul] at hh
  simpa only [realRankOne_pairing] using hh

/-- The exact scalar second moment after a centered sampled increment. -/
theorem positive_covarianceSample_shifted_square {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) (g : ι → ℝ) (M h : ℝ) :
    (∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s *
      (M + h * (g ⬝ᵥ WithLp.ofLp (covarianceSampleIncrement hQ s))) ^ 2) =
      M ^ 2 + h ^ 2 * (g ⬝ᵥ (Q *ᵥ g)) := by
  calc
    _ = M ^ 2 * (∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s) +
        (2 * M * h) * (∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s *
          (g ⬝ᵥ WithLp.ofLp (covarianceSampleIncrement hQ s))) +
        h ^ 2 * (∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s *
          (g ⬝ᵥ WithLp.ofLp (covarianceSampleIncrement hQ s)) ^ 2) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by rw [positive_covarianceSample_weight_sum hQ htrace,
      positive_covarianceSample_linear_mean hQ htrace,
      positive_covarianceSample_linear_variance hQ htrace]; ring

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
open scoped Matrix.Norms.L2Operator
local instance ownerSamplerMomentsCStar : CStarAlgebra (Matrix n n ℂ) := {}

/-- The actual saved certificate gradient gives the needed variance bound. -/
theorem positive_ownerCertificate_second_moment_le
    (Hstar : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, ‖A i‖ ≤ 1) (θ M h : ℝ)
    {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef) (hQ1 : Q ≤ 1) (htrace : 0 < realTrace Q) :
    (∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s *
      (M + h * (ownerCertificateGradient Hstar A θ ⬝ᵥ
        WithLp.ofLp (covarianceSampleIncrement hQ s))) ^ 2) ≤
      M ^ 2 + h ^ 2 * (Fintype.card ι : ℝ) := by
  rw [positive_covarianceSample_shifted_square hQ htrace]
  exact add_le_add_left (mul_le_mul_of_nonneg_left
    (ownerCertificateGradient_covariance_bound Hstar A hA hN θ hQ hQ1).2
      (sq_nonneg h)) _

end MatrixSpencer
