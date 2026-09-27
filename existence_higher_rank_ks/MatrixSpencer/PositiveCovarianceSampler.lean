import MatrixSpencer.CovarianceMovement

/-!
# Removing zero-weight spectral branches

Every child of this finite sampler has positive weight and belongs to the
actual covariance range. The original normalization and moments are retained.
-/

open scoped BigOperators MatrixOrder
open Matrix
noncomputable section
namespace MatrixSpencer

section Restriction
variable {α E : Type*} [Fintype α] [AddCommMonoid E] [Module ℝ E]

theorem sum_positive_weight_smul (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (f : α → E) :
    (∑ a : {a // 0 < w a}, w a • f a) = ∑ a, w a • f a := by
  classical
  have hh := Fintype.sum_subtype_add_sum_subtype (fun a => 0 < w a) (fun a => w a • f a)
  have hz : (∑ a : {a // ¬ 0 < w a}, w a • f a) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    have he : w a = 0 := le_antisymm (le_of_not_gt a.property) (hw a)
    rw [he, zero_smul]
  rw [hz, add_zero] at hh
  exact hh

end Restriction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev PositiveCovarianceOutcome {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef) :=
  {s : ι × Bool // 0 < covarianceSampleWeight hQ s}

theorem positive_covarianceSample_weight_sum {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) :
    (∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s) = 1 := by
  have hh := sum_positive_weight_smul (covarianceSampleWeight hQ)
    (covarianceSampleWeight_nonneg hQ htrace) (fun _ => (1 : ℝ))
  simpa only [smul_eq_mul, mul_one, covarianceSampleWeight_sum hQ htrace] using hh

theorem positive_covarianceSample_nonempty {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) : Nonempty (PositiveCovarianceOutcome hQ) := by
  classical
  by_contra hh
  haveI : IsEmpty (PositiveCovarianceOutcome hQ) := not_nonempty_iff.mp hh
  have hn := positive_covarianceSample_weight_sum hQ htrace
  simpa using hn

theorem positive_covarianceSample_mean_zero {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) :
    (∑ s : PositiveCovarianceOutcome hQ,
      covarianceSampleWeight hQ s • covarianceSampleIncrement hQ s) = 0 := by
  rw [sum_positive_weight_smul _ (covarianceSampleWeight_nonneg hQ htrace),
    covarianceSample_mean_zero]

theorem positive_covarianceSample_covariance {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) :
    (∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s •
      realRankOne (WithLp.ofLp (covarianceSampleIncrement hQ s))) = Q := by
  exact (sum_positive_weight_smul (covarianceSampleWeight hQ)
    (covarianceSampleWeight_nonneg hQ htrace) (fun s =>
      realRankOne (WithLp.ofLp (covarianceSampleIncrement hQ s)))).trans
        (covarianceSample_covariance hQ htrace)

theorem positive_covarianceSample_quadratic {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) (G : Matrix ι ι ℝ) :
    (∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s *
      (WithLp.ofLp (covarianceSampleIncrement hQ s) ⬝ᵥ
        (G *ᵥ WithLp.ofLp (covarianceSampleIncrement hQ s)))) = realTrace (Q * G) := by
  have hh := sum_positive_weight_smul (covarianceSampleWeight hQ)
    (covarianceSampleWeight_nonneg hQ htrace) (fun s =>
      WithLp.ofLp (covarianceSampleIncrement hQ s) ⬝ᵥ
        (G *ᵥ WithLp.ofLp (covarianceSampleIncrement hQ s)))
  simpa only [smul_eq_mul, covarianceSample_quadratic hQ htrace] using hh

/-- All retained branches satisfy support membership, without a zero-probability exception. -/
theorem positive_covarianceSample_mem_range {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (s : PositiveCovarianceOutcome hQ) :
    covarianceSampleIncrement hQ s ∈ LinearMap.range
      (Matrix.toEuclideanCLM (𝕜 := ℝ) Q).toLinearMap :=
  covarianceSample_mem_range hQ s.property

end MatrixSpencer
