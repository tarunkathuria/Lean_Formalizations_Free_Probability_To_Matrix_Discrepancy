import MatrixSpencer.CovarianceSampler
import MatrixSpencer.OwnerShort

/-!
# Legal matched covariance movements and exact finite moments

The decrement is the actual matrix `C - h² Q`. The sampler is the explicit
spectral sampler, with constraints asserted on every positive-weight branch.
-/

open scoped BigOperators MatrixOrder
open Matrix
noncomputable section
namespace MatrixSpencer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem covarianceMovement_lower {C Q : Matrix ι ι ℝ}
    (hQC : Q ≤ C) (h : ℝ) : (1 - h ^ 2) • C ≤ C - h ^ 2 • Q := by
  apply Matrix.le_iff.mpr
  have hp := (Matrix.le_iff.mp hQC).smul (sq_nonneg h)
  convert hp using 1 <;> module

theorem covarianceMovement_posSemidef_range {C Q : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (hQ : Q.PosSemidef) (hQC : Q ≤ C)
    {h : ℝ} (hh : h ^ 2 < 1) :
    (C - h ^ 2 • Q).PosSemidef ∧ C - h ^ 2 • Q ≤ C ∧
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (C - h ^ 2 • Q)).toLinearMap =
        LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap := by
  have hlower := covarianceMovement_lower hQC h
  have hp : (C - h ^ 2 • Q).PosSemidef :=
    ((hC.smul (sub_nonneg.mpr hh.le)).nonneg.trans hlower).posSemidef
  have hupper : C - h ^ 2 • Q ≤ C := sub_le_self C (hQ.smul (sq_nonneg h)).nonneg
  exact ⟨hp, hupper, posSemidef_range_eq_of_sandwich hp hC (sub_pos.mpr hh) hlower hupper⟩

theorem covarianceMovement_trace (C Q : Matrix ι ι ℝ) (h : ℝ) :
    realTrace (C - h ^ 2 • Q) = realTrace C - h ^ 2 * realTrace Q := by simp

theorem realTrace_rankOne_mul (u : ι → ℝ) (G : Matrix ι ι ℝ) :
    realTrace (realRankOne u * G) = u ⬝ᵥ (G *ᵥ u) := by
  simp only [realTrace, Matrix.trace, Matrix.diag, realRankOne, Matrix.mul_apply,
    Matrix.vecMulVec_apply, map_sum, RCLike.re_to_real, dotProduct, Matrix.mulVec,
    Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The exact quadratic expectation for any coefficient matrix. -/
theorem covarianceSample_quadratic {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) (G : Matrix ι ι ℝ) :
    (∑ s, covarianceSampleWeight hQ s *
      (WithLp.ofLp (covarianceSampleIncrement hQ s) ⬝ᵥ
        (G *ᵥ WithLp.ofLp (covarianceSampleIncrement hQ s)))) = realTrace (Q * G) := by
  conv_rhs => rw [← covarianceSample_covariance hQ htrace]
  rw [Matrix.sum_mul, realTrace_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Matrix.smul_mul, realTrace_smul, realTrace_rankOne_mul]

theorem covarianceSample_linear_mean (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef)
    (g : EuclideanSpace ℝ ι →ₗ[ℝ] ℝ) :
    (∑ s, covarianceSampleWeight hQ s * g (covarianceSampleIncrement hQ s)) = 0 := by
  have hm := congrArg g (covarianceSample_mean_zero hQ)
  simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using hm

/-- Each positive-weight branch obeys every linear constraint annihilating Q. -/
theorem covarianceSample_constraint {E : Type*} [AddCommGroup E] [Module ℝ E]
    {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] E)
    (hT : T.comp (Matrix.toEuclideanCLM (𝕜 := ℝ) Q).toLinearMap = 0)
    {s : ι × Bool} (hs : 0 < covarianceSampleWeight hQ s) :
    T (covarianceSampleIncrement hQ s) = 0 := by
  obtain ⟨u, hu⟩ := covarianceSample_mem_range hQ hs
  rw [← hu]
  exact LinearMap.congr_fun hT u

theorem covarianceSample_norm_gain {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (x : EuclideanSpace ℝ ι) (h : ℝ) (s : ι × Bool)
    (horth : inner ℝ x (covarianceSampleIncrement hQ s) = 0) :
    ‖x + h • covarianceSampleIncrement hQ s‖ ^ 2 = ‖x‖ ^ 2 + h ^ 2 * realTrace Q := by
  rw [norm_add_sq_real, real_inner_smul_right, horth, mul_zero, mul_zero, add_zero,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, covarianceSample_norm_sq]

end MatrixSpencer
