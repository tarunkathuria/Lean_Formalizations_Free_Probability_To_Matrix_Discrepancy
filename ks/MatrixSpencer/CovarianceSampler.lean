import MatrixSpencer.CovariancePreparation

/-!
# A finite centered covariance sampler of constant Euclidean length

For `Q ≥ 0` and `Tr Q > 0`, sample an eigenindex and a sign. The increment
is `±sqrt(Tr Q)` times its unit eigenvector, with weight `λ / (2 Tr Q)`.
Everything is stated using finite sums; no probability-space API is required.
-/

open scoped BigOperators MatrixOrder
open Matrix

namespace MatrixSpencer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two equally weighted signs attached to each eigenindex. -/
noncomputable def covarianceSampleWeight {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (s : ι × Bool) : ℝ := hQ.isHermitian.eigenvalues s.1 / (2 * realTrace Q)

/-- The increment is a vector in the Euclidean coefficient space. -/
noncomputable def covarianceSampleIncrement {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (s : ι × Bool) : EuclideanSpace ℝ ι :=
  if s.2 then Real.sqrt (realTrace Q) • hQ.isHermitian.eigenvectorBasis s.1
  else -(Real.sqrt (realTrace Q) • hQ.isHermitian.eigenvectorBasis s.1)

theorem realTrace_real_eq_sum_eigenvalues {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) :
    realTrace Q = ∑ j, hQ.eigenvalues j := by
  exact hQ.trace_eq_sum_eigenvalues

theorem sum_eigenvalue_rankOne {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) :
    (∑ j, hQ.eigenvalues j • realRankOne (WithLp.ofLp (hQ.eigenvectorBasis j))) = Q := by
  ext i k
  conv_rhs => rw [hQ.spectral_theorem]
  rw [Matrix.mul_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, realRankOne, Matrix.vecMulVec_apply,
    Matrix.mul_diagonal, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply, Function.comp_apply, RCLike.ofReal_real_eq_id,
    id_eq, star_trivial, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem covarianceSampleWeight_nonneg {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) (s : ι × Bool) : 0 ≤ covarianceSampleWeight hQ s := by
  exact div_nonneg (hQ.eigenvalues_nonneg _) (mul_nonneg (by norm_num) htrace.le)

theorem covarianceSampleWeight_sum {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) : (∑ s, covarianceSampleWeight hQ s) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [covarianceSampleWeight, Fintype.sum_bool]
  have hterm (j : ι) : hQ.isHermitian.eigenvalues j / (2 * realTrace Q) +
      hQ.isHermitian.eigenvalues j / (2 * realTrace Q) =
        hQ.isHermitian.eigenvalues j / realTrace Q := by ring
  simp only [hterm, ← Finset.sum_div, ← realTrace_real_eq_sum_eigenvalues]
  exact div_self htrace.ne'

theorem covarianceSample_mean_zero {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef) :
    (∑ s, covarianceSampleWeight hQ s • covarianceSampleIncrement hQ s) = 0 := by
  rw [Fintype.sum_prod_type]
  simp [covarianceSampleWeight, covarianceSampleIncrement]

theorem covarianceSample_norm_sq {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (s : ι × Bool) : ‖covarianceSampleIncrement hQ s‖ ^ 2 = realTrace Q := by
  rcases s with ⟨j, b⟩
  have he := hQ.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one j
  cases b <;> simp only [covarianceSampleIncrement, Bool.false_eq_true, ↓reduceIte,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), he,
    mul_one, Real.sq_sqrt (realTrace_nonneg hQ)]

omit [Fintype ι] [DecidableEq ι] in
theorem realRankOne_smul (a : ℝ) (u : ι → ℝ) :
    realRankOne (a • u) = a ^ 2 • realRankOne u := by
  ext i j
  simp only [realRankOne, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem realRankOne_neg (u : ι → ℝ) : realRankOne (-u) = realRankOne u := by
  ext i j
  simp only [realRankOne, Matrix.vecMulVec_apply, Pi.neg_apply, neg_mul_neg]

theorem covarianceSample_rankOne {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (s : ι × Bool) :
    realRankOne (WithLp.ofLp (covarianceSampleIncrement hQ s)) =
      realTrace Q • realRankOne (WithLp.ofLp (hQ.isHermitian.eigenvectorBasis s.1)) := by
  rcases s with ⟨j, b⟩
  cases b <;> simp only [covarianceSampleIncrement, Bool.false_eq_true, ↓reduceIte,
    WithLp.ofLp_neg, WithLp.ofLp_smul, realRankOne_neg, realRankOne_smul,
    Real.sq_sqrt (realTrace_nonneg hQ)]

/-- The weighted second moment is exactly the prescribed covariance. -/
theorem covarianceSample_covariance {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) :
    (∑ s, covarianceSampleWeight hQ s •
      realRankOne (WithLp.ofLp (covarianceSampleIncrement hQ s))) = Q := by
  conv_rhs => rw [← sum_eigenvalue_rankOne hQ.isHermitian]
  rw [Fintype.sum_prod_type]
  simp only [covarianceSample_rankOne, covarianceSampleWeight, Fintype.sum_bool, smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← add_smul]
  have hc : hQ.isHermitian.eigenvalues j / (2 * realTrace Q) * realTrace Q +
      hQ.isHermitian.eigenvalues j / (2 * realTrace Q) * realTrace Q =
        hQ.isHermitian.eigenvalues j := by
    field_simp
    ring
  rw [hc]

theorem covarianceEigenvector_mem_range {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian)
    {j : ι} (hj : hQ.eigenvalues j ≠ 0) :
    hQ.eigenvectorBasis j ∈ LinearMap.range
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Q).toLinearMap := by
  have he : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Q (hQ.eigenvectorBasis j) =
      hQ.eigenvalues j • hQ.eigenvectorBasis j := by
    apply (WithLp.equiv 2 (ι → ℝ)).injective
    exact hQ.mulVec_eigenvectorBasis j
  refine ⟨(hQ.eigenvalues j)⁻¹ • hQ.eigenvectorBasis j, ?_⟩
  change (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Q)
    ((hQ.eigenvalues j)⁻¹ • hQ.eigenvectorBasis j) = _
  rw [map_smul, he, smul_smul, inv_mul_cancel₀ hj, one_smul]

/-- Every outcome of positive weight belongs to the covariance's actual range. -/
theorem covarianceSample_mem_range {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    {s : ι × Bool} (hs : 0 < covarianceSampleWeight hQ s) :
    covarianceSampleIncrement hQ s ∈ LinearMap.range
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Q).toLinearMap := by
  have heig : hQ.isHermitian.eigenvalues s.1 ≠ 0 := by
    intro hz
    simp only [covarianceSampleWeight, hz, zero_div, lt_self_iff_false] at hs
  have he := covarianceEigenvector_mem_range hQ.isHermitian heig
  unfold covarianceSampleIncrement
  split_ifs
  · exact Submodule.smul_mem _ _ he
  · exact Submodule.neg_mem _ (Submodule.smul_mem _ _ he)

theorem covarianceSample_mem_subspace {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    {V : Submodule ℝ (EuclideanSpace ℝ ι)}
    (hV : LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Q).toLinearMap ≤ V)
    {s : ι × Bool} (hs : 0 < covarianceSampleWeight hQ s) :
    covarianceSampleIncrement hQ s ∈ V := hV (covarianceSample_mem_range hQ hs)

/-- The finite sampler, packaged with all normalization, moment, length, and support properties. -/
theorem exists_finite_covariance_sampler {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) :
    ∃ (w : ι × Bool → ℝ) (x : ι × Bool → EuclideanSpace ℝ ι),
      (∀ s, 0 ≤ w s) ∧ (∑ s, w s) = 1 ∧ (∑ s, w s • x s) = 0 ∧
      (∑ s, w s • realRankOne (WithLp.ofLp (x s))) = Q ∧
      (∀ s, ‖x s‖ ^ 2 = realTrace Q) ∧
      (∀ s, 0 < w s → x s ∈ LinearMap.range
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Q).toLinearMap) := by
  exact ⟨covarianceSampleWeight hQ, covarianceSampleIncrement hQ,
    covarianceSampleWeight_nonneg hQ htrace, covarianceSampleWeight_sum hQ htrace,
    covarianceSample_mean_zero hQ, covarianceSample_covariance hQ htrace,
    covarianceSample_norm_sq hQ, fun _ hs => covarianceSample_mem_range hQ hs⟩

end MatrixSpencer
