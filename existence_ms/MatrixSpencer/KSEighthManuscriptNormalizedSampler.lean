import MatrixSpencer.KSEighthManuscriptMovement
import MatrixSpencer.KSNumericalHessian
import MatrixSpencer.KSEighthComparison

/-!
# The same LDL draws in weighted Hessian coordinates

This is a proof-coordinate change of the actual physical sampler. It does not
alter the sampled covariance or the run. Undoing D½ sends its exact covariance
to Q, allowing the computed high-trace Hessian bound to control the mean of the
actual movement's second derivative.
-/

open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptNormalizedSampler
open KSEighthManuscriptSampler
variable {k : ℕ}

def inverseWeight (x : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal (fun i => (Real.sqrt (1-x i^2))⁻¹)

def normalized (x : Fin k → ℝ) (Q : Matrix (Fin k) (Fin k) ℝ)
    (z : Fin k × Bool) : EuclideanSpace ℝ (Fin k) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (inverseWeight x)
    (increment (KSSymmetricProgress.scaledCovariance x Q) z)

theorem sqrt_weight_pos (x : Fin k → ℝ) (hx : ∀i, |x i| ≤ (1/8 : ℝ)) (i : Fin k) :
    0 < Real.sqrt (1-x i^2) := by
  apply Real.sqrt_pos.mpr
  have h := KSEighthComparison.eighth_square_bound (hx i)
  linarith

theorem inverseWeight_isHermitian (x : Fin k → ℝ) : (inverseWeight x).IsHermitian := by
  simp [inverseWeight]

theorem inverseWeight_scaledCovariance (x : Fin k → ℝ)
    (hx : ∀i, |x i| ≤ (1/8 : ℝ)) (Q : Matrix (Fin k) (Fin k) ℝ) :
    inverseWeight x * KSSymmetricProgress.scaledCovariance x Q * inverseWeight x = Q := by
  let D := Matrix.diagonal (fun i => Real.sqrt (1-x i^2))
  have hRD : inverseWeight x * D = 1 := by
    simp only [inverseWeight, D, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j
      simp [inv_mul_cancel₀ (sqrt_weight_pos x hx i).ne']
    · simp [hij]
  have hDR : D * inverseWeight x = 1 := Matrix.mul_eq_one_comm.mp hRD
  change inverseWeight x * (D*Q*D) * inverseWeight x = Q
  calc
    _ = (inverseWeight x * D) * Q * (D * inverseWeight x) := by simp only [Matrix.mul_assoc]
    _ = Q := by rw [hRD,hDR,Matrix.one_mul,Matrix.mul_one]

theorem covariance (x : Fin k → ℝ) (hx : ∀i, |x i| ≤ (1/8 : ℝ))
    {Q : Matrix (Fin k) (Fin k) ℝ} (hQ : Q.PosSemidef) (hk : 0 < k) :
    (∑z, weight z • realRankOne (WithLp.ofLp (normalized x Q z))) = Q := by
  calc
    _ = ∑z, weight z • (inverseWeight x *
      realRankOne (WithLp.ofLp (increment (KSSymmetricProgress.scaledCovariance x Q) z)) * inverseWeight x) := by
      apply Finset.sum_congr rfl
      intro z _
      congr 1
      exact (realRankOne_congruence (inverseWeight_isHermitian x) _).symm
    _ = inverseWeight x * (∑z, weight z •
        realRankOne (WithLp.ofLp (increment (KSSymmetricProgress.scaledCovariance x Q) z))) * inverseWeight x := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = Q := by
      rw [KSEighthManuscriptSampler.covariance (KSSymmetricProgress.scaledCovariance_posSemidef x hQ) hk,
        inverseWeight_scaledCovariance x hx Q]

theorem mean_zero (x : Fin k → ℝ) (Q : Matrix (Fin k) (Fin k) ℝ) :
    (∑z, weight z • normalized x Q z) = 0 := by
  have h := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (inverseWeight x))
    (KSEighthManuscriptSampler.mean_zero (KSSymmetricProgress.scaledCovariance x Q))
  simpa only [map_sum,map_smul,map_zero] using h

theorem quadratic_mean (x : Fin k → ℝ) (hx : ∀i, |x i| ≤ (1/8 : ℝ))
    {Q : Matrix (Fin k) (Fin k) ℝ} (hQ : Q.PosSemidef) (hk : 0 < k)
    (G : Matrix (Fin k) (Fin k) ℝ) :
    (∑z, weight z * (WithLp.ofLp (normalized x Q z) ⬝ᵥ
      (G *ᵥ WithLp.ofLp (normalized x Q z)))) = realTrace (Q*G) := by
  conv_rhs => rw [← covariance x hx hQ hk]
  rw [Matrix.sum_mul,realTrace_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Matrix.smul_mul,realTrace_smul,realTrace_rankOne_mul]

theorem weighted_normalized (x : Fin k → ℝ) (hx : ∀i, |x i| ≤ (1/8 : ℝ))
    (Q : Matrix (Fin k) (Fin k) ℝ) (z : Fin k × Bool) (i : Fin k) :
    Real.sqrt (1-x i^2) * normalized x Q z i =
      increment (KSSymmetricProgress.scaledCovariance x Q) z i := by
  change Real.sqrt (1-x i^2) *
    ((inverseWeight x) *ᵥ WithLp.ofLp (increment (KSSymmetricProgress.scaledCovariance x Q) z)) i = _
  rw [inverseWeight, Matrix.mulVec_diagonal]
  rw [← mul_assoc,mul_inv_cancel₀ (sqrt_weight_pos x hx i).ne',one_mul]
  rfl

/-- Inverse weights have norm at most two throughout the eighth cube. -/
theorem inverse_weight_le_two (x : Fin k → ℝ) (hx : ∀i, |x i| ≤ (1/8 : ℝ)) (i : Fin k) :
    (Real.sqrt (1-x i^2))⁻¹ ≤ 2 := by
  have hs := sqrt_weight_pos x hx i
  have hsq := Real.sq_sqrt (show 0 ≤ 1-x i^2 by
    have h := KSEighthComparison.eighth_square_bound (hx i); linarith)
  have h := KSEighthComparison.eighth_square_bound (hx i)
  apply (inv_le_comm₀ hs (by norm_num : (0:ℝ)<2)).mpr
  norm_num
  nlinarith

theorem normalized_norm_le (x : Fin k → ℝ) (hx : ∀i, |x i| ≤ (1/8 : ℝ))
    (Q : Matrix (Fin k) (Fin k) ℝ) (z : Fin k × Bool) :
    ‖normalized x Q z‖ ≤ 2*‖increment (KSSymmetricProgress.scaledCovariance x Q) z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change |((inverseWeight x) *ᵥ WithLp.ofLp (increment (KSSymmetricProgress.scaledCovariance x Q) z)) i|^2 ≤ _
  rw [inverseWeight, Matrix.mulVec_diagonal, abs_mul, mul_pow]
  have h0 := (inv_pos.mpr (sqrt_weight_pos x hx i)).le
  have h2 := inverse_weight_le_two x hx i
  rw [sq_abs]
  have hb : ((Real.sqrt (1-x i^2))⁻¹)^2 ≤ 2^2 := by nlinarith
  exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)

def bounded (x : Fin k → ℝ) (Q : Matrix (Fin k) (Fin k) ℝ) (N : ℕ)
    (z : Fin k × Bool) : EuclideanSpace ℝ (Fin k) :=
  (Real.sqrt (N : ℝ))⁻¹ • normalized x Q z

theorem bounded_norm_le_two (x : Fin k → ℝ) (hx : ∀i, |x i| ≤ (1/8 : ℝ))
    {Q : Matrix (Fin k) (Fin k) ℝ} (hQ : Q.PosSemidef)
    (hP1 : KSSymmetricProgress.scaledCovariance x Q ≤ 1)
    {N : ℕ} (hN : 0 < N) (hkN : k ≤ N) (z : Fin k × Bool) :
    ‖bounded x Q N z‖ ≤ 2 := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hi := KSEighthManuscriptSampler.increment_norm_le
    (KSSymmetricProgress.scaledCovariance_posSemidef x hQ) hP1 z
  have hnorm : ‖normalized x Q z‖ ≤ 2*Real.sqrt (N : ℝ) :=
    (normalized_norm_le x hx Q z).trans (mul_le_mul_of_nonneg_left
      (hi.trans (Real.sqrt_le_sqrt (by exact_mod_cast hkN))) (by norm_num))
  unfold bounded
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  have h := mul_le_mul_of_nonneg_left hnorm (inv_pos.mpr hs).le
  simpa only [mul_left_comm (Real.sqrt (N : ℝ))⁻¹ 2, inv_mul_cancel₀ hs.ne', mul_one] using h

theorem bounded_quadratic_mean (x : Fin k → ℝ) (hx : ∀i, |x i| ≤ (1/8 : ℝ))
    {Q : Matrix (Fin k) (Fin k) ℝ} (hQ : Q.PosSemidef) (hk : 0 < k) (N : ℕ)
    (G : Matrix (Fin k) (Fin k) ℝ) :
    (∑z, weight z * KSRayleighAccuracy.realRayleigh G (bounded x Q N z)) =
      (N : ℝ)⁻¹ * realTrace (Q*G) := by
  have hscalar : ((Real.sqrt (N : ℝ))⁻¹)^2 = (N : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  have he (z : Fin k × Bool) : KSRayleighAccuracy.realRayleigh G (bounded x Q N z) =
      ((Real.sqrt (N : ℝ))⁻¹)^2 *
        (WithLp.ofLp (normalized x Q z) ⬝ᵥ (G *ᵥ WithLp.ofLp (normalized x Q z))) := by
    rw [KSRayleighAccuracy.realRayleigh_eq_quadratic]
    simp only [bounded, WithLp.ofLp_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]
    ring
  simp_rw [he, hscalar, ← mul_assoc, mul_comm (weight _) (N : ℝ)⁻¹, mul_assoc]
  rw [← Finset.mul_sum, quadratic_mean x hx hQ hk G]

theorem bounded_symmetric_average (x : Fin k → ℝ) (Q : Matrix (Fin k) (Fin k) ℝ)
    (N : ℕ) (f : EuclideanSpace ℝ (Fin k) → ℝ) :
    (∑z, weight z * ((f (bounded x Q N z)+f (-bounded x Q N z))/2)) =
      ∑z, weight z * f (bounded x Q N z) := by
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fintype.sum_bool, weight, bounded, normalized, increment,
    Bool.false_eq_true, ↓reduceIte, map_neg, smul_neg, neg_neg]
  ring

end MatrixSpencer.KSEighthManuscriptNormalizedSampler
