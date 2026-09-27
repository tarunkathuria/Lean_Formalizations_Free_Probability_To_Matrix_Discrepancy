import MatrixSpencer.CovarianceFace
import MatrixSpencer.CovarianceMovement

/-! A covariance dominated by a fixed face has exact coordinates in that face. -/
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
set_option maxHeartbeats 400000

theorem covarianceFace_projection_right (U : Matrix ι κ ℝ) (hU : Uᵀ * U = 1)
    (K : Matrix κ κ ℝ) {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (hQC : Q ≤ covarianceLift U K) : Q * (U * Uᵀ) = Q := by
  have hzero : covarianceLift U K * (1 - U * Uᵀ) = 0 := by
    simp only [covarianceLift, Matrix.mul_sub, Matrix.mul_one]
    have he : U * K * Uᵀ * (U * Uᵀ) = U * K * Uᵀ := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U Uᵀ, hU, Matrix.one_mul]
    rw [he, sub_self]
  have hz : Q * (1 - U * Uᵀ) = 0 := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    apply posSemidef_mulVec_eq_zero_of_le hQ hQC
    rw [Matrix.mulVec_mulVec, hzero, Matrix.zero_mulVec]
  have he : Q - Q * (U * Uᵀ) = 0 := by
    simpa only [Matrix.mul_sub, Matrix.mul_one] using hz
  exact (sub_eq_zero.mp he).symm

theorem covarianceFace_projection_left (U : Matrix ι κ ℝ) (hU : Uᵀ * U = 1)
    (K : Matrix κ κ ℝ) {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (hQC : Q ≤ covarianceLift U K) : U * Uᵀ * Q = Q := by
  have h := congrArg Matrix.transpose (covarianceFace_projection_right U hU K hQ hQC)
  have hQt : Qᵀ = Q := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.isHermitian.eq
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hQt] using h

/-- The compression exactly reconstructs every PSD covariance dominated by the face. -/
theorem covarianceFace_reconstruct_of_le (U : Matrix ι κ ℝ) (hU : Uᵀ * U = 1)
    (K : Matrix κ κ ℝ) {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (hQC : Q ≤ covarianceLift U K) : covarianceLift U (Uᵀ * Q * U) = Q := by
  calc
    _ = (U * Uᵀ) * Q * (U * Uᵀ) := by simp only [covarianceLift, Matrix.mul_assoc]
    _ = Q := by rw [covarianceFace_projection_left U hU K hQ hQC,
      covarianceFace_projection_right U hU K hQ hQC]

omit [DecidableEq ι] in
/-- Compression preserves the covariance cap in the fixed coordinates. -/
theorem covarianceFace_compress_le (U : Matrix ι κ ℝ) (hU : Uᵀ * U = 1)
    (K : Matrix κ κ ℝ) {Q : Matrix ι ι ℝ} (hQC : Q ≤ covarianceLift U K) :
    Uᵀ * Q * U ≤ K := by
  have h := covarianceLift_mono Uᵀ hQC
  change Uᵀ * Q * U ≤ Uᵀ * covarianceLift U K * U at h
  rwa [covarianceLift_compress U hU] at h

omit [DecidableEq ι] [DecidableEq κ] in
theorem covarianceFace_compress_posSemidef (U : Matrix ι κ ℝ)
    {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef) : (Uᵀ * Q * U).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.conjTranspose_mul_mul_same U

/-- Positive-weight sampler increments belong to the fixed original coefficient face. -/
theorem covarianceSample_mem_fixedFace (U : Matrix ι κ ℝ) (hU : Uᵀ * U = 1)
    (K : Matrix κ κ ℝ) {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (hQC : Q ≤ covarianceLift U K) {s : ι × Bool}
    (hs : 0 < covarianceSampleWeight hQ s) :
    WithLp.ofLp (covarianceSampleIncrement hQ s) ∈ LinearMap.range U.mulVecLin := by
  obtain ⟨x, hx⟩ := covarianceSample_mem_range hQ hs
  have hx' : Q *ᵥ WithLp.ofLp x = WithLp.ofLp (covarianceSampleIncrement hQ s) :=
    congrArg WithLp.ofLp hx
  refine ⟨Uᵀ *ᵥ (Q *ᵥ WithLp.ofLp x), ?_⟩
  change U *ᵥ (Uᵀ *ᵥ (Q *ᵥ WithLp.ofLp x)) = _
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    covarianceFace_projection_left U hU K hQ hQC, hx']

end
end MatrixSpencer
