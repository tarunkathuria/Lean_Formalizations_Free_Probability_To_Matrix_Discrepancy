import MatrixSpencer.KSEighthManuscriptInertia
import MatrixSpencer.CoefficientSupportFrame
import MatrixSpencer.KSJacobiStep

/-!
# A high-trace comparator supplied by actual negative inertia

This is only a comparison witness for the finite covariance algorithm. Its
orthonormal frame is proof data; the algorithm computes a Jacobi basis and
finite capped-simplex projection instead. Any negative subspace of sufficient
dimension supplies a PSD contraction of prescribed trace with nonpositive
Hessian pairing and Frobenius energy at most that trace.
-/

open Matrix Module
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptComparator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_comparator (K : Matrix ι ι ℝ) (W : Submodule ℝ (ι → ℝ))
    (hW : KSEighthInertia.StrictlyNegativeOn K W)
    {s : ℝ} (hs : 0 < s) (hrank : s ≤ (finrank ℝ W : ℝ)) :
    ∃ P : Matrix ι ι ℝ, P.PosSemidef ∧ P ≤ 1 ∧ Matrix.trace P = s ∧
      Matrix.trace (P * K) ≤ 0 ∧ KSJacobiStep.frobeniusEnergy P ≤ s := by
  let e := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm
  let V := W.map e.toLinearMap
  let U := CoefficientSupportFrame.frame V
  let R := U * Uᵀ
  have hr : finrank ℝ V = finrank ℝ W := e.finrank_map_eq W
  have hU : Uᵀ * U = 1 := CoefficientSupportFrame.frame_isometry V
  have hR : R.PosSemidef := by
    simpa only [R, covarianceLift, Matrix.mul_one] using
      covarianceLift_posSemidef U (Matrix.PosSemidef.one : (1 : Matrix _ _ ℝ).PosSemidef)
  have hR1 : R ≤ 1 := covarianceIsometry_projection_le_one U hU
  have hRt : Matrix.trace R = (finrank ℝ W : ℝ) := by
    rw [show R = U * Uᵀ from rfl, Matrix.trace_mul_comm, hU, Matrix.trace_one]
    simp only [CoefficientSupportFrame.FrameIndex, Fintype.card_fin, hr]
  have hRR : R * R = R := by
    dsimp only [R]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U Uᵀ, hU, Matrix.one_mul]
  have hRK : Matrix.trace (R * K) ≤ 0 := by
    have he : Matrix.trace (R * K) = Matrix.trace (Uᵀ * K * U) := by
      rw [show R = U * Uᵀ from rfl, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
    rw [he]
    apply Finset.sum_nonpos
    intro j _
    let u : ι → ℝ := fun i => U i j
    have hu : u ∈ W := by
      have hm := (stdOrthonormalBasis ℝ V j).property
      rcases hm with ⟨w, hw, hew⟩
      have hewu : w = u := by
        funext i
        exact congrArg (fun z : EuclideanSpace ℝ ι => z i) hew
      rwa [← hewu]
    have hq : u ⬝ᵥ (K *ᵥ u) ≤ 0 := by
      by_cases hz : u = 0
      · simp [hz]
      · exact (hW u hu hz).le
    convert hq using 1
    simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, dotProduct,
      Matrix.mulVec, Finset.sum_mul, u]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  let a := s / (finrank ℝ W : ℝ)
  have hdim : (0 : ℝ) < finrank ℝ W := hs.trans_le hrank
  have ha : 0 ≤ a := div_nonneg hs.le hdim.le
  have ha1 : a ≤ 1 := (div_le_one hdim).mpr hrank
  refine ⟨a • R, hR.smul ha, ?_, ?_, ?_, ?_⟩
  · exact (smul_le_smul_of_nonneg_right ha1 hR.nonneg).trans (by simpa using hR1)
  · rw [Matrix.trace_smul, hRt]
    exact div_mul_cancel₀ s hdim.ne'
  · rw [Matrix.smul_mul, Matrix.trace_smul]
    exact mul_nonpos_of_nonneg_of_nonpos ha hRK
  · have hRT : Rᵀ = R := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
    rw [KSJacobiStep.frobeniusEnergy_eq_trace, Matrix.transpose_smul,
      Matrix.smul_mul, Matrix.mul_smul, hRT, hRR, Matrix.trace_smul, Matrix.trace_smul, hRt]
    have he : a * (finrank ℝ W : ℝ) = s := div_mul_cancel₀ s hdim.ne'
    simp only [smul_eq_mul]
    rw [he]
    exact mul_le_of_le_one_left hs.le ha1


theorem exists_manuscript_comparator [Nonempty ι]
    (K : Matrix ι ι ℝ) (W : Submodule ℝ (ι → ℝ))
    (hdim : (13 / 16 : ℝ) * Fintype.card ι < (finrank ℝ W : ℝ))
    (hW : KSEighthInertia.StrictlyNegativeOn K W) :
    ∃ P : Matrix ι ι ℝ, P.PosSemidef ∧ P ≤ 1 ∧
      Matrix.trace P = (25 / 32 : ℝ) * Fintype.card ι ∧
      Matrix.trace (P * K) ≤ 0 ∧
      KSJacobiStep.frobeniusEnergy P ≤ (25 / 32 : ℝ) * Fintype.card ι := by
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  exact exists_comparator K W hW (by positivity) (by linarith)

end MatrixSpencer.KSEighthManuscriptComparator
