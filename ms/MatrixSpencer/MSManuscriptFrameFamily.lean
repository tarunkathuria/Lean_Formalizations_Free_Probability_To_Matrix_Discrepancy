import MatrixSpencer.MSManuscriptSupportedOwner
import MatrixSpencer.CovarianceFace
import MatrixSpencer.OwnerPotential

/-!
# Input bounds after the numerical owner's stored coefficient compression

The reduced matrices are actual finite linear combinations. Their norm cap is
N for original unit contractions; no unchanged unit cap is assumed. The owner
potential agrees exactly with the physical full-label covariance potential.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptFrameFamily
variable {N k d : ℕ}

theorem frame_entry_le_one (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1)
    (i : Fin N) (a : Fin k) : |U i a| ≤ 1 := by
  have he := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M a a) hU
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,ite_true] at he
  have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (U j a))
    (Finset.mem_univ i)
  rw [he] at hi
  have hs : |U i a|^2 ≤ (1 : ℝ)^2 := by nlinarith [sq_abs (U i a)]
  exact (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp hs

theorem family_norm_le (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i, ‖A i‖ ≤ 1)
    (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1) (a : Fin k) :
    ‖mixFamily A U a‖ ≤ N := by
  calc
    _ ≤ ∑i, ‖U i a • A i‖ := norm_sum_le _ _
    _ ≤ ∑i : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul (frame_entry_le_one U hU i a) (hA i) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by simp

theorem owner_potential_eq (H : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (U : Matrix (Fin N) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (θ : ℝ) :
    ownerPotential H A (U*C*Uᵀ) θ = ownerPotential H (mixFamily A U) C θ := by
  unfold ownerPotential
  congr 2
  funext S
  unfold ownerObjective
  rw [← covarianceSource_rectangular_mixing]
  rfl

theorem stored_family_norm_le (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i, ‖A i‖ ≤ 1) (O : MSManuscriptSupportedOwner.Owner N) {δ : ℝ}
    (hO : O.Valid δ) (a : Fin O.dim) : ‖mixFamily A O.frame a‖ ≤ N :=
  family_norm_le A hA O.frame hO.1 a

theorem stored_matrix_le_one (O : MSManuscriptSupportedOwner.Owner N) {δ : ℝ}
    (hO : O.Valid δ) (hphysical : O.physical ≤ 1) : O.matrix ≤ 1 := by
  have hh := covarianceLift_mono O.frameᵀ hphysical
  have he := covarianceLift_compress O.frame hO.1 O.matrix
  change O.frameᵀ*(O.frame*O.matrix*O.frameᵀ)*O.frame=O.matrix at he
  simpa only [covarianceLift,MSManuscriptSupportedOwner.Owner.physical,
    Matrix.transpose_transpose,Matrix.mul_one,he,hO.1] using hh

theorem stored_potential_eq (H : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (O : MSManuscriptSupportedOwner.Owner N) (θ : ℝ) :
    ownerPotential H A O.physical θ = ownerPotential H (mixFamily A O.frame) O.matrix θ :=
  owner_potential_eq H A O.frame O.matrix θ

end MatrixSpencer.MSManuscriptFrameFamily
