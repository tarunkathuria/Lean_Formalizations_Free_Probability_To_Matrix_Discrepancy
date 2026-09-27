import MatrixSpencer.MSManuscriptComplexCovarianceSource
import MatrixSpencer.KSObjectiveValueBound
import MatrixSpencer.ComplexGram

/-! Elementary polynomial norm bounds for the actual complex general-Kraus source. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptComplexSourceNorm
open MSManuscriptComplexCovarianceSource
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

/-- This coarse polynomial bound needs no source positivity or source spectral gap. -/
theorem source_norm_le (A : ι → Matrix n n ℂ) (hA : ∀i, ‖A i‖ ≤ 1)
    (C : Matrix ι ι ℂ) (S : Matrix n n ℂ) :
    ‖source A C S‖ ≤ (Fintype.card ι : ℝ)^2*‖C‖*‖S‖ := by
  have hterm (i j : ι) : ‖C i j • (A i*S*A j)‖ ≤ ‖C‖*‖S‖ := by
    have h1 := (norm_mul_le (A i*S) (A j)).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le (A i) S) (norm_nonneg _))
    have h2 : ‖A i‖*‖S‖*‖A j‖ ≤ ‖S‖ := by
      calc
        _ ≤ 1*‖S‖*1 := mul_le_mul
          (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg S)) (hA j)
          (norm_nonneg _) (by positivity)
        _ = _ := by ring
    rw [norm_smul]
    exact mul_le_mul (KSObjectiveValueBound.entry_norm_le C i j) (h1.trans h2)
      (norm_nonneg _) (norm_nonneg C)
  calc
    _ ≤ ∑i, ‖∑j, C i j • (A i*S*A j)‖ := norm_sum_le _ _
    _ ≤ ∑i, ∑j, ‖C i j • (A i*S*A j)‖ :=
      Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑i : ι, ∑j : ι, ‖C‖*‖S‖ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

theorem source_norm_le_of_caps (A : ι → Matrix n n ℂ) (hA : ∀i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℂ} {S : Matrix n n ℂ} {c s : ℝ}
    (hc : ‖C‖ ≤ c) (hs : ‖S‖ ≤ s) :
    ‖source A C S‖ ≤ (Fintype.card ι : ℝ)^2*c*s := by
  have hc0 := (norm_nonneg C).trans hc
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul hc hs (norm_nonneg S) hc0)
    (sq_nonneg (Fintype.card ι : ℝ))
  exact (source_norm_le A hA C S).trans (by nlinarith)

/-- Norm-two coefficient and density neighborhoods have a uniform4k² source cap. -/
theorem source_norm_le_four_card_sq (A : ι → Matrix n n ℂ) (hA : ∀i, ‖A i‖ ≤ 1)
    {C X : Matrix ι ι ℂ} {S Y : Matrix n n ℂ}
    (hc : ‖C‖ ≤ 1) (hs : ‖S‖ ≤ 1) (hx : ‖X‖ ≤ 1) (hy : ‖Y‖ ≤ 1) :
    ‖source A (C+X) (S+Y)‖ ≤ 4*(Fintype.card ι : ℝ)^2 := by
  have hc2 : ‖C+X‖ ≤ 2 := (norm_add_le C X).trans (by linarith)
  have hs2 : ‖S+Y‖ ≤ 2 := (norm_add_le S Y).trans (by linarith)
  exact (source_norm_le_of_caps A hA hc2 hs2).trans_eq (by ring)

theorem real_coefficient_norm_le_one {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1) :
    ‖realMatrixEmbedding C‖ ≤ 1 := by
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ zero_le_one
    (realMatrixEmbedding_posSemidef C hC).nonneg).mpr
  have hh := realMatrixEmbedding_mono hC1
  simpa using hh

end MatrixSpencer.MSManuscriptComplexSourceNorm
