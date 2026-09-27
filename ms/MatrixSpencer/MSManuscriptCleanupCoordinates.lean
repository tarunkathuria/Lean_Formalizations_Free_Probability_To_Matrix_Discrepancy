import MatrixSpencer.MSManuscriptCleanupSupport
import Mathlib.Data.List.NodupEquivFin

/-! Actual ordered enumeration of the retained cleanup coordinates. Forward
indexing is list lookup and inverse indexing is finite index search. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptCleanupCoordinates
open MSManuscriptJacobiCleanup
variable {d : ℕ}

def labels (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) : List (Fin d) :=
  (List.finRange d).filter (fun i => decide (3*δ ≤ rotated G δ i i))
def count (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) := (labels G δ).length

theorem labels_nodup (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) : (labels G δ).Nodup :=
  (List.nodup_finRange d).filter _
theorem mem_labels (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) (i : Fin d) :
    i ∈ labels G δ ↔ 3*δ ≤ rotated G δ i i := by simp [labels]

def equiv (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) : Fin (count G δ) ≃ Retained G δ :=
  ((labels_nodup G δ).getEquiv (labels G δ)).trans
    { toFun := fun i => ⟨i.val,(mem_labels G δ i.val).mp i.property⟩
      invFun := fun i => ⟨i.val,(mem_labels G δ i.val).mpr i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def matrix (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) :
    Matrix (Fin (count G δ)) (Fin (count G δ)) ℝ :=
  (retainedMatrix G δ).submatrix (equiv G δ) (equiv G δ)
def frame (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) : Matrix (Fin d) (Fin (count G δ)) ℝ :=
  (MSManuscriptCleanupFrame.frame G δ).submatrix id (equiv G δ)

theorem count_eq_card (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) :
    count G δ=Fintype.card (Retained G δ) := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (equiv G δ)

theorem frame_isometry (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) :
    (frame G δ)ᵀ*frame G δ=1 := by
  rw [frame,Matrix.transpose_submatrix,←Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    MSManuscriptCleanupFrame.frame_isometry,Matrix.submatrix_one _ (equiv G δ).injective]

theorem output_factorization (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef) (δ : ℝ) :
    output G δ=frame G δ*matrix G δ*(frame G δ)ᵀ := by
  rw [MSManuscriptCleanupFrame.output_eq_frame G hG δ]
  simp only [frame,matrix,Matrix.transpose_submatrix,Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id]

theorem matrix_floor (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    {δ : ℝ} (hδ : 0<δ) (hf : δ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ G) :
    (2*δ) • (1 : Matrix (Fin (count G δ)) (Fin (count G δ)) ℝ) ≤ matrix G δ := by
  have h := (Matrix.le_iff.mp (MSManuscriptJacobiCleanup.retained_floor G hG hδ hf)).submatrix (equiv G δ)
  apply Matrix.le_iff.mpr
  simpa only [Matrix.submatrix_sub,Matrix.submatrix_smul,Pi.sub_apply,Pi.smul_apply,Matrix.submatrix_one _ (equiv G δ).injective,matrix] using h

theorem count_le (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) : count G δ≤d := by
  unfold count labels
  exact (List.length_filter_le _ _).trans_eq List.length_finRange

theorem output_trace_loss_count (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    {δ : ℝ} (hδ : 0<δ) (hf : δ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ G) :
    realTrace G-realTrace (output G δ) ≤ 4*δ*(d-count G δ:ℕ) := by
  rw [count_eq_card]
  exact output_trace_loss G hG hδ hf

end MatrixSpencer.MSManuscriptCleanupCoordinates
