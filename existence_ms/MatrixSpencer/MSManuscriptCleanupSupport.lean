import MatrixSpencer.MSManuscriptCleanupFrame
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Exact support and rank-loss accounting for the computed cleanup output. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptCleanupSupport
open MSManuscriptJacobiCleanup MSManuscriptCleanupFrame
variable {d : ℕ}

def projector (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) := frame G δ * (frame G δ)ᵀ

theorem projector_posSemidef (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) :
    (projector G δ).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (frame G δ)
  simpa [projector,Matrix.conjTranspose_apply] using h

theorem projector_idempotent (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) :
    projector G δ * projector G δ = projector G δ := by
  unfold projector
  calc
    _ = frame G δ * ((frame G δ)ᵀ * frame G δ) * (frame G δ)ᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [frame_isometry,Matrix.mul_one]

theorem output_range_eq_projector (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    {δ : ℝ} (hδ : 0<δ) (hf : δ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ G) :
    LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (output G δ)).toLinearMap =
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (projector G δ)).toLinearMap := by
  apply le_antisymm
  · intro u hu
    obtain ⟨v,rfl⟩ := hu
    refine ⟨Matrix.toEuclideanCLM (𝕜 := ℝ) (output G δ) v,?_⟩
    change Matrix.toEuclideanCLM (𝕜 := ℝ) (projector G δ)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (output G δ) v) = _
    rw [←ContinuousLinearMap.mul_apply,←map_mul]
    rw [show projector G δ*output G δ=output G δ from output_preserved_by_projector G hG δ]
    rfl
  · have h := posSemidef_range_le_of_le ((projector_posSemidef G δ).smul (show 0≤2*δ by positivity))
      (output_posSemidef G hG δ) (output_projector_floor G hG hδ hf)
    rwa [euclideanMatrix_range_smul _ (show (2*δ)≠0 by positivity)] at h

theorem retained_posDef (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    {δ : ℝ} (hδ : 0<δ) (hf : δ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ G) :
    (retainedMatrix G δ).PosDef := by
  classical
  have h := (Matrix.PosDef.one.smul (show 0<2*δ by positivity)).add_posSemidef
    (Matrix.le_iff.mp (retained_floor G hG hδ hf))
  simpa only [add_sub_cancel] using h

theorem compression_output (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef) (δ : ℝ) :
    (frame G δ)ᵀ*output G δ*frame G δ=retainedMatrix G δ := by
  rw [output_eq_frame G hG δ]
  calc
    _ = ((frame G δ)ᵀ*frame G δ)*retainedMatrix G δ*((frame G δ)ᵀ*frame G δ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [frame_isometry,Matrix.one_mul,Matrix.mul_one]

theorem output_rank (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    {δ : ℝ} (hδ : 0<δ) (hf : δ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ G) :
    (output G δ).rank=Fintype.card (Retained G δ) := by
  classical
  apply le_antisymm
  · rw [output_eq_frame G hG δ]
    exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _))
  · have h₁ := Matrix.rank_mul_le_left ((frame G δ)ᵀ*output G δ) (frame G δ)
    have h₂ := Matrix.rank_mul_le_right (frame G δ)ᵀ (output G δ)
    rw [compression_output G hG δ,
      Matrix.rank_of_isUnit _ (retained_posDef G hG hδ hf).isUnit] at h₁
    exact h₁.trans h₂

theorem input_rank (G : Matrix (Fin d) (Fin d) ℝ) {δ : ℝ} (hδ : 0<δ)
    (hf : δ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ G) : G.rank=d := by
  have hp : G.PosDef := by
    have h := (Matrix.PosDef.one.smul hδ).add_posSemidef (Matrix.le_iff.mp hf)
    simpa only [add_sub_cancel] using h
  simpa using Matrix.rank_of_isUnit G hp.isUnit

/-- The unpaid loss is at most `4δ` times the actual decrease in matrix rank. -/
theorem output_trace_loss_rank (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    {δ : ℝ} (hδ : 0<δ) (hf : δ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ G) :
    realTrace G-realTrace (output G δ) ≤ 4*δ*(G.rank-(output G δ).rank:ℕ) := by
  rw [input_rank G hδ hf,output_rank G hG hδ hf]
  exact output_trace_loss G hG hδ hf

end MatrixSpencer.MSManuscriptCleanupSupport
