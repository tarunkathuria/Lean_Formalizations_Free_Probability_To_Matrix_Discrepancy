import MatrixSpencer.MSManuscriptJacobiCleanup

/-! The actual retained columns are an orthonormal basis for the cleaned owner.
This identifies the returned lower-dimensional floor with the physical output. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptCleanupFrame
open MSManuscriptJacobiCleanup MSManuscriptSchurCleanup MSManuscriptCleanupFloor
variable {d : ℕ}

def frame (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) : Matrix (Fin d) (Retained G δ) ℝ :=
  (basis G δ).submatrix id Subtype.val

theorem frame_isometry (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) :
    (frame G δ)ᵀ * frame G δ = 1 := by
  classical
  rw [frame,Matrix.transpose_submatrix,←Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    basis_transpose_mul,Matrix.submatrix_one _ Subtype.val_injective]

private theorem sum_high (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) (f : Fin d → ℝ)
    (hf : ∀ a, G a a < 3*δ → f a=0) : (∑ a : High G δ, f a.val) = ∑ a, f a := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun a : Fin d => 3*δ≤G a a) f
  have hz : (∑ a : {a : Fin d // ¬3*δ≤G a a}, f a.val)=0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact hf a.val (lt_of_not_ge a.property)
  simpa only [hz,add_zero] using h

theorem output_eq_frame (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef) (δ : ℝ) :
    output G δ = frame G δ * retainedMatrix G δ * (frame G δ)ᵀ := by
  classical
  let R := rotated G δ
  let P := runScan R δ d
  have hP := runScan_posSemidef R (rotated_posSemidef G hG δ) δ d
  have hz (a b : Fin d) (ha : R a a < 3*δ) : P b a = 0 :=
    final_zero_of_low R (rotated_posSemidef G hG δ) δ a ha b
  have hrow (a b : Fin d) (ha : R a a < 3*δ) : P a b = 0 := by
    have hs : P a b=P b a := by simpa using congrFun (congrFun hP.isHermitian.eq b) a
    rw [hs,hz a b ha]
  ext a b
  change (∑ j : Fin d, (∑ i : Fin d, basis G δ a i * P i j) * basis G δ b j) =
    ∑ j : High R δ, (∑ i : High R δ, basis G δ a i.val * P i.val j.val) * basis G δ b j.val
  symm
  calc
    _ = ∑ j : High R δ, (∑ i : Fin d, basis G δ a i * P i j.val) * basis G δ b j.val := by
      apply Finset.sum_congr rfl
      intro j _
      rw [sum_high R δ (fun i => basis G δ a i * P i j.val) (fun i hi => by dsimp; rw [hrow i j.val hi,mul_zero])]
    _ = _ := by
      apply sum_high R δ (fun j => (∑ i : Fin d, basis G δ a i * P i j) * basis G δ b j)
      intro j hj
      have hh : (∑ i : Fin d, basis G δ a i*P i j)=0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hz j i hj,mul_zero]
      rw [hh,zero_mul]

theorem output_projector_floor (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    {δ : ℝ} (hδ : 0<δ) (hf : δ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ G) :
    (2*δ) • (frame G δ * (frame G δ)ᵀ) ≤ output G δ := by
  have h := (Matrix.le_iff.mp (retained_floor G hG hδ hf)).mul_mul_conjTranspose_same (frame G δ)
  have ht : (frame G δ).conjTranspose=(frame G δ)ᵀ := by ext i j; simp
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,ht,←output_eq_frame G hG δ] using h

theorem output_preserved_by_projector (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef) (δ : ℝ) :
    (frame G δ * (frame G δ)ᵀ) * output G δ = output G δ := by
  rw [output_eq_frame G hG δ]
  calc
    _ = frame G δ * ((frame G δ)ᵀ * frame G δ) * retainedMatrix G δ * (frame G δ)ᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [frame_isometry,Matrix.mul_one]

end MatrixSpencer.MSManuscriptCleanupFrame
