import MatrixSpencer.KSEighthManuscriptLDL

/-! Explicit zero-pivot branches for scalar real-RAM execution of LDL.
The guarded recurrence is algebraically equal to the verified singular-safe
LDL factorization; its executed division branches have nonzero denominators. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalLDL
variable {d : ℕ}

def schur (P : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :=
  if P i i=0 then P else P-(P i i)⁻¹ • Matrix.vecMulVec (fun a => P a i) (fun a => P a i)

def residual (P : Matrix (Fin d) (Fin d) ℝ) : ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => P
  | j+1 => if hj : j<d then schur (residual P j) ⟨j,hj⟩ else residual P j

def pivot (P : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) := residual P j j j

def lowerColumn (P : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : Fin d → ℝ :=
  if pivot P j=0 then 0 else fun a => residual P j a j/pivot P j

@[simp] theorem schur_eq (P : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    schur P i=KSEighthManuscriptLDL.schur P i := by
  unfold schur
  split_ifs with hi
  · simp [KSEighthManuscriptLDL.schur,hi]
  · rfl

@[simp] theorem residual_eq (P : Matrix (Fin d) (Fin d) ℝ) (j : ℕ) :
    residual P j=KSEighthManuscriptLDL.residual P j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [residual,KSEighthManuscriptLDL.residual,schur_eq,ih]

@[simp] theorem pivot_eq (P : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    pivot P j=KSEighthManuscriptLDL.pivot P j := by simp only [pivot,residual_eq]; rfl

@[simp] theorem lowerColumn_eq (P : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    lowerColumn P j=KSEighthManuscriptLDL.lowerColumn P j := by
  unfold lowerColumn
  split_ifs with hj
  · ext a
    simp only [Pi.zero_apply,KSEighthManuscriptLDL.lowerColumn,←pivot_eq,hj,div_zero]
  · simp only [residual_eq,pivot_eq]
    rfl

theorem pivot_pos_of_selected (P : Matrix (Fin d) (Fin d) ℝ) (hP : P.PosSemidef)
    (j : Fin d) (hj : pivot P j≠0) : 0<pivot P j := by
  have h := KSEighthManuscriptLDL.pivot_nonneg hP j
  rw [←pivot_eq] at h
  exact lt_of_le_of_ne h (Ne.symm hj)

end MatrixSpencer.MSManuscriptNumericalLDL
