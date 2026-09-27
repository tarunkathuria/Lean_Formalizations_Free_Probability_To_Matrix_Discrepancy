import Mathlib.Analysis.Matrix.Order
import MatrixSpencer.InverseComparison



open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptLDL

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def column (P : Matrix ι ι ℝ) (i : ι) : ι → ℝ := fun a => P a i

def schur (P : Matrix ι ι ℝ) (i : ι) : Matrix ι ι ℝ :=
  P - (P i i)⁻¹ • Matrix.vecMulVec (column P i) (column P i)

theorem diagonal_nonneg {P : Matrix ι ι ℝ} (hP : P.PosSemidef) (i : ι) :
    0 ≤ P i i := by simpa using hP.2 (Pi.single i 1)

theorem column_zero_of_pivot_zero {P : Matrix ι ι ℝ} (hP : P.PosSemidef)
    (i : ι) (hi : P i i = 0) : column P i = 0 := by
  have h := (hP.dotProduct_mulVec_zero_iff (Pi.single i 1)).mp (by simpa using hi)
  simpa [column] using h

theorem column_pairing {P : Matrix ι ι ℝ} (hP : P.IsHermitian)
    (i : ι) (x : ι → ℝ) : x ⬝ᵥ column P i = (P *ᵥ x) i := by
  have hs : Pᵀ = P := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.eq
  simp only [dotProduct, column, Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro j _
  have h := congrFun (congrFun hs i) j
  simp only [Matrix.transpose_apply] at h
  rw [h, mul_comm]

theorem schur_quadratic (P : Matrix ι ι ℝ) (i : ι) (x : ι → ℝ) :
    x ⬝ᵥ (schur P i *ᵥ x) =
      x ⬝ᵥ (P *ᵥ x) - (P i i)⁻¹ * (x ⬝ᵥ column P i)^2 := by
  simp only [schur, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, Matrix.vecMulVec_mulVec]
  change x ⬝ᵥ (P *ᵥ x) - (P i i)⁻¹ *
    ((x ⬝ᵥ column P i) * (column P i ⬝ᵥ x)) = _
  rw [dotProduct_comm (column P i) x]
  ring

theorem schur_posSemidef {P : Matrix ι ι ℝ} (hP : P.PosSemidef) (i : ι) :
    (schur P i).PosSemidef := by
  by_cases hi : P i i = 0
  · simpa [schur, hi] using hP
  have hp : 0 < P i i := lt_of_le_of_ne (diagonal_nonneg hP i) (Ne.symm hi)
  refine ⟨hP.isHermitian.sub ((Matrix.posSemidef_vecMulVec_self_star (column P i)).smul
    (inv_nonneg.mpr hp.le)).isHermitian, ?_⟩
  intro x
  change 0 ≤ x ⬝ᵥ (schur P i *ᵥ x)
  rw [schur_quadratic, column_pairing hP.isHermitian]
  have h := hP.2 (x - ((P *ᵥ x) i / P i i) • (Pi.single i 1 : ι → ℝ))
  simp only [star_trivial, Matrix.mulVec_sub, Matrix.mulVec_smul,
    dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul,
    Matrix.mulVec_single_one, single_dotProduct, one_mul, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply, ite_true] at h
  have he : x ⬝ᵥ P.col i = (P *ᵥ x) i := column_pairing hP.isHermitian i x
  rw [he, show P.col i i = P i i from rfl] at h
  convert h using 1 <;> field_simp [hi] <;> ring

theorem schur_le {P : Matrix ι ι ℝ} (hP : P.PosSemidef) (i : ι) :
    schur P i ≤ P :=
  sub_le_self _ (((Matrix.posSemidef_vecMulVec_self_star (column P i)).smul
    (inv_nonneg.mpr (diagonal_nonneg hP i))).nonneg)

theorem schur_column_zero {P : Matrix ι ι ℝ} (hP : P.PosSemidef) (i : ι) :
    column (schur P i) i = 0 := by
  by_cases hi : P i i = 0
  · simp only [schur, hi, _root_.inv_zero, zero_smul, sub_zero]
    exact column_zero_of_pivot_zero hP i hi
  ext a
  simp only [column, schur, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, Pi.zero_apply]
  field_simp
  ring

theorem schur_preserves_zero_column {P : Matrix ι ι ℝ} {j : ι}
    (hP : P.IsHermitian) (hj : column P j = 0) (i : ι) : column (schur P i) j = 0 := by
  have hjj : P j i = 0 := by
    have hs : Pᵀ = P := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.eq
    have hs' := congrFun (congrFun hs j) i
    simpa only [Matrix.transpose_apply, show P i j = 0 from congrFun hj i] using hs'.symm
  ext a
  simp only [column, schur, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, Pi.zero_apply]
  rw [show P a j = 0 from congrFun hj a, hjj]
  simp

variable {d : ℕ}

/-- Visit each coordinate once; zero pivots produce zero Schur updates. -/
def residual (P : Matrix (Fin d) (Fin d) ℝ) : ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => P
  | j + 1 => if hj : j < d then schur (residual P j) ⟨j, hj⟩ else residual P j

def pivot (P : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : ℝ := residual P j j j

/-- The `j`th LDL column, with a harmless zero column for a zero pivot. -/
def lowerColumn (P : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : Fin d → ℝ :=
  fun a => residual P j a j / pivot P j

def term (P : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  pivot P j • Matrix.vecMulVec (lowerColumn P j) (lowerColumn P j)

def factorColumn (P : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : Fin d → ℝ :=
  Real.sqrt (pivot P j) • lowerColumn P j

theorem residual_posSemidef {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef)
    (j : ℕ) : (residual P j).PosSemidef := by
  induction j with
  | zero => exact hP
  | succ j ih =>
    simp only [residual]
    split
    · exact schur_posSemidef ih _
    · exact ih

theorem residual_le {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef)
    (j : ℕ) : residual P j ≤ P := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    simp only [residual]
    split
    · exact (schur_le (residual_posSemidef hP j) _).trans ih
    · exact ih

theorem pivot_nonneg {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef)
    (j : Fin d) : 0 ≤ pivot P j := diagonal_nonneg (residual_posSemidef hP j) j

theorem term_eq (P : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    term P j = (pivot P j)⁻¹ •
      Matrix.vecMulVec (column (residual P j) j) (column (residual P j) j) := by
  ext a b
  simp only [term, lowerColumn, column, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  by_cases hp : pivot P j = 0
  · simp [hp]
  · field_simp

theorem residual_succ (P : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    residual P (j.val + 1) = residual P j - term P j := by
  rw [residual, dif_pos j.isLt, term_eq]
  rfl

theorem residual_zero_columns {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef)
    (j : ℕ) (i : Fin d) (hi : i.val < j) : column (residual P j) i = 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hj : j < d
    · rw [residual, dif_pos hj]
      by_cases hij : i.val < j
      · exact schur_preserves_zero_column (residual_posSemidef hP j).isHermitian (ih hij) _
      · have he : i = ⟨j, hj⟩ := by
          apply Fin.ext
          change i.val = j
          omega
        subst i
        exact schur_column_zero (residual_posSemidef hP j) _
    · rw [residual, dif_neg hj]
      exact ih (by omega)

theorem residual_final {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) :
    residual P d = 0 := by
  ext a b
  exact congrFun (residual_zero_columns hP d b b.isLt) a

theorem sum_terms_add_residual (P : Matrix (Fin d) (Fin d) ℝ) (j : ℕ) (hj : j ≤ d) :
    (∑ i ∈ Finset.range j, if hi : i < d then term P ⟨i, hi⟩ else 0) + residual P j = P := by
  induction j with
  | zero => simp [residual]
  | succ j ih =>
    have hlt : j < d := by omega
    rw [Finset.sum_range_succ, dif_pos hlt]
    have hr := residual_succ P ⟨j, hlt⟩
    simp only [Fin.val_mk] at hr
    rw [hr]
    convert ih (by omega) using 1 <;> abel

/-- The actual arithmetic columns reconstruct every PSD input, including singular inputs. -/
theorem sum_terms {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) :
    (∑ j, term P j) = P := by
  have h := sum_terms_add_residual P d le_rfl
  rw [residual_final hP, add_zero] at h
  simpa only [← Fin.sum_univ_eq_sum_range, Fin.isLt, dif_pos, Fin.eta] using h

theorem factorColumn_outer {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef)
    (j : Fin d) :
    Matrix.vecMulVec (factorColumn P j) (factorColumn P j) = term P j := by
  ext a b
  simp only [factorColumn, term, Matrix.vecMulVec_apply, Matrix.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  have hs := Real.sq_sqrt (pivot_nonneg hP j)
  calc
    _ = Real.sqrt (pivot P j)^2 * (lowerColumn P j a * lowerColumn P j b) := by ring
    _ = _ := by rw [hs]

theorem factorColumn_sum {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) :
    (∑ j, Matrix.vecMulVec (factorColumn P j) (factorColumn P j)) = P := by
  simp_rw [factorColumn_outer hP]
  exact sum_terms hP

theorem term_posSemidef {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) (j : Fin d) :
    (term P j).PosSemidef := by
  rw [← factorColumn_outer hP]
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem term_le {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) (j : Fin d) :
    term P j ≤ P := by
  exact (Finset.single_le_sum (fun i _ => (term_posSemidef hP i).nonneg)
    (Finset.mem_univ j)).trans_eq (sum_terms hP)

end MatrixSpencer.KSEighthManuscriptLDL
