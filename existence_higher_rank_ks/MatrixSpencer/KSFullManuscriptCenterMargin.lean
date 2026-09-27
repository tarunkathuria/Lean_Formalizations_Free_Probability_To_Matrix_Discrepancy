import MatrixSpencer.KSFullManuscriptStrictFeasible
import MatrixSpencer.KSFullManuscriptSDPBlockPencil

/-! An explicit strictly feasible center for the single SDP block pencil. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptCenterMargin
open KSFullManuscriptStrictFeasible KSFullManuscriptSDPBlockPencil
variable {d : ℕ} {ι : Type*} [Fintype ι]

def margin (d : ℕ) (lam : ℝ) := min lam (1/(4*(d : ℝ)))

theorem margin_pos (hd : 0 < d) {lam : ℝ} (hlam : 0 < lam) : 0 < margin d lam := by
  unfold margin
  positivity

private theorem scalar_mono {n : Type*} [Fintype n] [DecidableEq n]
    {a b : ℝ} (h : a ≤ b) : a • (1 : Matrix n n ℂ) ≤ b • 1 := by
  apply Matrix.le_iff.mpr
  rw [← sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr h)

private theorem block_floor {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] {A : Matrix n n ℂ} {B : Matrix m m ℂ} {a : ℝ}
    (ha : a • 1 ≤ A) (hb : a • 1 ≤ B) :
    a • (1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) ≤ Matrix.fromBlocks A 0 0 B := by
  have he : Matrix.fromBlocks (a • (1 : Matrix n n ℂ)) 0 0 (a • (1 : Matrix m m ℂ)) =
      a • (1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply]
  simpa only [he] using fromBlocks_diagonal_mono ha hb

theorem center_floor (B : ι → Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d)
    {lam : ℝ} (hlam : 0 < lam) :
    margin d lam • (1 : Matrix (ComplexIndex (Fin d)) (ComplexIndex (Fin d)) ℂ) ≤
      block B lam (density d) (rootCenter d) 0 := by
  have hn : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hn1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hn
  have hrsq : (Real.sqrt (d : ℝ))^2 = d := Real.sq_sqrt hn.le
  have hrs : Real.sqrt (d : ℝ) ≤ d := by nlinarith
  have hm : margin d lam ≤ 1/(4*(d : ℝ)) := min_le_right _ _
  have hmd : margin d lam ≤ 1/(d : ℝ) := hm.trans (by
    apply one_div_le_one_div_of_le hn
    linarith)
  have hmr : margin d lam ≤ rootMargin d := hm.trans (by
    unfold rootMargin
    apply one_div_le_one_div_of_le (by positivity)
    linarith)
  have hmy : margin d lam ≤ 1/(2*Real.sqrt (d : ℝ)) := hm.trans (by
    apply one_div_le_one_div_of_le (by positivity)
    linarith)
  have hY : margin d lam • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ rootCenter d := scalar_mono hmy
  have hM := krausChannel_posSemidef B (density_posDef hd).posSemidef
  have hF := (scalar_mono (le_min hmd (min_le_left lam _))).trans
    (source_block_floor hd hM hlam)
  have hR := (scalar_mono hmr).trans (root_block_floor hd)
  simpa only [block, Matrix.conjTranspose_zero] using block_floor hY (block_floor hF hR)

end MatrixSpencer.KSFullManuscriptCenterMargin
