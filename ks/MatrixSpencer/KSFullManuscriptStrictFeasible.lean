import MatrixSpencer.KSFullManuscriptBlockBounds
import MatrixSpencer.SignedLift


open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptStrictFeasible
variable {d : ℕ}

def density (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := (1/(d : ℝ)) • 1
def rootCenter (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := (1/(2*Real.sqrt (d : ℝ))) • 1
def rootMargin (d : ℕ) : ℝ := 1/(2*(d : ℝ))

theorem density_posDef (hd : 0 < d) : (density d).PosDef :=
  Matrix.PosDef.one.smul (by positivity)

theorem density_trace (hd : 0 < d) : realTrace (density d) = 1 := by
  have hn : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd).ne'
  simp [density, realTrace_smul, realTrace, Matrix.trace, hn]

theorem rootCenter_posDef (hd : 0 < d) : (rootCenter d).PosDef :=
  Matrix.PosDef.one.smul (by positivity)

theorem rootMargin_pos (hd : 0 < d) : 0 < rootMargin d := by unfold rootMargin; positivity

theorem root_block_floor (hd : 0 < d) :
    rootMargin d • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ) ≤
      Matrix.fromBlocks (density d) (rootCenter d) (rootCenter d) 1 := by
  have hn : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hn1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hn
  have hrsq : (Real.sqrt (d : ℝ))^2 = d := Real.sq_sqrt hn.le
  let W : Matrix (Fin d ⊕ Fin d) (Fin d) ℂ :=
    Matrix.fromRows ((1/Real.sqrt (d : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) 1
  have hw := (Matrix.posSemidef_self_mul_conjTranspose W).smul (show (0 : ℝ) ≤ 1/2 by norm_num)
  have hc : 0 ≤ (1/2 : ℝ)-rootMargin d := by
    unfold rootMargin
    rw [sub_nonneg, div_le_iff₀ (by positivity : 0 < 2*(d : ℝ))]
    linarith
  have hb := posSemidef_fromBlocks_diagonal
    (Matrix.PosSemidef.zero : (0 : Matrix (Fin d) (Fin d) ℂ).PosSemidef)
    ((Matrix.PosSemidef.one : (1 : Matrix (Fin d) (Fin d) ℂ).PosSemidef).smul hc)
  apply Matrix.le_iff.mpr
  convert hw.add hb using 1
  have he : (1/Real.sqrt (d : ℝ))^2 = 1/(d : ℝ) := by rw [div_pow, one_pow, hrsq]
  have hec : ((Real.sqrt (d : ℝ) : ℂ)⁻¹)^2 = (d : ℂ)⁻¹ := by
    simpa only [one_div, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_natCast] using congrArg (fun x : ℝ => (x : ℂ)) he
  ext i j
  cases i <;> cases j <;>
    simp [W, density, rootCenter, rootMargin,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromRows_mul_fromCols, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_apply, smul_smul]
  all_goals split_ifs <;> simp_all [hec] <;> ring
  all_goals rw [inv_pow, hec]

/-- A regularized source has the explicit block-diagonal floor. -/
theorem source_block_floor (hd : 0 < d) {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M.PosSemidef) {ρ : ℝ} (hρ : 0 < ρ) :
    min (1/(d : ℝ)) ρ • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ) ≤
      Matrix.fromBlocks (density d) 0 0 (M+ρ • 1) := by
  have ha : 0 ≤ 1/(d : ℝ)-min (1/(d : ℝ)) ρ := sub_nonneg.mpr (min_le_left _ _)
  have hb : 0 ≤ ρ-min (1/(d : ℝ)) ρ := sub_nonneg.mpr (min_le_right _ _)
  have hp := posSemidef_fromBlocks_diagonal
    ((Matrix.PosSemidef.one : (1 : Matrix (Fin d) (Fin d) ℂ).PosSemidef).smul ha)
    (hM.add (Matrix.PosSemidef.one.smul hb))
  apply Matrix.le_iff.mpr
  convert hp using 1
  ext i j
  cases i <;> cases j <;> simp [density, Matrix.one_apply, sub_smul] <;> ring

end MatrixSpencer.KSFullManuscriptStrictFeasible
