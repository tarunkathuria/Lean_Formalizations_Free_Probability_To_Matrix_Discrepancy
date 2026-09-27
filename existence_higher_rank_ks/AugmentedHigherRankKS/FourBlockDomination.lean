import AugmentedHigherRankKS.FourBlockCompression
import HigherRankKS.CarrierOrder
import MatrixSpencer.KSSignSymmetry

/-! A coarse source bound valid at arbitrary full densities.  This avoids
requiring a symmetry hypothesis in the local response argument. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS KSSignSymmetry
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance dominationCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}

/-- Two-block partial trace bounds the original PSD matrix with factor two. -/
theorem le_twice_duplicate_marginal {S : Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hS : S.PosSemidef) :
    S ≤ (2 : ℝ) • HigherRankKS.spinAtom (HigherRankKS.marginal S) := by
  have hj := (conjugate_posSemidef signMatrix_isHermitian hS).nonneg
  have hr := (posSemidef_fromBlocks_diagonal
    (hS.submatrix Sum.inr) (hS.submatrix Sum.inl)).nonneg
  have hh := add_nonneg hj (smul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr)
  apply sub_nonneg.mp
  convert hh using 1
  rw [sign_conjugate_blocks]
  ext (i | i) (j | j) <;>
    simp [HigherRankKS.spinAtom, HigherRankKS.marginal, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₂, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁] <;> ring

/-- Four-block partial trace bounds the original PSD matrix with factor four. -/
theorem le_four_spinAtom_marginal {S : Matrix (FourSpin n) (FourSpin n) ℂ}
    (hS : S.PosSemidef) : S ≤ (4 : ℝ) • spinAtom (marginal S) := by
  have h₁ := le_twice_duplicate_marginal hS
  have h₂ := le_twice_duplicate_marginal (HigherRankKS.marginal_posSemidef hS)
  have hd : HigherRankKS.spinAtom (HigherRankKS.marginal S) ≤
      (2 : ℝ) • spinAtom (marginal S) := by
    apply sub_nonneg.mp
    have hh := (HigherRankKS.spinAtom_posSemidef
      (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h₂))).nonneg
    convert hh using 1
    ext (i | i) (j | j) <;> simp [spinAtom, HigherRankKS.spinAtom, marginal] <;> module
  exact h₁.trans ((smul_le_smul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
    (by simp only [smul_smul]; norm_num))

/-- The original power source dominates its unregularized physical carrier. -/
theorem sourceTerm_ge_carrier {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    spinAtom A * spinAtom (marginal S) * spinAtom A ≤ sourceTerm β A S := by
  have hm := HigherRankKS.carrier_posSemidef A (HigherRankKS.marginal_posSemidef hS)
  have ho := HigherRankKS.le_carrierPower hm hβ hβ1
  have hc := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr ho)).conjTranspose_mul_mul_same
    (CFC.sqrt A)
  have he : (HigherRankKS.sourceBlock β A (HigherRankKS.marginal S) - A * marginal S * A).PosSemidef := by
    convert hc using 1
    simp only [HigherRankKS.sourceBlock, Matrix.mul_sub, Matrix.sub_mul,
      (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq, HigherRankKS.carrier]
    congr 1
    simp only [← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self A hA.nonneg]
    simp only [Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self A hA.nonneg, marginal]
  have hs := (spinAtom_posSemidef he).nonneg
  apply sub_nonneg.mp
  convert hs using 1
  ext (i | i) (j | j) <;> cases i <;> cases j <;>
    simp [spinAtom, HigherRankKS.spinAtom, sourceTerm, HigherRankKS.sourceTerm,
      HigherRankKS.spinDuplicateCLM, Matrix.fromBlocks_multiply]

/-- A full-density source bound. No optimizer or spin symmetry is assumed. -/
theorem atom_density_atom_le_source {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    spinAtom A * S * spinAtom A ≤ (4 : ℝ) • sourceTerm β A S := by
  have h := (Matrix.nonneg_iff_posSemidef.mp
    (sub_nonneg.mpr (le_four_spinAtom_marginal hS))).conjTranspose_mul_mul_same (spinAtom A)
  have ha := (spinAtom_posSemidef hA).isHermitian.eq
  have h₁ : spinAtom A * S * spinAtom A ≤
      (4 : ℝ) • (spinAtom A * spinAtom (marginal S) * spinAtom A) := by
    apply sub_nonneg.mp
    simpa only [ha, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc] using h.nonneg
  exact h₁.trans (smul_le_smul_of_nonneg_left (sourceTerm_ge_carrier hA hS hβ hβ1)
    (by norm_num : (0 : ℝ) ≤ 4))


/-- The actual coefficient force for discrepancy and budget centers. -/
def forceAtom (x : ℝ) (A : Matrix n n ℂ) : Matrix (FourSpin n) (FourSpin n) ℂ :=
  Matrix.fromBlocks (signedLift A) 0 0 ((-2 * x) • signedLift A)

theorem forceAtom_isHermitian (x : ℝ) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (forceAtom x A).IsHermitian := by
  exact Matrix.IsHermitian.fromBlocks (signedLift_isHermitian hA)
    (by simp) (by
      change ((-2 * x) • signedLift A)ᴴ = (-2 * x) • signedLift A
      simp only [Matrix.conjTranspose_smul, starRingEnd_apply, star_trivial,
        (signedLift_isHermitian hA).eq])

/-- The force multiplier has squared size at most four on every spin block. -/
theorem force_carrier_le {A T : Matrix n n ℂ} (hA : A.PosSemidef) (hT : T.PosSemidef)
    {x : ℝ} (hx : |x| ≤ 1) :
    forceAtom x A * spinAtom T * forceAtom x A ≤
      (4 : ℝ) • (spinAtom A * spinAtom T * spinAtom A) := by
  have hATA : (A * T * A).PosSemidef := by
    simpa only [hA.isHermitian.eq] using hT.conjTranspose_mul_mul_same A
  have hcoef : 0 ≤ 4 - (-2 * x) * (-2 * x) := by
    have hsq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).mpr hx
    nlinarith
  have hP := (HigherRankKS.spinAtom_posSemidef hATA).nonneg
  have hs := (posSemidef_fromBlocks_diagonal
    (Matrix.nonneg_iff_posSemidef.mp (smul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hP))
    (Matrix.nonneg_iff_posSemidef.mp (smul_nonneg hcoef hP))).nonneg
  apply sub_nonneg.mp
  convert hs using 1
  ext (i | i) (j | j) <;> cases i <;> cases j <;>
    simp [forceAtom, signedLift, spinAtom, HigherRankKS.spinAtom,
      Matrix.fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, smul_smul] <;> ring

/-- The actual four-center force has energy at most sixteen source probes. -/
theorem force_density_force_le_source {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef)
    {β x : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hx : |x| ≤ 1) :
    forceAtom x A * S * forceAtom x A ≤ (16 : ℝ) • sourceTerm β A S := by
  have hh := (Matrix.nonneg_iff_posSemidef.mp
    (sub_nonneg.mpr (le_four_spinAtom_marginal hS))).conjTranspose_mul_mul_same (forceAtom x A)
  have hfirst : forceAtom x A * S * forceAtom x A ≤
      (4 : ℝ) • (forceAtom x A * spinAtom (marginal S) * forceAtom x A) := by
    apply sub_nonneg.mp
    simpa only [(forceAtom_isHermitian x hA.isHermitian).eq, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] using hh.nonneg
  have hsecond := smul_le_smul_of_nonneg_left
    (force_carrier_le hA (marginal_posSemidef hS) hx) (by norm_num : (0 : ℝ) ≤ 4)
  have hthird := smul_le_smul_of_nonneg_left
    (sourceTerm_ge_carrier hA hS hβ hβ1) (by norm_num : (0 : ℝ) ≤ 16)
  exact hfirst.trans (hsecond.trans (by norm_num only [smul_smul] at *; exact hthird))

end AugmentedHigherRankKS
