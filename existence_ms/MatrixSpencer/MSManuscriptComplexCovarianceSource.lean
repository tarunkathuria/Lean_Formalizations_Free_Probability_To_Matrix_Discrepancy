import MatrixSpencer.CovarianceSource
import MatrixSpencer.KrausContraction
import MatrixSpencer.KSAccretiveProductDomain

/-!
# Complex bilinear covariance source and order-controlled perturbations

The extension is the actual general Kraus source, not a trace-and-prepare
specialization. Coefficient and density matrices may be genuinely complex.
Hermitian order estimates are later applied to their real and imaginary
Hermitian parts, yielding a conservative source-gap-free complex domain.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptComplexCovarianceSource
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def source (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℂ) (S : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑i, ∑j, C i j • (A i * S * A j)

def mixed (A : ι → Matrix n n ℂ) (R : Matrix ι ι ℂ) (a : ι) := ∑i, R i a • A i

theorem source_real (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (S : Matrix n n ℂ) :
    source A (fun i j => (C i j : ℂ)) S = covarianceSource A C S := by
  ext a b
  simp [source,covarianceSource,Matrix.smul_apply,Complex.real_smul]

theorem source_factor (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    (R : Matrix ι ι ℂ) (S : Matrix n n ℂ) :
    source A (R*Rᴴ) S = krausChannel (mixed A R) S := by
  simp only [source,mixed,krausChannel,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Finset.sum_smul,Matrix.sum_mul,Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul,
    Finset.smul_sum,smul_smul,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,
    fun i => (hA i).eq]
  calc
    _ = ∑i, ∑a, ∑j, (R i a * star (R j a)) • (A i*S*A j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑a, ∑i, ∑j, (R i a * star (R j a)) • (A i*S*A j) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm (R j a) (star (R i a))]

theorem source_posSemidef (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    (source A C S).PosSemidef := by
  have he : CFC.sqrt C*(CFC.sqrt C)ᴴ = C := by
    rw [(CFC.sqrt_nonneg C).posSemidef.isHermitian.eq,CFC.sqrt_mul_sqrt_self C hC.nonneg]
  rw [←he,source_factor A hA]
  exact krausChannel_posSemidef _ hS

theorem source_add_left (A : ι → Matrix n n ℂ) (C X : Matrix ι ι ℂ) (S : Matrix n n ℂ) :
    source A (C+X) S = source A C S+source A X S := by
  simp [source,add_smul,Finset.sum_add_distrib]

theorem source_sub_left (A : ι → Matrix n n ℂ) (C X : Matrix ι ι ℂ) (S : Matrix n n ℂ) :
    source A (C-X) S = source A C S-source A X S := by
  simp [source,sub_smul,Finset.sum_sub_distrib]

theorem source_smul_left (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℂ) (S : Matrix n n ℂ) (a : ℂ) :
    source A (a • C) S = a • source A C S := by
  simp [source,Finset.smul_sum,smul_smul]

theorem source_real_smul_left (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℂ) (S : Matrix n n ℂ) (a : ℝ) :
    source A (a • C) S = a • source A C S := by
  simpa only [Complex.real_smul] using source_smul_left A C S (a:ℂ)

theorem source_add_right (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℂ) (S Y : Matrix n n ℂ) :
    source A C (S+Y) = source A C S+source A C Y := by
  simp [source,Matrix.mul_add,Matrix.add_mul,smul_add,Finset.sum_add_distrib]

theorem source_sub_right (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℂ) (S Y : Matrix n n ℂ) :
    source A C (S-Y) = source A C S-source A C Y := by
  simp [source,Matrix.mul_sub,Matrix.sub_mul,smul_sub,Finset.sum_sub_distrib]

theorem source_smul_right (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℂ) (S : Matrix n n ℂ) (a : ℂ) :
    source A C (a • S) = a • source A C S := by
  simp only [source,Matrix.mul_smul,Matrix.smul_mul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ _ _

theorem source_real_smul_right (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℂ) (S : Matrix n n ℂ) (a : ℝ) :
    source A C (a • S) = a • source A C S := by
  simpa only [Complex.real_smul] using source_smul_right A C S (a:ℂ)

theorem source_isHermitian (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    {C : Matrix ι ι ℂ} (hC : C.IsHermitian) {S : Matrix n n ℂ} (hS : S.IsHermitian) :
    (source A C S).IsHermitian := by
  unfold source Matrix.IsHermitian
  simp only [Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,
    fun i => (hA i).eq,hS.eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [←Matrix.conjTranspose_apply C, hC.eq,Matrix.mul_assoc]

/-- Positivity in both arguments implies a mixed two-sided order bound. -/
theorem source_mixed_order (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    {C X : Matrix ι ι ℂ} {S Y : Matrix n n ℂ} {a b : ℝ}
    (hx : (-a) • C ≤ X ∧ X ≤ a • C) (hy : (-b) • S ≤ Y ∧ Y ≤ b • S) :
    (-(a*b)) • source A C S ≤ source A X Y ∧ source A X Y ≤ (a*b) • source A C S := by
  have hxp : (a • C+X).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    have hh := add_le_add_left hx.1 (a • C)
    simpa only [neg_smul,add_neg_cancel] using hh
  have hxm : (a • C-X).PosSemidef := Matrix.le_iff.mp hx.2
  have hyp : (b • S+Y).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    have hh := add_le_add_left hy.1 (b • S)
    simpa only [neg_smul,add_neg_cancel] using hh
  have hym : (b • S-Y).PosSemidef := Matrix.le_iff.mp hy.2
  have hp := (source_posSemidef A hA hxp hyp).add (source_posSemidef A hA hxm hym)
  have hm := (source_posSemidef A hA hxp hym).add (source_posSemidef A hA hxm hyp)
  simp only [source_add_left,source_sub_left,source_add_right,source_sub_right,
    source_real_smul_left,source_real_smul_right,smul_add,smul_sub,smul_smul] at hp hm
  constructor
  · apply Matrix.le_iff.mpr
    have hh := hp.smul (by norm_num : (0 : ℝ) ≤ 1/2)
    convert hh using 1 <;> module
  · apply Matrix.le_iff.mpr
    have hh := hm.smul (by norm_num : (0 : ℝ) ≤ 1/2)
    convert hh using 1 <;> module

end MatrixSpencer.MSManuscriptComplexCovarianceSource
