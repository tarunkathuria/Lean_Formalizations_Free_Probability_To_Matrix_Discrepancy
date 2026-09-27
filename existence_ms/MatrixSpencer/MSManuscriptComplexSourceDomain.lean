import MatrixSpencer.MSManuscriptComplexSourcePerturbation
import MatrixSpencer.CovarianceSupport
import MatrixSpencer.ComplexGram
import MatrixSpencer.KSComplexSpinDomain



open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.MSManuscriptComplexSourceDomain
open MSManuscriptComplexCovarianceSource MSManuscriptComplexSourcePerturbation KSAccretiveProductDomain
variable {ι n m : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def radius (γ μ : ℝ) : ℝ := γ*μ/128

theorem radius_pos {γ μ : ℝ} (hγ : 0 < γ) (hμ : 0 < μ) : 0 < radius γ μ := by unfold radius; positivity

theorem radius_le_coefficient {γ μ : ℝ} (hγ : 0 ≤ γ) (hμ1 : μ ≤ 1) : radius γ μ ≤ γ/128 := by
  unfold radius
  nlinarith [mul_le_mul_of_nonneg_left hμ1 hγ]

theorem radius_le_density {γ μ : ℝ} (hμ : 0 ≤ μ) (hγ1 : γ ≤ 1) : radius γ μ ≤ μ/128 := by
  unfold radius
  nlinarith [mul_le_mul_of_nonneg_right hγ1 hμ]

/-- The conservative complex relative error is still strictly less than1/16. -/
theorem relative_source_bound (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    {C X : Matrix ι ι ℂ} {S Y : Matrix n n ℂ} {γ μ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hC : γ • (1 : Matrix ι ι ℂ) ≤ C) (hS : μ • (1 : Matrix n n ℂ) ≤ S)
    (hx : ‖X‖ ≤ radius γ μ) (hy : ‖Y‖ ≤ radius γ μ)
    (W : Matrix m n ℂ) (hW : W*source A C S*Wᴴ=1) :
    ‖W*source A (C+X) (S+Y)*Wᴴ-1‖ ≤ 129/4096 := by
  have hb := relative_source_norm A hA hγ hμ (radius_pos hγ hμ).le (radius_pos hγ hμ).le
    hC hS hx hy W hW
  have ha : radius γ μ/γ ≤ 1/128 := by
    apply (div_le_iff₀ hγ).mpr
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using radius_le_coefficient hγ.le hμ1
  have hc : radius γ μ/μ ≤ 1/128 := by
    apply (div_le_iff₀ hμ).mpr
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using radius_le_density hμ.le hγ1
  have hp := mul_le_mul ha hc (div_nonneg (radius_pos hγ hμ).le hμ.le) (by norm_num : (0:ℝ)≤1/128)
  exact hb.trans (by nlinarith)

def base (A : ι → Matrix n n ℂ) (V : Matrix n m ℂ) (C : Matrix ι ι ℂ) (S : Matrix n n ℂ) :=
  Vᴴ*source A C S*V

def whitener (A : ι → Matrix n n ℂ) (V : Matrix n m ℂ) (C : Matrix ι ι ℂ) (S : Matrix n n ℂ) :=
  (CFC.sqrt (base A V C S))⁻¹*Vᴴ

theorem whitener_congruence (A : ι → Matrix n n ℂ) (V : Matrix n m ℂ)
    (C : Matrix ι ι ℂ) (S T : Matrix n n ℂ) :
    whitener A V C S*T*(whitener A V C S)ᴴ =
      (CFC.sqrt (base A V C S))⁻¹*(Vᴴ*T*V)*(CFC.sqrt (base A V C S))⁻¹ := by
  have hs := ((CFC.sqrt_nonneg (base A V C S)).posSemidef.isHermitian.inv).eq
  simp only [whitener,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hs,Matrix.mul_assoc]

theorem whitener_normalizes (A : ι → Matrix n n ℂ) (V : Matrix n m ℂ)
    (C : Matrix ι ι ℂ) (S : Matrix n n ℂ) (hb : (base A V C S).PosDef) :
    whitener A V C S*source A C S*(whitener A V C S)ᴴ=1 := by
  rw [whitener_congruence]
  change (CFC.sqrt (base A V C S))⁻¹*base A V C S*(CFC.sqrt (base A V C S))⁻¹=1
  have hu := (CFC.sqrt (base A V C S)).isUnit_iff_isUnit_det.mp hb.posDef_sqrt.isUnit
  conv_lhs => lhs; rhs; rw [←CFC.sqrt_mul_sqrt_self _ hb.posSemidef.nonneg]
  rw [←Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hu,Matrix.one_mul,Matrix.mul_nonsing_inv _ hu]

theorem compressedSource_strictAccretive (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    (V : Matrix n m ℂ) {C X : Matrix ι ι ℂ} {S Y : Matrix n n ℂ}
    (hb : (base A V C S).PosDef) {γ μ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hC : γ • (1 : Matrix ι ι ℂ) ≤ C) (hS : μ • (1 : Matrix n n ℂ) ≤ S)
    (hx : ‖X‖ ≤ radius γ μ) (hy : ‖Y‖ ≤ radius γ μ) :
    StrictAccretive (Vᴴ*source A (C+X) (S+Y)*V) := by
  have hn := relative_source_bound A hA hγ hγ1 hμ hμ1 hC hS hx hy
    (whitener A V C S) (whitener_normalizes A V C S hb)
  rw [whitener_congruence] at hn
  have hu := (CFC.sqrt (base A V C S)).isUnit_iff_isUnit_det.mp hb.posDef_sqrt.isUnit
  have hh := sqrt_sandwich_strictAccretive hb (hn.trans_lt (by norm_num : (129:ℝ)/4096<1))
  have he : CFC.sqrt (base A V C S)*
      (1+((CFC.sqrt (base A V C S))⁻¹*(Vᴴ*source A (C+X) (S+Y)*V)*(CFC.sqrt (base A V C S))⁻¹-1))*
      CFC.sqrt (base A V C S) = Vᴴ*source A (C+X) (S+Y)*V := by
    rw [←add_sub_assoc,add_sub_cancel_left]
    simp only [←Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hu,Matrix.one_mul]
    rw [Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hu,Matrix.mul_one]
  rwa [he] at hh

theorem compressedDensity_strictAccretive (V : Matrix n m ℂ) (hV : Vᴴ*V=1)
    {S Y : Matrix n n ℂ} {γ μ : ℝ} (hγ1 : γ ≤ 1) (hμ : 0 < μ)
    (hS : μ • (1 : Matrix n n ℂ) ≤ S) (hy : ‖Y‖ ≤ radius γ μ) :
    StrictAccretive (Vᴴ*(S+Y)*V) := by
  apply KSComplexSpinDomain.compress_strictAccretive V hV
  apply KSComplexSpinDomain.density_strictAccretive hS
  have hr := radius_le_density hμ.le hγ1
  linarith

/-- Abstract compression interface, with no numerical source condition number. -/
theorem product_spectrum_subset_slitPlane (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    (V : Matrix n m ℂ) (hV : Vᴴ*V=1) {C X : Matrix ι ι ℂ} {S Y : Matrix n n ℂ}
    (hb : (base A V C S).PosDef) {γ μ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hC : γ • (1 : Matrix ι ι ℂ) ≤ C) (hS : μ • (1 : Matrix n n ℂ) ≤ S)
    (hx : ‖X‖ ≤ radius γ μ) (hy : ‖Y‖ ≤ radius γ μ) :
    spectrum ℂ ((Vᴴ*(S+Y)*V)*(Vᴴ*source A (C+X) (S+Y)*V)) ⊆ Complex.slitPlane :=
  KSAccretiveProductDomain.product_spectrum_subset_slitPlane
    (compressedDensity_strictAccretive V hV hγ1 hμ hS hy)
    (compressedSource_strictAccretive A hA V hb hγ hγ1 hμ hμ1 hC hS hx hy)

/-- The actual fixed-support source domain for arbitrary original Hermitian matrices.
Source support positivity is discharged from the coefficient and density floors. -/
theorem actual_product_spectrum_subset_slitPlane (A : ι → Matrix n n ℂ)
    (hA : ∀i, (A i).IsHermitian) {C : Matrix ι ι ℝ} {X : Matrix ι ι ℂ} {S Y : Matrix n n ℂ}
    {γ μ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hC : γ • (1 : Matrix ι ι ℝ) ≤ C) (hS : μ • (1 : Matrix n n ℂ) ≤ S)
    (hx : ‖X‖ ≤ radius γ μ) (hy : ‖Y‖ ≤ radius γ μ) :
    let V := krausSupportEmbedding A
    spectrum ℂ ((Vᴴ*(S+Y)*V)*(Vᴴ*source A (realMatrixEmbedding C+X) (S+Y)*V)) ⊆ Complex.slitPlane := by
  have hCp : C.PosDef := by
    have hh := (Matrix.PosDef.one.smul hγ).add_posSemidef (Matrix.le_iff.mp hC)
    simpa only [add_sub_cancel] using hh
  have hSp := KSComplexSpinDomain.posDef_of_floor hμ hS
  have hbase : (base A (krausSupportEmbedding A) (realMatrixEmbedding C) S).PosDef := by
    change ((krausSupportEmbedding A)ᴴ*source A (fun i j => (C i j : ℂ)) S*krausSupportEmbedding A).PosDef
    rw [source_real]
    exact covarianceCompressedSource_posDef A hA hCp hSp
  have hCc : γ • (1 : Matrix ι ι ℂ) ≤ realMatrixEmbedding C := by
    have hh := realMatrixEmbedding_mono hC
    simpa only [←Algebra.algebraMap_eq_smul_one,realMatrixEmbedding_algebraMap] using hh
  exact product_spectrum_subset_slitPlane A hA (krausSupportEmbedding A)
    (krausSupportEmbedding_isometry A) hbase hγ hγ1 hμ hμ1 hCc hS hx hy

end MatrixSpencer.MSManuscriptComplexSourceDomain
