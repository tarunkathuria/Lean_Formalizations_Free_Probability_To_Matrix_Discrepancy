import MatrixSpencer.MSManuscriptComplexCovarianceSource



open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.MSManuscriptComplexSourcePerturbation
open MSManuscriptComplexCovarianceSource
variable {ι n m : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def realPart (X : Matrix n n ℂ) : Matrix n n ℂ := (1/2 : ℝ) • (X+Xᴴ)
def imagPart (X : Matrix n n ℂ) : Matrix n n ℂ := realPart ((-Complex.I) • X)

theorem realPart_isHermitian (X : Matrix n n ℂ) : (realPart X).IsHermitian := by
  unfold realPart Matrix.IsHermitian
  simp only [Matrix.conjTranspose_smul,star_trivial,Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose,add_comm]

theorem imagPart_isHermitian (X : Matrix n n ℂ) : (imagPart X).IsHermitian := realPart_isHermitian _

theorem realPart_norm_le (X : Matrix n n ℂ) : ‖realPart X‖ ≤ ‖X‖ := by
  unfold realPart
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have hh := norm_add_le X Xᴴ
  rw [Matrix.l2_opNorm_conjTranspose] at hh
  linarith

theorem imagPart_norm_le (X : Matrix n n ℂ) : ‖imagPart X‖ ≤ ‖X‖ := by
  have hh := realPart_norm_le ((-Complex.I) • X)
  simpa only [imagPart,norm_smul,norm_neg,Complex.norm_I,one_mul] using hh

theorem parts_sum (X : Matrix n n ℂ) : realPart X+Complex.I • imagPart X = X := by
  ext i j
  simp [realPart,imagPart,Matrix.conjTranspose_smul,Matrix.conjTranspose_apply,
    Matrix.smul_apply,smul_eq_mul,Complex.real_smul]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- A scalar reference floor converts a Hermitian norm bound into relative order. -/
theorem relative_order_of_floor {C X : Matrix n n ℂ} (hX : X.IsHermitian) {γ r : ℝ}
    (hγ : 0 < γ) (hr : 0 ≤ r) (hfloor : γ • (1 : Matrix n n ℂ) ≤ C) (hx : ‖X‖ ≤ r) :
    (-(r/γ)) • C ≤ X ∧ X ≤ (r/γ) • C := by
  have upper {Y : Matrix n n ℂ} (hY : Y.IsHermitian) (hy : ‖Y‖ ≤ r) : Y ≤ (r/γ) • C := by
    have ho : Y ≤ ‖Y‖ • (1 : Matrix n n ℂ) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using (show IsSelfAdjoint Y from hY).le_algebraMap_norm_self
    have hn := smul_le_smul_of_nonneg_right hy (Matrix.PosSemidef.one.nonneg : (0:Matrix n n ℂ)≤1)
    have hf := smul_le_smul_of_nonneg_left hfloor (div_nonneg hr hγ.le)
    have he : (r/γ) • (γ • (1 : Matrix n n ℂ)) = r • (1 : Matrix n n ℂ) := by
      rw [smul_smul,div_mul_cancel₀ r hγ.ne']
    rw [he] at hf
    exact ho.trans (hn.trans hf)
  exact ⟨by simpa only [neg_smul,neg_neg] using neg_le_neg (upper hX.neg (by simpa using hx)),upper hX hx⟩

/-- Compression and exact whitening cost no factor involving a source eigenvalue. -/
theorem hermitian_source_norm (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    {C X : Matrix ι ι ℂ} {S Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : (-a) • C ≤ X ∧ X ≤ a • C) (hy : (-b) • S ≤ Y ∧ Y ≤ b • S)
    (W : Matrix m n ℂ) (hW : W*source A C S*Wᴴ=1) :
    ‖W*source A X Y*Wᴴ‖ ≤ a*b := by
  have hh := source_mixed_order A hA hx hy
  have hherm := Matrix.isHermitian_mul_mul_conjTranspose W (source_isHermitian A hA hX hY)
  apply KrausContraction.norm_le_of_order_interval hherm (mul_nonneg ha hb)
  · have hp := (Matrix.le_iff.mp hh.1).mul_mul_conjTranspose_same W
    apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,hW] using hp
  · have hp := (Matrix.le_iff.mp hh.2).mul_mul_conjTranspose_same W
    apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,hW] using hp

/-- The finite polynomial source is holomorphic on all complex coefficient/density coordinates. -/
theorem contDiff_source (A : ι → Matrix n n ℂ) :
    ContDiff ℂ ∞ (fun p : Matrix ι ι ℂ × Matrix n n ℂ => source A p.1 p.2) := by
  unfold source
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  let e : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun C => C i j
      map_add' := by intro C D; rfl
      map_smul' := by intro a C; rfl }
  exact (e.toContinuousLinearMap.contDiff.comp contDiff_fst).smul
    ((contDiff_const.mul contDiff_snd).mul contDiff_const)

def compressed (A : ι → Matrix n n ℂ) (W : Matrix m n ℂ)
    (C : Matrix ι ι ℂ) (S : Matrix n n ℂ) := W*source A C S*Wᴴ

theorem compressed_add_left (A : ι → Matrix n n ℂ) (W : Matrix m n ℂ)
    (C X : Matrix ι ι ℂ) (S : Matrix n n ℂ) :
    compressed A W (C+X) S = compressed A W C S+compressed A W X S := by
  simp only [compressed,source_add_left,Matrix.mul_add,Matrix.add_mul]

theorem compressed_add_right (A : ι → Matrix n n ℂ) (W : Matrix m n ℂ)
    (C : Matrix ι ι ℂ) (S Y : Matrix n n ℂ) :
    compressed A W C (S+Y) = compressed A W C S+compressed A W C Y := by
  simp only [compressed,source_add_right,Matrix.mul_add,Matrix.add_mul]

theorem compressed_smul_left (A : ι → Matrix n n ℂ) (W : Matrix m n ℂ)
    (C : Matrix ι ι ℂ) (S : Matrix n n ℂ) (a : ℂ) :
    compressed A W (a • C) S = a • compressed A W C S := by
  simp only [compressed,source_smul_left,Matrix.mul_smul,Matrix.smul_mul]

theorem compressed_smul_right (A : ι → Matrix n n ℂ) (W : Matrix m n ℂ)
    (C : Matrix ι ι ℂ) (S : Matrix n n ℂ) (a : ℂ) :
    compressed A W C (a • S) = a • compressed A W C S := by
  simp only [compressed,source_smul_right,Matrix.mul_smul,Matrix.smul_mul]

theorem norm_add_I_le {X Y : Matrix m m ℂ} {R : ℝ} (hx : ‖X‖ ≤ R) (hy : ‖Y‖ ≤ R) :
    ‖X+Complex.I • Y‖ ≤ 2*R := by
  have hh := norm_add_le X (Complex.I • Y)
  rw [norm_smul,Complex.norm_I,one_mul] at hh
  linarith

theorem complex_left_norm (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    {C X : Matrix ι ι ℂ} {S Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    {γ r b : ℝ} (hγ : 0 < γ) (hr : 0 ≤ r) (hb : 0 ≤ b)
    (hfloor : γ • (1 : Matrix ι ι ℂ) ≤ C) (hx : ‖X‖ ≤ r)
    (hy : (-b) • S ≤ Y ∧ Y ≤ b • S)
    (W : Matrix m n ℂ) (hW : W*source A C S*Wᴴ=1) :
    ‖compressed A W X Y‖ ≤ 2*(r/γ)*b := by
  have hrp := realPart_norm_le X |>.trans hx
  have hip := imagPart_norm_le X |>.trans hx
  have h1 := hermitian_source_norm A hA (realPart_isHermitian X) hY (div_nonneg hr hγ.le) hb
    (relative_order_of_floor (realPart_isHermitian X) hγ hr hfloor hrp) hy W hW
  have h2 := hermitian_source_norm A hA (imagPart_isHermitian X) hY (div_nonneg hr hγ.le) hb
    (relative_order_of_floor (imagPart_isHermitian X) hγ hr hfloor hip) hy W hW
  have he : compressed A W X Y = compressed A W (realPart X) Y+Complex.I • compressed A W (imagPart X) Y := by
    rw [←compressed_smul_left,←compressed_add_left,parts_sum]
  rw [he]
  exact (norm_add_I_le h1 h2).trans_eq (by ring)

theorem complex_right_norm (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    {C X : Matrix ι ι ℂ} {S Y : Matrix n n ℂ} (hX : X.IsHermitian)
    {μ r a : ℝ} (hμ : 0 < μ) (hr : 0 ≤ r) (ha : 0 ≤ a)
    (hx : (-a) • C ≤ X ∧ X ≤ a • C)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ S) (hy : ‖Y‖ ≤ r)
    (W : Matrix m n ℂ) (hW : W*source A C S*Wᴴ=1) :
    ‖compressed A W X Y‖ ≤ 2*a*(r/μ) := by
  have hrp := realPart_norm_le Y |>.trans hy
  have hip := imagPart_norm_le Y |>.trans hy
  have h1 := hermitian_source_norm A hA hX (realPart_isHermitian Y) ha (div_nonneg hr hμ.le)
    hx (relative_order_of_floor (realPart_isHermitian Y) hμ hr hfloor hrp) W hW
  have h2 := hermitian_source_norm A hA hX (imagPart_isHermitian Y) ha (div_nonneg hr hμ.le)
    hx (relative_order_of_floor (imagPart_isHermitian Y) hμ hr hfloor hip) W hW
  have he : compressed A W X Y = compressed A W X (realPart Y)+Complex.I • compressed A W X (imagPart Y) := by
    rw [←compressed_smul_right,←compressed_add_right,parts_sum]
  rw [he]
  exact (norm_add_I_le h1 h2).trans_eq (by ring)

/-- A complex perturbation in each argument costs four real-Hermitian components. -/
theorem complex_mixed_norm (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    {C X : Matrix ι ι ℂ} {S Y : Matrix n n ℂ} {γ μ r t : ℝ}
    (hγ : 0 < γ) (hμ : 0 < μ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hC : γ • (1 : Matrix ι ι ℂ) ≤ C) (hS : μ • (1 : Matrix n n ℂ) ≤ S)
    (hx : ‖X‖ ≤ r) (hy : ‖Y‖ ≤ t)
    (W : Matrix m n ℂ) (hW : W*source A C S*Wᴴ=1) :
    ‖compressed A W X Y‖ ≤ 4*(r/γ)*(t/μ) := by
  have hrp := realPart_norm_le Y |>.trans hy
  have hip := imagPart_norm_le Y |>.trans hy
  have h1 := complex_left_norm A hA (realPart_isHermitian Y) hγ hr (div_nonneg ht hμ.le) hC hx
    (relative_order_of_floor (realPart_isHermitian Y) hμ ht hS hrp) W hW
  have h2 := complex_left_norm A hA (imagPart_isHermitian Y) hγ hr (div_nonneg ht hμ.le) hC hx
    (relative_order_of_floor (imagPart_isHermitian Y) hμ ht hS hip) W hW
  have he : compressed A W X Y = compressed A W X (realPart Y)+Complex.I • compressed A W X (imagPart Y) := by
    rw [←compressed_smul_right,←compressed_add_right,parts_sum]
  rw [he]
  exact (norm_add_I_le h1 h2).trans_eq (by ring)

/-- The actual joint source perturbation is bounded without a source eigenvalue. -/
theorem relative_source_norm (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    {C X : Matrix ι ι ℂ} {S Y : Matrix n n ℂ} {γ μ r t : ℝ}
    (hγ : 0 < γ) (hμ : 0 < μ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hC : γ • (1 : Matrix ι ι ℂ) ≤ C) (hS : μ • (1 : Matrix n n ℂ) ≤ S)
    (hx : ‖X‖ ≤ r) (hy : ‖Y‖ ≤ t)
    (W : Matrix m n ℂ) (hW : W*source A C S*Wᴴ=1) :
    ‖W*source A (C+X) (S+Y)*Wᴴ-1‖ ≤ 2*(r/γ)+2*(t/μ)+4*(r/γ)*(t/μ) := by
  have hCp : C.PosSemidef := by
    have hh := (Matrix.PosDef.one.smul hγ).add_posSemidef (Matrix.le_iff.mp hC)
    exact (show C.PosDef by simpa only [add_sub_cancel] using hh).posSemidef
  have hSp : S.PosSemidef := by
    have hh := (Matrix.PosDef.one.smul hμ).add_posSemidef (Matrix.le_iff.mp hS)
    exact (show S.PosDef by simpa only [add_sub_cancel] using hh).posSemidef
  have h1 := complex_left_norm A hA hSp.isHermitian hγ hr zero_le_one hC hx
    (show (-1:ℝ) • S ≤ S ∧ S ≤ (1:ℝ) • S by
      simp only [neg_smul,one_smul]; exact ⟨neg_le_self hSp.nonneg,le_rfl⟩) W hW
  have h2 := complex_right_norm A hA hCp.isHermitian hμ ht zero_le_one
    (show (-1:ℝ) • C ≤ C ∧ C ≤ (1:ℝ) • C by
      simp only [neg_smul,one_smul]; exact ⟨neg_le_self hCp.nonneg,le_rfl⟩) hS hy W hW
  have h3 := complex_mixed_norm A hA hγ hμ hr ht hC hS hx hy W hW
  have he : W*source A (C+X) (S+Y)*Wᴴ-1 =
      compressed A W X S+compressed A W C Y+compressed A W X Y := by
    change compressed A W (C+X) (S+Y)-1 = _
    rw [compressed_add_left,compressed_add_right,compressed_add_right]
    change W*source A C S*Wᴴ+_+(_+_)-1 = _
    rw [hW]
    abel
  rw [he]
  have hh := (norm_add_le (compressed A W X S+compressed A W C Y) (compressed A W X Y)).trans
    (add_le_add_right (norm_add_le _ _) _)
  linarith

end MatrixSpencer.MSManuscriptComplexSourcePerturbation

