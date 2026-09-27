import MatrixSpencer.KSComplexSpinDomain

/-!
# Operator-norm and dimension bounds for the fixed complex source compression

Rectangular isometries contract arbitrary complex matrices. The concrete
Pauli source frame therefore contracts both density and source norms, and
its dimension is bounded by the physical dimension. Empty supports and
empty physical spaces are included.
-/

open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSComplexCompressionBounds
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq n] in
/-- Every rectangular isometry is an operator-norm contraction, including empty domains. -/
theorem isometry_norm_le_one (V : Matrix n m ℂ) (hV : Vᴴ*V=1) : ‖V‖ ≤ 1 := by
  have he := Matrix.l2_opNorm_conjTranspose_mul_self V
  rw [hV] at he
  have hi : ‖(1 : Matrix m m ℂ)‖ ≤ 1 := by
    rcases isEmpty_or_nonempty m with hm | hm
    · have he0 : (1 : Matrix m m ℂ) = 0 := Subsingleton.elim _ _
      rw [he0, norm_zero]
      norm_num
    · rw [norm_one]
  nlinarith [norm_nonneg V]

/-- Compression contracts arbitrary complex matrices; no Hermitian hypothesis is used. -/
theorem compression_norm_le (V : Matrix n m ℂ) (hV : Vᴴ*V=1) (A : Matrix n n ℂ) :
    ‖Vᴴ*A*V‖ ≤ ‖A‖ := by
  have hv := isometry_norm_le_one V hV
  have hvs : ‖Vᴴ‖ ≤ 1 := by simpa only [Matrix.l2_opNorm_conjTranspose] using hv
  calc
    ‖Vᴴ*A*V‖ ≤ ‖Vᴴ*A‖ * ‖V‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Vᴴ‖*‖A‖)*‖V‖ := mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1*‖A‖)*1 := by gcongr
    _ = ‖A‖ := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem spin_embedding_norm_le_one (A : ι → Matrix n n ℂ) :
    ‖KSSpinCompression.embedding A‖ ≤ 1 :=
  isometry_norm_le_one _ (KSSpinCompression.embedding_isometry A)

theorem spin_compression_norm_le (A : ι → Matrix n n ℂ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    ‖KSSupportSymmetry.compress (KSSpinCompression.embedding A) S‖ ≤ ‖S‖ :=
  compression_norm_le _ (KSSpinCompression.embedding_isometry A) S

omit [DecidableEq ι] in
/-- The fixed source support has at most the physical doubled dimension. -/
theorem support_card_le (A : ι → Matrix n n ℂ) :
    Fintype.card (KSSpinCompression.supportIndex A) ≤ Fintype.card (n ⊕ n) := by
  simpa only [KSSpinCompression.supportIndex, Fintype.card_fin, Module.finrank_pi,
    Module.finrank_self, mul_one, finrank_euclideanSpace] using Submodule.finrank_le (krausSupport (KSSpinSource.family A))

theorem actual_frame_norm_le_one (v : ι → n → ℂ) : ‖KSComplexSpinDomain.frame v‖ ≤ 1 :=
  spin_embedding_norm_le_one _

theorem actual_compressedDensity_norm_le (v : ι → n → ℂ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    ‖KSComplexSpinDomain.compressedDensity v S‖ ≤ ‖S‖ :=
  spin_compression_norm_le _ S

theorem actual_compressedSource_norm_le (v : ι → n → ℂ) (x h : ι → ℝ)
    (p : KSComplexSpinSource.Space n) :
    ‖KSComplexSpinDomain.compressedSource v x h p‖ ≤ ‖KSComplexSpinSource.source v x h p‖ :=
  spin_compression_norm_le _ _

omit [DecidableEq ι] in
theorem actual_support_card_le (v : ι → n → ℂ) :
    Fintype.card (KSComplexSpinDomain.Support v) ≤ Fintype.card (n ⊕ n) :=
  support_card_le _

end MatrixSpencer.KSComplexCompressionBounds
