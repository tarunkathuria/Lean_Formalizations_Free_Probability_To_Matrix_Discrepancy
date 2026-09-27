import MatrixSpencer.KSIndependentSource
import MatrixSpencer.KSBalancedSpin

/-! Block algebra for the  independent sign channels. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace MatrixSpencer.KSEighthBlocks

variable {ι n m k : Type*} [Fintype ι] [Fintype n] [Fintype m] [Fintype k]
  [DecidableEq ι] [DecidableEq n] [DecidableEq m] [DecidableEq k]

def blockDiag (A : Matrix n n ℂ) (B : Matrix m m ℂ) : Matrix (n ⊕ m) (n ⊕ m) ℂ :=
  Matrix.fromBlocks A 0 0 B

@[simp] theorem blockDiag_toBlocks11 (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    (blockDiag A B).toBlocks₁₁ = A := rfl

@[simp] theorem blockDiag_toBlocks22 (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    (blockDiag A B).toBlocks₂₂ = B := rfl

theorem blockDiag_isHermitian {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (blockDiag A B).IsHermitian :=
  Matrix.IsHermitian.fromBlocks hA (by simp) hB

theorem blockDiag_mul (A C : Matrix n n ℂ) (B D : Matrix m m ℂ) :
    blockDiag A B * blockDiag C D = blockDiag (A * C) (B * D) := by
  simp only [blockDiag, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add]

theorem blockDiag_add (A C : Matrix n n ℂ) (B D : Matrix m m ℂ) :
    blockDiag A B + blockDiag C D = blockDiag (A + C) (B + D) := by
  ext i j
  cases i <;> cases j <;> simp [blockDiag, Matrix.add_apply]

theorem blockDiag_sub (A C : Matrix n n ℂ) (B D : Matrix m m ℂ) :
    blockDiag A B - blockDiag C D = blockDiag (A - C) (B - D) := by
  ext i j
  cases i <;> cases j <;> simp [blockDiag, Matrix.sub_apply]

theorem blockDiag_smul (a : ℝ) (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    a • blockDiag A B = blockDiag (a • A) (a • B) := by
  ext i j
  cases i <;> cases j <;> simp [blockDiag, Matrix.smul_apply]

theorem blockDiag_sum (A : ι → Matrix n n ℂ) (B : ι → Matrix m m ℂ) :
    (∑ i, blockDiag (A i) (B i)) = blockDiag (∑ i, A i) (∑ i, B i) := by
  ext i j
  cases i <;> cases j <;> simp [blockDiag, Matrix.sum_apply]

theorem blockDiag_quadratic (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (x : n → ℂ) (y : m → ℂ) :
    star (Sum.elim x y) ⬝ᵥ (blockDiag A B *ᵥ Sum.elim x y) =
      star x ⬝ᵥ (A *ᵥ x) + star y ⬝ᵥ (B *ᵥ y) := by
  simp [blockDiag, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem blockDiag_posDef {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.PosDef) (hB : B.PosDef) : (blockDiag A B).PosDef := by
  refine ⟨blockDiag_isHermitian hA.isHermitian hB.isHermitian, fun x hx => ?_⟩
  rw [← Sum.elim_comp_inl_inr x, blockDiag_quadratic]
  by_cases hl : x ∘ Sum.inl = 0
  · have hr : x ∘ Sum.inr ≠ 0 := by
      intro hr
      apply hx
      rw [← Sum.elim_comp_inl_inr x, hl, hr]
      funext i
      cases i <;> rfl
    exact add_pos_of_nonneg_of_pos (hA.posSemidef.2 _) (hB.2 _ hr)
  · exact add_pos_of_pos_of_nonneg (hA.2 _ hl) (hB.posSemidef.2 _)

theorem principal_left_quadratic (X : Matrix (n ⊕ m) (n ⊕ m) ℂ) (x : n → ℂ) :
    star (Sum.elim x (0 : m → ℂ)) ⬝ᵥ (X *ᵥ Sum.elim x (0 : m → ℂ)) =
      star x ⬝ᵥ (X.toBlocks₁₁ *ᵥ x) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁]

theorem principal_right_quadratic (X : Matrix (n ⊕ m) (n ⊕ m) ℂ) (x : m → ℂ) :
    star (Sum.elim (0 : n → ℂ) x) ⬝ᵥ (X *ᵥ Sum.elim (0 : n → ℂ) x) =
      star x ⬝ᵥ (X.toBlocks₂₂ *ᵥ x) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₂]

theorem posDef_toBlocks11 {X : Matrix (n ⊕ m) (n ⊕ m) ℂ} (hX : X.PosDef) :
    X.toBlocks₁₁.PosDef := by
  refine ⟨hX.isHermitian.submatrix Sum.inl, fun x hx => ?_⟩
  rw [← principal_left_quadratic]
  apply hX.2
  intro he
  apply hx
  funext i
  exact congrFun he (Sum.inl i)

theorem posDef_toBlocks22 {X : Matrix (n ⊕ m) (n ⊕ m) ℂ} (hX : X.PosDef) :
    X.toBlocks₂₂.PosDef := by
  refine ⟨hX.isHermitian.submatrix Sum.inr, fun x hx => ?_⟩
  rw [← principal_right_quadratic]
  apply hX.2
  intro he
  apply hx
  funext i
  exact congrFun he (Sum.inr i)

def doubledRect (V : Matrix n m ℂ) : Matrix (n ⊕ n) (m ⊕ m) ℂ :=
  Matrix.fromBlocks V 0 0 V

theorem doubledRect_isometry {V : Matrix n m ℂ} (hV : Vᴴ * V = 1) :
    (doubledRect V)ᴴ * doubledRect V = 1 := by
  simp only [doubledRect, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    hV, Matrix.fromBlocks_one]

theorem blockDiag_inv {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    (blockDiag A B)⁻¹ = blockDiag A⁻¹ B⁻¹ := by
  letI : Invertible A := hA.isUnit.invertible
  letI : Invertible B := hB.isUnit.invertible
  apply Matrix.inv_eq_right_inv
  rw [blockDiag_mul, Matrix.mul_inv_of_invertible, Matrix.mul_inv_of_invertible]
  exact Matrix.fromBlocks_one

theorem realTrace_blockDiag (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    realTrace (blockDiag A B) = realTrace A + realTrace B := by
  simp [realTrace, Matrix.trace, Matrix.diag, blockDiag, Matrix.fromBlocks,
    Fintype.sum_sum_type]

theorem realTrace_blockDiag_mul (A C : Matrix n n ℂ) (B D : Matrix m m ℂ) :
    realTrace (blockDiag A B * blockDiag C D) = realTrace (A * C) + realTrace (B * D) := by
  rw [blockDiag_mul, realTrace_blockDiag]

theorem realTrace_mul_blockDiag (S : Matrix (n ⊕ m) (n ⊕ m) ℂ)
    (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    realTrace (S * blockDiag A B) =
      realTrace (S.toBlocks₁₁ * A) + realTrace (S.toBlocks₂₂ * B) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks S]
  simp [blockDiag, Matrix.fromBlocks_multiply, realTrace, Matrix.trace, Matrix.diag,
    Fintype.sum_sum_type]

theorem doubledRect_congruence (V : Matrix n m ℂ) (A B : Matrix m m ℂ) :
    doubledRect V * blockDiag A B * (doubledRect V)ᴴ =
      blockDiag (V * A * Vᴴ) (V * B * Vᴴ) := by
  simp only [doubledRect, blockDiag, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem doubledRect_compression (V : Matrix n m ℂ)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    (doubledRect V)ᴴ * X * doubledRect V = Matrix.fromBlocks
      (Vᴴ * X.toBlocks₁₁ * V) (Vᴴ * X.toBlocks₁₂ * V)
      (Vᴴ * X.toBlocks₂₁ * V) (Vᴴ * X.toBlocks₂₂ * V) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks X]
  simp only [doubledRect, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem independent_source_blocks (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    covarianceSource (KSIndependentSource.family A) (KSIndependentSource.coefficientCovariance c) X =
      blockDiag (∑ i, c i • (A i * X.toBlocks₁₁ * A i))
        (∑ i, c i • (A i * X.toBlocks₂₂ * A i)) := by
  rw [KSIndependentSource.source_eq_sum]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks X]
  simp only [leftDensity, rightDensity, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, zero_add, add_zero]
  ext a b
  cases a <;> cases b <;>
    simp [blockDiag, Matrix.fromBlocks, Matrix.of_apply, Matrix.sum_apply,
      Matrix.add_apply, Matrix.smul_apply]

theorem independent_rankOne_source_blocks (v : ι → n → ℂ) (c : ι → ℝ)
    {X : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hX : X.IsHermitian) :
    covarianceSource (KSIndependentSource.family (fun i => KSRankOne.atom (v i)))
      (KSIndependentSource.coefficientCovariance c) X =
      blockDiag (KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) c X.toBlocks₁₁)
        (KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) c X.toBlocks₂₂) := by
  rw [independent_source_blocks]
  congr 1 <;> unfold KSBalancedSpin.source
  · apply Finset.sum_congr rfl
    intro i _
    have hh : X.toBlocks₁₁.IsHermitian := hX.submatrix Sum.inl
    rw [KSRankOne.atom_sandwich_real (v i) hh, smul_smul]
  · apply Finset.sum_congr rfl
    intro i _
    have hh : X.toBlocks₂₂.IsHermitian := hX.submatrix Sum.inr
    rw [KSRankOne.atom_sandwich_real (v i) hh, smul_smul]

theorem independent_weighted_sum (A : ι → Matrix n n ℂ) (w : ι × Bool → ℝ) :
    (∑ j, w j • KSIndependentSource.family A j) =
      blockDiag (∑ i, w (i, true) • A i) (∑ i, w (i, false) • A i) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, KSIndependentSource.family, Bool.false_eq_true,
    if_false, if_true]
  ext i j
  cases i <;> cases j <;>
    simp [blockDiag, leftDensity, rightDensity, Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply]

theorem realTrace_left_mul (A : Matrix n n ℂ) (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    realTrace (leftDensity A * X) = realTrace (A * X.toBlocks₁₁) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks X]
  simp [leftDensity, Matrix.fromBlocks_multiply, realTrace, Matrix.trace, Matrix.diag,
    Fintype.sum_sum_type]

theorem realTrace_right_mul (A : Matrix n n ℂ) (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    realTrace (rightDensity A * X) = realTrace (A * X.toBlocks₂₂) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks X]
  simp [rightDensity, Matrix.fromBlocks_multiply, realTrace, Matrix.trace, Matrix.diag,
    Fintype.sum_sum_type]

theorem realTrace_independent_mul (A : ι → Matrix n n ℂ)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) (j : ι × Bool) :
    realTrace (KSIndependentSource.family A j * X) =
      if j.2 then realTrace (A j.1 * X.toBlocks₁₁) else realTrace (A j.1 * X.toBlocks₂₂) := by
  rcases j with ⟨i, b⟩
  cases b <;> simp [KSIndependentSource.family, realTrace_left_mul, realTrace_right_mul]

theorem realTrace_mul_independent (A : ι → Matrix n n ℂ)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) (j : ι × Bool) :
    realTrace (X * KSIndependentSource.family A j) =
      if j.2 then realTrace (X.toBlocks₁₁ * A j.1) else realTrace (X.toBlocks₂₂ * A j.1) := by
  rw [realTrace_mul_comm, realTrace_independent_mul]
  split_ifs <;> apply realTrace_mul_comm

theorem independent_prepare_blocks (A : ι → Matrix n n ℂ) (c : ι × Bool → ℝ)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    KSBalancedSpin.source (KSIndependentSource.family A) c X =
      blockDiag (KSBalancedSpin.source A (fun i => c (i, true)) X.toBlocks₁₁)
        (KSBalancedSpin.source A (fun i => c (i, false)) X.toBlocks₂₂) := by
  simp only [KSBalancedSpin.source, independent_weighted_sum, realTrace_independent_mul,
    if_true, Bool.false_eq_true, if_false]

theorem physicalForce_blocks (A : ι → Matrix n n ℂ) (J₁ J₂ : Matrix n n ℂ)
    (u : ℝ) (x h q : ι × Bool → ℝ) :
    KSBalancedSpin.physicalForce (KSIndependentSource.family A) (blockDiag J₁ J₂) u x h q =
      blockDiag (KSBalancedSpin.physicalForce A J₁ u
        (fun i => x (i, true)) (fun i => h (i, true)) (fun i => q (i, true)))
        (KSBalancedSpin.physicalForce A J₂ u
        (fun i => x (i, false)) (fun i => h (i, false)) (fun i => q (i, false))) := by
  have hs : (∑ j, h j • (blockDiag J₁ J₂ * KSIndependentSource.family A j)) =
      blockDiag J₁ J₂ * (∑ j, h j • KSIndependentSource.family A j) := by
    simp only [Matrix.mul_sum, Matrix.mul_smul]
  unfold KSBalancedSpin.physicalForce
  rw [hs, independent_weighted_sum, independent_weighted_sum, blockDiag_mul, blockDiag_add]
  simp only [Matrix.mul_sum, Matrix.mul_smul]

theorem physicalAcceleration_blocks (A : ι → Matrix n n ℂ)
    {Z₁ Z₂ : Matrix n n ℂ} (hZ₁ : Z₁.PosDef) (hZ₂ : Z₂.PosDef)
    (U₁ U₂ : Matrix n n ℂ) (u : ℝ) (x h q : ι × Bool → ℝ) :
    KSBalancedSpin.physicalAcceleration (KSIndependentSource.family A)
      (blockDiag Z₁ Z₂) (blockDiag U₁ U₂) u x h q =
      blockDiag (KSBalancedSpin.physicalAcceleration A Z₁ U₁ u
        (fun i => x (i, true)) (fun i => h (i, true)) (fun i => q (i, true)))
        (KSBalancedSpin.physicalAcceleration A Z₂ U₂ u
        (fun i => x (i, false)) (fun i => h (i, false)) (fun i => q (i, false))) := by
  unfold KSBalancedSpin.physicalAcceleration
  rw [blockDiag_inv hZ₁ hZ₂]
  simp only [blockDiag_mul, blockDiag_smul, independent_weighted_sum,
    realTrace_independent_mul, if_true, Bool.false_eq_true, if_false,
    blockDiag_toBlocks11, blockDiag_toBlocks22]
  exact blockDiag_add _ _ _ _

theorem physical_velocity_blocks (A : ι → Matrix n n ℂ) (J₁ J₂ : Matrix n n ℂ)
    {Z₁ Z₂ : Matrix n n ℂ} (hZ₁ : Z₁.PosDef) (hZ₂ : Z₂.PosDef)
    (U₁ U₂ : Matrix n n ℂ) (u : ℝ) (c x h q : ι × Bool → ℝ) :
    KSBalancedSpin.physicalForce (KSIndependentSource.family A) (blockDiag J₁ J₂) u x h q -
      (blockDiag Z₁ Z₂)⁻¹ * blockDiag U₁ U₂ * (blockDiag Z₁ Z₂)⁻¹ +
      KSBalancedSpin.source (KSIndependentSource.family A) c (blockDiag U₁ U₂) =
      blockDiag
        (KSBalancedSpin.physicalForce A J₁ u
          (fun i => x (i, true)) (fun i => h (i, true)) (fun i => q (i, true)) -
          Z₁⁻¹ * U₁ * Z₁⁻¹ + KSBalancedSpin.source A (fun i => c (i, true)) U₁)
        (KSBalancedSpin.physicalForce A J₂ u
          (fun i => x (i, false)) (fun i => h (i, false)) (fun i => q (i, false)) -
          Z₂⁻¹ * U₂ * Z₂⁻¹ + KSBalancedSpin.source A (fun i => c (i, false)) U₂) := by
  rw [physicalForce_blocks, blockDiag_inv hZ₁ hZ₂, blockDiag_mul, blockDiag_mul,
    independent_prepare_blocks, blockDiag_toBlocks11, blockDiag_toBlocks22,
    blockDiag_sub, blockDiag_add]

theorem physical_acceleration_pairing_blocks (A : ι → Matrix n n ℂ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    {Z₁ Z₂ : Matrix n n ℂ} (hZ₁ : Z₁.PosDef) (hZ₂ : Z₂.PosDef)
    (U₁ U₂ : Matrix n n ℂ) (u : ℝ) (x h q : ι × Bool → ℝ) :
    realTrace (S * KSBalancedSpin.physicalAcceleration (KSIndependentSource.family A)
      (blockDiag Z₁ Z₂) (blockDiag U₁ U₂) u x h q) =
      realTrace (S.toBlocks₁₁ * KSBalancedSpin.physicalAcceleration A Z₁ U₁ u
        (fun i => x (i, true)) (fun i => h (i, true)) (fun i => q (i, true))) +
      realTrace (S.toBlocks₂₂ * KSBalancedSpin.physicalAcceleration A Z₂ U₂ u
        (fun i => x (i, false)) (fun i => h (i, false)) (fun i => q (i, false))) := by
  rw [physicalAcceleration_blocks A hZ₁ hZ₂, realTrace_mul_blockDiag]

end MatrixSpencer.KSEighthBlocks
