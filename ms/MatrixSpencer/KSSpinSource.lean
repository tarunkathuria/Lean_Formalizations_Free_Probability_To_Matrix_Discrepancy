import MatrixSpencer.KSRankOne
import MatrixSpencer.SignedLift



open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer.KSSpinSource

set_option maxHeartbeats 800000

variable {n : Type*} [Fintype n] [DecidableEq n]

def doubled (A : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks A 0 0 A

def pauli (A : Matrix n n ℂ) : Fin 4 → Matrix (n ⊕ n) (n ⊕ n) ℂ
  | 0 => doubled A
  | 1 => Matrix.fromBlocks 0 A A 0
  | 2 => Matrix.fromBlocks 0 (-Complex.I • A) (Complex.I • A) 0
  | 3 => signedLift A

theorem doubled_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (doubled A).IsHermitian := Matrix.IsHermitian.fromBlocks hA (by simp) hA

theorem doubled_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (doubled A).PosSemidef := posSemidef_fromBlocks_diagonal hA hA

theorem pauli_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) (a : Fin 4) :
    (pauli A a).IsHermitian := by
  fin_cases a
  · exact doubled_isHermitian hA
  · exact Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero hA.eq Matrix.isHermitian_zero
  · apply Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero _ Matrix.isHermitian_zero
    simp [Matrix.conjTranspose_smul, hA.eq]
  · exact signedLift_isHermitian hA

/-- The Pauli averaging identity before the rank-one specialization. -/
theorem pauli_average (A : Matrix n n ℂ) (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    (∑ a, pauli A a * X * pauli A a) =
      (2 : ℂ) • doubled (A * (X.toBlocks₁₁ + X.toBlocks₂₂) * A) := by
  rw [← Matrix.fromBlocks_toBlocks X]
  simp only [Fin.sum_univ_four, pauli, doubled, signedLift,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg,
    smul_smul, Matrix.fromBlocks_add, Matrix.fromBlocks_smul,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₂]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply,
      smul_eq_mul, Matrix.mul_add, Matrix.add_mul, Complex.I_mul_I] <;> ring

theorem doubled_trace_mul (A : Matrix n n ℂ)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    Matrix.trace (doubled A * X) = Matrix.trace (A * (X.toBlocks₁₁ + X.toBlocks₂₂)) := by
  rw [← Matrix.fromBlocks_toBlocks X]
  simp [doubled, Matrix.fromBlocks_multiply, Matrix.trace, Matrix.diag,
    Fintype.sum_sum_type, Matrix.mul_add, Finset.sum_add_distrib]

/-- The actual source identity on arbitrary complex doubled matrices. -/
theorem rankOne_pauli_average (v : n → ℂ)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    (∑ a, pauli (KSRankOne.atom v) a * X * pauli (KSRankOne.atom v) a) =
      (2 * Matrix.trace (doubled (KSRankOne.atom v) * X)) • doubled (KSRankOne.atom v) := by
  rw [pauli_average, KSRankOne.atom_sandwich, doubled_trace_mul]
  simp only [doubled, Matrix.fromBlocks_smul, smul_zero, smul_smul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def family (A : ι → Matrix n n ℂ) (j : ι × Fin 4) := pauli (A j.1) j.2

/-- The factor 1/2 is the square of the Kraus normalization 1/sqrt(2). -/
def coefficientCovariance (c : ι → ℝ) : Matrix (ι × Fin 4) (ι × Fin 4) ℝ :=
  Matrix.diagonal (fun j => c j.1 / 2)

theorem family_isHermitian (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (j : ι × Fin 4) :
    (family A j).IsHermitian := pauli_isHermitian (hA j.1) j.2

theorem coefficientCovariance_posSemidef {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    (coefficientCovariance c).PosSemidef :=
  Matrix.posSemidef_diagonal_iff.mpr (fun j => div_nonneg (hc j.1) (by norm_num))

theorem source_eq_pauli_sum (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    covarianceSource (family A) (coefficientCovariance c) X =
      ∑ i, (c i / 2) • (∑ a, pauli (A i) a * X * pauli (A i) a) := by
  simp only [covarianceSource, coefficientCovariance, Matrix.diagonal_apply,
    ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Fintype.sum_prod_type]
  simp only [family, Finset.smul_sum]


theorem source_eq_tracePrepare (v : ι → n → ℂ) (c : ι → ℝ)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    covarianceSource (family (fun i => KSRankOne.atom (v i))) (coefficientCovariance c) X =
      ∑ i, ((c i : ℂ) * Matrix.trace (doubled (KSRankOne.atom (v i)) * X)) •
        doubled (KSRankOne.atom (v i)) := by
  rw [source_eq_pauli_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [rankOne_pauli_average]
  ext a b
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_ofNat]
  ring

theorem source_eq_tracePrepare_real (v : ι → n → ℂ) (c : ι → ℝ)
    {X : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hX : X.IsHermitian) :
    covarianceSource (family (fun i => KSRankOne.atom (v i))) (coefficientCovariance c) X =
      ∑ i, (c i * realTrace (doubled (KSRankOne.atom (v i)) * X)) •
        doubled (KSRankOne.atom (v i)) := by
  rw [source_eq_tracePrepare]
  apply Finset.sum_congr rfl
  intro i _
  rw [KSRankOne.trace_mul_eq_realTrace (doubled_isHermitian (KSRankOne.atom_isHermitian _)) hX]
  simp only [← Complex.ofReal_mul]
  rfl

theorem source_identity (A : ι → Matrix n n ℂ) (c : ι → ℝ) :
    covarianceSource (family A) (coefficientCovariance c) 1 =
      ∑ i, (2 * c i) • doubled (A i * A i) := by
  rw [source_eq_pauli_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pauli_average]
  have h11 : (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ).toBlocks₁₁ = 1 := by
    ext a b
    simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  have h22 : (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ).toBlocks₂₂ = 1 := by
    ext a b
    simp [Matrix.toBlocks₂₂, Matrix.one_apply]
  simp only [h11, h22, Matrix.mul_add,
    Matrix.mul_one, Matrix.add_mul]
  ext a b
  cases a <;> cases b <;>
    simp [doubled, Matrix.fromBlocks, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul, Complex.ofReal_div] <;> ring

end MatrixSpencer.KSSpinSource
