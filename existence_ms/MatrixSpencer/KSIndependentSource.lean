import MatrixSpencer.KSInitialBounds

/-! The  two independent sign-block sources and initial budget. -/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer.KSIndependentSource

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

def family (A : ι → Matrix n n ℂ) (j : ι × Bool) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  if j.2 then leftDensity (A j.1) else rightDensity (A j.1)

def coefficientCovariance (c : ι → ℝ) : Matrix (ι × Bool) (ι × Bool) ℝ :=
  Matrix.diagonal (fun j => c j.1)

theorem family_isHermitian (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (j : ι × Bool) : (family A j).IsHermitian := by
  rcases j with ⟨i, b⟩
  cases b
  · exact Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero (by simp) (hA i)
  · exact Matrix.IsHermitian.fromBlocks (hA i) (by simp) Matrix.isHermitian_zero

theorem coefficientCovariance_posSemidef {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    (coefficientCovariance c).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr (fun j => hc j.1)

theorem source_eq_sum (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    covarianceSource (family A) (coefficientCovariance c) X =
      ∑ i, c i • (rightDensity (A i) * X * rightDensity (A i) +
        leftDensity (A i) * X * leftDensity (A i)) := by
  simp only [covarianceSource, coefficientCovariance, Matrix.diagonal_apply,
    ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, family, Bool.false_eq_true, if_false, if_true, smul_add]
  apply Finset.sum_congr rfl
  intro i _
  exact add_comm _ _

theorem source_identity_constant (A : ι → Matrix n n ℂ) (u : ℝ) :
    covarianceSource (family A) (coefficientCovariance (fun _ => u)) 1 =
      u • KSSpinSource.doubled (∑ i, A i * A i) := by
  rw [source_eq_sum, KSSpinSource.doubled_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [leftDensity, rightDensity, KSSpinSource.doubled, Matrix.mul_one,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  ext a b
  cases a <;> cases b <;> simp [Matrix.fromBlocks, Matrix.add_apply]

theorem initial_variance_le (v : ι → n → ℂ)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1) {ε u : ℝ}
    (hε : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε) (hu : 0 ≤ u) :
    covarianceSource (family (fun i => KSRankOne.atom (v i)))
      (coefficientCovariance (fun _ => u)) 1 ≤ (u * ε) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  rw [source_identity_constant]
  have h := smul_le_smul_of_nonneg_left
    (KSSpinSource.doubled_mono (ks_parseval_square_sum_le v hparseval hε)) hu
  simpa only [KSSpinSource.doubled_smul, KSSpinSource.doubled_one, smul_smul] using h

theorem initial_bound [Nonempty n] (v : ι → n → ℂ)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1) {ε : ℝ} (hεpos : 0 < ε)
    (hε : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε) :
    ownerPotential 0 (family (fun i => KSRankOne.atom (v i)))
      (coefficientCovariance (fun _ => 64)) (ksRegularizerScale ε n) ≤ 18 * Real.sqrt ε := by
  have hb := ks_ownerPotential_le_variance Matrix.isHermitian_zero
    (family (fun i => KSRankOne.atom (v i)))
    (family_isHermitian _ (fun i => KSRankOne.atom_isHermitian _))
    (coefficientCovariance_posSemidef (fun _ => by norm_num))
    (ksRegularizerScale_pos (n := n) hεpos).le
    (initial_variance_le v hparseval hε (by norm_num : (0 : ℝ) ≤ 64))
  rw [norm_zero, zero_add, ksRegularizerScale_budget,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64)] at hb
  norm_num at hb
  linarith

end MatrixSpencer.KSIndependentSource
