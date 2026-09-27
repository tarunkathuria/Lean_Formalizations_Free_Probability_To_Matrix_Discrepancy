import MatrixSpencer.KSSpinSource
import MatrixSpencer.KSVarianceBounds

/-! The epsilon variance budgets and the two exact initial-potential constants. -/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

local instance ksInitialCStarAlgebra : CStarAlgebra (Matrix n n ℂ) := {}
local instance ksInitialDoubledCStarAlgebra : CStarAlgebra (Matrix (n ⊕ n) (n ⊕ n) ℂ) := {}

theorem ks_parseval_square_sum_le (v : ι → n → ℂ)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1) {ε : ℝ}
    (hε : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε) :
    (∑ i, KSRankOne.atom (v i) * KSRankOne.atom (v i)) ≤ ε • (1 : Matrix n n ℂ) := by
  calc
    _ = ∑ i, realTrace (KSRankOne.atom (v i)) • KSRankOne.atom (v i) := by
      simp only [KSRankOne.atom_sq_real]
    _ ≤ ∑ i, ε • KSRankOne.atom (v i) := by
      apply Finset.sum_le_sum
      intro i _
      apply smul_le_smul_of_nonneg_right
      · simpa only [KSRankOne.atom_norm] using hε i
      · exact (KSRankOne.atom_posSemidef _).nonneg
    _ = _ := by rw [← Finset.smul_sum, hparseval]

namespace KSSpinSource

theorem doubled_smul (r : ℝ) (A : Matrix n n ℂ) : doubled (r • A) = r • doubled A := by
  simp [doubled, Matrix.fromBlocks_smul]

theorem doubled_sum (A : ι → Matrix n n ℂ) : doubled (∑ i, A i) = ∑ i, doubled (A i) := by
  ext a b
  cases a <;> cases b <;> simp [doubled, Matrix.fromBlocks, Matrix.sum_apply]

theorem doubled_one : doubled (1 : Matrix n n ℂ) = 1 := by
  exact Matrix.fromBlocks_one

theorem doubled_mono {A B : Matrix n n ℂ} (h : A ≤ B) : doubled A ≤ doubled B :=
  fromBlocks_diagonal_mono h h

theorem source_identity_constant (A : ι → Matrix n n ℂ) (u : ℝ) :
    covarianceSource (family A) (coefficientCovariance (fun _ => u)) 1 =
      (2 * u) • doubled (∑ i, A i * A i) := by
  rw [source_identity, ← Finset.smul_sum, ← doubled_sum]

theorem initial_variance_le (v : ι → n → ℂ)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1) {ε u : ℝ}
    (hε : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε) (hu : 0 ≤ u) :
    covarianceSource (family (fun i => KSRankOne.atom (v i)))
      (coefficientCovariance (fun _ => u)) 1 ≤ (2 * u * ε) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  rw [source_identity_constant]
  have h := smul_le_smul_of_nonneg_left
    (doubled_mono (ks_parseval_square_sum_le v hparseval hε))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu)
  simpa only [doubled_smul, doubled_one, smul_smul] using h

end KSSpinSource

/-- The regularizer is fixed throughout both walks, including on lower-dimensional faces. -/
def ksRegularizerScale (ε : ℝ) (n : Type*) [Fintype n] : ℝ :=
  Real.sqrt ε / Real.sqrt (Fintype.card (n ⊕ n) : ℝ)

theorem ksRegularizerScale_pos [Nonempty n] {ε : ℝ} (hε : 0 < ε) :
    0 < ksRegularizerScale ε n := by
  unfold ksRegularizerScale
  exact div_pos (Real.sqrt_pos.mpr hε) (Real.sqrt_pos.mpr (by positivity))

theorem ksRegularizerScale_budget [Nonempty n] (ε : ℝ) :
    2 * ksRegularizerScale ε n * Real.sqrt (Fintype.card (n ⊕ n) : ℝ) = 2 * Real.sqrt ε := by
  have hD : Real.sqrt (Fintype.card (n ⊕ n) : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  unfold ksRegularizerScale
  field_simp

theorem ks_spin_initial_bound [Nonempty n] (v : ι → n → ℂ)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1) {ε : ℝ} (hεpos : 0 < ε)
    (hε : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε) :
    ownerPotential 0 (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance (fun _ => 64)) (ksRegularizerScale ε n) ≤
        (16 * Real.sqrt 2 + 2) * Real.sqrt ε := by
  have hb := ks_ownerPotential_le_variance Matrix.isHermitian_zero
    (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
    (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian _))
    (KSSpinSource.coefficientCovariance_posSemidef (fun _ => by norm_num))
    (ksRegularizerScale_pos (n := n) hεpos).le
    (KSSpinSource.initial_variance_le v hparseval hε (by norm_num : (0 : ℝ) ≤ 64))
  rw [norm_zero, zero_add, ksRegularizerScale_budget] at hb
  have hs : Real.sqrt (2 * 64 * ε) = 8 * Real.sqrt 2 * Real.sqrt ε := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 * 64)]
    congr 1
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have h0 := Real.sqrt_nonneg (2 : ℝ)
    have h128 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2 * 64)
    have h1280 := Real.sqrt_nonneg (2 * 64 : ℝ)
    nlinarith
  rw [hs] at hb
  nlinarith

end MatrixSpencer
