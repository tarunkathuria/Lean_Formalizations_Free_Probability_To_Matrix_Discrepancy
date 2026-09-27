import MatrixSpencer.KrausReducedFamily
import MatrixSpencer.BalancedBudgets
import MatrixSpencer.KrausContraction

/-!
# Original-label budgets after physical compression

The original contractions are compressed before covariance mixing. Their
count and the global Tsallis parameter are unchanged, including at zero rank.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer

variable {ι m n : Type*} [Fintype ι] [Fintype m] [Fintype n]
  [DecidableEq ι] [DecidableEq m] [DecidableEq n]

local instance compressedBudgetCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}

omit [Fintype ι] [DecidableEq ι] in
theorem isometry_projection_le_one (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) : V * Vᴴ ≤ 1 := by
  apply isHermitian_idempotent_le_one (Matrix.posSemidef_self_mul_conjTranspose V).isHermitian
  calc
    _ = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.mul_one]

omit [Fintype ι] [DecidableEq ι] in
theorem realTrace_isometry_compression_le {S : Matrix n n ℂ} (hS : S.PosSemidef)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) :
    realTrace (Vᴴ * S * V) ≤ realTrace S := by
  have h := realTrace_mul_mono hS (isometry_projection_le_one V hV)
  rw [Matrix.mul_one] at h
  have heq : realTrace (Vᴴ * S * V) = realTrace (S * (V * Vᴴ)) := by
    rw [realTrace_rectangular_mul_comm, realTrace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [heq]
  exact h

omit [Fintype ι] [DecidableEq ι] in
theorem isometry_compression_isHermitian (V : Matrix n m ℂ) {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : (Vᴴ * A * V).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hA.eq]
  simp only [Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
/-- Physical compression preserves each original Euclidean contraction bound. -/
theorem isometry_compression_norm_le_one (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (hN : ‖A‖ ≤ 1) : ‖Vᴴ * A * V‖ ≤ 1 := by
  have hu : A ≤ (1 : Matrix n n ℂ) := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self hA
    rw [Algebra.algebraMap_eq_smul_one] at h
    exact h.trans (by simpa only [one_smul] using smul_le_smul_of_nonneg_right hN (zero_le_one :
      (0 : Matrix n n ℂ) ≤ 1))
  have hn : -A ≤ (1 : Matrix n n ℂ) := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self hA.neg
    rw [Algebra.algebraMap_eq_smul_one, norm_neg] at h
    exact h.trans (by simpa only [one_smul] using smul_le_smul_of_nonneg_right hN (zero_le_one :
      (0 : Matrix n n ℂ) ≤ 1))
  have huc : Vᴴ * A * V ≤ (1 : Matrix m m ℂ) := by
    apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV] using
      (Matrix.le_iff.mp hu).conjTranspose_mul_mul_same V
  have hnc : -(Vᴴ * A * V) ≤ (1 : Matrix m m ℂ) := by
    apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV,
      Matrix.mul_neg, Matrix.neg_mul] using (Matrix.le_iff.mp hn).conjTranspose_mul_mul_same V
  apply KrausContraction.norm_le_of_order_interval (isometry_compression_isHermitian V hA)
    (by norm_num : (0 : ℝ) ≤ 1)
  · simpa only [neg_smul, one_smul] using (neg_le.mp hnc)
  · simpa only [one_smul] using huc

def compressedOriginalFamily (A : ι → Matrix n n ℂ) (V : Matrix n m ℂ) (a : ι) : Matrix m m ℂ :=
  Vᴴ * A a * V

/-- Covariance mixing commutes with the same fixed physical compression. -/
theorem covarianceKraus_compressedOriginalFamily (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (V : Matrix n m ℂ) (a : ι) :
    covarianceKraus (compressedOriginalFamily A V) C a = Vᴴ * covarianceKraus A C a * V := by
  simp only [covarianceKraus, mixedKraus, compressedOriginalFamily,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- The actual reduced Kraus family retains its original contraction realization and label count. -/
theorem krausReducedFamily_eq_covarianceKraus_compressed (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) :
    krausReducedFamily (covarianceKraus A C) =
      covarianceKraus (compressedOriginalFamily A (krausSupportEmbedding (covarianceKraus A C))) C := by
  funext a
  exact (covarianceKraus_compressedOriginalFamily A C _ a).symm

/-- Balanced trace budgets at a compressed density use the original count, not the support rank. -/
theorem compressed_balancedTransport_budgets (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {S : Matrix n n ℂ} (hS : S.PosDef) (htrace : realTrace S ≤ 1)
    (hM : (covarianceSource (compressedOriginalFamily A V) C (Vᴴ * S * V)).PosDef) :
    let S₀ := Vᴴ * S * V
    let Z₀ := transportOptimizer S₀ (covarianceSource (compressedOriginalFamily A V) C S₀)
    realTrace (balancedDensity S₀ Z₀) ≤ Real.sqrt (Fintype.card ι : ℝ) ∧
      realTrace (balancedRoot S₀ Z₀ * balancedRoot S₀ Z₀) ≤ (Fintype.card ι : ℝ) :=
  balancedTransport_covariance_budgets (compressedOriginalFamily A V)
    (fun i => isometry_compression_isHermitian V (hA i))
    (fun i => isometry_compression_norm_le_one V hV (hA i) (hN i)) hC0 hC1
    (posDef_isometry_compression V hV hS)
    ((realTrace_isometry_compression_le hS.posSemidef V hV).trans htrace) hM

end MatrixSpencer
