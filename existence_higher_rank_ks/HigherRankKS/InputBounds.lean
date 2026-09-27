import MatrixSpencer.KSPotentialModels

/-! Positivity gives a unit discrepancy bound for every point of the cube. -/

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

theorem center_order_bounds (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    -(1 : Matrix n n ℂ) ≤ KSPotentialModels.center A x ∧
      KSPotentialModels.center A x ≤ 1 := by
  constructor
  · calc
      -(1 : Matrix n n ℂ) ≤ -(∑ i, A i) := neg_le_neg hsum
      _ = ∑ i, (-1 : ℝ) • A i := by simp
      _ ≤ KSPotentialModels.center A x :=
        Finset.sum_le_sum (fun i _ => smul_le_smul_of_nonneg_right (hx.1 i) (hA i).nonneg)
  · calc
      KSPotentialModels.center A x ≤ ∑ i, (1 : ℝ) • A i :=
        Finset.sum_le_sum (fun i _ => smul_le_smul_of_nonneg_right (hx.2 i) (hA i).nonneg)
      _ = ∑ i, A i := by simp
      _ ≤ 1 := hsum

theorem center_norm_le_one [Nonempty n] (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    ‖KSPotentialModels.center A x‖ ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := center_order_bounds A hA hsum hx
  exact hermitian_norm_le_of_order
    (KSPotentialModels.center_isHermitian A (fun i => (hA i).isHermitian) x)
    (by simpa using hlo) (by simpa using hhi)

theorem real_signing_mem_cube {x : Fin N → ℝ}
    (hx : ∀ i, x i = 1 ∨ x i = -1) : x ∈ ksCube 1 := by
  constructor <;> intro i <;> rcases hx i with h | h <;> rw [h] <;> norm_num

end HigherRankKS
