import HigherRankKS.Potential
import HigherRankKS.TracePower
import MatrixSpencer.OwnerBounds

/-!
# The initial source budget

Only the rank-sensitive trace inequality sees the rank of an atom.
The remaining bounds use its operator norm and the subisotropy of the
original family.
-/

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance sourceBudgetCStar : CStarAlgebra (Matrix n n ℂ) := {}

omit [DecidableEq n] in
theorem realTrace_marginal (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    realTrace (marginal S) = realTrace S := by
  simp [realTrace, marginal, Matrix.trace, Matrix.diag, Fintype.sum_sum_type,
    Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Finset.sum_add_distrib]

theorem realTrace_carrier {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    realTrace (carrier A S) = realTrace (A * marginal S) := by
  rw [carrier, realTrace_mul_cycle, CFC.sqrt_mul_sqrt_self A hA.nonneg]

theorem rank_sqrt_eq {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (CFC.sqrt A).rank = A.rank := by
  have h := Matrix.rank_conjTranspose_mul_self (CFC.sqrt A)
  rw [(CFC.sqrt_nonneg A).posSemidef.isHermitian.eq,
    CFC.sqrt_mul_sqrt_self A hA.nonneg] at h
  exact h.symm

theorem carrier_rank_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    (carrier A S).rank ≤ A.rank := by
  unfold carrier
  exact (Matrix.rank_mul_le_right _ _).trans_eq (rank_sqrt_eq hA)

theorem realTrace_sourceTerm (β : ℝ) (A : Matrix n n ℂ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    realTrace (sourceTerm β A S) = 2 * realTrace (sourceBlock β A S) := by
  simp [sourceTerm, realTrace, Matrix.trace, Matrix.diag, Fintype.sum_sum_type,
    two_mul]

theorem sourceBlock_trace_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 ≤ ε) (hN : ‖A‖ ≤ ε)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {r : ℕ} (hr : A.rank ≤ r) :
    realTrace (sourceBlock β A S) ≤
      ε * ((r : ℝ) ^ β * realTrace (carrier A S)) := by
  have horder : A ≤ ε • (1 : Matrix n n ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CStarAlgebra.norm_le_iff_le_algebraMap A hε hA.nonneg).mp hN
  have hmono := realTrace_mul_mono
    (carrierPower_posSemidef β (carrier_posSemidef A hS)) horder
  rw [Matrix.mul_smul, Matrix.mul_one, realTrace_smul] at hmono
  calc
    realTrace (sourceBlock β A S) =
        realTrace (carrierPower β (carrier A S) * A) := by
      rw [sourceBlock, realTrace_mul_cycle,
        CFC.sqrt_mul_sqrt_self A hA.nonneg, realTrace_mul_comm]
    _ ≤ ε * realTrace (carrierPower β (carrier A S)) := hmono
    _ ≤ ε * ((r : ℝ) ^ β * realTrace (carrier A S)) :=
      mul_le_mul_of_nonneg_left
        (realTrace_carrierPower_le (carrier_posSemidef A hS) hβ hβ1
          ((carrier_rank_le hA S).trans hr)) hε

theorem sum_carrier_trace_le_one (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S ∈ densitySet) :
    ∑ i, realTrace (carrier (A i) S) ≤ 1 := by
  have h := realTrace_mul_mono (marginal_posSemidef hS.1) hsum
  rw [Matrix.mul_one, realTrace_marginal, hS.2] at h
  simpa only [realTrace_carrier (hA _), Matrix.mul_sum, realTrace_sum,
    realTrace_mul_comm] using h

theorem source_trace_le (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {c : ι → ℝ}
    {L : ℝ} (hL : 0 ≤ L) (hcap : ∀ i, c i ≤ L)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S ∈ densitySet) :
    realTrace (source A β c S) ≤ 2 * L * ε * (r : ℝ) ^ β := by
  have hp : 0 ≤ (r : ℝ) ^ β := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    realTrace (source A β c S) =
        ∑ i, c i * (2 * realTrace (sourceBlock β (A i) S)) := by
      simp [source, realTrace_sourceTerm]
    _ ≤ ∑ i, L * (2 * (ε * ((r : ℝ) ^ β * realTrace (carrier (A i) S)))) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul (hcap i)
        (mul_le_mul_of_nonneg_left
          (sourceBlock_trace_le (hA i) hε (hN i) hS.1 hβ hβ1 (hr i)) (by norm_num))
        (mul_nonneg (by norm_num)
          (realTrace_nonneg (sourceBlock_posSemidef β (A i) hS.1))) hL
    _ = (2 * L * ε * (r : ℝ) ^ β) * ∑ i, realTrace (carrier (A i) S) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (2 * L * ε * (r : ℝ) ^ β) * 1 :=
      mul_le_mul_of_nonneg_left (sum_carrier_trace_le_one A hA hsum hS) (by positivity)
    _ = 2 * L * ε * (r : ℝ) ^ β := mul_one _

theorem potential_zero_le_source_budget [Nonempty n]
    (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {B θ : ℝ} (hθ : 0 ≤ θ)
    (hbudget : ∀ S ∈ densitySet, realTrace (source A β c S) ≤ B) :
    potential 0 A β c θ ≤ 2 * Real.sqrt B +
      2 * θ * Real.sqrt (Fintype.card (n ⊕ n) : ℝ) := by
  obtain ⟨S, hS, hmax⟩ := exists_optimizer 0 A hβ hβ1 hc θ
  rw [potential_eq_of_optimizer 0 A β c θ hS hmax]
  have hf := fidelity_le_sqrt_trace_mul hS.1 (source_posSemidef A β hc hS.1)
  rw [hS.2, one_mul] at hf
  have hf' := hf.trans (Real.sqrt_le_sqrt (hbudget S hS))
  have hr := mul_le_mul_of_nonneg_left (density_trace_sqrt_le_sqrt_card hS)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ)
  simp only [objective, Matrix.zero_mul, realTrace_zero, zero_add]
  linarith

end HigherRankKS
