import HigherRankKS.CarrierPower
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.Tactic

/-!
# Rank-sensitive trace budget for the carrier power

The finite scalar estimate is Jensen's inequality on the nonzero eigenvalues.
The rank in the resulting matrix estimate is the actual matrix rank.
-/

noncomputable section
open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace HigherRankKS

theorem sum_rpow_le_card_rpow_mul_sum_rpow {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∑ i ∈ s, (a i) ^ (1 - β) ≤
      (s.card : ℝ) ^ β * (∑ i ∈ s, a i) ^ (1 - β) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [Real.zero_rpow hβ.ne']
  have hn : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  have hsumnonneg : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
  have hsumw : ∑ _i ∈ s, (s.card : ℝ)⁻¹ = 1 := by simp [hn.ne']
  have hj := (Real.concaveOn_rpow (by linarith : 0 ≤ 1 - β) (by linarith : 1 - β ≤ 1)).le_map_sum
    (t := s) (w := fun _ => (s.card : ℝ)⁻¹) (p := a)
    (fun _ _ => inv_nonneg.mpr hn.le) hsumw ha
  simp only [smul_eq_mul, ← Finset.mul_sum] at hj
  have hj' := mul_le_mul_of_nonneg_left hj hn.le
  have hnexp : (s.card : ℝ) ^ (1 - β) * (s.card : ℝ) ^ β = (s.card : ℝ) := by
    rw [← Real.rpow_add hn]
    simp
  have hexp : (s.card : ℝ) * ((s.card : ℝ)⁻¹ * ∑ i ∈ s, a i) ^ (1 - β) =
      (s.card : ℝ) ^ β * (∑ i ∈ s, a i) ^ (1 - β) := by
    rw [Real.mul_rpow (inv_nonneg.mpr hn.le) hsumnonneg, Real.inv_rpow hn.le]
    have hpow : (s.card : ℝ) ^ (1 - β) ≠ 0 := (Real.rpow_pos_of_pos hn _).ne'
    calc
      (s.card : ℝ) * (((s.card : ℝ) ^ (1 - β))⁻¹ * (∑ i ∈ s, a i) ^ (1 - β)) =
          ((s.card : ℝ) ^ (1 - β) * (s.card : ℝ) ^ β) *
            (((s.card : ℝ) ^ (1 - β))⁻¹ * (∑ i ∈ s, a i) ^ (1 - β)) := by rw [hnexp]
      _ = _ := by field_simp
  rw [hexp] at hj'
  simpa [← mul_assoc, hn.ne'] using hj'

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance tracePowerCStar : CStarAlgebra (Matrix n n ℂ) := {}

theorem realTrace_cfc_eq_sum {M : Matrix n n ℂ} (hM : M.IsHermitian) (f : ℝ → ℝ) :
    realTrace (cfc f M) = ∑ i, f (hM.eigenvalues i) := by
  rw [hM.cfc_eq, Matrix.IsHermitian.cfc, realTrace_mul_cycle]
  simp only [unitary.star_mul_self_of_mem (SetLike.coe_mem _), one_mul]
  simp [realTrace, Matrix.trace_diagonal, Function.comp_def]

theorem realTrace_rpow_eq_sum {M : Matrix n n ℂ} (hM : M.PosSemidef) (α : ℝ) :
    realTrace (CFC.rpow M α) = ∑ i, (hM.isHermitian.eigenvalues i) ^ α := by
  rw [CFC.rpow, cfc_nnreal_eq_real _ _ hM.nonneg, realTrace_cfc_eq_sum hM.isHermitian]
  apply Finset.sum_congr rfl
  intro i hi
  simp [NNReal.coe_rpow, Real.toNNReal_of_nonneg (hM.eigenvalues_nonneg i)]

/-- The real-power trace estimate uses only the nonzero eigenvalues. -/
theorem realTrace_rpow_le_rank_rpow_mul_trace_rpow {M : Matrix n n ℂ}
    (hM : M.PosSemidef) {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    realTrace (CFC.rpow M (1 - β)) ≤
      (M.rank : ℝ) ^ β * (realTrace M) ^ (1 - β) := by
  classical
  let s : Finset n := Finset.univ.filter fun i => hM.isHermitian.eigenvalues i ≠ 0
  have hcard : s.card = M.rank := by
    simpa [s, Fintype.card_subtype] using hM.isHermitian.rank_eq_card_non_zero_eigs.symm
  have hsum : ∑ i ∈ s, hM.isHermitian.eigenvalues i = realTrace M := by
    rw [realTrace_eq_sum_eigenvalues hM.isHermitian]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    have hz : hM.isHermitian.eigenvalues i = 0 := by simpa [s] using hnot
    exact hz
  have hsumPow : ∑ i ∈ s, (hM.isHermitian.eigenvalues i) ^ (1 - β) =
      realTrace (CFC.rpow M (1 - β)) := by
    rw [realTrace_rpow_eq_sum hM]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    have hz : hM.isHermitian.eigenvalues i = 0 := by simpa [s] using hnot
    simp [hz, Real.zero_rpow (by linarith : 1 - β ≠ 0)]
  have h := sum_rpow_le_card_rpow_mul_sum_rpow s hM.isHermitian.eigenvalues hβ hβ1
    (fun i _ => hM.eigenvalues_nonneg i)
  simpa only [hsumPow, hcard, hsum] using h

/-- The nonlinear carrier pays the beta power of its actual rank. -/
theorem realTrace_carrierPower_le_rank {M : Matrix n n ℂ} (hM : M.PosSemidef)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    realTrace (carrierPower β M) ≤ (M.rank : ℝ) ^ β * realTrace M := by
  rw [carrierPower, realTrace_smul]
  calc
    (realTrace M) ^ β * realTrace (CFC.rpow M (1 - β)) ≤
        (realTrace M) ^ β * ((M.rank : ℝ) ^ β * (realTrace M) ^ (1 - β)) :=
      mul_le_mul_of_nonneg_left (realTrace_rpow_le_rank_rpow_mul_trace_rpow hM hβ hβ1)
        (Real.rpow_nonneg (realTrace_nonneg hM) β)
    _ = (M.rank : ℝ) ^ β * ((realTrace M) ^ β * (realTrace M) ^ (1 - β)) := by ring
    _ = (M.rank : ℝ) ^ β * realTrace M := by
      rw [← Real.rpow_add_of_nonneg (realTrace_nonneg hM) hβ.le (by linarith)]
      simp


theorem realTrace_carrierPower_le {M : Matrix n n ℂ} (hM : M.PosSemidef)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {r : ℕ} (hr : M.rank ≤ r) :
    realTrace (carrierPower β M) ≤ (r : ℝ) ^ β * realTrace M := by
  apply (realTrace_carrierPower_le_rank hM hβ hβ1).trans
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hr) hβ.le)
    (realTrace_nonneg hM)

end HigherRankKS
