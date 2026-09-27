import HigherRankKS.CubePotential
import HigherRankKS.SourceBudget
import HigherRankKS.Parameters

/-! The complete initial-potential bound for the actual matrix family. -/

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

theorem cubePotential_zero_le_reserve
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    cubePotential A β θ 0 ≤
      2 * Real.sqrt (2 * SourceProfile.owner β 0 * ε * (r : ℝ) ^ β) +
      2 * θ * Real.sqrt (Fintype.card (n ⊕ n) : ℝ) := by
  have hc : 0 ≤ SourceProfile.owner β 0 :=
    (SourceProfile.owner_pos hβ (by constructor <;> norm_num)).le
  have hzero : signedLift (KSPotentialModels.center A 0) = 0 := by
    simp [KSPotentialModels.center, signedLift]
  unfold cubePotential
  simp only [hzero, Pi.zero_apply]
  exact potential_zero_le_source_budget A hβ.le hβ1.le (fun _ => hc) hθ
    (fun _ hS => source_trace_le A hA hsum hε hN hr hβ hβ1 hc
      (fun _ => le_rfl) hS)

theorem cubePotential_zero_le_seventy_five
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r q : ℕ} (hr : 1 ≤ r) (hrank : ∀ i, (A i).rank ≤ r)
    (hq : 2 ≤ q) (hqlog : logRank r ≤ q)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    cubePotential A ((1 : ℝ) / q) θ 0 ≤
      75 * q * Real.sqrt ε + 2 * θ * Real.sqrt (Fintype.card (n ⊕ n) : ℝ) := by
  have hb := reciprocal_scale_bounds hq
  exact (cubePotential_zero_le_reserve A hA hsum hε hN hrank hb.1
    (by linarith [hb.2]) hθ).trans
      (add_le_add_right (initial_reserve_le_seventy_five hr hq hqlog hε) _)

theorem cubePotential_zero_le_logarithmic
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r q : ℕ} (hr : 1 ≤ r) (hrank : ∀ i, (A i).rank ≤ r)
    (hq : 2 ≤ q) (hqlog : logRank r ≤ q)
    (hqupper : (q : ℝ) ≤ 2 * logRank r)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    cubePotential A ((1 : ℝ) / q) θ 0 ≤
      250 * Real.sqrt ε * Real.log (2 * (r : ℝ)) +
        2 * θ * Real.sqrt (Fintype.card (n ⊕ n) : ℝ) := by
  exact (cubePotential_zero_le_seventy_five A hA hsum hε hN hr hrank hq hqlog hθ).trans
    (add_le_add_right (discrepancy_constant_conversion hr hqupper ε) _)

end HigherRankKS
