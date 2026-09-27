import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-! A finite geometric-epoch argument. The concrete matrix theorem supplies
its epoch and terminal-rounding lemmas; neither is a public input assumption. -/

noncomputable section
namespace AugmentedHigherRankKS

/-- Halving a mass reduces its square root by at least a factor `3/4`.
The rational factor leaves room for a clean finite geometric estimate. -/
theorem sqrt_half_budget {b b' : ℝ} (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hh : b' ≤ b / 2) : 4 * Real.sqrt b' ≤ 3 * Real.sqrt b := by
  have h1 := Real.sq_sqrt hb
  have h2 := Real.sq_sqrt hb'
  have h3 := Real.sqrt_nonneg b
  have h4 := Real.sqrt_nonneg b'
  nlinarith

/-- A terminal residual of mass at most `δ²` can be rounded within the
same square-root budget. -/
theorem terminal_rounding_budget {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (hsmall : b ≤ δ ^ 2) : 2 * b ≤ 4 * δ * Real.sqrt b := by
  have hs := Real.sqrt_nonneg b
  have hsq := Real.sq_sqrt hb
  have hsδ : Real.sqrt b ≤ δ := by nlinarith
  have hm := mul_nonneg hs (sub_nonneg.mpr hsδ)
  nlinarith

/-- Explicit finite completion from contracting epochs. The natural-number
rank prevents an infinite-time or limiting completion argument. -/
theorem finite_epoch_completion {X E : Type*} [NormedAddCommGroup E]
    (position : X → E) (mass : X → ℝ) (rank : X → ℕ) (terminal : X → Prop)
    {δ : ℝ} (hδ : 0 ≤ δ) (hmass : ∀ x, 0 ≤ mass x)
    (hfinish : ∀ x, mass x ≤ δ ^ 2 →
      ∃ z, terminal z ∧ ‖position z - position x‖ ≤ 2 * mass x)
    (hstep : ∀ x, δ ^ 2 < mass x → ∃ y,
      rank y < rank x ∧ mass y ≤ mass x / 2 ∧
      ‖position y - position x‖ ≤ δ * Real.sqrt (mass x)) :
    ∀ x, ∃ z, terminal z ∧
      ‖position z - position x‖ ≤ 4 * δ * Real.sqrt (mass x) := by
  intro x
  induction hn : rank x using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hs : mass x ≤ δ ^ 2
    · obtain ⟨z, hz, hzx⟩ := hfinish x hs
      exact ⟨z, hz, hzx.trans (terminal_rounding_budget hδ (hmass x) hs)⟩
    · obtain ⟨y, hry, hmy, hyx⟩ := hstep x (lt_of_not_ge hs)
      obtain ⟨z, hz, hzy⟩ := ih (rank y) (by simpa [hn] using hry) y rfl
      refine ⟨z, hz, ?_⟩
      have hhalf := sqrt_half_budget (hmass x) (hmass y) hmy
      have hmul := mul_le_mul_of_nonneg_left hhalf hδ
      calc
        ‖position z - position x‖ ≤ ‖position z - position y‖ +
            ‖position y - position x‖ := by
              simpa only [sub_add_sub_cancel] using
                norm_add_le (position z - position y) (position y - position x)
        _ ≤ 4 * δ * Real.sqrt (mass y) + δ * Real.sqrt (mass x) :=
          add_le_add hzy hyx
        _ ≤ 4 * δ * Real.sqrt (mass x) := by nlinarith

end AugmentedHigherRankKS
