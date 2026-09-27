import MatrixSpencer.PhaseEpochProgress
import MatrixSpencer.EpochState
import Mathlib.Logic.Relation

/-!
# Finite half-phase assembly with changing live labels

This module assembles an explicitly supplied actual epoch continuation
relation on ambient cube vectors. Each epoch's live count is computed from
the actual frozen-coordinate finset. The continuation and its potential
bound are premises to be discharged by restriction and the actual epoch.
-/

open scoped BigOperators
noncomputable section
namespace MatrixSpencer
namespace FiniteHalfPhase

variable {ι : Type*} [Fintype ι]

def Cube (x : EuclideanSpace ℝ ι) : Prop := ∀ i, |x i| ≤ 1

def liveCount (x : EuclideanSpace ℝ ι) : ℕ :=
  Fintype.card ι - (frozenCoordinates x).card

def Terminal (x : EuclideanSpace ℝ ι) : Prop :=
  Fintype.card ι ≤ 2 * (frozenCoordinates x).card ∨ liveCount x < 32

/-- All progress and preservation fields are about the actual ambient point.
The potential is an explicit function to be instantiated by the remaining-family owner potential. -/
structure EpochAdvance (potential : EuclideanSpace ℝ ι → ℝ) (τ B : ℝ)
    (x y : EuclideanSpace ℝ ι) (time : ℝ) : Prop where
  cube : Cube y
  frozen : frozenCoordinates x ⊆ frozenCoordinates y
  time_nonneg : 0 ≤ time
  norm_progress : ‖x‖ ^ 2 + (liveCount x : ℝ) / 16 * time ≤ ‖y‖ ^ 2
  successful : τ ≤ time ∨ (liveCount x : ℝ) / 64 ≤
    ((frozenCoordinates y).card : ℝ) - (frozenCoordinates x).card
  cost : potential y ≤ potential x + B * Real.sqrt (liveCount x : ℝ)

theorem liveCount_le (x : EuclideanSpace ℝ ι) : liveCount x ≤ Fintype.card ι :=
  Nat.sub_le _ _

theorem liveCount_lower_of_nonterminal {x : EuclideanSpace ℝ ι} (hx : ¬Terminal x) :
    (Fintype.card ι : ℝ) / 2 ≤ (liveCount x : ℝ) := by
  have hf : 2 * (frozenCoordinates x).card < Fintype.card ι :=
    Nat.lt_of_not_ge (fun h => hx (Or.inl h))
  have hf' : (2 : ℝ) * (frozenCoordinates x).card < Fintype.card ι := by exact_mod_cast hf
  have hcard := frozenCoordinates_card_le x
  rw [liveCount, Nat.cast_sub hcard]
  linarith

theorem liveCount_large_of_nonterminal {x : EuclideanSpace ℝ ι} (hx : ¬Terminal x) :
    32 ≤ liveCount x := Nat.le_of_not_gt (fun h => hx (Or.inr h))

/-- The terminal test is exactly enough for the outer half-coloring iteration,
except for the separately handled small live set. -/
theorem terminal_liveCount {x : EuclideanSpace ℝ ι} (hx : Terminal x) :
    liveCount x ≤ Fintype.card ι / 2 ∨ liveCount x < 32 := by
  rcases hx with h | h
  · left
    have hf := frozenCoordinates_card_le x
    unfold liveCount
    omega
  · exact Or.inr h

theorem EpochAdvance.uniform_norm_progress {potential : EuclideanSpace ℝ ι → ℝ}
    {τ B time : ℝ} {x y : EuclideanSpace ℝ ι} (h : EpochAdvance potential τ B x y time)
    (hx : ¬Terminal x) :
    ‖x‖ ^ 2 + (Fintype.card ι : ℝ) / 32 * time ≤ ‖y‖ ^ 2 := by
  have hl := mul_le_mul_of_nonneg_right (liveCount_lower_of_nonterminal hx) h.time_nonneg
  have hg := h.norm_progress
  nlinarith

theorem EpochAdvance.uniform_success {potential : EuclideanSpace ℝ ι → ℝ}
    {τ B time : ℝ} {x y : EuclideanSpace ℝ ι} (h : EpochAdvance potential τ B x y time)
    (hx : ¬Terminal x) :
    τ ≤ time ∨ (Fintype.card ι : ℝ) / 128 ≤
      ((frozenCoordinates y).card : ℝ) - (frozenCoordinates x).card := by
  rcases h.successful with ht | hf
  · exact Or.inl ht
  · right
    have hl := liveCount_lower_of_nonterminal hx
    linarith

theorem EpochAdvance.uniform_cost {potential : EuclideanSpace ℝ ι → ℝ}
    {τ B time : ℝ} {x y : EuclideanSpace ℝ ι} (h : EpochAdvance potential τ B x y time)
    (hB : 0 ≤ B) :
    potential y ≤ potential x + B * Real.sqrt (Fintype.card ι : ℝ) := by
  have hc : (liveCount x : ℝ) ≤ Fintype.card ι := Nat.cast_le.mpr (liveCount_le x)
  have hs := Real.sqrt_le_sqrt hc
  have hb := mul_le_mul_of_nonneg_left hs hB
  linarith [h.cost]

/-- An actual finite continuation relation reaches half-frozen or small-live
termination within the explicit finite ledger bound. The bound includes all
selected epoch costs and retains actual relation reachability. -/
theorem exists_terminal_of_epoch_continuation
    (potential : EuclideanSpace ℝ ι → ℝ)
    (step : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → Prop)
    (invariant : EuclideanSpace ℝ ι → Prop)
    (B : ℝ) (hB : 0 ≤ B)
    {τ : ℝ} (hτ : 0 < τ) (hk : 0 < Fintype.card ι) (N : ℕ)
    (hN : 32 / τ + 128 < (N : ℝ))
    (continuation : ∀ x, Cube x → invariant x → ¬Terminal x →
      ∃ y time, step x y ∧ invariant y ∧ EpochAdvance potential τ B x y time)
    (start : EuclideanSpace ℝ ι) (hstart : Cube start) (hstartInv : invariant start) :
    ∃ finish, Relation.ReflTransGen step start finish ∧ Cube finish ∧ invariant finish ∧
      frozenCoordinates start ⊆ frozenCoordinates finish ∧ Terminal finish ∧
      potential finish ≤ potential start + B * (N : ℝ) * Real.sqrt (Fintype.card ι : ℝ) := by
  classical
  let Point := {x : EuclideanSpace ℝ ι // Cube x ∧ invariant x}
  have hnext : ∀ x : Point, ∃ y : Point, ∃ time : ℝ,
      (y = x ∧ time = 0 ∧ Terminal x.val) ∨
        (¬Terminal x.val ∧ step x.val y.val ∧ EpochAdvance potential τ B x.val y.val time) := by
    intro x
    by_cases ht : Terminal x.val
    · exact ⟨x, 0, Or.inl ⟨rfl, rfl, ht⟩⟩
    · obtain ⟨y, time, hstep, hyInv, hy⟩ := continuation x.val x.property.1 x.property.2 ht
      exact ⟨⟨y, hy.cube, hyInv⟩, time, Or.inr ⟨ht, hstep, hy⟩⟩
  choose next duration hnext using hnext
  let path : ℕ → Point := Nat.rec ⟨start, hstart, hstartInv⟩ (fun _ x => next x)
  let x : ℕ → EuclideanSpace ℝ ι := fun j => (path j).val
  let time : ℕ → ℝ := fun j => duration (path j)
  have hx0 : x 0 = start := rfl
  have hcase (j : ℕ) :
      (x (j + 1) = x j ∧ time j = 0 ∧ Terminal (x j)) ∨
        (¬Terminal (x j) ∧ step (x j) (x (j + 1)) ∧
          EpochAdvance potential τ B (x j) (x (j + 1)) (time j)) := by
    rcases hnext (path j) with ⟨hy, ht, hterm⟩ | h
    · exact Or.inl ⟨congrArg Subtype.val hy, ht, hterm⟩
    · exact Or.inr h
  have hcube (j : ℕ) : Cube (x j) := (path j).property.1
  have hInv (j : ℕ) : invariant (x j) := (path j).property.2
  have htime (j : ℕ) : 0 ≤ time j := by
    rcases hcase j with ⟨_, ht, _⟩ | ⟨_, _, h⟩
    · rw [ht]
    · exact h.time_nonneg
  have hfrozen (j : ℕ) : frozenCoordinates (x j) ⊆ frozenCoordinates (x (j + 1)) := by
    rcases hcase j with ⟨hy, _, _⟩ | ⟨_, _, h⟩
    · rw [hy]
    · exact h.frozen
  have hgain (j : ℕ) : ‖x j‖ ^ 2 + (Fintype.card ι : ℝ) / 32 * time j ≤ ‖x (j + 1)‖ ^ 2 := by
    rcases hcase j with ⟨hy, ht, _⟩ | ⟨hactive, _, h⟩
    · simp only [hy, ht, mul_zero, add_zero, le_refl]
    · exact h.uniform_norm_progress hactive
  have hsuccess (j : ℕ) (hactive : ¬Terminal (x j)) :
      τ ≤ time j ∨ (Fintype.card ι : ℝ) / 128 ≤
        ((frozenCoordinates (x (j + 1))).card : ℝ) - (frozenCoordinates (x j)).card := by
    rcases hcase j with ⟨_, _, ht⟩ | ⟨_, _, h⟩
    · exact False.elim (hactive ht)
    · exact h.uniform_success hactive
  have hcost (j : ℕ) : potential (x (j + 1)) ≤ potential (x j) + B * Real.sqrt (Fintype.card ι : ℝ) := by
    rcases hcase j with ⟨hy, _, _⟩ | ⟨_, _, h⟩
    · rw [hy]
      exact le_add_of_nonneg_right (mul_nonneg hB (Real.sqrt_nonneg (Fintype.card ι : ℝ)))
    · exact h.uniform_cost hB
  have hreach (j : ℕ) : Relation.ReflTransGen step start (x j) := by
    induction j with
    | zero => rw [hx0]
    | succ j ih =>
      rcases hcase j with ⟨hy, _, _⟩ | ⟨_, hstep, _⟩
      · rwa [hy]
      · exact ih.tail hstep
  have hpreserve (j : ℕ) : frozenCoordinates start ⊆ frozenCoordinates (x j) := by
    induction j with
    | zero => rw [hx0]
    | succ j ih => exact ih.trans (hfrozen j)
  obtain ⟨j, hj, hterminal⟩ := phase_epoch_terminal_before_bound x time (fun j => Terminal (x j)) N
    hk hτ (by norm_num : (0 : ℝ) < 1 / 64) (by norm_num at ⊢; exact hN)
    (hcube N) (fun j _ => htime j) (fun j _ => hfrozen j) (fun j _ => hgain j) (by
      intro j _ hactive
      rcases hsuccess j hactive with ht | hf
      · exact Or.inl ht
      · right
        linarith)
  refine ⟨x j, hreach j, hcube j, hInv j, hpreserve j, hterminal, ?_⟩
  have hp := FiniteProcessMoments.telescope_le (fun j => potential (x j))
    (fun _ => 0) (fun _ => B * Real.sqrt (Fintype.card ι : ℝ)) j (by
      intro l _
      simpa only [add_zero] using hcost l)
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, hx0] at hp
  have hj' : (j : ℝ) ≤ N := Nat.cast_le.mpr hj.le
  have hn := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hj' (Real.sqrt_nonneg (Fintype.card ι : ℝ))) hB
  nlinarith

/-- With the actual epoch time limit, 49,377 selected epochs is a sufficient
uniform finite ceiling for a half-phase or the global small-live stop. -/
theorem exists_terminal_of_actual_epoch_continuation
    (potential : EuclideanSpace ℝ ι → ℝ)
    (step : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → Prop)
    (invariant : EuclideanSpace ℝ ι → Prop)
    (B : ℝ) (hB : 0 ≤ B)
    (hk : 0 < Fintype.card ι)
    (continuation : ∀ x, Cube x → invariant x → ¬Terminal x →
      ∃ y time, step x y ∧ invariant y ∧ EpochAdvance potential epochTimeLimit B x y time)
    (start : EuclideanSpace ℝ ι) (hstart : Cube start) (hstartInv : invariant start) :
    ∃ finish, Relation.ReflTransGen step start finish ∧ Cube finish ∧ invariant finish ∧
      frozenCoordinates start ⊆ frozenCoordinates finish ∧ Terminal finish ∧
      potential finish ≤ potential start + (B * 49377 : ℝ) * Real.sqrt (Fintype.card ι : ℝ) := by
  exact exists_terminal_of_epoch_continuation potential step invariant B hB (by norm_num [epochTimeLimit]) hk 49377
    (by norm_num [epochTimeLimit]) continuation start hstart hstartInv

end FiniteHalfPhase
end MatrixSpencer
