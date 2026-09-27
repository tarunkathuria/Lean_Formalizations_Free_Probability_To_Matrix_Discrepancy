import MatrixSpencer.PhasePotential
import MatrixSpencer.FiniteHalfPhase
import MatrixSpencer.SmallLiveRounding

/-! An actual half-coloring phase, with every epoch-continuation premise
discharged by the concrete matrix walk. -/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer
open PhaseRestriction

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance actualHalfPhaseCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance actualHalfPhaseSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def squarePhaseCost : ℝ := 22 * 49377 + 64

theorem squarePhaseCost_nonneg : 0 ≤ squarePhaseCost := by norm_num [squarePhaseCost]

theorem cubeRegular_of_full_signs (ε : ℝ) (x : EuclideanSpace ℝ ι)
    (hx : ∀ i, IsSign (x i)) : CubeRegular ε x :=
  ⟨fun i => (hx i).abs_eq_one.le, fun i => Or.inl (hx i)⟩

/-- In the actual remaining-family potential, a finite phase halves the number
of labels. The small-live stop is completed by the proved boundary rounding. -/
theorem exists_actual_half_phase (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (hsmall : (Fintype.card ι : ℝ) * ε ≤ 1 / 1000)
    (hk : 0 < Fintype.card ι) (start : EuclideanSpace ℝ ι) (hstart : CubeRegular ε start) :
    ∃ finish : EuclideanSpace ℝ ι, CubeRegular ε finish ∧
      2 * Fintype.card (Live finish) ≤ Fintype.card ι ∧
      remainingPotential offset A hA finish ≤ remainingPotential offset A hA start +
        squarePhaseCost * Real.sqrt (Fintype.card ι : ℝ) := by
  classical
  let potential := remainingPotential offset A hA
  let step := fun _ _ : EuclideanSpace ℝ ι => True
  have hcontinue : ∀ x, FiniteHalfPhase.Cube x → CubeRegular ε x → ¬ FiniteHalfPhase.Terminal x →
      ∃ y time, step x y ∧ CubeRegular ε y ∧
        FiniteHalfPhase.EpochAdvance potential epochTimeLimit 22 x y time := by
    intro x _ hx ht
    have hl : 32 ≤ Fintype.card (Live x) := by
      simpa only [live_card, FiniteHalfPhase.liveCount] using
        FiniteHalfPhase.liveCount_large_of_nonterminal ht
    obtain ⟨y, time, hy, _, hfrozen, ht0, _, hgain, hsuccess, hcost⟩ :=
      exists_lifted_successful_epoch offset A hA hN x ε hε hsmall hx hl
    refine ⟨y, time, trivial, hy, hy.1, hfrozen, ht0, ?_, ?_, ?_⟩
    · simpa only [live_card, FiniteHalfPhase.liveCount] using hgain
    · rcases hsuccess with htime | hfreeze
      · exact Or.inl htime.ge
      · exact Or.inr (by simpa only [live_card, FiniteHalfPhase.liveCount] using hfreeze)
    · change remainingPotential offset A hA y ≤ remainingPotential offset A hA x + _
      simpa only [live_card, FiniteHalfPhase.liveCount, add_comm] using (sub_le_iff_le_add.mp hcost)
  obtain ⟨finish, _, hcube, hregular, _, hterm, hcost⟩ :=
    FiniteHalfPhase.exists_terminal_of_actual_epoch_continuation potential step
      (CubeRegular ε) 22 (by norm_num) hk hcontinue start hstart.1 hstart
  rcases hterm with hhalf | hsmallLive
  · refine ⟨finish, hregular, ?_, ?_⟩
    · rw [live_card]
      have hc := Finset.card_le_univ (frozenCoordinates finish)
      omega
    · change potential finish ≤ potential start + _
      have hr := Real.sqrt_nonneg (Fintype.card ι : ℝ)
      dsimp only [squarePhaseCost]
      nlinarith
  · have hl : Fintype.card (Live finish) < 32 := by
      simpa only [live_card, FiniteHalfPhase.liveCount] using hsmallLive
    obtain ⟨z, hz, _, _, hzlive, hzcost⟩ :=
      SmallLiveRounding.exists_small_live_completion offset A hA hN hcube hl
    refine ⟨z, cubeRegular_of_full_signs ε z hz, by rw [hzlive]; omega, ?_⟩
    have hcard : (Fintype.card (Live finish) : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates finish)
    have hsqrt := Real.sqrt_le_sqrt hcard
    change remainingPotential offset A hA finish ≤ remainingPotential offset A hA start + _ at hcost
    dsimp only [squarePhaseCost]
    nlinarith

end MatrixSpencer
