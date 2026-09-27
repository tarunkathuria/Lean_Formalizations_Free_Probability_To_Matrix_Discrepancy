import MatrixSpencer.DyadicPhasePotential
import MatrixSpencer.DyadicSmallLiveRounding

/-! Finite half-phases for the actual dyadic remaining potential.
The sole analytic premise is the uniform construction of actual epoch inputs. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
namespace DyadicHalfPhase
noncomputable section
universe u v
open PhaseRestriction
variable {ι : Type u} {n : Type v} [Fintype ι] [Fintype n]
  [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance dyadicHalfPhaseCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicHalfPhaseSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- The extra unit absorbs the complete small-live boundary rounding. -/
def phaseCost (B : ℝ) : ℝ := 76 * 23 * (B + 1)

theorem phaseCost_nonneg {B : ℝ} (hB : 2 ≤ B) : 0 ≤ phaseCost B := by
  unfold phaseCost
  positivity

theorem phaseCost_covers_rounding {B : ℝ} (hB : 2 ≤ B) :
    76 * 22 * (B + 1) + 64 ≤ phaseCost B := by
  unfold phaseCost
  linarith

/-- A finite number of selected actual epochs halves the labels; the small-live
stop is completed by actual boundary rounding. -/
theorem exists_half_phase (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (B : ℝ) (hB : 2 ≤ B) (N : ℕ)
    (hinputs : DyadicPhasePotential.HasEpochInputs.{u,v} n m θ B N)
    (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1) (hcount : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) (hsmall : (Fintype.card ι : ℝ) * ε ≤ 1 / 1000)
    (hk : 0 < Fintype.card ι) (start : EuclideanSpace ℝ ι) (hstart : CubeRegular ε start) :
    ∃ finish : EuclideanSpace ℝ ι, CubeRegular ε finish ∧
      2 * Fintype.card (Live finish) ≤ Fintype.card ι ∧
      rectangularRemainingPotential m θ offset A hA finish ≤
        rectangularRemainingPotential m θ offset A hA start +
          phaseCost B * Real.sqrt (Fintype.card ι : ℝ) := by
  classical
  let potential := rectangularRemainingPotential m θ offset A hA
  let step := fun _ _ : EuclideanSpace ℝ ι => True
  have hcontinue : ∀ x, FiniteHalfPhase.Cube x → CubeRegular ε x → ¬ FiniteHalfPhase.Terminal x →
      ∃ y time, step x y ∧ CubeRegular ε y ∧
        FiniteHalfPhase.EpochAdvance potential (RectangularEpochParameters.duration B) 22 x y time := by
    intro x _ hx ht
    have hl : 32 ≤ Fintype.card (Live x) := by
      simpa only [live_card, FiniteHalfPhase.liveCount] using
        FiniteHalfPhase.liveCount_large_of_nonterminal ht
    obtain ⟨y, time, hy, _, hfrozen, ht0, _, hgain, hsuccess, hcost⟩ :=
      DyadicPhasePotential.exists_lifted_successful_epoch m hm θ hθ B hB N hinputs
        offset A hA hN hcount x ε hε hsmall hx hl
    refine ⟨y, time, trivial, hy, hy.1, hfrozen, ht0, ?_, ?_, ?_⟩
    · simpa only [live_card, FiniteHalfPhase.liveCount] using hgain
    · rcases hsuccess with htime | hfreeze
      · exact Or.inl htime.ge
      · exact Or.inr (by simpa only [live_card, FiniteHalfPhase.liveCount] using hfreeze)
    · change rectangularRemainingPotential m θ offset A hA y ≤
        rectangularRemainingPotential m θ offset A hA x + _
      simpa only [live_card, FiniteHalfPhase.liveCount, add_comm] using (sub_le_iff_le_add.mp hcost)
  obtain ⟨finish, _, hcube, hregular, _, hterm, hcost⟩ :=
    RectangularEpochParameters.exists_half_terminal_of_continuation potential step
      (CubeRegular ε) hB (by norm_num : (0 : ℝ) ≤ 22) hk hcontinue start hstart.1 hstart
  have hcoef := phaseCost_covers_rounding hB
  have hr := Real.sqrt_nonneg (Fintype.card ι : ℝ)
  rcases hterm with hhalf | hsmallLive
  · refine ⟨finish, hregular, ?_, ?_⟩
    · rw [live_card]
      have hc := Finset.card_le_univ (frozenCoordinates finish)
      omega
    · change potential finish ≤ potential start + _
      nlinarith
  · have hl : Fintype.card (Live finish) < 32 := by
      simpa only [live_card, FiniteHalfPhase.liveCount] using hsmallLive
    obtain ⟨z, hz, _, _, hzlive, hzcost⟩ :=
      DyadicSmallLiveRounding.exists_small_live_completion m θ offset A hA hN hcube hl
    refine ⟨z, ⟨fun i => (hz i).abs_eq_one.le, fun i => Or.inl (hz i)⟩,
      by rw [hzlive]; omega, ?_⟩
    have hcard : (Fintype.card (Live finish) : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates finish)
    have hsqrt := Real.sqrt_le_sqrt hcard
    change rectangularRemainingPotential m θ offset A hA finish ≤
      rectangularRemainingPotential m θ offset A hA start + _ at hcost
    nlinarith

end
end DyadicHalfPhase
end MatrixSpencer
