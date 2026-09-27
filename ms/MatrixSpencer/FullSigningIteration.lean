import MatrixSpencer.ActualHalfPhase
import MatrixSpencer.SigningPotential
import MatrixSpencer.PartialColoringIteration

/-! Actual iteration of the matrix half-coloring phases to a full signing.
Every phase is constructed on the current live labels and then lifted back
to the original coefficients. No phase-existence premise is assumed. -/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer
open PhaseRestriction

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance fullSigningIterationCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance fullSigningIterationSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- A phase halves the current live set, irrespective of the original label count. -/
theorem exists_actual_live_halving (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (hsmall : (Fintype.card ι : ℝ) * ε ≤ 1 / 1000)
    (x : EuclideanSpace ℝ ι) (hx : CubeRegular ε x) (hk : 0 < Fintype.card (Live x)) :
    ∃ z : EuclideanSpace ℝ ι, CubeRegular ε z ∧
      (Fintype.card (Live z) : ℝ) ≤ (1 - (1 / 2 : ℝ)) * Fintype.card (Live x) ∧
      remainingPotential offset A hA z ≤ remainingPotential offset A hA x +
        squarePhaseCost * Real.sqrt (Fintype.card (Live x) : ℝ) := by
  classical
  have hsmallLive : (Fintype.card (Live x) : ℝ) * ε ≤ 1 / 1000 := by
    have hc : (Fintype.card (Live x) : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x)
    exact (mul_le_mul_of_nonneg_right hc hε.le).trans hsmall
  obtain ⟨y, hy, hhalf, hcost⟩ := exists_actual_half_phase
    (restrictedOffset offset A hA x) (restrictedFamily A x)
    (restrictedFamily_hermitian A hA x) (restrictedFamily_contractions A hN x)
    ε hε hsmallLive hk (restrictPoint x) (restrictPoint_regular hx)
  refine ⟨liftPoint x y, liftPoint_regular hx hy, ?_, ?_⟩
  · rw [live_card_liftPoint]
    have hh : (2 : ℝ) * Fintype.card (Live y) ≤ Fintype.card (Live x) := by exact_mod_cast hhalf
    linarith
  · have hend := remainingPotential_lift_le_nested offset A hA x y
    have hstart := remainingPotential_nested_start_le offset A hA x
    linarith

/-- The concrete finite matrix phases produce a full coloring with the total
geometric square-root budget. -/
theorem exists_actual_full_coloring (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (hsmall : (Fintype.card ι : ℝ) * ε ≤ 1 / 1000)
    (start : EuclideanSpace ℝ ι) (hstart : CubeRegular ε start) :
    ∃ finish : EuclideanSpace ℝ ι, CubeRegular ε finish ∧ Fintype.card (Live finish) = 0 ∧
      remainingPotential offset A hA finish ≤ remainingPotential offset A hA start +
        (4 * squarePhaseCost) * Real.sqrt (Fintype.card (Live start) : ℝ) := by
  classical
  let step := fun _ _ : EuclideanSpace ℝ ι => True
  have hphase : ∀ x, CubeRegular ε x → 0 < Fintype.card (Live x) →
      ∃ y, step x y ∧ CubeRegular ε y ∧
        (Fintype.card (Live y) : ℝ) ≤ (1 - (1 / 2 : ℝ)) * Fintype.card (Live x) ∧
        remainingPotential offset A hA y ≤ remainingPotential offset A hA x +
          squarePhaseCost * Real.sqrt (Fintype.card (Live x) : ℝ) := by
    intro x hx hk
    obtain ⟨y, hy, hh, hc⟩ := exists_actual_live_halving offset A hA hN ε hε hsmall x hx hk
    exact ⟨y, trivial, hy, hh, hc⟩
  obtain ⟨finish, _, hregular, hzero, hcost⟩ := PartialColoringIteration.exists_terminal_of_phases
    (fun x => Fintype.card (Live x)) (remainingPotential offset A hA) (CubeRegular ε) step
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    squarePhaseCost_nonneg hphase start hstart
  refine ⟨finish, hregular, hzero, ?_⟩
  convert hcost using 1 <;> ring

/-- With physical dimension at most twice the number of matrices, the actual
full coloring has a universal square-root potential bound. -/
theorem exists_actual_bounded_full_coloring
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (hd : Fintype.card n ≤ 2 * Fintype.card ι) :
    ∃ finish : EuclideanSpace ℝ ι, Fintype.card (Live finish) = 0 ∧
      remainingPotential 0 A hA finish ≤
        (4 * squarePhaseCost + 5) * Real.sqrt (Fintype.card ι : ℝ) := by
  classical
  obtain ⟨finish, _, hz, hcost⟩ := exists_actual_full_coloring 0 A hA hN (signingEpsilon ι)
    signingEpsilon_pos signingEpsilon_count_small 0 signing_zero_regular
  have hinitial := remainingPotential_zero_le_five A hA hN hd
  have hcard : (Fintype.card (Live (0 : EuclideanSpace ℝ ι)) : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates (0 : EuclideanSpace ℝ ι))
  have hsqrt := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcard)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) squarePhaseCost_nonneg)
  exact ⟨finish, hz, by nlinarith⟩

end MatrixSpencer
