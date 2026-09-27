import MatrixSpencer.DyadicHalfPhase

/-! Iterating actual dyadic half-phases to a full signing. The explicit analytic
input builder is retained until it is discharged by the global response budget. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
namespace DyadicFullSigningIteration
noncomputable section
universe u v
open PhaseRestriction
variable {ι : Type u} {n : Type v} [Fintype ι] [Fintype n]
  [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance dyadicFullSigningCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicFullSigningSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- Halve the current live set using the same global exponent, weight, and response coefficient. -/
theorem exists_live_halving (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (B : ℝ) (hB : 2 ≤ B) (N : ℕ)
    (hinputs : DyadicPhasePotential.HasEpochInputs.{u,v} n m θ B N)
    (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1) (hcount : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) (hsmall : (Fintype.card ι : ℝ) * ε ≤ 1 / 1000)
    (x : EuclideanSpace ℝ ι) (hx : CubeRegular ε x) (hk : 0 < Fintype.card (Live x)) :
    ∃ z : EuclideanSpace ℝ ι, CubeRegular ε z ∧
      (Fintype.card (Live z) : ℝ) ≤ Fintype.card (Live x) / 2 ∧
      rectangularRemainingPotential m θ offset A hA z ≤
        rectangularRemainingPotential m θ offset A hA x +
          DyadicHalfPhase.phaseCost B * Real.sqrt (Fintype.card (Live x) : ℝ) := by
  classical
  have hcard : Fintype.card (Live x) ≤ Fintype.card ι :=
    Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x)
  have hsmallLive : (Fintype.card (Live x) : ℝ) * ε ≤ 1 / 1000 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hε.le).trans hsmall
  obtain ⟨y, hy, hhalf, hcost⟩ := DyadicHalfPhase.exists_half_phase m hm θ hθ B hB N hinputs
    (restrictedOffset offset A hA x) (restrictedFamily A x)
    (restrictedFamily_hermitian A hA x) (restrictedFamily_contractions A hN x)
    (hcard.trans hcount) ε hε hsmallLive hk (restrictPoint x) (restrictPoint_regular hx)
  refine ⟨liftPoint x y, liftPoint_regular hx hy, ?_, ?_⟩
  · rw [live_card_liftPoint]
    have hh : (2 : ℝ) * Fintype.card (Live y) ≤ Fintype.card (Live x) := by exact_mod_cast hhalf
    linarith
  · have hend := rectangularRemainingPotential_lift_le_nested m θ offset A hA x y
    have hstart := rectangularRemainingPotential_nested_start_le m θ offset A hA x
    linarith

/-- Finite geometric iteration of the proved actual half-phases, conditional only
on the construction of actual analytic inputs for each restricted epoch. -/
theorem exists_full_coloring (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (B : ℝ) (hB : 2 ≤ B) (N : ℕ)
    (hinputs : DyadicPhasePotential.HasEpochInputs.{u,v} n m θ B N)
    (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1) (hcount : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) (hsmall : (Fintype.card ι : ℝ) * ε ≤ 1 / 1000)
    (start : EuclideanSpace ℝ ι) (hstart : CubeRegular ε start) :
    ∃ finish : EuclideanSpace ℝ ι, CubeRegular ε finish ∧ Fintype.card (Live finish) = 0 ∧
      rectangularRemainingPotential m θ offset A hA finish ≤
        rectangularRemainingPotential m θ offset A hA start +
          (304 * 23 * (B + 1)) * Real.sqrt (Fintype.card (Live start) : ℝ) := by
  classical
  let step := fun _ _ : EuclideanSpace ℝ ι => True
  have hphase : ∀ x, CubeRegular ε x → 0 < Fintype.card (Live x) →
      ∃ y, step x y ∧ CubeRegular ε y ∧
        (Fintype.card (Live y) : ℝ) ≤ Fintype.card (Live x) / 2 ∧
        rectangularRemainingPotential m θ offset A hA y ≤
          rectangularRemainingPotential m θ offset A hA x +
            (76 * 23 * (B + 1)) * Real.sqrt (Fintype.card (Live x) : ℝ) := by
    intro x hx hk
    obtain ⟨y, hy, hh, hc⟩ := exists_live_halving m hm θ hθ B hB N hinputs
      offset A hA hN hcount ε hε hsmall x hx hk
    exact ⟨y, trivial, hy, hh, hc⟩
  obtain ⟨finish, _, hregular, hzero, hcost⟩ :=
    RectangularEpochParameters.exists_terminal_of_half_phases
      (fun x => Fintype.card (Live x)) (rectangularRemainingPotential m θ offset A hA)
      (CubeRegular ε) step hB (by norm_num : (0 : ℝ) ≤ 23) hphase start hstart
  exact ⟨finish, hregular, hzero, hcost⟩

/-- Initial bias and all phase costs, with dimension and original count kept separate. -/
theorem exists_bounded_full_coloring (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (B : ℝ) (hB : 2 ≤ B) (N : ℕ)
    (hinputs : DyadicPhasePotential.HasEpochInputs.{u,v} n m θ B N)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (hcount : Fintype.card ι ≤ N) :
    ∃ finish : EuclideanSpace ℝ ι, Fintype.card (Live finish) = 0 ∧
      rectangularRemainingPotential m θ 0 A hA finish ≤
        2 * Real.sqrt (Fintype.card ι : ℝ) +
          θ * (Fintype.card n : ℝ) ^ (1 / (2 ^ m : ℝ)) / (1 - 1 / (2 ^ m : ℝ)) +
          (304 * 23 * (B + 1)) * Real.sqrt (Fintype.card ι : ℝ) := by
  classical
  obtain ⟨finish, _, hz, hcost⟩ := exists_full_coloring m hm θ hθ B hB N hinputs
    0 A hA hN hcount (signingEpsilon ι) signingEpsilon_pos signingEpsilon_count_small
    0 signing_zero_regular
  have hinitial := rectangularRemainingPotential_zero_le hm hθ.le A hA hN
  have hcard : (Fintype.card (Live (0 : EuclideanSpace ℝ ι)) : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates (0 : EuclideanSpace ℝ ι))
  have hcoef : 0 ≤ 304 * 23 * (B + 1) := by positivity
  have hsqrt := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcard) hcoef
  exact ⟨finish, hz, by linarith⟩

end
end DyadicFullSigningIteration
end MatrixSpencer
