import FaithfulMS.RectangularDirectEpochRun

/-! Exact preservation of previously frozen original coordinate values and
pathwise norm progress for the actual constructed fixed-universe epoch. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectEpochStateFacts
open RectangularRidgeEpochInput RectangularDirectEpochRun
open RectangularRidgePreparationData (floor)
variable {N d : ℕ} [Nonempty (Fin d)]
attribute [local irreducible] prepare preparationResult run

lemma moveValue_frozen (c : Config N d) (s : Certified c)
    (hf : s.val.owner.Valid (2 * floor)) (hn : ¬Stopped c s.val)
    (z : MSManuscriptNumericalEpochLedger.Draws s.val) (i : Fin N) (hi : i ∈ oldFrozen c) :
    (moveValue c s hf hn z).val.point i = s.val.point i :=
  MSManuscriptNumericalCoordinateStep.rounded_preserves_frozen
    (s.property.1.owner_valid.physical_posSemidef _ (by norm_num [floor]))
    (margin N) s.val.point (mesh c) z (s.property.1.frozen_subset hi)

theorem next_frozen (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) (s : Certified c) (i : Fin N) (hi : i ∈ oldFrozen c) :
    ∀ z : (next solver a c s).Draws, ((next solver a c s).value z).val.point i = s.val.point i := by
  classical
  by_cases hs : Stopped c s.val
  · rw [next_stopped solver a c s hs]
    intro z
    rfl
  · rw [next, dif_neg hs]
    dsimp only
    by_cases hp : Stopped c (prepare solver a c s).val
    · rw [dif_pos hp]
      intro z
      exact congrArg (fun x => x i) (prepare_point solver a c s)
    · rw [dif_neg hp]
      intro z
      exact (moveValue_frozen c (prepare solver a c s) (prepare_floor solver a c s) hp z i hi).trans
        (congrArg (fun x => x i) (prepare_point solver a c s))

theorem run_frozen (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) (k : ℕ) (s : Certified c) (i : Fin N) (hi : i ∈ oldFrozen c) :
    ∀ z : (run solver a c k s).Draws, ((run solver a c k s).value z).val.point i = s.val.point i := by
  induction k generalizing s with
  | zero => rw [run]; intro z; rfl
  | succ k ih =>
    rw [run]
    intro z
    exact (ih ((next solver a c s).value z.1) z.2).trans (next_frozen solver a c s i hi z.1)

/-- Old signs keep their actual values, not only their membership in the frozen set. -/
theorem output_frozen (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) (z : (output solver a c).Draws) (i : Fin N) (hi : i ∈ oldFrozen c) :
    ((output solver a c).value z).val.point i = c.start i :=
  run_frozen solver a c (count c) (initial c) i hi z

theorem output_norm_progress (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) (z : (output solver a c).Draws) :
    ‖c.start‖ ^ 2 + (live c : ℝ) / 16 * ((output solver a c).value z).val.time ≤
      ‖((output solver a c).value z).val.point‖ ^ 2 := by
  have hh := output_invariant solver a c z
  linarith [hh.norm_progress, hh.variance_ge]

end MatrixSpencer.RectangularDirectEpochStateFacts
