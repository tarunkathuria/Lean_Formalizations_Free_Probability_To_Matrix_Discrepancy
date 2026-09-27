import MatrixSpencer.DyadicEpochDriftMesh
import MatrixSpencer.DyadicEpochPreparation
import MatrixSpencer.DyadicEpochTree

/-! Actual preparation and the proved support mesh discharge all finite epoch inputs. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance dyadicActualEpochCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicActualEpochSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- The only parameter hypothesis is the explicit scalar response budget.
No preparation, derivative, transition, moment, or termination assumption remains. -/
def dyadicEpochAnalyticInputs (cfg : DyadicEpochConfig ι n)
    (hbudget : DyadicEpochPreparation.HasResponseBudget cfg) : DyadicEpochAnalyticInputs cfg where
  prepare H upper hupper hupper1 :=
    DyadicEpochPreparation.exists_preparedCovariance cfg H (upper := upper) hupper hupper1 hbudget
  mesh K := Classical.choose (exists_dyadic_epoch_drift_mesh cfg K)
  mesh_pos K := (Classical.choose_spec (exists_dyadic_epoch_drift_mesh cfg K)).1
  mesh_le_half K := (Classical.choose_spec (exists_dyadic_epoch_drift_mesh cfg K)).2.1
  mesh_rounding K := (Classical.choose_spec (exists_dyadic_epoch_drift_mesh cfg K)).2.2.1
  drift s hs hactive h hh hmesh :=
    (Classical.choose_spec (exists_dyadic_epoch_drift_mesh cfg s.support)).2.2.2
      s hs hactive rfl h ⟨hh, hmesh⟩

theorem exists_actual_successful_dyadic_epoch (cfg : DyadicEpochConfig ι n)
    (hbudget : DyadicEpochPreparation.HasResponseBudget cfg) :
    ∃ (y : EuclideanSpace ℝ ι) (time : ℝ), CubeRegular cfg.epsilon y ∧
      0 ≤ time ∧ time ≤ cfg.duration ∧
      ‖cfg.start‖ ^ 2 + (Fintype.card ι : ℝ) / 16 * time ≤ ‖y‖ ^ 2 ∧
      (time = cfg.duration ∨ (Fintype.card ι : ℝ) / 64 ≤ (frozenCoordinates y).card) ∧
      cfg.potential (cfg.center y) 1 - cfg.potential cfg.anchor 1 ≤
        22 * Real.sqrt (Fintype.card ι : ℝ) :=
  exists_successful_dyadic_epoch cfg (dyadicEpochAnalyticInputs cfg hbudget)

end
end MatrixSpencer
