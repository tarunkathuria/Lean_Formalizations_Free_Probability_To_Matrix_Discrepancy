import MatrixSpencer.KSNumericalDensityRun
import MatrixSpencer.KSObjectiveValueBound
import MatrixSpencer.KSOwnerOptimizerDomain

/-!
# Finite numerical evaluation of the optimized owner potential

All numerical definitions use the input entries, explicit scalar parameter
formulas, finite projected iterations and Jacobi reports. The canonical
optimizer and Hilbert chart occur only in the accuracy proof. The final
accuracy theorem has only the actual Hermitian/PSD input conditions and
positive regularization/error parameters.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSNumericalOwnerPotential

open KSOwnerOptimizerDomain KSOwnerInputBounds KSFullHermitianChart
open KSComplexProjectionGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance

def distanceTolerance (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ ε : ℝ) : ℝ :=
  KSObjectiveValueBound.distanceAccuracy (n := Fin d) (centerBound H) (optimizerFloor H A C θ)
    (krausBudget A C) θ (ε / 2)

/-- The returned density is produced by the actual finite physical loop. -/
def densityReport (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) (hd : 0 < d) (ε : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  KSNumericalDensityRun.output H A C θ (optimizerFloor H A C θ) (krausBudget A C)
    (distanceTolerance H A C θ ε) hd (initialDensity hd)

/-- Finite optimization followed by finite objective evaluation. -/
def report (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) (hd : 0 < d) (ε : ℝ) : ℝ :=
  KSNumericalOwnerObjective.report H A C θ (densityReport H A C θ hd ε) (ε / 2)

theorem densityReport_feasible (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ) (hd : 0 < d) (ε : ℝ) :
    ComplexFeasible (optimizerFloor H A C θ) 1 (densityReport H A C θ hd ε) := by
  exact KSNumericalDensityRun.run_feasible H A C θ _ _ _ hd
    (optimizerFloor_scaled_le_one H A C θ) (initialDensity hd)
    ⟨(initialDensity hd).property, initialDensity_mem_floor H A C θ hd⟩ _

/-- Accuracy against the original supremum over every density matrix.
Neither an optimization oracle nor a numerical success premise appears. -/
theorem report_accuracy (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ ε : ℝ}
    (hθ : 0 < θ) (hε : 0 < ε) (hd : 0 < d) :
    |report H A C θ hd ε - ownerPotential H A C θ| ≤ ε := by
  let a := optimizerFloor H A C θ
  let κ := krausBudget A C
  let R := centerBound H
  let τ := distanceTolerance H A C θ ε
  have ha : 0 < a := optimizerFloor_pos H A C hθ hd
  have hκ : 0 < κ := krausBudget_pos A C
  have hR : ‖H‖ ≤ R := (centerBound_spec H hH).2
  have hτ : 0 < τ := KSObjectiveValueBound.distanceAccuracy_pos
    (matrixBound_pos H).le ha.le hθ.le (by linarith : 0 < ε / 2)
  have has : (d : ℝ) * a ≤ 1 := optimizerFloor_scaled_le_one H A C θ
  have hbudget := covarianceKraus_budget A hA hC
  let x₀ := initialCoordinates hd
  let xstar := optimizerCoordinates H A C θ hd
  let k := KSNumericalDensityRun.iterationCount (d := d) a κ θ τ
  let y := KSNumericalDensityRun.coordinateRun H A C θ a κ τ hd has x₀ k
  have hstart : x₀ ∈ KSObjectiveChart.densityFloor (chart (Fin d)) a :=
    initialCoordinates_mem_floor H A C θ hd
  have hxstar : xstar ∈ KSObjectiveChart.densityFloor (chart (Fin d)) a :=
    optimizerCoordinates_mem_floor H hH A hA hC hθ hd
  have hmax := optimizer_isMaxOn_objective H hH A hA hC hθ hd
  have hdist : dist y xstar ≤ τ := KSNumericalDensityRun.coordinateRun_accuracy
    H A hA hC hθ ha hκ.le hτ hd has hbudget x₀ xstar hstart hxstar hmax
  have hinit : chart (Fin d) x₀ = initialDensity hd := (chartEquiv (Fin d)).apply_symm_apply _
  have hphysical : (chart (Fin d) y : Matrix (Fin d) (Fin d) ℂ) = densityReport H A C θ hd ε := by
    have hh := KSNumericalDensityRun.coordinateRun_physical H A C θ a κ τ hd has x₀ k
    rw [hinit] at hh
    exact hh
  have hfeas := densityReport_feasible H A C θ hd ε
  have hy : y ∈ KSObjectiveChart.densityFloor (chart (Fin d)) a := by
    change _ ∧ _
    rw [hphysical]
    exact hfeas.2
  have hv := KSObjectiveValueBound.objective_value_error_of_distance H (covarianceKraus A C)
    hθ.le hR ha hκ.le (by linarith : 0 < ε / 2) (chart (Fin d))
    (chart_trace_square (Fin d)) hbudget hy hxstar hdist
  have heqy : KSObjectiveChart.objective H (covarianceKraus A C) θ (chart (Fin d)) y =
      ownerObjective H A C θ (densityReport H A C θ hd ε) := by
    change densityObjective H (covarianceKraus A C) θ (chart (Fin d) y) = _
    rw [hphysical, ownerObjective_eq_densityObjective H A hA hC θ]
  have heqstar : KSObjectiveChart.objective H (covarianceKraus A C) θ (chart (Fin d)) xstar =
      ownerPotential H A C θ := by
    have he : chart (Fin d) xstar = optimizer H A C θ hd := (chartEquiv (Fin d)).apply_symm_apply _
    change densityObjective H (covarianceKraus A C) θ (chart (Fin d) xstar) = _
    rw [he, ownerPotential_eq_optimizer H A hA hC θ hd,
      ownerObjective_eq_densityObjective H A hA hC θ]
  rw [heqy, heqstar] at hv
  have hpsd := (Matrix.PosDef.one.smul ha).add_posSemidef (Matrix.le_iff.mp hfeas.2.1)
  have hpsd' : (densityReport H A C θ hd ε).PosSemidef := by
    simpa only [a, add_sub_cancel] using hpsd.posSemidef
  have heval := KSNumericalOwnerObjective.report_accuracy H A hA hC θ hpsd'
    (by linarith : 0 < ε / 2)
  have htri := abs_sub_le (report H A C θ hd ε)
    (ownerObjective H A C θ (densityReport H A C θ hd ε)) (ownerPotential H A C θ)
  change |report H A C θ hd ε - ownerObjective H A C θ (densityReport H A C θ hd ε)| ≤ ε / 2 at heval
  linarith

end MatrixSpencer.KSNumericalOwnerPotential
