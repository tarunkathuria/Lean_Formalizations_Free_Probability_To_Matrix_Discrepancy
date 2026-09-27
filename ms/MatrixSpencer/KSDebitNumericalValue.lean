import MatrixSpencer.KSOwnerReindex
import MatrixSpencer.KSNumericalOwnerPotential
import MatrixSpencer.KSDebitPreparation

/-!
# A finite numerical value report for the actual debit state

The two physical sign blocks are explicitly relabelled by `finSumFinEquiv`.
The report then runs the finite numerical owner optimization and objective
routine on those input matrices. Its definition contains no optimized
potential. The correctness proof compares it with the original full-density
state potential via the reindexing bijection.

For positive `η`, the specialization to tolerance `η / 8` supplies exactly
the value-accuracy field required by the debit walk controller. This module
does not construct the controller's movement direction or assert a runtime.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitNumericalValue

variable {N d : ℕ}

/-- The concrete coordinate map used by all numerical matrix operations. -/
def blockIndex (d : ℕ) : Fin (d + d) ≃ (Fin d ⊕ Fin d) := finSumFinEquiv.symm

/-- The actual signed center minus the debit stored at the current state. -/
def stateCenter (v : Fin N → Fin d → ℂ) (δ η : ℝ) (x : Fin N → ℝ) :
    Matrix (Fin (d + d)) (Fin (d + d)) ℂ :=
  (KSDebitCenter.center
    (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x)
    (KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x)).submatrix
      (blockIndex d) (blockIndex d)

/-- Every original atom retains all four of its spin-source labels. -/
def stateFamily (v : Fin N → Fin d → ℂ) :
    (Fin N × Fin 4) → Matrix (Fin (d + d)) (Fin (d + d)) ℂ :=
  fun j => (KSSpinSource.family (fun i => KSRankOne.atom (v i)) j).submatrix
    (blockIndex d) (blockIndex d)

/-- The coefficient matrix is computed from the current natural owner weights. -/
def stateCovariance (x : Fin N → ℝ) : Matrix (Fin N × Fin 4) (Fin N × Fin 4) ℝ :=
  KSSpinSource.coefficientCovariance (KSPotentialModels.naturalOwners 64 x)

/-- Finite physical optimization and evaluation, at the requested value tolerance. -/
def stateReport (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0 < d)
    (ε : ℝ) (x : Fin N → ℝ) : ℝ :=
  KSNumericalOwnerPotential.report (stateCenter v δ η x) (stateFamily v)
    (stateCovariance x) θ (by omega : 0 < d + d) ε

theorem stateCenter_isHermitian (v : Fin N → Fin d → ℂ)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (x : Fin N → ℝ) :
    (stateCenter v δ η x).IsHermitian := by
  exact (KSDebitCenter.center_isHermitian_of_posSemidef
    (KSPotentialModels.center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) x)
    (KSDebitBudget.debit_posSemidef _ (fun i => KSRankOne.atom_posSemidef (v i))
      hδ hη x)).submatrix (blockIndex d)

theorem stateFamily_isHermitian (v : Fin N → Fin d → ℂ) (j : Fin N × Fin 4) :
    (stateFamily v j).IsHermitian :=
  (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) j).submatrix
    (blockIndex d)

theorem stateCovariance_posSemidef {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    (stateCovariance x).PosSemidef :=
  KSSpinSource.coefficientCovariance_posSemidef
    (KSPotentialModels.naturalOwners_nonneg (by norm_num) le_rfl hx)

/-- Equality with the original potential over the entire doubled density domain. -/
theorem ownerPotential_eq_statePotential (v : Fin N → Fin d → ℂ)
    (δ η θ : ℝ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    ownerPotential (stateCenter v δ η x) (stateFamily v) (stateCovariance x) θ =
      KSDebitPreparation.statePotential v δ η θ x := by
  exact KSOwnerReindex.ownerPotential_reindex _ _
    (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)))
    (stateCovariance_posSemidef hx) θ (blockIndex d)

/-- No oracle premise: accuracy follows from the stated input conditions. -/
theorem stateReport_accuracy (v : Fin N → Fin d → ℂ) {δ η θ ε : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hθ : 0 < θ) (hε : 0 < ε) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    |stateReport v δ η θ hd ε x - KSDebitPreparation.statePotential v δ η θ x| ≤ ε := by
  have h := KSNumericalOwnerPotential.report_accuracy
    (stateCenter v δ η x) (stateCenter_isHermitian v hδ hη x)
    (stateFamily v) (stateFamily_isHermitian v) (stateCovariance_posSemidef hx)
    hθ hε (by omega : 0 < d + d)
  rw [ownerPotential_eq_statePotential v δ η θ hx] at h
  exact h

/-- The callable value procedure used in the retirement controller. -/
def controllerReport (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0 < d) :
    (Fin N → ℝ) → ℝ := stateReport v δ η θ hd (η / 8)

/-- This has the exact shape of `KSDebitWalkRun.Controller.accuracy`. -/
theorem controller_accuracy (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 < η) (hθ : 0 < θ) (hd : 0 < d) :
    ∀ x ∈ ksCube 1, |controllerReport v δ η θ hd x -
      KSDebitPreparation.statePotential v δ η θ x| ≤ η / 8 := by
  intro x hx
  exact stateReport_accuracy v hδ hη.le hθ (div_pos hη (by norm_num)) hd hx

end MatrixSpencer.KSDebitNumericalValue
