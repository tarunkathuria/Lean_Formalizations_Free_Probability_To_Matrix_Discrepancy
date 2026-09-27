import MatrixSpencer.KSConvexValueOracle
import MatrixSpencer.KSSpinSource
import MatrixSpencer.KSDebitPreparation

/-!
# Full-cube debit reports from the permitted convex value solver

Each value query explicitly builds the polynomial-size affine PSD program.
Only the solver's accuracy at an attained affine maximum is assumed. The
report remains valid at singular sources and zero owners.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullConvexOracleValue

variable {N d : ℕ}

def blockIndex (d : ℕ) : Fin (d + d) ≃ (Fin d ⊕ Fin d) := finSumFinEquiv.symm

/-- General spin-source report, with the matrix debit already in `H`. -/
def spinReport (O : KSConvexValueOracle.Solver)
    (H : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ)
    (v : Fin N → Fin d → ℂ) (c : Fin N → ℝ) (hd : 0 < d) (θ ν : ℝ) : ℝ :=
  KSConvexValueOracle.reindexedOwnerReport O ⟨0, by omega⟩ (blockIndex d) H
    (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
    (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)))
    (KSSpinSource.coefficientCovariance (fun i => max 0 (c i)))
    (KSSpinSource.coefficientCovariance_posSemidef (fun _ => le_max_left _ _))
    (by omega) θ ν

theorem spinReport_accuracy (O : KSConvexValueOracle.Solver)
    (H : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ)
    (v : Fin N → Fin d → ℂ) (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hd : 0 < d) {θ ν : ℝ} (hθ : 0 < θ) (hν : 0 < ν) :
    |spinReport O H v c hd θ ν - ownerPotential H
      (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) θ| ≤ ν := by
  have h := KSConvexValueOracle.reindexedOwnerReport_accuracy O
    (a := (⟨0, by omega⟩ : Fin (d+d))) (blockIndex d) H
    (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
    (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)))
    (KSSpinSource.coefficientCovariance (fun i => max 0 (c i)))
    (KSSpinSource.coefficientCovariance_posSemidef (fun _ => le_max_left _ _))
    (by omega) hθ hν
  have he : (fun i => max 0 (c i)) = c := funext (fun i => max_eq_right (hc i))
  change |spinReport O H v c hd θ ν - _| ≤ ν at h
  rwa [he] at h

/-- The report's center is the signed center minus exactly the stored debit. -/
def stateReport (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0 < d)
    (ν : ℝ) (x : Fin N → ℝ) : ℝ :=
  spinReport O (KSDebitCenter.center
    (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x)
    (KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x))
    v (KSPotentialModels.naturalOwners 64 x) hd θ ν

/-- Primitive-input accuracy for every actual cube state. -/
theorem stateReport_accuracy (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (δ η : ℝ)
    {θ ν : ℝ} (hθ : 0 < θ) (hν : 0 < ν) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    |stateReport O v δ η θ hd ν x - KSDebitPreparation.statePotential v δ η θ x| ≤ ν :=
  spinReport_accuracy O _ v _ (KSPotentialModels.naturalOwners_nonneg (by norm_num) le_rfl hx)
    hd hθ hν

/-- This convex value report is used for all retirement tests. -/
def controllerReport (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0 < d) :
    (Fin N → ℝ) → ℝ := stateReport O v δ η θ hd (η / 8)

theorem controller_accuracy (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (δ : ℝ)
    {η θ : ℝ} (hη : 0 < η) (hθ : 0 < θ) (hd : 0 < d) :
    ∀ x ∈ ksCube 1, |controllerReport O v δ η θ hd x -
      KSDebitPreparation.statePotential v δ η θ x| ≤ η / 8 := by
  intro x hx
  exact stateReport_accuracy O v δ η hθ (div_pos hη (by norm_num)) hd hx

/-- The actual preparation using convex value queries. -/
def prepare (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0 < d)
    (x : Fin N → ℝ) : Fin N → ℝ :=
  KSDebitPreparation.prepare η (controllerReport O v δ η θ hd) x

theorem prepare_mem_cube (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) : prepare O v δ η θ hd x ∈ ksCube 1 :=
  KSDebitPreparation.prepare_mem_cube _ _ hx

theorem prepare_nonincreasing (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (δ : ℝ)
    {η θ : ℝ} (hη : 0 < η) (hθ : 0 < θ) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    KSDebitPreparation.statePotential v δ η θ (prepare O v δ η θ hd x) ≤
      KSDebitPreparation.statePotential v δ η θ x :=
  KSDebitPreparation.prepare_nonincreasing hη.le _ _ (controller_accuracy O v δ hη hθ hd) hx

end MatrixSpencer.KSFullConvexOracleValue
