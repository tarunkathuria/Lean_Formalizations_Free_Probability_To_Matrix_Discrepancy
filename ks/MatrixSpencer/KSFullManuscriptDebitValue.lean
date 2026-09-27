import MatrixSpencer.KSFullManuscriptDiagonalValue
import MatrixSpencer.KSDebitPreparation



open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptDebitValue

variable {N d : ℕ}

def blockIndex (d : ℕ) : Fin (d + d) ≃ (Fin d ⊕ Fin d) := finSumFinEquiv.symm

/-- General spin-source report, with the matrix debit already in `H`. -/
def spinReport (H : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ)
    (v : Fin N → Fin d → ℂ) (c : Fin N → ℝ) (hd : 0 < d) (θ ν : ℝ) : ℝ :=
  KSFullManuscriptDiagonalValue.reindexedReport ⟨0, by omega⟩ (blockIndex d) H
    (KSSpinSource.family (fun i => KSRankOne.atom (v i))) (fun j => c j.1 / 2)
    (by omega) θ ν

theorem spinReport_accuracy (H : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ)
    (v : Fin N → Fin d → ℂ) (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hd : 0 < d) {θ ν : ℝ} (hθ : 0 ≤ θ) (hν : 0 < ν) :
    |spinReport H v c hd θ ν - ownerPotential H
      (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) θ| ≤ ν :=
  KSFullManuscriptDiagonalValue.reindexedReport_accuracy _ _ H _
    (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)))
    _ (fun j => div_nonneg (hc j.1) (by norm_num)) _ hθ hν

/-- The report's center is the signed center minus exactly the stored debit. -/
def stateReport (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0 < d)
    (ν : ℝ) (x : Fin N → ℝ) : ℝ :=
  spinReport (KSDebitCenter.center
    (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x)
    (KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x))
    v (KSPotentialModels.naturalOwners 64 x) hd θ ν

/-- Primitive-input accuracy for every actual cube state. -/
theorem stateReport_accuracy (v : Fin N → Fin d → ℂ) (δ η : ℝ)
    {θ ν : ℝ} (hθ : 0 ≤ θ) (hν : 0 < ν) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    |stateReport v δ η θ hd ν x - KSDebitPreparation.statePotential v δ η θ x| ≤ ν :=
  spinReport_accuracy _ v _ (KSPotentialModels.naturalOwners_nonneg (by norm_num) le_rfl hx)
    hd hθ hν

/-- This exact finite ellipsoid report is used for all retirement tests. -/
def controllerReport (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0 < d) :
    (Fin N → ℝ) → ℝ := stateReport v δ η θ hd (η / 8)

theorem controller_accuracy (v : Fin N → Fin d → ℂ) (δ : ℝ)
    {η θ : ℝ} (hη : 0 < η) (hθ : 0 ≤ θ) (hd : 0 < d) :
    ∀ x ∈ ksCube 1, |controllerReport v δ η θ hd x -
      KSDebitPreparation.statePotential v δ η θ x| ≤ η / 8 := by
  intro x hx
  exact stateReport_accuracy v δ η hθ (div_pos hη (by norm_num)) hd hx


def prepare (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0 < d)
    (x : Fin N → ℝ) : Fin N → ℝ :=
  KSDebitPreparation.prepare η (controllerReport v δ η θ hd) x

theorem prepare_mem_cube (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) : prepare v δ η θ hd x ∈ ksCube 1 :=
  KSDebitPreparation.prepare_mem_cube _ _ hx

theorem prepare_nonincreasing (v : Fin N → Fin d → ℂ) (δ : ℝ)
    {η θ : ℝ} (hη : 0 < η) (hθ : 0 ≤ θ) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    KSDebitPreparation.statePotential v δ η θ (prepare v δ η θ hd x) ≤
      KSDebitPreparation.statePotential v δ η θ x :=
  KSDebitPreparation.prepare_nonincreasing hη.le _ _ (controller_accuracy v δ hη hθ hd) hx

end MatrixSpencer.KSFullManuscriptDebitValue
