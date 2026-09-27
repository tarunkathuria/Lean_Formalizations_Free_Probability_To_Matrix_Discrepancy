import MatrixSpencer.KSDebitPreparation
import MatrixSpencer.KSDebitFullRetirement

/-!
# The actual numerical full-cube preparation has a live margin

The finite retirement loop's reported tests imply rejection of each actual
transport query, with frozen zero owners retained in the full original family.
The proved debit-assisted retirement inequality therefore supplies the strict
live margin required by the symmetric movement. No optimizer, transport,
potential minimum, or boundary-margin hypothesis is supplied to the result.
The accuracy of the finite value-report algorithm remains to be constructed.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitPreparedMargin

open KSDebitPreparation KSPotentialModels KSDebitActualRetirement
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

def stateCenter (v : Fin N → n → ℂ) (δ η : ℝ) (x : Fin N → ℝ) :=
  KSDebitCenter.center (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x)
    (KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x)

theorem statePotential_eq (v : Fin N → n → ℂ) (δ η θ : ℝ) (x : Fin N → ℝ) :
    statePotential v δ η θ x = value (stateCenter v δ η x) v (naturalOwners 64 x) θ := rfl

theorem center_update_debit (H B A : Matrix n n ℂ) (t δ : ℝ) :
    KSDebitCenter.center (H + t • A) (B + δ • A) =
      KSDebitCenter.center H B + t • signedLift A - δ • KSSpinSource.doubled A := by
  ext i j
  cases i <;> cases j <;>
    simp [KSDebitCenter.center, signedLift, KSSpinSource.doubled, Matrix.fromBlocks,
      smul_add, smul_neg] <;> ring

theorem queryPotential_eq_queriedValue (v : Fin N → n → ℂ) (δ η θ : ℝ)
    (x : Fin N → ℝ) (c : Retirement.Candidate N) :
    queryPotential v δ η θ x c =
      queriedValue (stateCenter v δ η x) v (naturalOwners 64 x) θ c.1
        (Retirement.endpoint 1 c.2 - x c.1) δ := by
  unfold queryPotential KSDebitPotential.potential
  change ownerPotential (KSDebitCenter.center
      (KSPotentialModels.center _ (Function.update x c.1 (Retirement.endpoint 1 c.2))) _)
      _ (KSSpinSource.coefficientCovariance
        (naturalOwners 64 (Function.update x c.1 (Retirement.endpoint 1 c.2)))) θ = _
  rw [KSPotentialModels.center_update, naturalOwners_update_endpoint 64 x c.1 (endpoint_isSign c.2),
    center_update_debit]
  rfl

def nearestCandidate (x : Fin N → ℝ) (i : Fin N) : Retirement.Candidate N :=
  (i, decide (0 ≤ x i))

theorem nearestCandidate_endpoint (x : Fin N → ℝ) (i : Fin N) :
    Retirement.endpoint 1 (nearestCandidate x i).2 = nearestSign (x i) := by
  classical
  by_cases hi : 0 ≤ x i <;> simp [nearestCandidate, Retirement.endpoint, nearestSign, hi]

/-- This supplies the full-family exact rejection premise for the actual
curvature proof, directly from the output of the numerical preparation. -/
theorem prepared_exact_rejection [Nonempty n] (v : Fin N → n → ℂ)
    (δ : ℝ) {η θ : ℝ} (hη : 0 ≤ η) (hθ : 0 < θ)
    (report : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ x ∈ ksCube 1, |report x - statePotential v δ η θ x| ≤ η / 8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) (i : Fin N)
    (hlive : |prepare η report x i| < 1) :
    let y := prepare η report x
    value (stateCenter v δ η y) v (naturalOwners 64 y) θ <
      queriedValue (stateCenter v δ η y) v (naturalOwners 64 y) θ i
        (nearestSign (y i) - y i) δ := by
  let y := prepare η report x
  have hr := query_rejected_after_prepare v δ hη hθ report haccuracy hx
    (nearestCandidate y i) hlive
  rw [statePotential_eq, queryPotential_eq_queriedValue, nearestCandidate_endpoint] at hr
  exact hr

/-- Every remaining live coordinate is strictly farther than `δ` from the
boundary. It is derived from numerical tests and genuine value estimates. -/
theorem prepared_live_margin [Nonempty n] (v : Fin N → n → ℂ)
    {δ η θ : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hθ : 0 < θ)
    (report : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ x ∈ ksCube 1, |report x - statePotential v δ η θ x| ≤ η / 8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) (i : Fin N)
    (hlive : |prepare η report x i| < 1) : δ < 1 - |prepare η report x i| := by
  have hy := prepare_mem_cube η report hx
  have hr := prepared_exact_rejection v δ hη hθ report haccuracy hx i hlive
  exact (KSDebitFullRetirement.rejected_nearest_margin_and_noSafe _ v
    (naturalOwners_nonneg (by norm_num) le_rfl hy) hθ i ⟨hy.1 i, hy.2 i⟩ hδ hr).1

end MatrixSpencer.KSDebitPreparedMargin
