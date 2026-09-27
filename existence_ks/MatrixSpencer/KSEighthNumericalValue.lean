import MatrixSpencer.KSOwnerReindex
import MatrixSpencer.KSNumericalOwnerPotential
import MatrixSpencer.KSPotentialModels

/-!
# Finite value reports for the actual eighth-cube potential

The numerical data use the two independent sign-block families of the eighth
proof. Their optimized value equals the original signed-pencil potential.
The center always contains every original coefficient. State reports delete
boundary owners, while retained-mask reports keep a fixed live mask for finite
Hessian queries. Both call the existing finite physical density optimization;
no exact optimizer is evaluated by a report definition.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthNumericalValue

open KSPotentialModels
variable {N d : ℕ}

def blockIndex (d : ℕ) : Fin (d+d) ≃ (Fin d ⊕ Fin d) := finSumFinEquiv.symm

def physicalCenter (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) :
    Matrix (Fin (d+d)) (Fin (d+d)) ℂ :=
  (signedLift (center (fun i => KSRankOne.atom (v i)) x)).submatrix
    (blockIndex d) (blockIndex d)

def physicalFamily (v : Fin N → Fin d → ℂ) :
    (Fin N × Bool) → Matrix (Fin (d+d)) (Fin (d+d)) ℂ :=
  fun j => (KSIndependentSource.family (fun i => KSRankOne.atom (v i)) j).submatrix
    (blockIndex d) (blockIndex d)

/-- Actual finite optimization, with arbitrary explicitly supplied owner weights. -/
def ownerReport (v : Fin N → Fin d → ℂ) (θ : ℝ) (hd : 0 < d)
    (c : Fin N → ℝ) (ν : ℝ) (x : Fin N → ℝ) : ℝ :=
  KSNumericalOwnerPotential.report (physicalCenter v x) (physicalFamily v)
    (KSIndependentSource.coefficientCovariance c) θ (by omega : 0 < d+d) ν

def stateReport (v : Fin N → Fin d → ℂ) (θ : ℝ) (hd : 0 < d)
    (ν : ℝ) (x : Fin N → ℝ) : ℝ :=
  ownerReport v θ hd (truncatedOwners (1/8) 64 x) ν x

/-- Fixed-mask reports retain owners even at query endpoints. -/
def retainedReport (v : Fin N → Fin d → ℂ) (θ : ℝ) (hd : 0 < d)
    (L : Finset (Fin N)) (ν : ℝ) (x : Fin N → ℝ) : ℝ :=
  ownerReport v θ hd (maskedOwners 64 L x) ν x

theorem physicalCenter_isHermitian (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) :
    (physicalCenter v x).IsHermitian :=
  (signedLift_isHermitian (center_isHermitian _
    (fun i => KSRankOne.atom_isHermitian (v i)) x)).submatrix (blockIndex d)

theorem physicalFamily_isHermitian (v : Fin N → Fin d → ℂ) (j : Fin N × Bool) :
    (physicalFamily v j).IsHermitian :=
  (KSIndependentSource.family_isHermitian _
    (fun i => KSRankOne.atom_isHermitian (v i)) j).submatrix (blockIndex d)

/-- Accuracy against the original signed-pencil owner potential, with no oracle input. -/
theorem ownerReport_accuracy (v : Fin N → Fin d → ℂ) {θ ν : ℝ}
    (hθ : 0 < θ) (hν : 0 < ν) (hd : 0 < d) (c : Fin N → ℝ)
    (hc : ∀ i, 0 ≤ c i) (x : Fin N → ℝ) :
    |ownerReport v θ hd c ν x - commonPotential (fun i => KSRankOne.atom (v i)) θ x c| ≤ ν := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hC := KSIndependentSource.coefficientCovariance_posSemidef hc
  have hr := KSNumericalOwnerPotential.report_accuracy (physicalCenter v x)
    (physicalCenter_isHermitian v x) (physicalFamily v) (physicalFamily_isHermitian v)
    hC hθ hν (by omega : 0 < d+d)
  have he := KSOwnerReindex.ownerPotential_reindex
    (signedLift (center (fun i => KSRankOne.atom (v i)) x))
    (KSIndependentSource.family (fun i => KSRankOne.atom (v i)))
    (KSIndependentSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)))
    hC θ (blockIndex d)
  change ownerPotential (physicalCenter v x) (physicalFamily v)
    (KSIndependentSource.coefficientCovariance c) θ = _ at he
  rw [he] at hr
  rw [commonPotential, KSCommonSource.potential_eq_independent _ _
    (fun i => KSRankOne.atom_isHermitian (v i)) hc hθ]
  exact hr

theorem stateReport_accuracy (v : Fin N → Fin d → ℂ) {θ ν : ℝ}
    (hθ : 0 < θ) (hν : 0 < ν) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) :
    |stateReport v θ hd ν x - eighthPotential (fun i => KSRankOne.atom (v i)) θ x| ≤ ν :=
  ownerReport_accuracy v hθ hν hd _
    (maskedOwners_nonneg (by norm_num) (by norm_num) hx (live (1/8) x)) x

theorem retainedReport_accuracy (v : Fin N → Fin d → ℂ) {θ ν a : ℝ}
    (hθ : 0 < θ) (hν : 0 < ν) (hd : 0 < d) (L : Finset (Fin N))
    (ha : a ≤ 1) {x : Fin N → ℝ} (hx : x ∈ ksCube a) :
    |retainedReport v θ hd L ν x -
      commonPotential (fun i => KSRankOne.atom (v i)) θ x (maskedOwners 64 L x)| ≤ ν :=
  ownerReport_accuracy v hθ hν hd _ (maskedOwners_nonneg (by norm_num) ha hx L) x

end MatrixSpencer.KSEighthNumericalValue
