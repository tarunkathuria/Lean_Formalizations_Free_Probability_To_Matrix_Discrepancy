import MatrixSpencer.MSManuscriptNumericalEpochLedger
import MatrixSpencer.MSConvexSupportedPreparation

/-! The original square walk with convex owner-value queries substituted.
The state, invariants, tuning constants and non-query primitives remain original. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexNumericalEpochLedger
open MSManuscriptNumericalEpochLedger MSManuscriptSupportedOwner MSManuscriptSupportedGamma MSManuscriptSupportedPaid
variable [MSConvexOwnerValue.Oracle]
variable {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
attribute [local irreducible] ownerPotential

theorem afterPrepare_invariant (P : Parameters N d) (hP : P.Valid)
    {ε E₀ : ℝ} {s : State N} (hs : Invariant ε P.floor E₀ s)
    {y : Owner N × ℕ} (ho : MSConvexSupportedPreparation.output P s.owner=some y) :
    Invariant ε P.floor E₀ (afterPrepare P s y) := by
  have hc := MSConvexSupportedPreparation.output_sound P hP s.owner
    ⟨hs.owner_valid,hs.owner_le_one,hs.dim_le⟩ ho
  have hv := hc.state P hP ⟨hs.owner_valid,hs.owner_le_one,hs.dim_le⟩
  have hnonneg : 0≤realTrace s.owner.physical-realTrace y.1.physical-paidSize P*(y.2:ℝ) := by
    linarith [hc.trace_paid]
  refine ⟨hs.regular,hv.1,hv.2.1,hv.2.2,hs.time_nonneg,hs.variance_nonneg,
    add_nonneg hs.paid_nonneg (mul_nonneg (paidSize_pos P hP).le (Nat.cast_nonneg _)),
    add_nonneg hs.dust_nonneg hnonneg,hs.rounding_nonneg,?_,hs.variance_le,hs.variance_ge,?_,
    hs.rounding_le,hs.norm_progress⟩
  · change realTrace y.1.physical+(s.paid+paidSize P*(y.2:ℝ))+
      (s.dust+(realTrace s.owner.physical-realTrace y.1.physical-paidSize P*(y.2:ℝ)))+s.variance=N
    linarith [hs.trace_balance]
  · have hdim : N-y.1.dim=(N-s.owner.dim)+(s.owner.dim-y.1.dim) := by
      have hi:=hs.dim_le; have hj:=hc.dim_le; omega
    change s.dust+(realTrace s.owner.physical-realTrace y.1.physical-paidSize P*(y.2:ℝ))≤
      4*P.floor*(N-y.1.dim:ℕ)
    rw [hdim,Nat.cast_add]
    linarith [hs.dust_le,hc.trace_loss]

end MatrixSpencer.MSConvexNumericalEpochLedger
