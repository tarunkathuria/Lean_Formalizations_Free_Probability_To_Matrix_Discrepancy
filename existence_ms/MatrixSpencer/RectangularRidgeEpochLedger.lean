import MatrixSpencer.RectangularRidgePreparationRun
import MatrixSpencer.MSManuscriptNumericalEpochLedger

/-!
# Pathwise bookkeeping for the actual rectangular ridge preparation

The cube state and matched-move bookkeeping are independent of the potential.
They are reused literally. The preparation transition below instead executes
the ridge preparation and charges its proved paid and discarded trace losses.
-/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.RectangularRidgeEpochLedger
open MSManuscriptSupportedOwner MSManuscriptNumericalEpochLedger
open RectangularRidgePreparationData
variable {N d : ℕ} [Nonempty (Fin d)]
set_option maxHeartbeats 1000000

/-- Only covariance preparation changes; cube position and operational time
are preserved exactly. -/
def afterPrepare (P : Parameters N d) (s : MSManuscriptNumericalEpochLedger.State N)
    (y : Owner N × ℕ) : MSManuscriptNumericalEpochLedger.State N :=
  {s with
    owner := y.1,
    paid := s.paid + paidSize P * (y.2 : ℝ),
    dust := s.dust + (realTrace s.owner.physical - realTrace y.1.physical - paidSize P * (y.2 : ℝ))}

/-- Every state invariant is preserved by the actual completed ridge preparation. -/
theorem afterPrepare_invariant (P : Parameters N d) (hP : P.Valid) (R : Report P)
    {ε E₀ : ℝ} {s : MSManuscriptNumericalEpochLedger.State N}
    (hs : Invariant ε floor E₀ s) {y : Owner N × ℕ}
    (ho : RectangularRidgePreparationRun.output P R s.owner = some y) :
    Invariant ε floor E₀ (afterPrepare P s y) := by
  have hc := RectangularRidgePreparationRun.output_sound P hP R s.owner
    ⟨hs.owner_valid, hs.owner_le_one, hs.dim_le⟩ ho
  have hv := hc.state P ⟨hs.owner_valid, hs.owner_le_one, hs.dim_le⟩
  have hnonneg : 0 ≤ realTrace s.owner.physical - realTrace y.1.physical - paidSize P * (y.2 : ℝ) := by
    linarith [hc.trace_paid]
  refine ⟨hs.regular, hv.1, hv.2.1, hv.2.2, hs.time_nonneg, hs.variance_nonneg,
    add_nonneg hs.paid_nonneg (mul_nonneg (paidSize_pos P).le (Nat.cast_nonneg _)),
    add_nonneg hs.dust_nonneg hnonneg, hs.rounding_nonneg, ?_, hs.variance_le, hs.variance_ge, ?_,
    hs.rounding_le, hs.norm_progress⟩
  · change realTrace y.1.physical + (s.paid + paidSize P * (y.2 : ℝ)) +
      (s.dust + (realTrace s.owner.physical - realTrace y.1.physical - paidSize P * (y.2 : ℝ))) +
        s.variance = N
    linarith [hs.trace_balance]
  · have hdim : N - y.1.dim = (N - s.owner.dim) + (s.owner.dim - y.1.dim) := by
      have hi := hs.dim_le
      have hj := hc.dim_le
      omega
    change s.dust + (realTrace s.owner.physical - realTrace y.1.physical - paidSize P * (y.2 : ℝ)) ≤
      4 * floor * ((N - y.1.dim : ℕ) : ℝ)
    rw [hdim, Nat.cast_add]
    linarith [hs.dust_le, hc.trace_loss]

/-- Preparation does not alter the centered movement or threshold snaps. -/
theorem centered_afterPrepare (P : Parameters N d)
    {s : MSManuscriptNumericalEpochLedger.State N} {x₀ : EuclideanSpace ℝ (Fin N)}
    (hs : CenteredInvariant x₀ s) (y : Owner N × ℕ) :
    CenteredInvariant x₀ (afterPrepare P s y) := hs

@[simp] theorem afterPrepare_time (P : Parameters N d)
    (s : MSManuscriptNumericalEpochLedger.State N) (y : Owner N × ℕ) :
    (afterPrepare P s y).time = s.time := rfl

end MatrixSpencer.RectangularRidgeEpochLedger
