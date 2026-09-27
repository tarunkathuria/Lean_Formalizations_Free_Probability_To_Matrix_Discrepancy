import MatrixSpencer.RectangularRidgeEpochLedger
import MatrixSpencer.RectangularRidgeLiveShort
import SimpleMS.RelativeLiveTrace

/-!
# Epoch invariants with fixed original labels and a separate live count

The actual center retains every original coordinate. Only covariance support,
trace budget and newly frozen labels use the live count of the current epoch.
This module proves the actual preparation and matched coordinate movement
preserve that ledger; it does not reset or discard frozen matrix contributions.
-/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.RectangularRidgeLiveEpochLedger
open MSManuscriptSupportedOwner
open MSManuscriptNumericalEpochLedger (State Q Draws afterMove)
open RectangularRidgePreparationData
variable {N d : ℕ}
set_option maxHeartbeats 1200000

structure Invariant (ε δ E₀ : ℝ) (ℓ : ℕ) (F₀ : Finset (Fin N)) (s : State N) : Prop where
  regular : CubeRegular ε s.point
  owner_valid : s.owner.Valid δ
  owner_le_one : s.owner.physical ≤ 1
  dim_le : s.owner.dim ≤ ℓ
  annihilates : ∀ i ∈ F₀, s.owner.physical *ᵥ Pi.single i 1 = 0
  frozen_subset : F₀ ⊆ frozenCoordinates s.point
  time_nonneg : 0 ≤ s.time
  variance_nonneg : 0 ≤ s.variance
  paid_nonneg : 0 ≤ s.paid
  dust_nonneg : 0 ≤ s.dust
  rounding_nonneg : 0 ≤ s.rounding
  trace_balance : realTrace s.owner.physical + s.paid + s.dust + s.variance = ℓ
  variance_le : s.variance ≤ ℓ * s.time
  variance_ge : (ℓ : ℝ) / 16 * s.time ≤ s.variance
  dust_le : s.dust ≤ 4 * δ * ((ℓ - s.owner.dim : ℕ) : ℝ)
  rounding_le : s.rounding ≤ ε * ((frozenCoordinates s.point \ F₀).card : ℝ)
  norm_progress : E₀ + s.variance ≤ ‖s.point‖ ^ 2

/-- The actual short covariance has trace bounded by this epoch's live count. -/
theorem covariance_trace_le {ε δ E₀ : ℝ} {ℓ : ℕ} {F₀ : Finset (Fin N)}
    {s : State N} (hδ : 0 ≤ δ) (hs : Invariant ε δ E₀ ℓ F₀ s) : realTrace (Q s) ≤ ℓ := by
  have hc := hs.owner_valid.physical_posSemidef s.owner hδ
  have hq := MSManuscriptNumericalCoordinateStep.covariance_le s.owner.physical hc s.point
  have ht := realTrace_nonneg (Matrix.le_iff.mp hq)
  rw [realTrace_sub] at ht
  change realTrace (MSManuscriptNumericalCoordinateStep.covariance s.owner.physical s.point) ≤ ℓ
  linarith [hs.trace_balance, hs.paid_nonneg, hs.dust_nonneg, hs.variance_nonneg]

/-- Preparation keeps the original frozen constraints and all live trace accounts. -/
theorem afterPrepare_of_certificate [Nonempty (Fin d)] (P : Parameters N d)
    {ε E₀ : ℝ} {ℓ : ℕ} {F₀ : Finset (Fin N)} (hℓN : ℓ ≤ N)
    {s : State N} (hs : Invariant ε floor E₀ ℓ F₀ s) {fuel : ℕ} {y : Owner N × ℕ}
    (hc : RectangularRidgePreparationRun.Certificate P s.owner fuel y) :
    Invariant ε floor E₀ ℓ F₀ (RectangularRidgeEpochLedger.afterPrepare P s y) := by
  have hO : RectangularRidgePreparationData.State s.owner :=
    ⟨hs.owner_valid, hs.owner_le_one, hs.dim_le.trans hℓN⟩
  have hv := hc.state P hO
  have hnonneg : 0 ≤ realTrace s.owner.physical - realTrace y.1.physical - paidSize P * (y.2 : ℝ) := by
    linarith [hc.trace_paid]
  have hann := RectangularRidgeLiveShort.annihilators_mono s.owner.physical y.1.physical
    (hv.1.physical_posSemidef _ (by norm_num [floor])) hc.below F₀ hs.annihilates
  refine ⟨hs.regular, hv.1, hv.2.1, hc.dim_le.trans hs.dim_le, hann, hs.frozen_subset,
    hs.time_nonneg, hs.variance_nonneg,
    add_nonneg hs.paid_nonneg (mul_nonneg (paidSize_pos P).le (Nat.cast_nonneg _)),
    add_nonneg hs.dust_nonneg hnonneg, hs.rounding_nonneg, ?_, hs.variance_le, hs.variance_ge, ?_,
    hs.rounding_le, hs.norm_progress⟩
  · change realTrace y.1.physical + (s.paid + paidSize P * (y.2 : ℝ)) +
      (s.dust + (realTrace s.owner.physical - realTrace y.1.physical - paidSize P * (y.2 : ℝ))) +
        s.variance = ℓ
    linarith [hs.trace_balance]
  · have hdim : ℓ - y.1.dim = (ℓ - s.owner.dim) + (s.owner.dim - y.1.dim) := by
      have hi := hs.dim_le
      have hj := hc.dim_le
      omega
    change s.dust + (realTrace s.owner.physical - realTrace y.1.physical - paidSize P * (y.2 : ℝ)) ≤
      4 * floor * ((ℓ - y.1.dim : ℕ) : ℝ)
    rw [hdim, Nat.cast_add]
    linarith [hs.dust_le, hc.trace_loss]

theorem afterPrepare_invariant [Nonempty (Fin d)] (P : Parameters N d) (hP : P.Valid) (R : Report P)
    {ε E₀ : ℝ} {ℓ : ℕ} {F₀ : Finset (Fin N)} (hℓN : ℓ ≤ N)
    {s : State N} (hs : Invariant ε floor E₀ ℓ F₀ s) {y : Owner N × ℕ}
    (ho : RectangularRidgePreparationRun.output P R s.owner = some y) :
    Invariant ε floor E₀ ℓ F₀ (RectangularRidgeEpochLedger.afterPrepare P s y) :=
  afterPrepare_of_certificate P hℓN hs
    (RectangularRidgePreparationRun.output_sound P hP R s.owner
      ⟨hs.owner_valid, hs.owner_le_one, hs.dim_le.trans hℓN⟩ ho)

/-- Actual matching, threshold rounding and support-preserving covariance
withdrawal maintain the ledger on every finite LDL draw. -/
theorem afterMove_invariant {ε δ E₀ : ℝ} {ℓ : ℕ} {F₀ : Finset (Fin N)}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) {s : State N} (hs : Invariant ε δ E₀ ℓ F₀ s)
    (hfloor : s.owner.Valid (2 * δ)) {h : ℝ} (hh : 0 ≤ h)
    (hsmall : h * Real.sqrt (N : ℝ) ≤ ε) (hh2 : h ^ 2 ≤ 1 / 2)
    (hq : (ℓ : ℝ) / 16 ≤ realTrace (Q s)) (z : Draws s) :
    Invariant ε δ E₀ ℓ F₀ (afterMove ε s h z) := by
  have hC := hs.owner_valid.physical_posSemidef s.owner hδ
  have hQ : (Q s).PosSemidef := MSManuscriptNumericalCoordinateStep.covariance_posSemidef _ hC _
  have hQC : Q s ≤ s.owner.physical := MSManuscriptNumericalCoordinateStep.covariance_le _ hC _
  have hqℓ := covariance_trace_le hδ hs
  have ht := MSManuscriptOwnerAdvance.trace s.owner hs.owner_valid (Q s) hQ hQC h
  have hn := MSManuscriptNumericalCoordinateStep.rounded_norm_gain hC hs.owner_le_one hs.regular hh hsmall z
  have hc := MSManuscriptNumericalCoordinateStep.rounding_cost_le_new_frozen hC hs.owner_le_one hε hs.regular hh hsmall z
  have hf := MSManuscriptNumericalCoordinateStep.frozen_subset hC ε s.point h z
  have hv := MSManuscriptOwnerAdvance.valid s.owner hδ hfloor (Q s) hQC hh2
  have hb := MSManuscriptOwnerAdvance.below s.owner hs.owner_valid (Q s) hQ hQC h
  have hann := RectangularRidgeLiveShort.annihilators_mono s.owner.physical
    (MSManuscriptOwnerAdvance.advance s.owner (Q s) h).physical (hv.physical_posSemidef _ hδ)
    hb F₀ hs.annihilates
  refine ⟨MSManuscriptNumericalCoordinateStep.rounded_regular hC hs.owner_le_one hs.regular hh hsmall z,
    hv, hb.trans hs.owner_le_one, hs.dim_le, hann, hs.frozen_subset.trans hf,
    add_nonneg hs.time_nonneg (sq_nonneg h),
    add_nonneg hs.variance_nonneg (mul_nonneg (sq_nonneg h) (realTrace_nonneg hQ)),
    hs.paid_nonneg, hs.dust_nonneg,
    add_nonneg hs.rounding_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)), ?_, ?_, ?_,
    hs.dust_le, ?_, ?_⟩
  · change realTrace (MSManuscriptOwnerAdvance.advance s.owner (Q s) h).physical + s.paid + s.dust +
      (s.variance + h ^ 2 * realTrace (Q s)) = ℓ
    rw [ht]
    linarith [hs.trace_balance]
  · change s.variance + h ^ 2 * realTrace (Q s) ≤ (ℓ : ℝ) * (s.time + h ^ 2)
    nlinarith [hs.variance_le, mul_le_mul_of_nonneg_left hqℓ (sq_nonneg h)]
  · change (ℓ : ℝ) / 16 * (s.time + h ^ 2) ≤ s.variance + h ^ 2 * realTrace (Q s)
    nlinarith [hs.variance_ge, mul_le_mul_of_nonneg_left hq (sq_nonneg h)]
  · have hcard := Finset.card_le_card hf
    have h0card := Finset.card_le_card hs.frozen_subset
    have h0newcard := Finset.card_le_card (hs.frozen_subset.trans hf)
    rw [Nat.cast_sub hcard] at hc
    have hold := hs.rounding_le
    rw [Finset.card_sdiff_of_subset hs.frozen_subset, Nat.cast_sub h0card] at hold
    change s.rounding + _ ≤ ε * ((frozenCoordinates
      (MSManuscriptNumericalCoordinateStep.rounded ε s.owner.physical s.point h z) \ F₀).card : ℝ)
    rw [Finset.card_sdiff_of_subset (hs.frozen_subset.trans hf), Nat.cast_sub h0newcard]
    nlinarith
  · change E₀ + (s.variance + h ^ 2 * realTrace (Q s)) ≤
      ‖MSManuscriptNumericalCoordinateStep.rounded ε s.owner.physical s.point h z‖ ^ 2
    change ‖s.point‖ ^ 2 + h ^ 2 * realTrace (Q s) ≤ _ at hn
    linarith [hs.norm_progress]

/-- Stop decisions use this epoch's new frozen labels and cleaning mass. -/
def Terminal (τ : ℝ) (ℓ : ℕ) (F₀ : Finset (Fin N)) (s : State N) : Prop :=
  τ ≤ s.time ∨ (ℓ : ℝ) / 64 ≤ ((frozenCoordinates s.point \ F₀).card : ℝ) ∨
    (ℓ : ℝ) / 64 < s.paid + s.dust

/-- The next concrete uniform spectral distribution is normalized whenever the current
live epoch has not met a stopping test. -/
theorem short_trace_lower {ε δ E₀ τ : ℝ} {ℓ : ℕ} {F₀ : Finset (Fin N)}
    (hδ : 0 ≤ δ) {s : State N} (hs : Invariant ε δ E₀ ℓ F₀ s)
    (hℓ : 32 ≤ ℓ) (hτ : τ ≤ 1 / 3) (hnt : ¬Terminal τ ℓ F₀ s) :
    (ℓ : ℝ) / 16 ≤ realTrace (Q s) ∧ 0 < realTrace (Q s) := by
  have hh := not_or.mp hnt
  have hf := not_or.mp hh.2
  have ht : s.time < τ := lt_of_not_ge hh.1
  have hp : s.paid + s.dust ≤ (ℓ : ℝ) / 64 := le_of_not_gt hf.2
  have hF : ((frozenCoordinates s.point \ F₀).card : ℝ) ≤ (ℓ : ℝ) / 64 := (lt_of_not_ge hf.1).le
  have hrank : s.owner.physical.rank ≤ s.owner.dim := by
    unfold MSManuscriptSupportedOwner.Owner.physical
    exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width s.owner.frame))
  exact SimpleMS.RelativeLiveTrace.trace_positive_of_ledger
    (hs.owner_valid.physical_posSemidef _ hδ) hs.owner_le_one F₀ (frozenCoordinates s.point)
    s.point ℓ (s.paid+s.dust) s.variance τ (by exact_mod_cast hℓ) hs.annihilates
    (by exact_mod_cast hrank.trans hs.dim_le) (by linarith [hs.trace_balance]) hp
    (hs.variance_le.trans (mul_le_mul_of_nonneg_left ht.le (Nat.cast_nonneg ℓ))) hτ hF

end MatrixSpencer.RectangularRidgeLiveEpochLedger
