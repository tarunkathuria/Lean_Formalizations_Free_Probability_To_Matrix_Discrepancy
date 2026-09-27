import MatrixSpencer.RectangularRidgeLiveDomination
import MatrixSpencer.SigningExtraction

/-!
# Remaining mixed potential on the original coefficient universe

The center always contains every original coordinate, including the frozen
ones. Only the actual coordinate projection is reinstalled at a restart.
These are pointwise bounds and composition interfaces for accepted epochs;
they do not assume or assert an epoch success theorem.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeRemainingPotential
open RectangularRidgeLiveOwner
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
local instance ridgeRemainingCStar : CStarAlgebra (Matrix n n ℂ) := {}

def liveCount (x : EuclideanSpace ℝ (Fin N)) : ℕ := count (frozenCoordinates x)

def potential (m : ℕ) (θ κ : ℝ) (offset : selfAdjoint (Matrix n n ℂ))
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  RectangularRidgeCovarianceCalculus.ownerPotential m (epochCenter offset A hA x) A
    (owner (frozenCoordinates x)).physical θ κ

theorem liveCount_eq (x : EuclideanSpace ℝ (Fin N)) :
    liveCount x = Fintype.card (PhaseRestriction.Live x) := by
  simp only [liveCount, count_eq, PhaseRestriction.live_card, Fintype.card_fin]

theorem liveCount_le (x : EuclideanSpace ℝ (Fin N)) : liveCount x ≤ N := count_le _

theorem projection_posSemidef (F : Finset (Fin N)) : (owner F).physical.PosSemidef :=
  covarianceLift_posSemidef (frame F) Matrix.PosSemidef.one

/-- Freezing additional coordinates decreases the actual coordinate projection. -/
theorem projection_antitone {F G : Finset (Fin N)} (hFG : F ⊆ G) :
    (owner G).physical ≤ (owner F).physical :=
  RectangularRidgeLiveDomination.covariance_le_projection _ (projection_posSemidef G)
    (owner_le_one G) F (fun i hi => owner_annihilates G i (hFG hi))

theorem liveCount_antitone {x y : EuclideanSpace ℝ (Fin N)}
    (hxy : frozenCoordinates x ⊆ frozenCoordinates y) : liveCount y ≤ liveCount x := by
  simp only [liveCount, count_eq]
  exact Nat.sub_le_sub_left (Finset.card_le_card hxy) N

variable [Nonempty n]

theorem base_le (m : ℕ) (θ κ : ℝ) (offset : selfAdjoint (Matrix n n ℂ))
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ (Fin N)) :
    RectangularRidgeOwnerBounds.basePotential m (epochCenter offset A hA x : Matrix n n ℂ) θ κ ≤
      potential m θ κ offset A hA x :=
  RectangularRidgeOwnerBounds.base_le_owner m _ A hA (projection_posSemidef _) θ κ

/-- Deletion keeps the full final center, including all frozen contributions. -/
theorem deletion_le (m : ℕ) (θ κ : ℝ) (offset : selfAdjoint (Matrix n n ℂ))
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {x y : EuclideanSpace ℝ (Fin N)} (hxy : frozenCoordinates x ⊆ frozenCoordinates y) :
    potential m θ κ offset A hA y ≤
      RectangularRidgeCovarianceCalculus.ownerPotential m (epochCenter offset A hA y)
        A (owner (frozenCoordinates x)).physical θ κ :=
  RectangularRidgeOwnerBounds.mono_covariance m _ A hA (projection_posSemidef _)
    (projection_posSemidef _) (projection_antitone hxy) θ κ

/-- Any PSD final covariance may be replaced by the new live projection,
at a cost depending only on the new live count. -/
theorem reinstall_le (m : ℕ) (θ κ : ℝ) (offset : selfAdjoint (Matrix n n ℂ))
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (x : EuclideanSpace ℝ (Fin N))
    {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef) :
    potential m θ κ offset A hA x -
      RectangularRidgeCovarianceCalculus.ownerPotential m (epochCenter offset A hA x) A C θ κ ≤
        2 * Real.sqrt (liveCount x : ℝ) := by
  have hp := RectangularRidgeLiveOwnerBounds.projection_excess_le
    (epochCenter offset A hA x) A hA hAn (frozenCoordinates x) m θ κ
  rw [RectangularRidgeOwnerBounds.owner_zero] at hp
  have hb := RectangularRidgeOwnerBounds.base_le_owner m (epochCenter offset A hA x) A hA hC θ κ
  change _ - _ ≤ 2 * Real.sqrt (count (frozenCoordinates x) : ℝ)
  unfold potential
  linarith

/-- A bound on the actual accepted certificate and saved tangent gives the
restart potential bound without resetting the accumulated center. -/
theorem accepted_epoch_reinstall (m : ℕ) (θ κ : ℝ)
    (offset : selfAdjoint (Matrix n n ℂ)) (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hAn : ∀ i, ‖A i‖ ≤ 1)
    (x y : EuclideanSpace ℝ (Fin N)) {C : Matrix (Fin N) (Fin N) ℝ}
    (hC : C.PosSemidef) {b : ℝ}
    (haccepted : RectangularRidgeCertificate.certificate (epochCenter offset A hA x : Matrix n n ℂ)
      A m θ κ (epochCenter offset A hA y) C +
        |RectangularRidgeCertificate.tangent (epochCenter offset A hA x : Matrix n n ℂ) m θ κ
          (epochCenter offset A hA y)| ≤ b) :
    potential m θ κ offset A hA y ≤ potential m θ κ offset A hA x + b +
      2 * Real.sqrt (liveCount y : ℝ) := by
  have ht := RectangularRidgeCertificate.certificate_terminal_le
    (epochCenter offset A hA x : Matrix n n ℂ) (epochCenter offset A hA y) A hA m θ κ
    (Cend := C) (projection_posSemidef (frozenCoordinates x))
    (RectangularRidgeCertificate.tangent (epochCenter offset A hA x : Matrix n n ℂ) m θ κ
      (epochCenter offset A hA y)) rfl
  have hr := reinstall_le m θ κ offset A hA hAn y hC
  change RectangularRidgeCovarianceCalculus.ownerPotential m _ A C θ κ -
    potential m θ κ offset A hA x ≤ _ at ht
  linarith

theorem initial_le {m : ℕ} (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hAn : ∀ i, ‖A i‖ ≤ 1) :
    potential m θ κ 0 A hA (0 : EuclideanSpace ℝ (Fin N)) ≤
      2 * Real.sqrt (N : ℝ) +
        (θ * (Fintype.card n : ℝ) ^ (1 / (2 ^ m : ℝ)) / (1 - 1 / (2 ^ m : ℝ)) +
          2 * κ * Real.sqrt (Fintype.card n : ℝ)) := by
  unfold potential
  rw [epochCenter_zero_zero]
  simpa only [norm_zero, zero_add, Fintype.card_fin] using
    RectangularRidgeOwnerBounds.le_norm_add m hm (Matrix.isHermitian_zero (n := n))
      A hA hAn (projection_posSemidef _) (owner_le_one _) hθ hκ

section Extraction
variable {D : ℕ}

/-- The ordinary two-sided spectral norm is bounded by the actual completed
mixed remaining potential on the original labels. -/
theorem spectralNorm_le [Nonempty (Fin D)] {m : ℕ} (hm : 1 ≤ m) {θ κ : ℝ}
    (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) (B : Fin N → CMatrix D)
    (hB : ∀ i, (B i).IsHermitian) (x : EuclideanSpace ℝ (Fin N)) (hx : liveCount x = 0) :
    spectralNorm (signedSum B (WithLp.ofLp x)) ≤
      potential m θ κ 0 (fun i => signedLift (B i))
        (fun i => signedLift_isHermitian (hB i)) x := by
  have hs := SigningExtraction.fullSigning_of_live_card_zero x ((liveCount_eq x).symm.trans hx)
  rw [spectralNorm_eq_scopedMatrixNorm]
  have hn := RectangularRidgeOwnerBounds.norm_le_signedLift_base m hm
    (signedSum_isHermitian_of_fullSigning B (WithLp.ofLp x) hB hs) hθ hκ
  have hb := base_le m θ κ 0 (fun i => signedLift (B i))
    (fun i => signedLift_isHermitian (hB i)) x
  rw [SigningExtraction.lifted_center_eq_signedLift B hB x] at hb
  exact hn.trans hb

theorem extract_signing (hD : 0 < D) {m : ℕ} (hm : 1 ≤ m) {θ κ : ℝ}
    (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) (B : Fin N → CMatrix D)
    (hB : ∀ i, (B i).IsHermitian) (x : EuclideanSpace ℝ (Fin N))
    (hx : liveCount x = 0) {bound : ℝ}
    (hb : potential m θ κ 0 (fun i => signedLift (B i))
      (fun i => signedLift_isHermitian (hB i)) x ≤ bound) :
    ∃ ε : Fin N → ℝ, IsFullSigning ε ∧ spectralNorm (signedSum B ε) ≤ bound := by
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  exact ⟨WithLp.ofLp x,
    SigningExtraction.fullSigning_of_live_card_zero x ((liveCount_eq x).symm.trans hx),
    (spectralNorm_le hm hθ hκ B hB x hx).trans hb⟩

end Extraction
end MatrixSpencer.RectangularRidgeRemainingPotential
