import MatrixSpencer.DyadicTsallisBounds
import MatrixSpencer.RegularizedFamilyDeletion
import MatrixSpencer.SigningExtraction
import MatrixSpencer.PhasePotential

/-!
# Pointwise initial and final bounds for the rectangular signing potential

The same physical dyadic regularizer is retained as coefficient labels
disappear. These are bounds on actual potentials and actual completed
points; no epoch, phase, or signing-existence premise is supplied here.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer
open PhaseRestriction

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance rectangularSigningPotentialCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance rectangularSigningPotentialSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstance

/-- The actual live-family potential with one globally fixed dyadic regularizer. -/
def rectangularRemainingPotential (m : ℕ) (θ : ℝ) (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (x : EuclideanSpace ℝ ι) : ℝ :=
  regularizedOwnerPotential (epochCenter offset A hA x) (restrictedFamily A x) 1
    (dyadicTsallisRegularizer m θ)

theorem regularizedBase_le_rectangularRemainingPotential [Nonempty n]
    (m : ℕ) (θ : ℝ) (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    regularizedBasePotential (epochCenter offset A hA x : Matrix n n ℂ)
      (dyadicTsallisRegularizer m θ) ≤ rectangularRemainingPotential m θ offset A hA x :=
  regularizedBasePotential_le_owner (epochCenter offset A hA x : Matrix n n ℂ)
    (restrictedFamily A x) (restrictedFamily_hermitian A hA x) Matrix.PosSemidef.one
    (dyadicTsallisRegularizer m θ) (continuousOn_density_dyadicTsallisRegularizer m θ)

/-- The physical dimension and original matrix count have separate initial contributions. -/
theorem rectangularRemainingPotential_zero_le [Nonempty n] {m : ℕ} (hm : 1 ≤ m)
    {θ : ℝ} (hθ : 0 ≤ θ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, ‖A i‖ ≤ 1) :
    rectangularRemainingPotential m θ 0 A hA (0 : EuclideanSpace ℝ ι) ≤
      2 * Real.sqrt (Fintype.card ι : ℝ) +
        θ * (Fintype.card n : ℝ) ^ (1 / (2 ^ m : ℝ)) / (1 - 1 / (2 ^ m : ℝ)) := by
  have hcard : Fintype.card (Live (0 : EuclideanSpace ℝ ι)) = Fintype.card ι := by
    rw [live_card]
    have hz : frozenCoordinates (0 : EuclideanSpace ℝ ι) = ∅ := by
      ext i
      simp [mem_frozenCoordinates, IsSign]
    simp [hz]
  unfold rectangularRemainingPotential
  rw [epochCenter_zero_zero]
  have hb := regularizedOwnerPotential_le_norm_add (Matrix.isHermitian_zero (n := n))
    (restrictedFamily A (0 : EuclideanSpace ℝ ι)) (restrictedFamily_hermitian A hA _)
    (restrictedFamily_contractions A hN _) Matrix.PosSemidef.one le_rfl
    (dyadicTsallisRegularizer m θ) (continuousOn_density_dyadicTsallisRegularizer m θ)
    (fun S hS => dyadicTsallisRegularizer_density_bound_reciprocal hm hθ hS)
  simpa only [norm_zero, zero_add, hcard] using hb

theorem rectangularRemainingPotential_le_oldFamily [Nonempty n]
    (m : ℕ) (θ : ℝ) (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {x z : EuclideanSpace ℝ ι}
    (h : frozenCoordinates x ⊆ frozenCoordinates z) :
    rectangularRemainingPotential m θ offset A hA z ≤
      regularizedOwnerPotential (epochCenter offset A hA z) (restrictedFamily A x) 1
        (dyadicTsallisRegularizer m θ) :=
  regularizedOwnerPotential_subfamily_le (epochCenter offset A hA z : Matrix n n ℂ)
    (restrictedFamily A x) (restrictedFamily_hermitian A hA x) (liveOfFrozenSubset h)
    (dyadicTsallisRegularizer m θ) (continuousOn_density_dyadicTsallisRegularizer m θ)

theorem rectangularRemainingPotential_lift_le [Nonempty n]
    (m : ℕ) (θ : ℝ) (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    rectangularRemainingPotential m θ offset A hA (liftPoint x y) ≤
      regularizedOwnerPotential (epochCenter (restrictedOffset offset A hA x) (restrictedFamily A x)
        (restrictedFamily_hermitian A hA x) y) (restrictedFamily A x) 1
          (dyadicTsallisRegularizer m θ) := by
  have h := rectangularRemainingPotential_le_oldFamily m θ offset A hA (frozen_subset_liftPoint x y)
  rwa [center_liftPoint] at h

theorem rectangularRemainingPotential_lift_le_nested [Nonempty n]
    (m : ℕ) (θ : ℝ) (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    rectangularRemainingPotential m θ offset A hA (liftPoint x y) ≤
      rectangularRemainingPotential m θ (restrictedOffset offset A hA x) (restrictedFamily A x)
        (restrictedFamily_hermitian A hA x) y := by
  unfold rectangularRemainingPotential
  rw [center_liftPoint]
  exact regularizedOwnerPotential_subfamily_le
    (epochCenter (restrictedOffset offset A hA x) (restrictedFamily A x)
      (restrictedFamily_hermitian A hA x) y : Matrix n n ℂ)
    (restrictedFamily (restrictedFamily A x) y)
    (restrictedFamily_hermitian (restrictedFamily A x) (restrictedFamily_hermitian A hA x) y)
    (liveLiftEmbedding x y) (dyadicTsallisRegularizer m θ)
    (continuousOn_density_dyadicTsallisRegularizer m θ)

theorem rectangularRemainingPotential_nested_start_le [Nonempty n]
    (m : ℕ) (θ : ℝ) (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    rectangularRemainingPotential m θ (restrictedOffset offset A hA x) (restrictedFamily A x)
        (restrictedFamily_hermitian A hA x) (restrictPoint x) ≤
      rectangularRemainingPotential m θ offset A hA x := by
  have hc := center_liftPoint offset A hA x (restrictPoint x)
  rw [liftPoint_restrictPoint] at hc
  unfold rectangularRemainingPotential
  rw [← hc]
  exact regularizedOwnerPotential_subfamily_le (epochCenter offset A hA x : Matrix n n ℂ)
    (restrictedFamily A x) (restrictedFamily_hermitian A hA x) (liveEmbedding (restrictPoint x))
    (dyadicTsallisRegularizer m θ) (continuousOn_density_dyadicTsallisRegularizer m θ)

omit [Fintype ι] [DecidableEq ι] in
/-- Any nonnegative continuous regularizer preserves the signed-lift spectral lower bound. -/
theorem norm_le_signedLift_regularizedBasePotential [Nonempty n] {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (R : Matrix (n ⊕ n) (n ⊕ n) ℂ → ℝ)
    (hR : ContinuousOn R densitySet) (hR0 : ∀ S ∈ densitySet, 0 ≤ R S) :
    ‖B‖ ≤ regularizedBasePotential (signedLift B) R := by
  obtain ⟨S, hS, hval⟩ := exists_signedLift_density_norm hB
  have hle := regularizedBaseObjective_le_potential (signedLift B) R hR hS
  have hnonneg := hR0 S hS
  unfold regularizedBaseObjective at hle
  rw [hval] at hle
  linarith

section Extraction
variable {N D : ℕ}

/-- Signed doubling changes only the physical dimension in the initial budget. -/
theorem lifted_rectangularRemainingPotential_zero_le [Nonempty (Fin D)]
    {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 ≤ θ)
    (B : Fin N → CMatrix D) (hB : ∀ i, (B i).IsHermitian)
    (hN : ∀ i, spectralNorm (B i) ≤ 1) :
    rectangularRemainingPotential m θ 0 (fun i => signedLift (B i))
      (fun i => signedLift_isHermitian (hB i)) (0 : EuclideanSpace ℝ (Fin N)) ≤
      2 * Real.sqrt (N : ℝ) +
        θ * (2 * (D : ℝ)) ^ (1 / (2 ^ m : ℝ)) / (1 - 1 / (2 ^ m : ℝ)) := by
  have hnorm : ∀ i, ‖signedLift (B i)‖ ≤ 1 := by
    intro i
    rw [signedLift_norm (hB i), ← spectralNorm_eq_scopedMatrixNorm]
    exact hN i
  have h := rectangularRemainingPotential_zero_le hm hθ (fun i => signedLift (B i))
    (fun i => signedLift_isHermitian (hB i)) hnorm
  simpa only [Fintype.card_fin, Fintype.card_sum, Nat.cast_add, two_mul] using h

/-- A completed point gives the original Euclidean spectral norm, without changing its labels. -/
theorem spectralNorm_le_rectangularRemainingPotential [Nonempty (Fin D)]
    {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 ≤ θ)
    (B : Fin N → CMatrix D) (hB : ∀ i, (B i).IsHermitian)
    (x : EuclideanSpace ℝ (Fin N)) (hx : Fintype.card (Live x) = 0) :
    spectralNorm (signedSum B (WithLp.ofLp x)) ≤
      rectangularRemainingPotential m θ 0 (fun i => signedLift (B i))
        (fun i => signedLift_isHermitian (hB i)) x := by
  rw [spectralNorm_eq_scopedMatrixNorm]
  have hnorm := norm_le_signedLift_regularizedBasePotential
    (signedSum_isHermitian_of_fullSigning B (WithLp.ofLp x) hB
      (SigningExtraction.fullSigning_of_live_card_zero x hx))
    (dyadicTsallisRegularizer m θ) (continuousOn_density_dyadicTsallisRegularizer m θ)
    (fun S hS => dyadicTsallisRegularizer_nonneg hm hθ hS.1)
  have hbase := regularizedBase_le_rectangularRemainingPotential m θ 0
    (fun i => signedLift (B i)) (fun i => signedLift_isHermitian (hB i)) x
  rw [SigningExtraction.lifted_center_eq_signedLift B hB x] at hbase
  exact hnorm.trans hbase

/-- Extraction uses any pointwise potential bound, without assuming a walk or completion theorem. -/
theorem extract_signing_of_rectangularRemainingPotential_le (hD : 0 < D)
    {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 ≤ θ)
    (B : Fin N → CMatrix D) (hB : ∀ i, (B i).IsHermitian)
    (x : EuclideanSpace ℝ (Fin N)) (hx : Fintype.card (Live x) = 0) {bound : ℝ}
    (hpotential : rectangularRemainingPotential m θ 0 (fun i => signedLift (B i))
      (fun i => signedLift_isHermitian (hB i)) x ≤ bound) :
    ∃ ε : Fin N → ℝ, IsFullSigning ε ∧ spectralNorm (signedSum B ε) ≤ bound := by
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  exact ⟨WithLp.ofLp x, SigningExtraction.fullSigning_of_live_card_zero x hx,
    (spectralNorm_le_rectangularRemainingPotential hm hθ B hB x hx).trans hpotential⟩

end Extraction
end MatrixSpencer
