import MatrixSpencer.PhaseRestriction
import MatrixSpencer.FamilyDeletion
import MatrixSpencer.EpochTree

/-! Actual potential monotonicity when live labels disappear, and the resulting
ambient successful-epoch statement. -/
open Set Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
namespace PhaseRestriction
noncomputable section
set_option maxHeartbeats 800000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance phasePotentialCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance phasePotentialPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- The new live family embeds into the old one when old frozen coordinates remain frozen. -/
def liveOfFrozenSubset {x z : EuclideanSpace ℝ ι}
    (h : frozenCoordinates x ⊆ frozenCoordinates z) : Live z ↪ Live x where
  toFun i := ⟨i, fun hi => i.property (h hi)⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun q : Live x => (q : ι)) hij

/-- Removing any newly frozen original labels decreases the actual identity-owner potential. -/
theorem remainingPotential_le_oldFamily (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {x z : EuclideanSpace ℝ ι}
    (h : frozenCoordinates x ⊆ frozenCoordinates z) :
    remainingPotential offset A hA z ≤
      ownerPotential (epochCenter offset A hA z) (restrictedFamily A x) 1 1 := by
  exact ownerPotential_subfamily_le (epochCenter offset A hA z : Matrix n n ℂ)
    (restrictedFamily A x) (restrictedFamily_hermitian A hA x) (liveOfFrozenSubset h) 1

/-- Exact deletion monotonicity in the restricted epoch's own full physical center. -/
theorem remainingPotential_lift_le (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    remainingPotential offset A hA (liftPoint x y) ≤
      ownerPotential (epochCenter (restrictedOffset offset A hA x) (restrictedFamily A x)
        (restrictedFamily_hermitian A hA x) y) (restrictedFamily A x) 1 1 := by
  have h := remainingPotential_le_oldFamily offset A hA (frozen_subset_liftPoint x y)
  rwa [center_liftPoint] at h

/-- The actual successful epoch, lifted to the original coordinates, gives an
actual step for the changing-live-family phase potential. -/
theorem exists_lifted_successful_epoch (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (x : EuclideanSpace ℝ ι) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (Fintype.card ι : ℝ) * ε ≤ 1 / 1000) (hx : CubeRegular ε x)
    (hlarge : 32 ≤ Fintype.card (Live x)) :
    ∃ (z : EuclideanSpace ℝ ι) (time : ℝ), CubeRegular ε z ∧
      (∀ i ∈ frozenCoordinates x, z i = x i) ∧
      frozenCoordinates x ⊆ frozenCoordinates z ∧
      0 ≤ time ∧ time ≤ epochTimeLimit ∧
      ‖x‖ ^ 2 + (Fintype.card (Live x) : ℝ) / 16 * time ≤ ‖z‖ ^ 2 ∧
      (time = epochTimeLimit ∨ (Fintype.card (Live x) : ℝ) / 64 ≤
        ((frozenCoordinates z).card : ℝ) - (frozenCoordinates x).card) ∧
      remainingPotential offset A hA z - remainingPotential offset A hA x ≤
        22 * Real.sqrt (Fintype.card (Live x) : ℝ) := by
  let cfg := epochConfig offset A hA hN x ε hε hsmall hx hlarge
  obtain ⟨y, time, hy, ht0, ht1, hgain, hsuccess, hgrowth⟩ := exists_successful_epoch cfg
  refine ⟨liftPoint x y, time, liftPoint_regular hx hy,
    (fun i hi => liftPoint_frozen x y hi), frozen_subset_liftPoint x y,
    ht0, ht1, norm_gain_liftPoint x y _ hgain, ?_, ?_⟩
  · rw [frozen_card_gain_real]
    exact hsuccess
  · have hdrop := remainingPotential_lift_le offset A hA x y
    change remainingPotential offset A hA (liftPoint x y) ≤
      ownerPotential (cfg.center y) cfg.matrices 1 1 at hdrop
    have hbase : ownerPotential cfg.anchor cfg.matrices 1 1 = remainingPotential offset A hA x := by
      have hc := center_liftPoint offset A hA x (restrictPoint x)
      rw [liftPoint_restrictPoint] at hc
      change ownerPotential (epochCenter (restrictedOffset offset A hA x) (restrictedFamily A x)
          (restrictedFamily_hermitian A hA x) (restrictPoint x)) (restrictedFamily A x) 1 1 = _
      rw [← hc]
      rfl
    rw [hbase] at hgrowth
    linarith

/-- The live labels after a global lift inject into the still-live restricted labels. -/
def liveLiftEmbedding (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    Live (liftPoint x y) ↪ Live y where
  toFun i :=
    ⟨liveOfFrozenSubset (frozen_subset_liftPoint x y) i, by
      intro hi
      apply i.property
      rw [mem_frozenCoordinates]
      have hj := (mem_frozenCoordinates y _).mp hi
      simpa only [← liftPoint_live x y (liveOfFrozenSubset (frozen_subset_liftPoint x y) i)] using hj⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun q : Live y => ((q : Live x) : ι)) hij

/-- Global and nested restrictions have exactly the same remaining coordinate count. -/
theorem live_card_liftPoint (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    Fintype.card (Live (liftPoint x y)) = Fintype.card (Live y) := by
  have h0 := live_card_add_frozen x
  have h1 := live_card_add_frozen (liftPoint x y)
  have h2 := live_card_add_frozen y
  have h3 := frozen_card_liftPoint x y
  omega

/-- A nested restricted-family potential bounds the actual global remaining potential
without an added cost when the restricted endpoint is lifted. -/
theorem remainingPotential_lift_le_nested (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    remainingPotential offset A hA (liftPoint x y) ≤
      remainingPotential (restrictedOffset offset A hA x) (restrictedFamily A x)
        (restrictedFamily_hermitian A hA x) y := by
  unfold remainingPotential
  rw [center_liftPoint]
  exact ownerPotential_subfamily_le
    (epochCenter (restrictedOffset offset A hA x) (restrictedFamily A x)
      (restrictedFamily_hermitian A hA x) y : Matrix n n ℂ)
    (restrictedFamily (restrictedFamily A x) y)
    (restrictedFamily_hermitian (restrictedFamily A x) (restrictedFamily_hermitian A hA x) y)
    (liveLiftEmbedding x y) 1

/-- The initial nested remaining potential is no larger than the actual original
remaining potential at the start of the outer phase. -/
theorem remainingPotential_nested_start_le (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    remainingPotential (restrictedOffset offset A hA x) (restrictedFamily A x)
        (restrictedFamily_hermitian A hA x) (restrictPoint x) ≤
      remainingPotential offset A hA x := by
  have hc := center_liftPoint offset A hA x (restrictPoint x)
  rw [liftPoint_restrictPoint] at hc
  unfold remainingPotential
  rw [← hc]
  exact ownerPotential_subfamily_le (epochCenter offset A hA x : Matrix n n ℂ)
    (restrictedFamily A x) (restrictedFamily_hermitian A hA x) (liveEmbedding (restrictPoint x)) 1

end
end PhaseRestriction
end MatrixSpencer
