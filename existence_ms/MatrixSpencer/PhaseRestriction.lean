import MatrixSpencer.EpochSelection
import MatrixSpencer.PhaseEpochProgress

/-! Actual restriction to live coordinates, and lifting back to the original
coefficient space while retaining its frozen offset. -/
open Set Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
namespace PhaseRestriction
noncomputable section
set_option maxHeartbeats 800000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance phaseRestrictionCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance phaseRestrictionPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- The actual coordinates that have not yet reached either sign. -/
abbrev Live (x : EuclideanSpace ℝ ι) := {i : ι // i ∉ frozenCoordinates x}

def restrictPoint (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ (Live x) :=
  WithLp.toLp 2 (fun i => x i)

def restrictedFamily (A : ι → Matrix n n ℂ) (x : EuclideanSpace ℝ ι) (i : Live x) : Matrix n n ℂ := A i

def liftPoint (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => if hi : i ∈ frozenCoordinates x then x i else y ⟨i, hi⟩)

omit [DecidableEq ι] in
@[simp] theorem restrictPoint_apply (x : EuclideanSpace ℝ ι) (i : Live x) : restrictPoint x i = x i := rfl

@[simp] theorem liftPoint_frozen (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x))
    {i : ι} (hi : i ∈ frozenCoordinates x) : liftPoint x y i = x i := by
  change (if hj : i ∈ frozenCoordinates x then x i else y ⟨i, hj⟩) = x i
  rw [dif_pos hi]

@[simp] theorem liftPoint_live (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x))
    (i : Live x) : liftPoint x y i = y i := by
  change (if hj : (i : ι) ∈ frozenCoordinates x then x i else y ⟨i, hj⟩) = y i
  rw [dif_neg i.property]

theorem liftPoint_restrictPoint (x : EuclideanSpace ℝ ι) : liftPoint x (restrictPoint x) = x := by
  ext i
  by_cases hi : i ∈ frozenCoordinates x
  · exact liftPoint_frozen x _ hi
  · exact liftPoint_live x _ ⟨i, hi⟩

theorem restrictPoint_unfrozen (x : EuclideanSpace ℝ ι) (i : Live x) : ¬ IsSign (restrictPoint x i) := by
  exact fun h => i.property ((mem_frozenCoordinates x i).mpr h)

omit [DecidableEq ι] in
theorem restrictPoint_regular {ε : ℝ} {x : EuclideanSpace ℝ ι} (hx : CubeRegular ε x) :
    CubeRegular ε (restrictPoint x) := by
  exact ⟨fun i => hx.1 i, fun i => hx.2 i⟩

theorem liftPoint_regular {ε : ℝ} {x : EuclideanSpace ℝ ι} (hx : CubeRegular ε x)
    {y : EuclideanSpace ℝ (Live x)} (hy : CubeRegular ε y) : CubeRegular ε (liftPoint x y) := by
  constructor
  · intro i
    by_cases hi : i ∈ frozenCoordinates x
    · rw [liftPoint_frozen x y hi]; exact hx.1 i
    · simpa only [liftPoint_live x y ⟨i, hi⟩] using hy.1 ⟨i, hi⟩
  · intro i
    by_cases hi : i ∈ frozenCoordinates x
    · rw [liftPoint_frozen x y hi]; exact Or.inl ((mem_frozenCoordinates x i).mp hi)
    · simpa only [liftPoint_live x y ⟨i, hi⟩] using hy.2 ⟨i, hi⟩

theorem frozen_subset_liftPoint (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    frozenCoordinates x ⊆ frozenCoordinates (liftPoint x y) :=
  frozenCoordinates_subset_of_preserved (fun _ hi => liftPoint_frozen x y hi)

theorem sum_frozen_add_live {E : Type*} [AddCommMonoid E]
    (x : EuclideanSpace ℝ ι) (f : ι → E) :
    (∑ i ∈ frozenCoordinates x, f i) + (∑ i : Live x, f i) = ∑ i, f i := by
  rw [← Finset.sum_subtype (frozenCoordinates x)ᶜ (fun _ => Finset.mem_compl) f]
  exact Finset.sum_add_sum_compl _ _

theorem live_card (x : EuclideanSpace ℝ ι) :
    Fintype.card (Live x) = Fintype.card ι - (frozenCoordinates x).card := by
  have h : Fintype.card (Live x) = (frozenCoordinates x)ᶜ.card :=
    Fintype.card_of_subtype (frozenCoordinates x)ᶜ (fun _ => Finset.mem_compl)
  exact h.trans (Finset.card_compl _)

theorem live_card_add_frozen (x : EuclideanSpace ℝ ι) :
    Fintype.card (Live x) + (frozenCoordinates x).card = Fintype.card ι := by
  rw [live_card]
  exact Nat.sub_add_cancel (Finset.card_le_univ _)

/-- The frozen terms are incorporated into the full physical offset. -/
def restrictedOffset (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (x : EuclideanSpace ℝ ι) : selfAdjoint (Matrix n n ℂ) :=
  offset + ∑ i ∈ frozenCoordinates x, x i • hermitianMatrixFamily A hA i

omit [Fintype n] [DecidableEq ι] [DecidableEq n] in
theorem restrictedFamily_hermitian (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ ι) (i : Live x) : (restrictedFamily A x i).IsHermitian := hA i

omit [DecidableEq ι] in
theorem restrictedFamily_contractions (A : ι → Matrix n n ℂ) (hA : ∀ i, ‖A i‖ ≤ 1)
    (x : EuclideanSpace ℝ ι) (i : Live x) : ‖restrictedFamily A x i‖ ≤ 1 := hA i

/-- The restricted epoch center is exactly the original full physical center after lifting. -/
theorem center_liftPoint (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    epochCenter offset A hA (liftPoint x y) =
      epochCenter (restrictedOffset offset A hA x) (restrictedFamily A x)
        (restrictedFamily_hermitian A hA x) y := by
  unfold epochCenter restrictedOffset
  rw [← sum_frozen_add_live x (fun i => liftPoint x y i • hermitianMatrixFamily A hA i)]
  have hfixed : (∑ i ∈ frozenCoordinates x, liftPoint x y i • hermitianMatrixFamily A hA i) =
      ∑ i ∈ frozenCoordinates x, x i • hermitianMatrixFamily A hA i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [liftPoint_frozen x y hi]
  rw [hfixed]
  simp only [liftPoint_live, add_assoc]
  rfl

/-- The norm contribution of already frozen coordinates is unchanged by lifting. -/
theorem norm_liftPoint_sq (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    ‖liftPoint x y‖ ^ 2 = (∑ i ∈ frozenCoordinates x, ‖x i‖ ^ 2) + ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, ← sum_frozen_add_live x]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [liftPoint_frozen x y hi]
  · simp only [liftPoint_live, EuclideanSpace.norm_sq_eq]

theorem norm_sq_difference (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    ‖liftPoint x y‖ ^ 2 - ‖x‖ ^ 2 = ‖y‖ ^ 2 - ‖restrictPoint x‖ ^ 2 := by
  have hx := norm_liftPoint_sq x (restrictPoint x)
  rw [liftPoint_restrictPoint] at hx
  rw [norm_liftPoint_sq, hx]
  ring

def liveEmbedding (x : EuclideanSpace ℝ ι) : Live x ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩

/-- Original frozen coordinates and newly frozen live coordinates are disjoint. -/
theorem frozen_disjoint_lift (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    Disjoint (frozenCoordinates x) ((frozenCoordinates y).map (liveEmbedding x)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨j, _, hji⟩ := Finset.mem_map.mp hj
  change (j : ι) = i at hji
  exact j.property (hji.symm ▸ hi)

/-- The actual frozen set splits exactly into old signs and newly frozen live coordinates. -/
theorem frozen_liftPoint (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    frozenCoordinates (liftPoint x y) = frozenCoordinates x ∪ (frozenCoordinates y).map (liveEmbedding x) := by
  ext i
  rw [Finset.mem_union]
  constructor
  · intro hi
    by_cases hf : i ∈ frozenCoordinates x
    · exact Or.inl hf
    · right
      apply Finset.mem_map.mpr
      refine ⟨⟨i, hf⟩, ?_, rfl⟩
      rw [mem_frozenCoordinates]
      have hsign := (mem_frozenCoordinates (liftPoint x y) i).mp hi
      simpa only [liftPoint_live x y ⟨i, hf⟩] using hsign
  · rintro (hi | hi)
    · exact frozen_subset_liftPoint x y hi
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      rw [mem_frozenCoordinates]
      change IsSign (liftPoint x y (j : ι))
      rw [liftPoint_live]
      exact (mem_frozenCoordinates y j).mp hj

theorem frozen_card_liftPoint (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    (frozenCoordinates (liftPoint x y)).card = (frozenCoordinates x).card + (frozenCoordinates y).card := by
  rw [frozen_liftPoint, Finset.card_union_of_disjoint (frozen_disjoint_lift x y), Finset.card_map]

theorem frozen_card_gain (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    (frozenCoordinates (liftPoint x y)).card - (frozenCoordinates x).card = (frozenCoordinates y).card := by
  rw [frozen_card_liftPoint, Nat.add_sub_cancel_left]

theorem frozen_card_gain_real (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    ((frozenCoordinates (liftPoint x y)).card : ℝ) - (frozenCoordinates x).card = (frozenCoordinates y).card := by
  rw [frozen_card_liftPoint, Nat.cast_add]
  ring

/-- Exact transfer of the epoch's Euclidean progress to the original cube vector. -/
theorem norm_gain_liftPoint (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x))
    (gain : ℝ) (hgain : ‖restrictPoint x‖ ^ 2 + gain ≤ ‖y‖ ^ 2) :
    ‖x‖ ^ 2 + gain ≤ ‖liftPoint x y‖ ^ 2 := by
  have he := norm_sq_difference x y
  linarith

/-- A live-coordinate epoch config with the shared original rounding tolerance. -/
def epochConfig (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (x : EuclideanSpace ℝ ι) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (Fintype.card ι : ℝ) * ε ≤ 1 / 1000)
    (hx : CubeRegular ε x) (hlarge : 32 ≤ Fintype.card (Live x)) : EpochConfig (Live x) n where
  matrices := restrictedFamily A x
  hermitian := restrictedFamily_hermitian A hA x
  contractions := restrictedFamily_contractions A hN x
  offset := restrictedOffset offset A hA x
  start := restrictPoint x
  epsilon := ε
  epsilon_pos := hε
  epsilon_small := (mul_le_mul_of_nonneg_right
    (show (Fintype.card (Live x) : ℝ) ≤ Fintype.card ι by exact_mod_cast Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x))
    hε.le).trans hsmall
  start_regular := restrictPoint_regular hx
  start_unfrozen := restrictPoint_unfrozen x
  count_large := hlarge

/-- The actual potential with precisely the currently live original family. -/
def remainingPotential (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (x : EuclideanSpace ℝ ι) : ℝ :=
  ownerPotential (epochCenter offset A hA x) (restrictedFamily A x) 1 1

end
end PhaseRestriction
end MatrixSpencer
