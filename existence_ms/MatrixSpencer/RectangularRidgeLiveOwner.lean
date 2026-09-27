import MatrixSpencer.RectangularRidgeLiveEpochLedger

/-!
# Actual coordinate inclusion for an epoch's live labels

The original labels are scanned in order. The retained list supplies forward
indexing by lookup and inverse indexing by finite search; no eigenbasis or
range basis is selected. Its covariance is the live coordinate projection.
-/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.RectangularRidgeLiveOwner
open MSManuscriptSupportedOwner
variable {N : ℕ}

abbrev Live (F₀ : Finset (Fin N)) := {i : Fin N // i ∉ F₀}

def labels (F₀ : Finset (Fin N)) : List (Fin N) :=
  (List.finRange N).filter (fun i => decide (i ∉ F₀))

def count (F₀ : Finset (Fin N)) : ℕ := (labels F₀).length

theorem labels_nodup (F₀ : Finset (Fin N)) : (labels F₀).Nodup := (List.nodup_finRange N).filter _
theorem mem_labels (F₀ : Finset (Fin N)) (i : Fin N) : i ∈ labels F₀ ↔ i ∉ F₀ := by simp [labels]

def equiv (F₀ : Finset (Fin N)) : Fin (count F₀) ≃ Live F₀ :=
  ((labels_nodup F₀).getEquiv (labels F₀)).trans
    { toFun := fun i => ⟨i.val, (mem_labels F₀ i.val).mp i.property⟩
      invFun := fun i => ⟨i.val, (mem_labels F₀ i.val).mpr i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def index (F₀ : Finset (Fin N)) (i : Fin (count F₀)) : Fin N := (equiv F₀ i).val

theorem index_injective (F₀ : Finset (Fin N)) : Function.Injective (index F₀) :=
  Subtype.val_injective.comp (equiv F₀).injective

theorem index_live (F₀ : Finset (Fin N)) (i : Fin (count F₀)) : index F₀ i ∉ F₀ :=
  (equiv F₀ i).property

theorem count_eq (F₀ : Finset (Fin N)) : count F₀ = N - F₀.card := by
  have he : (labels F₀).toFinset = F₀ᶜ := by ext i; simp [mem_labels]
  have hc := List.toFinset_card_of_nodup (labels_nodup F₀)
  rw [he, Finset.card_compl, Fintype.card_fin] at hc
  exact hc.symm

theorem count_le (F₀ : Finset (Fin N)) : count F₀ ≤ N := by rw [count_eq]; exact Nat.sub_le _ _

def frame (F₀ : Finset (Fin N)) : Matrix (Fin N) (Fin (count F₀)) ℝ :=
  (1 : Matrix (Fin N) (Fin N) ℝ).submatrix id (index F₀)

theorem frame_isometry (F₀ : Finset (Fin N)) : (frame F₀)ᵀ * frame F₀ = 1 := by
  rw [frame, Matrix.transpose_submatrix, Matrix.transpose_one,
    ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.one_mul,
    Matrix.submatrix_one _ (index_injective F₀)]

def owner (F₀ : Finset (Fin N)) : Owner N where
  dim := count F₀
  frame := frame F₀
  matrix := 1

theorem owner_valid (F₀ : Finset (Fin N)) {δ : ℝ} (hδ : δ ≤ 1) : (owner F₀).Valid δ := by
  refine ⟨frame_isometry F₀, ?_⟩
  change δ • (1 : Matrix (Fin (count F₀)) (Fin (count F₀)) ℝ) ≤ 1
  apply Matrix.le_iff.mpr
  have hh := (Matrix.PosSemidef.one : (1 : Matrix (Fin (count F₀)) (Fin (count F₀)) ℝ).PosSemidef).smul (sub_nonneg.mpr hδ)
  simpa only [sub_smul, one_smul] using hh

theorem owner_le_one (F₀ : Finset (Fin N)) : (owner F₀).physical ≤ 1 := by
  simpa only [Owner.physical, owner, Matrix.mul_one] using
    covarianceIsometry_projection_le_one (frame F₀) (frame_isometry F₀)

theorem owner_trace (F₀ : Finset (Fin N)) : realTrace (owner F₀).physical = count F₀ := by
  rw [trace_physical _ (frame_isometry F₀)]
  simp [owner, realTrace]

theorem owner_annihilates (F₀ : Finset (Fin N)) (i : Fin N) (hi : i ∈ F₀) :
    (owner F₀).physical *ᵥ Pi.single i 1 = 0 := by
  have ht : (frame F₀)ᵀ *ᵥ Pi.single i 1 = 0 := by
    rw [Matrix.mulVec_single]
    ext j
    have he : i ≠ index F₀ j := by
      intro hh
      exact index_live F₀ j (hh ▸ hi)
    simp [frame, Matrix.submatrix_apply, Matrix.one_apply, he.symm]
  rw [Owner.physical]
  dsimp only [owner]
  rw [Matrix.mul_one, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_zero]

/-- Fresh epoch state retains the full original point and resets only its
live covariance and per-epoch accounts. -/
def initial (x : EuclideanSpace ℝ (Fin N)) : MSManuscriptNumericalEpochLedger.State N where
  point := x
  owner := owner (frozenCoordinates x)
  time := 0
  variance := 0
  paid := 0
  dust := 0
  rounding := 0
  centered := 0

theorem initial_invariant {ε δ : ℝ} (hδ : δ ≤ 1)
    (x : EuclideanSpace ℝ (Fin N)) (hx : CubeRegular ε x) :
    RectangularRidgeLiveEpochLedger.Invariant ε δ (‖x‖ ^ 2) (count (frozenCoordinates x))
      (frozenCoordinates x) (initial x) := by
  refine ⟨hx, owner_valid _ hδ, owner_le_one _, le_rfl, owner_annihilates _,
    Finset.Subset.refl _, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [initial, zero_add, add_zero] using owner_trace (frozenCoordinates x)
  · simp [initial]
  · simp [initial]
  · simp [initial, owner]
  · simp [initial]
  · simp [initial]

theorem initial_centered (x : EuclideanSpace ℝ (Fin N)) :
    MSManuscriptNumericalEpochLedger.CenteredInvariant x (initial x) := by
  simp [MSManuscriptNumericalEpochLedger.CenteredInvariant, initial]

end MatrixSpencer.RectangularRidgeLiveOwner
