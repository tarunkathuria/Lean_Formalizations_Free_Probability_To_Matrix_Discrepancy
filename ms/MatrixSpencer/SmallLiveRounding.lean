import MatrixSpencer.PhaseRestriction

/-! Direct completion of a cube point with few live coordinates. All costs
are charged to the actual live subtype, and all matrix norms use the
Euclidean spectral operator norm. -/

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer
namespace SmallLiveRounding
open PhaseRestriction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complete every coordinate with its nearest boundary sign. -/
def complete (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => ThresholdRounding.boundarySign (x i))

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma complete_apply (x : EuclideanSpace ℝ ι) (i : ι) :
    complete x i = ThresholdRounding.boundarySign (x i) := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma complete_isSign (x : EuclideanSpace ℝ ι) (i : ι) : IsSign (complete x i) :=
  ThresholdRounding.boundarySign_isSign _

lemma complete_frozen (x : EuclideanSpace ℝ ι) {i : ι}
    (hi : i ∈ frozenCoordinates x) : complete x i = x i := by
  rcases (mem_frozenCoordinates x i).mp hi with hp | hn
  · simp [complete_apply, hp, ThresholdRounding.boundarySign]
  · simp [complete_apply, hn, ThresholdRounding.boundarySign]

omit [Fintype ι] [DecidableEq ι] in
lemma complete_cube (x : EuclideanSpace ℝ ι) : ∀ i, |complete x i| ≤ 1 :=
  fun i => (IsSign.abs_eq_one (complete_isSign x i)).le

omit [Fintype ι] [DecidableEq ι] in
lemma complete_regular (x : EuclideanSpace ℝ ι) (ε : ℝ) : CubeRegular ε (complete x) :=
  ⟨complete_cube x, fun i => Or.inl (complete_isSign x i)⟩

lemma complete_frozen_eq_univ (x : EuclideanSpace ℝ ι) :
    frozenCoordinates (complete x) = Finset.univ := by
  ext i
  simp only [mem_frozenCoordinates, Finset.mem_univ, iff_true]
  exact complete_isSign x i

lemma complete_live_card (x : EuclideanSpace ℝ ι) : Fintype.card (Live (complete x)) = 0 := by
  rw [live_card, complete_frozen_eq_univ]
  simp

lemma complete_eq_of_live_card_zero (x : EuclideanSpace ℝ ι)
    (hx : Fintype.card (Live x) = 0) : complete x = x := by
  have hempty : IsEmpty (Live x) := Fintype.card_eq_zero_iff.mp hx
  ext i
  apply complete_frozen
  by_contra hi
  exact hempty.false ⟨i, hi⟩

lemma complete_idempotent (x : EuclideanSpace ℝ ι) : complete (complete x) = complete x :=
  complete_eq_of_live_card_zero _ (complete_live_card x)

omit [DecidableEq ι] in
lemma complete_norm_sq (x : EuclideanSpace ℝ ι) : ‖complete x‖ ^ 2 = Fintype.card ι := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, IsSign.abs_eq_one (complete_isSign x _), one_pow,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

omit [DecidableEq ι] in
lemma complete_norm_sq_ge {x : EuclideanSpace ℝ ι} (hx : ∀ i, |x i| ≤ 1) :
    ‖x‖ ^ 2 ≤ ‖complete x‖ ^ 2 := by
  rw [complete_norm_sq, EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ _i : ι, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Real.norm_eq_abs]
      nlinarith [hx i, abs_nonneg (x i)]
    _ = _ := by simp

/-- Only live coordinates incur cost, and nearest-sign rounding costs at most one each. -/
lemma complete_cost_le {x : EuclideanSpace ℝ ι} (hx : ∀ i, |x i| ≤ 1) :
    ∑ i, |complete x i - x i| ≤ Fintype.card (Live x) := by
  rw [← sum_frozen_add_live x (fun i => |complete x i - x i|)]
  have hz : (∑ i ∈ frozenCoordinates x, |complete x i - x i|) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [complete_frozen x hi, sub_self, abs_zero]
  rw [hz, zero_add]
  calc
    _ ≤ ∑ _i : Live x, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [complete_apply, ThresholdRounding.abs_boundarySign_sub (hx i)]
      linarith [abs_nonneg (x i)]
    _ = _ := by simp

lemma complete_cost_eq_zero {x : EuclideanSpace ℝ ι}
    (hx : Fintype.card (Live x) = 0) : ∑ i, |complete x i - x i| = 0 := by
  rw [complete_eq_of_live_card_zero x hx]
  simp

lemma small_nat_le_sqrt {k : ℕ} (hk : k < 32) : (k : ℝ) ≤ 64 * Real.sqrt (k : ℝ) := by
  by_cases hz : k = 0
  · simp [hz]
  · have hkone : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    have hroot : (1 : ℝ) ≤ Real.sqrt (k : ℝ) := by
      simpa using Real.sqrt_le_sqrt hkone
    have hsmall : (k : ℝ) < 32 := by exact_mod_cast hk
    linarith

lemma complete_cost_le_small_sqrt {x : EuclideanSpace ℝ ι} (hx : ∀ i, |x i| ≤ 1)
    (hsmall : Fintype.card (Live x) < 32) :
    ∑ i, |complete x i - x i| ≤ 64 * Real.sqrt (Fintype.card (Live x) : ℝ) :=
  (complete_cost_le hx).trans (small_nat_le_sqrt hsmall)

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance smallLiveCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance smallLivePhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

lemma complete_center_norm_le (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {x : EuclideanSpace ℝ ι} (hx : ∀ i, |x i| ≤ 1) :
    ‖(epochCenter offset A hA (complete x) : Matrix n n ℂ) - epochCenter offset A hA x‖ ≤
      Fintype.card (Live x) := by
  simp only [epochCenter_coe, add_sub_add_left_eq_sub]
  exact (ThresholdRounding.combination_norm_sub_le_l1 A hN
    (WithLp.ofLp x) (WithLp.ofLp (complete x))).trans (complete_cost_le hx)

lemma complete_center_norm_le_small_sqrt (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {x : EuclideanSpace ℝ ι} (hx : ∀ i, |x i| ≤ 1) (hsmall : Fintype.card (Live x) < 32) :
    ‖(epochCenter offset A hA (complete x) : Matrix n n ℂ) - epochCenter offset A hA x‖ ≤
      64 * Real.sqrt (Fintype.card (Live x) : ℝ) :=
  (complete_center_norm_le offset A hA hN hx).trans (small_nat_le_sqrt hsmall)

/-- At any fixed PSD covariance, actual owner potential pays at most the live count. -/
lemma complete_ownerPotential_abs_le (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {x : EuclideanSpace ℝ ι} (hx : ∀ i, |x i| ≤ 1)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : κ → Matrix n n ℂ) (hB : ∀ i, (B i).IsHermitian)
    {C : Matrix κ κ ℝ} (hC : C.PosSemidef) (θ : ℝ) :
    |ownerPotential (epochCenter offset A hA (complete x)) B C θ -
      ownerPotential (epochCenter offset A hA x) B C θ| ≤ Fintype.card (Live x) :=
  (abs_ownerPotential_sub_le_norm (epochCenter offset A hA x).property
    (epochCenter offset A hA (complete x)).property B hB hC θ).trans
      (complete_center_norm_le offset A hA hN hx)

lemma complete_ownerPotential_le_small_sqrt (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {x : EuclideanSpace ℝ ι} (hx : ∀ i, |x i| ≤ 1) (hsmall : Fintype.card (Live x) < 32)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : κ → Matrix n n ℂ) (hB : ∀ i, (B i).IsHermitian)
    {C : Matrix κ κ ℝ} (hC : C.PosSemidef) (θ : ℝ) :
    ownerPotential (epochCenter offset A hA (complete x)) B C θ ≤
      ownerPotential (epochCenter offset A hA x) B C θ +
        64 * Real.sqrt (Fintype.card (Live x) : ℝ) := by
  have h := (le_abs_self _).trans
    ((complete_ownerPotential_abs_le offset A hA hN hx B hB hC θ).trans (small_nat_le_sqrt hsmall))
  linarith

/-- Full completion has zero live covariance and pays at most its actual rounding cost. -/
lemma complete_remainingPotential_le (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {x : EuclideanSpace ℝ ι} (hx : ∀ i, |x i| ≤ 1) :
    remainingPotential offset A hA (complete x) ≤
      remainingPotential offset A hA x + Fintype.card (Live x) := by
  have hbase := ownerPotential_le_base_add (epochCenter offset A hA (complete x))
    (restrictedFamily A (complete x)) (restrictedFamily_hermitian A hA (complete x))
    (restrictedFamily_contractions A hN (complete x)) Matrix.PosSemidef.one le_rfl 1
  rw [complete_live_card] at hbase
  simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, add_zero] at hbase
  have hold := baseDensityPotential_le_owner (epochCenter offset A hA (complete x))
    (restrictedFamily A x) (restrictedFamily_hermitian A hA x) Matrix.PosSemidef.one 1
  have hcost := complete_ownerPotential_abs_le offset A hA hN hx
    (restrictedFamily A x) (restrictedFamily_hermitian A hA x) Matrix.PosSemidef.one 1
  have hcost' := (le_abs_self _).trans hcost
  change ownerPotential (epochCenter offset A hA (complete x)) (restrictedFamily A (complete x)) 1 1 ≤
    ownerPotential (epochCenter offset A hA x) (restrictedFamily A x) 1 1 + Fintype.card (Live x)
  exact (hbase.trans hold).trans (by linarith)

lemma complete_remainingPotential_le_small_sqrt (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {x : EuclideanSpace ℝ ι} (hx : ∀ i, |x i| ≤ 1) (hsmall : Fintype.card (Live x) < 32) :
    remainingPotential offset A hA (complete x) ≤
      remainingPotential offset A hA x + 64 * Real.sqrt (Fintype.card (Live x) : ℝ) :=
  (complete_remainingPotential_le offset A hA hN hx).trans
    (add_le_add_left (small_nat_le_sqrt hsmall) _)

/-- A concrete full signing for the small-live branch; it preserves every existing sign. -/
theorem exists_small_live_completion (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {x : EuclideanSpace ℝ ι} (hx : ∀ i, |x i| ≤ 1) (hsmall : Fintype.card (Live x) < 32) :
    ∃ z : EuclideanSpace ℝ ι,
      (∀ i, IsSign (z i)) ∧
      (∀ i ∈ frozenCoordinates x, z i = x i) ∧
      ‖x‖ ^ 2 ≤ ‖z‖ ^ 2 ∧
      Fintype.card (Live z) = 0 ∧
      remainingPotential offset A hA z ≤ remainingPotential offset A hA x +
        64 * Real.sqrt (Fintype.card (Live x) : ℝ) :=
  ⟨complete x, complete_isSign x, fun _ hi => complete_frozen x hi,
    complete_norm_sq_ge hx, complete_live_card x,
    complete_remainingPotential_le_small_sqrt offset A hA hN hx hsmall⟩

end SmallLiveRounding
end MatrixSpencer
