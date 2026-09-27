import AugmentedHigherRankKS.EpochActive
import AugmentedHigherRankKS.FourBlockDomination
import AugmentedHigherRankKS.FourBlockPotentialSmoothness
import HigherRankKS.CompactVertex

/-! Exact centered curves and the local-minimum curvature condition. -/
open Matrix MatrixSpencer Set Filter
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

def liftActiveDirection (z : EpochState ι) (h : ActiveOwners z → ℝ) : ι → ℝ :=
  fun i => if hi : i ∈ positiveReserves z then h ⟨i, hi⟩ else 0

@[simp] theorem liftActiveDirection_active (z : EpochState ι) (h : ActiveOwners z → ℝ)
    (i : ActiveOwners z) : liftActiveDirection z h i = h i := by
  simp only [liftActiveDirection, dif_pos i.property]

theorem liftActiveDirection_zero (z : EpochState ι) (h : ActiveOwners z → ℝ)
    (i : ι) (hi : reserve z i = 0) : liftActiveDirection z h i = 0 := by
  have hn : i ∉ positiveReserves z := by simp [hi]
  simp only [liftActiveDirection, dif_neg hn]

theorem augmentedCenter_force_sum (A : ι → Matrix n n ℂ) (x h : ι → ℝ) :
    augmentedCenter (∑ i, h i • A i) ((-2 : ℝ) • ∑ i, (x i * h i) • A i) =
      ∑ i, h i • forceAtom (x i) (A i) := by
  ext (u | u) (v | v) <;> cases u <;> cases v <;>
    simp [augmentedCenter, signedLift, forceAtom, Matrix.sum_apply, Matrix.smul_apply,
      Finset.smul_sum, smul_smul,
      mul_assoc, mul_left_comm, mul_comm]

theorem augmentedCenter_movement (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ)
    (a : ℝ) (z : EpochState ι) (h : ι → ℝ) (t : ℝ) :
    augmentedCenter (discrepancy A x₀ (movement a z h t))
      (budgetCenter A x₀ (movement a z h t)) =
      augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z) +
        t • ∑ i, h i • forceAtom (position z i) (A i) := by
  rw [discrepancy_movement, budgetCenter_movement]
  have he : -(2 * t) • ∑ i, (position z i * h i) • A i =
      t • ((-2 : ℝ) • ∑ i, (position z i * h i) • A i) := by
    rw [smul_smul]
    congr 1
    ring
  rw [sub_eq_add_neg, ← neg_smul, he, augmentedCenter_add, augmentedCenter_smul,
    augmentedCenter_force_sum]

theorem active_force_sum (A : ι → Matrix n n ℂ) (z : EpochState ι)
    (h : ActiveOwners z → ℝ) :
    (∑ i, liftActiveDirection z h i • forceAtom (position z i) (A i)) =
      ∑ i : ActiveOwners z, h i • forceAtom (position z i) (A i) := by
  have hs := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ positiveReserves z)
    (fun i => liftActiveDirection z h i • forceAtom (position z i) (A i))
  have hz : (∑ i : {i // i ∉ positiveReserves z},
      liftActiveDirection z h i • forceAtom (position z i) (A i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [liftActiveDirection, dif_neg i.property, zero_smul]
  rw [hz, add_zero] at hs
  rw [← hs]
  apply Finset.sum_congr (by ext i; simp)
  intro i hi
  rw [liftActiveDirection_active]

theorem epochPotential_movement_eq (A : ι → Matrix n n ℂ) (β θ : ℝ)
    (x₀ : ι → ℝ) {a R : ℝ} {z : EpochState ι} (hz : z ∈ epochDomain a R)
    (h : ActiveOwners z → ℝ) (t : ℝ) :
    epochPotential A β θ x₀ (movement a z (liftActiveDirection z h) t) =
      potential (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z) +
          t • ∑ i : ActiveOwners z, h i • forceAtom (position z i) (A i))
        (fun i : ActiveOwners z => A i) β
        (fun i => reserve z i - a * t^2 * (h i)^2) θ := by
  unfold epochPotential
  rw [augmentedCenter_movement, active_force_sum]
  rw [potential_eq_restrict _ A β θ (positiveReserves z) _ (by
    intro i hi
    change reserve z i - a * t^2 * (liftActiveDirection z h i)^2 = 0
    rw [reserve_zero_of_not_positive hz i hi]
    simp only [liftActiveDirection, dif_neg hi, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, sub_zero])]
  congr 1
  funext i
  change reserve z i - a * t^2 * (liftActiveDirection z h i)^2 = _
  rw [liftActiveDirection_active]

theorem contDiffAt_epoch_movement [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ) (x₀ : ι → ℝ)
    {a R : ℝ} {z : EpochState ι} (hz : z ∈ epochDomain a R)
    (h : ActiveOwners z → ℝ) :
    ContDiffAt ℝ ∞ (fun t : ℝ => epochPotential A ((1 : ℝ) / 2 ^ k) θ x₀
      (movement a z (liftActiveDirection z h) t)) 0 := by
  have heq := funext (epochPotential_movement_eq A ((1 : ℝ) / 2 ^ k) θ x₀ hz h)
  rw [heq]
  apply contDiffAt_potential_of_positive_weights (fun i : ActiveOwners z => A i)
    (fun i => hA i) k hk θ hθ
  · fun_prop
  · apply contDiffAt_pi.mpr
    intro i
    fun_prop
  · intro i
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul, sub_zero] using
      (mem_positiveReserves z i).mp i.property

/-- A compact minimum has nonnegative second derivative on every feasible
centered curve. This is an actual local minimum, not a supplied certificate. -/
theorem epoch_movement_second_nonneg [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ) (x₀ : ι → ℝ)
    {a R : ℝ} (ha : 0 < a) {z : EpochState ι} (hz : z ∈ epochDomain a R)
    (hmin : IsMinOn (epochPotential A ((1 : ℝ) / 2 ^ k) θ x₀) (epochDomain a R) z)
    (hfaces : ∀ i, |position z i| = 1 → reserve z i = 0)
    (h : ActiveOwners z → ℝ) :
    0 ≤ iteratedDeriv 2 (fun t : ℝ => epochPotential A ((1 : ℝ) / 2 ^ k) θ x₀
      (movement a z (liftActiveDirection z h) t)) 0 := by
  have hfeas := eventually_movement_mem ha hz hfaces (liftActiveDirection z h)
    (liftActiveDirection_zero z h)
  have hloc : IsLocalMin (fun t : ℝ => epochPotential A ((1 : ℝ) / 2 ^ k) θ x₀
      (movement a z (liftActiveDirection z h) t)) 0 := by
    filter_upwards [hfeas] with t ht
    simpa only [movement_zero] using hmin ht
  by_contra hn
  have hs := (contDiffAt_epoch_movement A hA k hk θ hθ x₀ hz h).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  apply (ks_not_isLocalMin_of_hessian_neg _ 0 1 hs ?_) hloc
  simpa only [iteratedDeriv, iteratedFDeriv_two_apply] using lt_of_not_ge hn

end AugmentedHigherRankKS
