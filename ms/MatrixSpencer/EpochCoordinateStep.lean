import MatrixSpencer.OwnerMovementCovariance
import MatrixSpencer.PositiveCovarianceSampler
import MatrixSpencer.ThresholdRounding

/-!
# The actual sampled and rounded cube step

Frozen coordinates are the coordinates already equal to a sign. The step
uses the concrete short and spectral sampler, then the actual threshold rule.
-/

open scoped BigOperators MatrixOrder
open Matrix
noncomputable section
namespace MatrixSpencer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def frozenCoordinates (x : EuclideanSpace ℝ ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => IsSign (x i))

@[simp] theorem mem_frozenCoordinates (x : EuclideanSpace ℝ ι) (i : ι) :
    i ∈ frozenCoordinates x ↔ IsSign (x i) := by simp [frozenCoordinates]

def CubeRegular (ε : ℝ) (x : EuclideanSpace ℝ ι) : Prop :=
  (∀ i, |x i| ≤ 1) ∧ (∀ i, IsSign (x i) ∨ |x i| < 1 - ε)

def epochCoordinateIncrement (C : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι)
    (s : ι × Bool) : EuclideanSpace ℝ ι :=
  covarianceSampleIncrement (epochCovariance_posSemidef C (frozenCoordinates x) x) s

def epochMovedPoint (C : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι)
    (h : ℝ) (s : ι × Bool) : EuclideanSpace ℝ ι := x + h • epochCoordinateIncrement C x s

def epochRoundedPoint (ε : ℝ) (C : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι)
    (h : ℝ) (s : ι × Bool) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (ThresholdRounding.roundVector ε (WithLp.ofLp (epochMovedPoint C x h s)))

theorem epochCoordinateIncrement_norm_le {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (hC1 : C ≤ 1) (x : EuclideanSpace ℝ ι) (s : ι × Bool) :
    ‖epochCoordinateIncrement C x s‖ ≤ Real.sqrt (Fintype.card ι : ℝ) := by
  have hh := realTrace_le_card_of_le_one ((epochCovariance_le hC (frozenCoordinates x) x).trans hC1)
  have hn := covarianceSample_norm_sq (epochCovariance_posSemidef C (frozenCoordinates x) x) s
  change ‖epochCoordinateIncrement C x s‖ ^ 2 = _ at hn
  calc
    _ = Real.sqrt (‖epochCoordinateIncrement C x s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_le_sqrt (hn.trans_le hh)

theorem epochCoordinateIncrement_abs_le {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (hC1 : C ≤ 1) (x : EuclideanSpace ℝ ι) (s : ι × Bool) (i : ι) :
    |epochCoordinateIncrement C x s i| ≤ Real.sqrt (Fintype.card ι : ℝ) := by
  exact (show |epochCoordinateIncrement C x s i| ≤ ‖epochCoordinateIncrement C x s‖ from
    (Real.norm_eq_abs _ ▸ PiLp.norm_apply_le (epochCoordinateIncrement C x s) i)).trans
      (epochCoordinateIncrement_norm_le hC hC1 x s)

theorem epochMovedPoint_cube {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    {ε : ℝ} {x : EuclideanSpace ℝ ι} (hx : CubeRegular ε x)
    {h : ℝ} (hh : 0 ≤ h) (hsmall : h * Real.sqrt (Fintype.card ι : ℝ) ≤ ε)
    {s : ι × Bool}
    (hs : 0 < covarianceSampleWeight (epochCovariance_posSemidef C (frozenCoordinates x) x) s) :
    ∀ i, |epochMovedPoint C x h s i| ≤ 1 := by
  have hc := epochSample_constraints C (frozenCoordinates x) x hs
  apply ThresholdRounding.move_cube (frozen := (frozenCoordinates x : Set ι))
  · intro i hi
    exact ⟨hx.1 i, hc.1 i hi⟩
  · intro i hi
    rcases hx.2 i with hi' | hi'
    · exact False.elim (hi ((mem_frozenCoordinates x i).mpr hi'))
    · exact hi'.le
  · intro i _
    rw [abs_of_nonneg hh]
    exact (mul_le_mul_of_nonneg_left (epochCoordinateIncrement_abs_le hC hC1 x s i) hh).trans hsmall

theorem epochRoundedPoint_regular {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    {ε : ℝ} {x : EuclideanSpace ℝ ι} (hx : CubeRegular ε x)
    {h : ℝ} (hh : 0 ≤ h) (hsmall : h * Real.sqrt (Fintype.card ι : ℝ) ≤ ε)
    {s : ι × Bool}
    (hs : 0 < covarianceSampleWeight (epochCovariance_posSemidef C (frozenCoordinates x) x) s) :
    CubeRegular ε (epochRoundedPoint ε C x h s) := by
  have hm := epochMovedPoint_cube hC hC1 hx hh hsmall hs
  constructor
  · intro i
    exact ThresholdRounding.roundScalar_abs_le (hm i)
  · intro i
    exact ThresholdRounding.roundScalar_sign_or_interior ε _

theorem epochRoundedPoint_preserves_frozen (ε : ℝ) (C : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) (h : ℝ) {s : ι × Bool}
    (hs : 0 < covarianceSampleWeight (epochCovariance_posSemidef C (frozenCoordinates x) x) s)
    {i : ι} (hi : i ∈ frozenCoordinates x) :
    epochRoundedPoint ε C x h s i = x i := by
  have hm := epochSample_frozen_preserved C (frozenCoordinates x) x h hs hi
  change epochMovedPoint C x h s i = x i at hm
  change ThresholdRounding.roundScalar ε (epochMovedPoint C x h s i) = x i
  rw [hm]
  exact ThresholdRounding.roundScalar_of_isSign ε ((mem_frozenCoordinates x i).mp hi)

theorem epochRoundedPoint_frozen_subset (ε : ℝ) (C : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) (h : ℝ) {s : ι × Bool}
    (hs : 0 < covarianceSampleWeight (epochCovariance_posSemidef C (frozenCoordinates x) x) s) :
    frozenCoordinates x ⊆ frozenCoordinates (epochRoundedPoint ε C x h s) := by
  intro i hi
  rw [mem_frozenCoordinates, epochRoundedPoint_preserves_frozen ε C x h hs hi]
  exact (mem_frozenCoordinates x i).mp hi

theorem epochRoundedPoint_norm_gain {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    {ε : ℝ} {x : EuclideanSpace ℝ ι} (hx : CubeRegular ε x)
    {h : ℝ} (hh : 0 ≤ h) (hsmall : h * Real.sqrt (Fintype.card ι : ℝ) ≤ ε)
    {s : ι × Bool}
    (hs : 0 < covarianceSampleWeight (epochCovariance_posSemidef C (frozenCoordinates x) x) s) :
    ‖x‖ ^ 2 + h ^ 2 * realTrace (epochCovariance C (frozenCoordinates x) x) ≤
      ‖epochRoundedPoint ε C x h s‖ ^ 2 := by
  have hm := epochSample_norm_gain C (frozenCoordinates x) x h hs
  change ‖epochMovedPoint C x h s‖ ^ 2 = _ at hm
  rw [← hm]
  exact ThresholdRounding.roundVector_euclidean_norm_sq_ge
    (epochMovedPoint_cube hC hC1 hx hh hsmall hs)

/-- Every nonzero rounding charge is paid by a newly frozen coordinate. -/
theorem epochRoundedPoint_cost_le_new_frozen
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) {x : EuclideanSpace ℝ ι} (hx : CubeRegular ε x)
    {h : ℝ} (hh : 0 ≤ h) (hsmall : h * Real.sqrt (Fintype.card ι : ℝ) ≤ ε)
    {s : ι × Bool}
    (hs : 0 < covarianceSampleWeight (epochCovariance_posSemidef C (frozenCoordinates x) x) s) :
    (∑ i, |epochRoundedPoint ε C x h s i - epochMovedPoint C x h s i|) ≤
      ε * ((frozenCoordinates (epochRoundedPoint ε C x h s)).card -
        (frozenCoordinates x).card : ℕ) := by
  classical
  let y := epochRoundedPoint ε C x h s
  let z := epochMovedPoint C x h s
  let G := frozenCoordinates y \ frozenCoordinates x
  let cost := fun i => |y i - z i|
  have hsub : frozenCoordinates x ⊆ frozenCoordinates y :=
    epochRoundedPoint_frozen_subset ε C x h hs
  have hc (i : ι) : cost i ≤ ε :=
    ThresholdRounding.roundScalar_cost_le hε (epochMovedPoint_cube hC hC1 hx hh hsmall hs i)
  have hz (i : ι) (hi : i ∉ G) : cost i = 0 := by
    by_cases hf : i ∈ frozenCoordinates x
    · have hy : y i = x i := epochRoundedPoint_preserves_frozen ε C x h hs hf
      have hz' : z i = x i := epochSample_frozen_preserved C (frozenCoordinates x) x h hs hf
      simp only [cost, hy, hz', sub_self, abs_zero]
    · have hnf : i ∉ frozenCoordinates y := by
        intro hy
        exact hi (Finset.mem_sdiff.mpr ⟨hy, hf⟩)
      have he : y i = z i := by
        by_contra hne
        exact hnf ((mem_frozenCoordinates y i).mpr
          (ThresholdRounding.roundScalar_isSign_of_changed hne))
      simp only [cost, he, sub_self, abs_zero]
  have he : (∑ i ∈ G, cost i) = ∑ i, cost i :=
    Finset.sum_subset (Finset.subset_univ G) (fun i _ hi => hz i hi)
  change (∑ i, cost i) ≤ _
  rw [← he]
  calc
    _ ≤ ∑ _i ∈ G, ε := Finset.sum_le_sum (fun i _ => hc i)
    _ = ε * ((frozenCoordinates y).card - (frozenCoordinates x).card : ℕ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [show G.card = (frozenCoordinates y).card - (frozenCoordinates x).card from
        Finset.card_sdiff_of_subset hsub]
      ring

end MatrixSpencer
