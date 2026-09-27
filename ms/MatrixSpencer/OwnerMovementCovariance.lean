import MatrixSpencer.CovarianceTraceLedger
import MatrixSpencer.OwnerResponseGeometry

/-!
# The covariance used by a concrete finite epoch

The constraints are the actual frozen coordinates and the radial inner
product. The resulting short loses at most one trace unit per constraint.
-/

open scoped BigOperators MatrixOrder
open Matrix
noncomputable section
namespace MatrixSpencer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def frozenRestriction (F : Finset ι) : EuclideanSpace ℝ ι →ₗ[ℝ] (F → ℝ) where
  toFun u := fun i => u i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def epochConstraint (F : Finset ι) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι →ₗ[ℝ] ((F → ℝ) × ℝ) :=
  (frozenRestriction F).prod (innerSL ℝ x).toLinearMap

def epochCovariance (C : Matrix ι ι ℝ) (F : Finset ι) (x : EuclideanSpace ℝ ι) :
    Matrix ι ι ℝ := ownerShort C (epochConstraint F x)

theorem epochCovariance_posSemidef (C : Matrix ι ι ℝ) (F : Finset ι)
    (x : EuclideanSpace ℝ ι) : (epochCovariance C F x).PosSemidef :=
  ownerShort_posSemidef C (epochConstraint F x)

theorem epochCovariance_le {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (F : Finset ι) (x : EuclideanSpace ℝ ι) : epochCovariance C F x ≤ C :=
  ownerShort_le hC (epochConstraint F x)

theorem epochCovariance_trace_lower {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (hC1 : C ≤ 1) (F : Finset ι) (x : EuclideanSpace ℝ ι) :
    realTrace C - (F.card : ℝ) - 1 ≤ realTrace (epochCovariance C F x) := by
  have hh := ownerShort_trace_loss_le_dim hC hC1 (epochConstraint F x)
  have hd : Module.finrank ℝ ((F → ℝ) × ℝ) = F.card + 1 := by simp
  rw [hd, Nat.cast_add, Nat.cast_one, realTrace_sub] at hh
  change realTrace C - realTrace (epochCovariance C F x) ≤ (F.card : ℝ) + 1 at hh
  linarith

theorem epochCovariance_range_constraints (C : Matrix ι ι ℝ) (F : Finset ι)
    (x u : EuclideanSpace ℝ ι)
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (epochCovariance C F x)).toLinearMap) :
    (∀ i ∈ F, u i = 0) ∧ inner ℝ x u = 0 := by
  have hh := ownerShort_range_le_ker C (epochConstraint F x) hu
  change (frozenRestriction F u, inner ℝ x u) = 0 at hh
  refine ⟨?_, congrArg Prod.snd hh⟩
  intro i hi
  exact congrFun (congrArg Prod.fst hh) ⟨i, hi⟩

/-- Every positive-probability sampled movement preserves frozen coordinates and is radial-tangent. -/
theorem epochSample_constraints (C : Matrix ι ι ℝ) (F : Finset ι)
    (x : EuclideanSpace ℝ ι) {s : ι × Bool}
    (hs : 0 < covarianceSampleWeight (epochCovariance_posSemidef C F x) s) :
    (∀ i ∈ F, covarianceSampleIncrement (epochCovariance_posSemidef C F x) s i = 0) ∧
      inner ℝ x (covarianceSampleIncrement (epochCovariance_posSemidef C F x) s) = 0 :=
  epochCovariance_range_constraints C F x _ (covarianceSample_mem_range _ hs)

theorem epochSample_norm_gain (C : Matrix ι ι ℝ) (F : Finset ι)
    (x : EuclideanSpace ℝ ι) (h : ℝ) {s : ι × Bool}
    (hs : 0 < covarianceSampleWeight (epochCovariance_posSemidef C F x) s) :
    ‖x + h • covarianceSampleIncrement (epochCovariance_posSemidef C F x) s‖ ^ 2 =
      ‖x‖ ^ 2 + h ^ 2 * realTrace (epochCovariance C F x) :=
  covarianceSample_norm_gain _ x h s (epochSample_constraints C F x hs).2

theorem epochSample_frozen_preserved (C : Matrix ι ι ℝ) (F : Finset ι)
    (x : EuclideanSpace ℝ ι) (h : ℝ) {s : ι × Bool}
    (hs : 0 < covarianceSampleWeight (epochCovariance_posSemidef C F x) s)
    {i : ι} (hi : i ∈ F) :
    (x + h • covarianceSampleIncrement (epochCovariance_posSemidef C F x) s) i = x i := by
  change x i + h * covarianceSampleIncrement (epochCovariance_posSemidef C F x) s i = x i
  rw [(epochSample_constraints C F x hs).1 i hi, mul_zero, add_zero]

/-- The trace ledger and stopping thresholds guarantee a nonzero finite sampler. -/
theorem epochCovariance_trace_positive {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (hC1 : C ≤ 1) (F : Finset ι) (x : EuclideanSpace ℝ ι) {dc : ℝ}
    (hell : 32 ≤ Fintype.card ι)
    (htrace : (Fintype.card ι : ℝ) / 8 - dc ≤ realTrace C)
    (hdc : dc ≤ (Fintype.card ι : ℝ) / 64)
    (hF : (F.card : ℝ) ≤ (Fintype.card ι : ℝ) / 64) :
    (Fintype.card ι : ℝ) / 16 ≤ realTrace (epochCovariance C F x) ∧
      0 < realTrace (epochCovariance C F x) := by
  apply movement_trace_positive_of_ledger (by exact_mod_cast hell) hdc hF
  have hh := epochCovariance_trace_lower hC hC1 F x
  linarith

end MatrixSpencer
