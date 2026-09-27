import MatrixSpencer.RectangularRidgeLiveOwner
import MatrixSpencer.RectangularRidgeCertificate

/-!
# Original-label source and initialization bounds at the live projection

All polynomial numerical conditioning retains the original ambient dimension.
The source trace and owner reinstall cost use only the actual retained original
unit atoms, through the explicitly computed coordinate inclusion.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeLiveOwnerBounds
open RectangularRidgeLiveOwner
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
local instance ridgeLiveOwnerBoundsCStar : CStarAlgebra (Matrix n n ℂ) := {}

/-- A coordinate inclusion retains the original atoms exactly. -/
theorem mixFamily_frame (A : Fin N → Matrix n n ℂ) (F₀ : Finset (Fin N)) :
    mixFamily A (frame F₀) = fun j => A (index F₀ j) := by
  funext j
  simp [mixFamily, frame, Matrix.submatrix_apply, Matrix.one_apply, ite_smul]

/-- The actual covariance source at the initial live projection. -/
theorem source_projection (A : Fin N → Matrix n n ℂ) (F₀ : Finset (Fin N)) (S : Matrix n n ℂ) :
    covarianceSource A (owner F₀).physical S =
      covarianceSource (fun j => A (index F₀ j)) 1 S := by
  change covarianceSource A (covarianceLift (frame F₀) 1) S = _
  rw [covarianceSource_rectangular_mixing, mixFamily_frame]

/-- The source bound is valid for every PSD density, with no normalization
assumption and no contraction assumption on support-mixed atoms. -/
theorem source_trace_le (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (F₀ : Finset (Fin N))
    (C : Matrix (Fin N) (Fin N) ℝ) (hC : C ≤ (owner F₀).physical)
    (S : Matrix n n ℂ) (hS : S.PosSemidef) :
    realTrace (covarianceSource A C S) ≤ (count F₀ : ℝ) * realTrace S := by
  have hm := covarianceSource_mono A hA hC hS
  have ht := realTrace_nonneg (Matrix.le_iff.mp hm)
  rw [realTrace_sub, source_projection] at ht
  have hb := realTrace_covarianceSource_le_card (fun j => A (index F₀ j))
    (fun j => hA _) (fun j => hAn _) Matrix.PosSemidef.one le_rfl hS
  simp only [Fintype.card_fin] at hb
  linarith

/-- Potential identification at the live projection keeps the same global
regularizer, depth and strength. -/
theorem potential_projection (H : Matrix n n ℂ) (A : Fin N → Matrix n n ℂ)
    (F₀ : Finset (Fin N)) (m : ℕ) (θ κ : ℝ) :
    RectangularRidgeCovarianceCalculus.ownerPotential m H A (owner F₀).physical θ κ =
      RectangularRidgeCovarianceCalculus.ownerPotential m H (fun j => A (index F₀ j)) 1 θ κ := by
  unfold RectangularRidgeCovarianceCalculus.ownerPotential regularizedOwnerPotential
  congr 2
  funext S
  unfold regularizedOwnerObjective
  rw [source_projection]

/-- The computed inclusion projection is idempotent. -/
theorem projection_idempotent (F₀ : Finset (Fin N)) :
    (owner F₀).physical * (owner F₀).physical = (owner F₀).physical := by
  simp only [MSManuscriptSupportedOwner.Owner.physical, owner, Matrix.mul_one]
  calc
    _ = frame F₀ * ((frame F₀)ᵀ * frame F₀) * (frame F₀)ᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [frame_isometry, Matrix.mul_one]

/-- The projection fixes every retained original coordinate. -/
theorem projection_live (F₀ : Finset (Fin N)) (i : Fin N) (hi : i ∉ F₀) :
    (owner F₀).physical *ᵥ Pi.single i 1 = Pi.single i 1 := by
  let j : Fin (count F₀) := (equiv F₀).symm ⟨i, hi⟩
  have he : index F₀ j = i := by simp [index, j]
  have ha : frame F₀ *ᵥ Pi.single j 1 = Pi.single i 1 := by
    rw [Matrix.mulVec_single]
    ext k
    simp [frame, Matrix.submatrix_apply, Matrix.one_apply, he, Pi.single_apply, eq_comm]
  have hm : (owner F₀).physical * frame F₀ = frame F₀ := by
    simp only [MSManuscriptSupportedOwner.Owner.physical, owner, Matrix.mul_one]
    rw [Matrix.mul_assoc, frame_isometry, Matrix.mul_one]
  rw [← ha, Matrix.mulVec_mulVec, hm]

variable [Nonempty n]

/-- Reinstalling the live coordinate covariance costs at most twice square
root of its live count, even though the center keeps all original labels. -/
theorem projection_excess_le (H : Matrix n n ℂ) (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hAn : ∀ i, ‖A i‖ ≤ 1)
    (F₀ : Finset (Fin N)) (m : ℕ) (θ κ : ℝ) :
    RectangularRidgeCovarianceCalculus.ownerPotential m H A (owner F₀).physical θ κ -
      RectangularRidgeCovarianceCalculus.ownerPotential m H A 0 θ κ ≤ 2 * Real.sqrt (count F₀ : ℝ) := by
  rw [potential_projection, RectangularRidgeOwnerBounds.owner_zero]
  have hb := RectangularRidgeOwnerBounds.owner_le_base_add m H (fun j => A (index F₀ j))
    (fun j => hA _) (fun j => hAn _) Matrix.PosSemidef.one le_rfl θ κ
  simp only [Fintype.card_fin] at hb
  linarith

/-- The actual anchored ridge certificate has the required live initialization bound. -/
theorem certificate_initial_le (H : Matrix n n ℂ) (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hAn : ∀ i, ‖A i‖ ≤ 1)
    (F₀ : Finset (Fin N)) (m : ℕ) (θ κ : ℝ) :
    RectangularRidgeCertificate.certificate H A m θ κ H (owner F₀).physical ≤
      2 * Real.sqrt (count F₀ : ℝ) := by
  rw [RectangularRidgeCertificate.certificate_eq_owner_difference]
  simp only [sub_self, Matrix.mul_zero, realTrace_zero, sub_zero]
  exact projection_excess_le H A hA hAn F₀ m θ κ

end MatrixSpencer.RectangularRidgeLiveOwnerBounds
