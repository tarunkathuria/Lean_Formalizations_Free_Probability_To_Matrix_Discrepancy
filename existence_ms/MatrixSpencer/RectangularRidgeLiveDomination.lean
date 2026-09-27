import MatrixSpencer.RectangularRidgeLiveOwnerBounds

/-! Frozen-coordinate annihilators imply domination by the actual live
coordinate projection, so the existing ledger invariant supplies the smaller
source budget without adding a new invariant field. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.RectangularRidgeLiveDomination
open RectangularRidgeLiveOwner
variable {N : ℕ}

theorem projection_right (C : Matrix (Fin N) (Fin N) ℝ) (F₀ : Finset (Fin N))
    (hF : ∀i∈F₀, C*ᵥPi.single i 1=0) : C*(owner F₀).physical=C := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [←Matrix.mulVec_mulVec]
  by_cases hi : i∈F₀
  · rw [owner_annihilates F₀ i hi,Matrix.mulVec_zero,hF i hi]
  · rw [RectangularRidgeLiveOwnerBounds.projection_live F₀ i hi]

/-- A PSD contraction that annihilates the original frozen coordinates is
bounded by the explicitly computed live coordinate projection. -/
theorem covariance_le_projection (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.PosSemidef)
    (hC1 : C≤1) (F₀ : Finset (Fin N)) (hF : ∀i∈F₀, C*ᵥPi.single i 1=0) :
    C≤(owner F₀).physical := by
  let P := (owner F₀).physical
  have hP : P.PosSemidef := covarianceLift_posSemidef (frame F₀) Matrix.PosSemidef.one
  have hPt : Pᵀ=P := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.isHermitian.eq
  have hCt : Cᵀ=C := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hC.isHermitian.eq
  have hr : C*P=C := projection_right C F₀ hF
  have hl : P*C=C := by
    have hh := congrArg Matrix.transpose hr
    simpa only [Matrix.transpose_mul,hPt,hCt] using hh
  have hh := covarianceLift_mono P hC1
  change P*C*Pᵀ≤P*1*Pᵀ at hh
  rw [hPt,hl,hr,Matrix.mul_one] at hh
  simpa only [P,RectangularRidgeLiveOwnerBounds.projection_idempotent] using hh

end MatrixSpencer.RectangularRidgeLiveDomination
