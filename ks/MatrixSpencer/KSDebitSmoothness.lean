import MatrixSpencer.KSDebitLocalState
import MatrixSpencer.JointOwnerResponse

/-!
# Smoothness of the actual debit potential along live coefficient curves

This is joint smoothness of the genuine optimized owner potential composed
with the explicit affine center and quadratic coefficient covariance.  All
owners are positive at the starting state.  No optimizer, failed retirement
test, Hessian approximation, or numerical oracle is assumed.
-/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSDebitSmoothness

open KSSpinLocalState KSDebitLocalState

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

/-- The diagonal covariance is real linear in its owner coefficients. -/
def coefficientCovarianceCLM : (ι → ℝ) →L[ℝ]
    selfAdjoint (Matrix (ι × Fin 4) (ι × Fin 4) ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => ⟨KSSpinSource.coefficientCovariance c,
        Matrix.isHermitian_diagonal _⟩
      map_add' := by
        intro c d
        apply Subtype.ext
        ext i j
        simp [KSSpinSource.coefficientCovariance, Matrix.diagonal_apply, add_div]
      map_smul' := by
        intro r c
        apply Subtype.ext
        ext i j
        simp [KSSpinSource.coefficientCovariance, Matrix.diagonal_apply, smul_eq_mul]
        split_ifs <;> simp [mul_div_assoc] }

@[simp] theorem coefficientCovarianceCLM_coe (c : ι → ℝ) :
    (coefficientCovarianceCLM c : Matrix (ι × Fin 4) (ι × Fin 4) ℝ) =
      KSSpinSource.coefficientCovariance c := rfl

omit [DecidableEq ι] in
theorem contDiff_ownerCurve (x h : ι → ℝ) : ContDiff ℝ ∞ (ownerCurve x h) := by
  apply contDiff_pi.mpr
  intro i
  dsimp [ownerCurve]
  fun_prop

/-- The full actual curve potential is infinitely differentiable at every
state where the live coefficient owners are positive. -/
theorem contDiffAt_curvePotential [Nonempty n]
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) {θ : ℝ} (hθ : 0 < θ)
    (x h : ι → ℝ) (hx : ∀ i, |x i| < 1) :
    ContDiffAt ℝ ∞ (curvePotential M v θ x h) 0 := by
  let Hh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) := ⟨M, hM⟩
  let Kh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
    ⟨∑ i, h i • signedLift (atoms v i), by
      change (∑ i, h i • signedLift (atoms v i))ᴴ = ∑ i, h i • signedLift (atoms v i)
      simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial]
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun M => h i • M)
        (signedLift_isHermitian (KSRankOne.atom_isHermitian (v i))).eq)⟩
  let P := fun t : ℝ => (Hh + t • Kh, coefficientCovarianceCLM (ownerCurve x h t))
  have hP : ContDiff ℝ ∞ P := by
    apply ContDiff.prodMk
    · exact contDiff_const.add (contDiff_id.smul contDiff_const)
    · exact coefficientCovarianceCLM.contDiff.comp (contDiff_ownerCurve x h)
  have hC : ((P 0).2 : Matrix (ι × Fin 4) (ι × Fin 4) ℝ).PosDef := by
    change (KSSpinSource.coefficientCovariance (ownerCurve x h 0)).PosDef
    rw [ownerCurve_zero]
    exact KSSpinCompression.coefficientCovariance_posDef (owners_pos hx)
  have hj := contDiffAt_jointHermitianOwnerPotential
    (KSSpinSource.family (atoms v))
    (KSSpinSource.family_isHermitian (atoms v) (fun i => KSRankOne.atom_isHermitian (v i)))
    hθ (P 0).1 (P 0).2 hC
  convert hj.comp 0 hP.contDiffAt using 1

/-- The concrete walk center `signedLift H - doubled B` meets the center
hypothesis as soon as its physical signed sum and debit are Hermitian. -/
theorem contDiffAt_debitCurvePotential [Nonempty n]
    (H B : Matrix n n ℂ) (hH : H.IsHermitian) (hB : B.IsHermitian)
    (v : ι → n → ℂ) {θ : ℝ} (hθ : 0 < θ)
    (x h : ι → ℝ) (hx : ∀ i, |x i| < 1) :
    ContDiffAt ℝ ∞ (curvePotential (KSDebitCenter.center H B) v θ x h) 0 :=
  contDiffAt_curvePotential _ (KSDebitCenter.center_isHermitian hH hB) v hθ x h hx

end MatrixSpencer.KSDebitSmoothness
