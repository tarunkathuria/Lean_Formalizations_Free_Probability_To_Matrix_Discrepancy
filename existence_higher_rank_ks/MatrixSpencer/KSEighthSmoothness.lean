import MatrixSpencer.KSEighthLocalState
import MatrixSpencer.JointOwnerResponse

/-!
# Smoothness of the actual retained-owner eighth-cube curve

The proof composes the joint owner-potential theorem with the actual affine
signed center and quadratic independent-block covariance. It assumes neither
nonzero atoms nor an optimizer oracle. Uniform quantitative derivative bounds
are established separately; this module only proves actual smoothness.
-/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSEighthSmoothness

open KSEighthLocalState KSEighthActualState

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

/-- The diagonal covariance is real linear in its owner coefficients. -/
def coefficientCovarianceCLM : (ι → ℝ) →L[ℝ]
    selfAdjoint (Matrix (ι × Bool) (ι × Bool) ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => ⟨KSIndependentSource.coefficientCovariance c,
        Matrix.isHermitian_diagonal _⟩
      map_add' := by
        intro c d
        apply Subtype.ext
        ext i j
        simp [KSIndependentSource.coefficientCovariance, Matrix.diagonal_apply]
      map_smul' := by
        intro r c
        apply Subtype.ext
        ext i j
        simp [KSIndependentSource.coefficientCovariance, Matrix.diagonal_apply, smul_eq_mul] }

@[simp] theorem coefficientCovarianceCLM_coe (c : ι → ℝ) :
    (coefficientCovarianceCLM c : Matrix (ι × Bool) (ι × Bool) ℝ) =
      KSIndependentSource.coefficientCovariance c := rfl

omit [DecidableEq ι] in
theorem contDiff_curveOwners (x h : ι → ℝ) : ContDiff ℝ ∞ (curveOwners x h) := by
  apply contDiff_pi.mpr
  intro i
  dsimp [curveOwners]
  fun_prop

/-- The full actual curve potential is infinitely differentiable at every
state where the live coefficient owners are positive. -/
theorem contDiffAt_curvePotential [Nonempty n]
    (Q : Matrix n n ℂ) (hQ : Q.IsHermitian)
    (v : ι → n → ℂ) {θ : ℝ} (hθ : 0 < θ)
    (x h : ι → ℝ) (hx : ∀ i, |x i| < 1) :
    ContDiffAt ℝ ∞ (curvePotential Q v θ x h) 0 := by
  let Hh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) := ⟨signedLift Q, signedLift_isHermitian hQ⟩
  let Kh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
    ⟨∑ i, h i • signedLift (KSRankOne.atom (v i)), by
      change (∑ i, h i • signedLift (KSRankOne.atom (v i)))ᴴ = ∑ i, h i • signedLift (KSRankOne.atom (v i))
      simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial]
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun M => h i • M)
        (signedLift_isHermitian (KSRankOne.atom_isHermitian (v i))).eq)⟩
  let P := fun t : ℝ => (Hh + t • Kh, coefficientCovarianceCLM (curveOwners x h t))
  have hP : ContDiff ℝ ∞ P := by
    apply ContDiff.prodMk
    · exact contDiff_const.add (contDiff_id.smul contDiff_const)
    · exact coefficientCovarianceCLM.contDiff.comp (contDiff_curveOwners x h)
  have hC : ((P 0).2 : Matrix (ι × Bool) (ι × Bool) ℝ).PosDef := by
    change (KSIndependentSource.coefficientCovariance (curveOwners x h 0)).PosDef
    change (Matrix.diagonal (fun j : ι × Bool => curveOwners x h 0 j.1)).PosDef
    apply Matrix.posDef_diagonal_iff.mpr
    intro j
    have hi := abs_lt.mp (hx j.1)
    dsimp [curveOwners]
    nlinarith [mul_pos (sub_pos.mpr hi.2) (by linarith : 0 < 1 + x j.1)]
  have hj := contDiffAt_jointHermitianOwnerPotential
    (family v) (family_isHermitian v)
    hθ (P 0).1 (P 0).2 hC
  convert hj.comp 0 hP.contDiffAt using 1

end MatrixSpencer.KSEighthSmoothness
