import MatrixSpencer.KSFullManuscriptLiveCoordinates
import MatrixSpencer.KSDebitSmoothness
import MatrixSpencer.KSSpinLiveSource
import MatrixSpencer.KSNumericalHessian

/-!
# Ambient smoothness of the actual debit potential on a live face

The stored debit is constant in a neighborhood of the base point in the
entire unweighted live-coordinate space. Dead owners vanish identically
on that face. Restricting only the coefficient labels therefore identifies
the actual full-density potential with a jointly smooth owner potential
whose remaining coefficient covariance is positive definite at the base.
This also proves symmetry of the actual coordinate Hessian.
-/

open Matrix Set Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSFullManuscriptFaceSmoothness

open KSFullManuscriptLiveCoordinates KSPotentialModels KSLiveCurve
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

theorem contDiff_face_apply (x : Fin N → ℝ) (i : Fin N) :
    ContDiff ℝ ∞ (fun z => face x z i) := by
  exact contDiff_const.add ((PiLp.proj 2 (fun _ : Fin N => ℝ) i).contDiff.comp
    (linear x).contDiff)

/-- Smooth Hermitian center with the debit held at its actual base value. -/
def fixedCenter (v : Fin N → n → ℂ) (δ η : ℝ) (x : Fin N → ℝ)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) :
    EuclideanSpace ℝ (Fin (KSLiveEnumeration.count x)) → selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
  fun z => (∑ i, face x z i •
    (⟨signedLift (KSRankOne.atom (v i)),
      signedLift_isHermitian (KSRankOne.atom_isHermitian (v i))⟩ :
      selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))) -
    ⟨KSSpinSource.doubled (KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x),
      KSSpinSource.doubled_isHermitian (KSDebitBudget.debit_posSemidef _
        (fun i => KSRankOne.atom_posSemidef (v i)) hδ hη x).isHermitian⟩

theorem fixedCenter_coe (v : Fin N → n → ℂ) (δ η : ℝ) (x : Fin N → ℝ)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (z : EuclideanSpace ℝ (Fin (KSLiveEnumeration.count x))) :
    (fixedCenter v δ η x hδ hη z : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      KSDebitCenter.center (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) (face x z))
        (KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x) := by
  simp [fixedCenter, KSDebitCenter.center, KSPotentialModels.center, signedLift_sum_smul]

theorem contDiff_fixedCenter (v : Fin N → n → ℂ) (δ η : ℝ) (x : Fin N → ℝ)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) : ContDiff ℝ ∞ (fixedCenter v δ η x hδ hη) := by
  apply ContDiff.sub _ contDiff_const
  apply ContDiff.sum
  intro i _
  exact (contDiff_face_apply x i).smul contDiff_const

/-- Quadratic owners, indexed only by the original labels live at the base. -/
def faceOwners (x : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin (KSLiveEnumeration.count x))) :
    Live 1 x → ℝ := fun i => 64 * (1 - (face x z i) ^ 2)

theorem contDiff_faceOwners (x : Fin N → ℝ) : ContDiff ℝ ∞ (faceOwners x) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.mul (contDiff_const.sub ((contDiff_face_apply x i).pow 2))

theorem faceOwners_zero_pos (x : Fin N → ℝ) (i : Live 1 x) : 0 < faceOwners x 0 i := by
  simp only [faceOwners, face_zero]
  have hi := i.property
  have hi' := abs_lt.mp hi
  nlinarith [sq_nonneg (x i)]

/-- The actual state function is smooth in all unweighted live coordinates. -/
theorem contDiffAt_statePotential_face [Nonempty n] (v : Fin N → n → ℂ)
    {δ η θ : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hθ : 0 < θ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    ContDiffAt ℝ ∞ (fun z => KSDebitPreparation.statePotential v δ η θ (face x z)) 0 := by
  let A := KSSpinSource.family (fun i : Live 1 x => KSRankOne.atom (v i))
  let P := fun z => (fixedCenter v δ η x hδ hη z,
    KSDebitSmoothness.coefficientCovarianceCLM (faceOwners x z))
  have hP : ContDiff ℝ ∞ P :=
    (contDiff_fixedCenter v δ η x hδ hη).prodMk
      ((KSDebitSmoothness.coefficientCovarianceCLM (ι := Live 1 x)).contDiff.comp
        (contDiff_faceOwners x))
  have hC : ((P 0).2 : Matrix (Live 1 x × Fin 4) (Live 1 x × Fin 4) ℝ).PosDef :=
    KSSpinCompression.coefficientCovariance_posDef (faceOwners_zero_pos x)
  have hA : ∀ i, (A i).IsHermitian :=
    KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i))
  have hs := (contDiffAt_jointHermitianOwnerPotential A hA hθ (P 0).1 (P 0).2 hC).comp
    0 hP.contDiffAt
  apply hs.congr_of_eventuallyEq
  filter_upwards [eventually_same_frozen x] with z hz
  have hb := KSDebitBudget.debit_eq_of_same_frozen (fun i => KSRankOne.atom (v i)) δ η hz
  have hzero : ∀ i, ¬ |x i| < 1 → naturalOwners 64 (face x z) i = 0 := by
    intro i hi
    change 64 * (1 - (face x z i) ^ 2) = 0
    rw [face_dead x z i hi]
    exact naturalOwner_dead hx 64 i hi
  change KSDebitPreparation.statePotential v δ η θ (face x z) =
    ownerPotential (fixedCenter v δ η x hδ hη z) A
      (KSSpinSource.coefficientCovariance (faceOwners x z)) θ
  unfold KSDebitPreparation.statePotential KSDebitPotential.potential
  rw [hb, fixedCenter_coe]
  exact KSSpinLiveSource.potential_restrict v 1 x (naturalOwners 64 (face x z)) hzero _ θ

theorem statePotential_face_hessian_isSymm [Nonempty n] (v : Fin N → n → ℂ)
    {δ η θ : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hθ : 0 < θ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    (KSNumericalHessian.hessian
      (fun z => KSDebitPreparation.statePotential v δ η θ (face x z)) 0).IsSymm := by
  apply KSNumericalHessian.hessian_isSymm
  exact (contDiffAt_statePotential_face v hδ hη hθ hx).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))

end MatrixSpencer.KSFullManuscriptFaceSmoothness
